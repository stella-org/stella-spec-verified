(**
 * Typing is preserved by a substitution of term variables (design §1.1,
 * §3.1, §4.2).
 *
 * A term substitution `σ` goes from `Γ` to `Γ'` (`tm_sub_ok`) when `Γ'`
 * extends `Γ` in everything but its term variables
 * (`Stella.Core.Kinding.Subst.ctx_ext`, `layouts_ext`), and the substitute
 * `σ i` of each term variable `i : τ` of `Γ` is one of the following
 * (`sub_entry`):
 *
 *   - a term variable of `Γ'` of type `τ`;
 *   - a run-time value (`Stella.Core.Value.is_value`) of type `τ` in `Γ'`,
 *     typed at `()` under no join point;
 *   - `force ν`, a location of `Γ_N` of type `τ`, `τ` closed: kinded in
 *     `closed_ctx` over the regions of `Γ'`, as `T_Force` asks.
 *
 * Reduction substitutes values (spec 06 §Ordinary reduction, §Join points,
 * §Operations and handlers), and the allocation of a `letrec` substitutes
 * `force ν̄` for its members (spec 06 §Recursive bindings); the variables
 * are what lifting under a term binder adds. All three stand anywhere:
 * each is typed at every well-kinded row and under every `Δ` (`T_Var`,
 * `T_Force`, `Stella.Core.Typing.Values`), so the substituted term keeps
 * the type, the row and the `Δ` of the original. Another non-value would
 * not: it may perform an effect, or jump.
 *
 * The substitute at every index, not only at the variables of `Γ`, is
 * locally closed for regions and has no free join point (`tm_sub_props`;
 * design §3.1, §4.3): opening a region and crossing a join binder act on
 * the whole substitution. A value typed in a well-formed `Γ'` has both by
 * its scope (`Stella.Core.Typing.Scope`), and a variable and a `force`
 * have both.
 *
 * The condition carries the derivations of the values, so it is data. It
 * is re-established under every binder of the rules:
 *
 *   - a term binder or a telescope (`upn_esub`): the new variables are
 *     themselves, the old substitutes are shifted past them;
 *   - a type binder or a telescope (`tyup_esub`): the substitutes are
 *     shifted in their types, the types of both contexts likewise; the
 *     closed type of a `force` is fixed (`check_closed_ren`);
 *   - a join binder (`jup_esub`): a substitute has no free join point, so
 *     the shift fixes it;
 *   - an assumption, and a region entered with an atom outside `Γ'`; the
 *     closed type of a `force` stays closed as the regions grow.
 *
 * The excluded set of the cofinite premise of `region` grows: the atoms of
 * a term are among those of its image (`Stella.Core.Typing.Subst.Tm.Facts`),
 * and `Γ'` has the regions of `Γ`. Opening a region commutes with the
 * substitution of locally closed terms
 * (`Stella.Core.Region.Lemmas.open_region_sub_tm`). The group of a
 * `letrec` stays initialization-safe
 * (`Stella.Core.Typing.Subst.Tm.Init.init_safe_sub_tm`).
 *
 * The theorems assume `sig_ok sg` and `wf_ctx sg g'`, which retyping a
 * value needs, and which every binder of the rules keeps. The judgements
 * on decision trees also assume that the types of `Ω` are kinded in `Γ'`
 * (`Stella.Core.Typing.Wf.octx_ok`): a `bind` pushes the type of its
 * occurrence. The branches of a `switchCtor` assume the kinding of the
 * data type the switch reads, which their refinements of `Ω` need, and
 * the clauses of a handler that their effect is one of `Σ`.
 *)
module Stella.Core.Typing.Subst.Tm
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Wf
open Stella.Core.Typing.Rename.Tm
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * The context morphism *)

(** The substitute `e` of a term variable of type `t`, in `g'`. *)
noeq type sub_entry (sg: sig) (ln: lctx) (g': ctx) (e: exp) (t: typ) : Type =
  | SE_Var :
      j:nat ->
      squash (e == EVar j /\ L.nth g'.vars j == Some t) ->
      sub_entry sg ln g' e t
  | SE_Val :
      squash (V.is_value sg e) ->
      typing sg ln g' [] e t TRowEmpty ->
      sub_entry sg ln g' e t
  | SE_Force :
      nu:atom ->
      squash (e == EForce nu /\ L.nth ln nu == Some t /\ check sg (closed_ctx g'.regions) t KType) ->
      sub_entry sg ln g' e t

(** The conditions on the contexts and on the syntax of every
    substitute. *)
let tm_sub_props (sigma: esub) (g g': ctx) : prop =
  ctx_ext g g' /\ layouts_ext g g' /\
  (forall (i: nat). V.jp_scoped 0 (sigma i) /\ lc_exp (sigma i))

noeq type tm_sub_ok (sg: sig) (ln: lctx) (sigma: esub) (g g': ctx) : Type =
  | TmSubOk :
      squash (tm_sub_props sigma g g') ->
      (i: nat -> t: typ -> squash (L.nth g.vars i == Some t) -> sub_entry sg ln g' (sigma i) t) ->
      tm_sub_ok sg ln sigma g g'

val tm_sub_ok_props (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Lemma (tm_sub_props sigma g g')

(** A substitution pointwise equal to one from `g` to `g'`. *)
val tm_sub_ok_ext (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g') (sigma': esub)
  : Pure (tm_sub_ok sg ln sigma' g g') (requires forall (i: nat). sigma' i == sigma i)
         (ensures fun _ -> True)

val tm_sub_ok_up (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g') (t: typ)
  : tm_sub_ok sg ln (up_esub sigma) (push_var g t) (push_var g' t)

(** The members of a `letrec`, the parameters of a join point. *)
val tm_sub_ok_upn (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g') (ts: list typ)
  : tm_sub_ok sg ln (upn_esub (L.length ts) sigma) (push_vars g ts) (push_vars g' ts)

val tm_sub_ok_push_tvar (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g') (k: kind)
  : Pure (tm_sub_ok sg ln (tyup_esub 1 sigma) (push_tvar g k) (push_tvar g' k))
         (requires sig_ok sg) (ensures fun _ -> True)

(** The type binders of a clause. *)
val tm_sub_ok_push_tvars (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g') (ks: list kind)
  : Pure (tm_sub_ok sg ln (tyup_esub (L.length ks) sigma) (push_tvars g ks) (push_tvars g' ks))
         (requires sig_ok sg) (ensures fun _ -> True)

(** The join binder of a `letjoin`. *)
val tm_sub_ok_jup (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : tm_sub_ok sg ln (jup_esub sigma) g g'

val tm_sub_ok_assump (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g') (c: constr)
  : tm_sub_ok sg ln sigma (add_assump g c) (add_assump g' c)

val tm_sub_ok_enter_region (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g') (a: atom) (l: layout)
  : Pure (tm_sub_ok sg ln sigma (enter_region g a l) (enter_region g' a l))
         (requires ~(L.mem a (rdom g')))
         (ensures fun _ -> True)

(** The excluded set of the cofinite premise grows. *)
val tm_sub_ok_fresh (#sg: sig) (#ln: lctx) (#sigma: esub) (#g #g': ctx)
  (hs: tm_sub_ok sg ln sigma g g') (a: atom) (body: exp)
  : Lemma (requires ~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp (sub_tm sigma body))))
          (ensures ~(L.mem a (rdom g)) /\ ~(L.mem a (frn_exp body)))

(** * The judgements *)

val occ_typing_sub_tm (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t) (g': ctx)
  : Pure (occ_typing sg g' om o t) (requires ctx_ext g g') (ensures fun _ -> True)

val typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (#sigma: esub) (#g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (typing sg ln g' d (sub_tm sigma e) t r)
         (requires sig_ok sg /\ wf_ctx sg g')
         (ensures fun _ -> True)

val exps_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d r es ts) (#sigma: esub) (#g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (exps_typing sg ln g' d r (sub_tm_exps sigma es) ts)
         (requires sig_ok sg /\ wf_ctx sg g')
         (ensures fun _ -> True)

val chain_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (#sigma: esub) (#g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (chain_typing sg ln g' d r (sub_tm sigma e))
         (requires sig_ok sg /\ wf_ctx sg g')
         (ensures fun _ -> True)

val binds_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (#sigma: esub) (#g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (binds_typing sg ln g' (sub_tm_binds sigma bs))
         (requires sig_ok sg /\ wf_ctx sg g')
         (ensures fun _ -> True)

val cells_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay) (#sigma: esub) (#g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (cells_typing sg ln g' (sub_tm_cells sigma cells) lay)
         (requires sig_ok sg /\ wf_ctx sg g')
         (ensures fun _ -> True)

val match_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx)
  (h: match_typing sg ln g d r th om) (#sigma: esub) (#g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (match_typing sg ln g' d r (sub_tm_exps sigma th) om)
         (requires sig_ok sg /\ wf_ctx sg g')
         (ensures fun _ -> True)

val dt_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d om dt t r) (#sigma: esub) (#g': ctx) (hs: tm_sub_ok sg ln sigma g g')
  : Pure (dt_typing sg ln g' d om (sub_tm_dt sigma dt) t r)
         (requires sig_ok sg /\ wf_ctx sg g' /\ octx_ok sg g' om)
         (ensures fun _ -> True)

val ctor_brs_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ)
  (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (#sigma: esub) (#g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (ctor_brs_typing sg ln g' d om o ks ss cs (sub_tm_brs sigma bs) t r)
         (requires sig_ok sg /\ wf_ctx sg g' /\ octx_ok sg g' om /\
                   (exists (tq: qname). check sg g' (tapps (TCon tq ks) ss) KType /\
                      has_class sg tq (TcData cs)))
         (ensures fun _ -> True)

val lit_brs_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (#sigma: esub) (#g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (lit_brs_typing sg ln g' d om lt (sub_tm_brs sigma bs) t r)
         (requires sig_ok sg /\ wf_ctx sg g' /\ octx_ok sg g' om)
         (ensures fun _ -> True)

val key_brs_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (#sigma: esub) (#g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (key_brs_typing sg ln g' d om o kts (sub_tm_brs sigma bs) t r)
         (requires sig_ok sg /\ wf_ctx sg g' /\ octx_ok sg g' om)
         (ensures fun _ -> True)

val clauses_typing_sub_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause)
  (h: clauses_typing sg ln g ei ts r b cs) (#sigma: esub) (#g': ctx)
  (hs: tm_sub_ok sg ln sigma g g')
  : Pure (clauses_typing sg ln g' ei ts r b (sub_tm_cls sigma cs))
         (requires sig_ok sg /\ wf_ctx sg g' /\ (exists (q: qname). sg.effects q == Some ei))
         (ensures fun _ -> True)
