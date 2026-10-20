(**
 * Typing is preserved by a renaming of term variables (design §1.1, §4.2).
 *
 * A term renaming `ξ` goes from `Γ` to `Γ'` (`tm_ren_ok`) when `Γ'`
 * extends `Γ` in everything but its term variables
 * (`Stella.Core.Kinding.Subst.ctx_ext`: the same kind and type
 * variables, hypotheses entailing those of `Γ`, more regions), keeps the
 * layout of every region of `Γ` (`layouts_ext`), and gives the term
 * variable `ξ i` the type of the term variable `i` of `Γ`. Types mention no
 * term variable, so a term renaming changes no type: the judgement keeps
 * its type, its row, `Δ` and `Ω`.
 *
 * The condition is re-established under every binder of the rules: a term
 * binder or a telescope of them with `ξ` lifted past it, a type binder
 * (whose shift acts on the types of both contexts alike), an assumption, a
 * region entered. The excluded set of the cofinite premise of `region`
 * grows, since a term renaming keeps the atoms of a term.
 *
 * The only hypothesis of the theorems is `tm_ren_ok`. Nothing in the rules
 * reads `Σ` differently in `Γ'`, and the closed types of `force`, `fill`
 * and `region⟨a⟩` are kinded in `closed_ctx g.regions`, which grows with
 * the regions. The group of a `letrec` stays initialization-safe because
 * the renaming under it is lifted past its members
 * (`Stella.Core.Init.Rename.init_safe_ren_tm`).
 *)
module Stella.Core.Typing.Rename.Tm
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot

(** * The context morphism *)

(** Every region of `g` is a region of `g'` with the same layout. *)
let layouts_ext (g g': ctx) : prop =
  forall (a: atom). {:pattern L.assoc a g.regions}
    match L.assoc a g.regions with
    | Some l -> L.assoc a g'.regions == Some l
    | None -> True

let tm_ren_ok (xi: ren) (g g': ctx) : prop =
  ctx_ext g g' /\ layouts_ext g g' /\
  (forall (i: nat). {:pattern L.nth g.vars i}
     i < L.length g.vars ==> L.nth g'.vars (xi i) == L.nth g.vars i)

val tm_ren_ok_ext (xi xi': ren) (g g': ctx)
  : Lemma (requires tm_ren_ok xi g g' /\ (forall (i: nat). xi' i == xi i))
          (ensures tm_ren_ok xi' g g')

val tm_ren_ok_up (xi: ren) (g g': ctx) (t: typ)
  : Lemma (requires tm_ren_ok xi g g')
          (ensures tm_ren_ok (up_ren xi) (push_var g t) (push_var g' t))

(** The members of a `letrec` and the parameters of a join point. *)
val tm_ren_ok_upn (xi: ren) (g g': ctx) (ts: list typ)
  : Lemma (requires tm_ren_ok xi g g')
          (ensures tm_ren_ok (upn_ren (L.length ts) xi) (push_vars g ts) (push_vars g' ts))

val tm_ren_ok_push_tvar (xi: ren) (g g': ctx) (k: kind)
  : Lemma (requires tm_ren_ok xi g g') (ensures tm_ren_ok xi (push_tvar g k) (push_tvar g' k))

val tm_ren_ok_push_tvars (xi: ren) (g g': ctx) (ks: list kind)
  : Lemma (requires tm_ren_ok xi g g') (ensures tm_ren_ok xi (push_tvars g ks) (push_tvars g' ks))

val tm_ren_ok_assumps (xi: ren) (g g': ctx) (cs: list constr)
  : Lemma (requires tm_ren_ok xi g g') (ensures tm_ren_ok xi (add_assumps g cs) (add_assumps g' cs))

val tm_ren_ok_assump (xi: ren) (g g': ctx) (c: constr)
  : Lemma (requires tm_ren_ok xi g g') (ensures tm_ren_ok xi (add_assump g c) (add_assump g' c))

val tm_ren_ok_enter_region (xi: ren) (g g': ctx) (a: atom) (l: layout)
  : Lemma (requires tm_ren_ok xi g g')
          (ensures tm_ren_ok xi (enter_region g a l) (enter_region g' a l))

(** The excluded set of the cofinite premise grows. *)
val tm_ren_ok_fresh (xi: ren) (g g': ctx) (a: atom) (body: exp)
  : Lemma (requires tm_ren_ok xi g g' /\ ~(L.mem a (rdom g')) /\
                    ~(L.mem a (frn_exp (ren_tm xi body))))
          (ensures ~(L.mem a (rdom g)) /\ ~(L.mem a (frn_exp body)))

(** Binding an unused term variable is the renaming `↑1`. *)
val tm_ren_ok_shift (g: ctx) (t: typ) : Lemma (tm_ren_ok (shift 1) g (push_var g t))

(** An extension of `g` whose term variables start with those of `g` is
    reached by the identity. *)
val tm_ren_ok_id (g g': ctx)
  : Lemma (requires ctx_ext g g' /\ layouts_ext g g' /\
                    (forall (i: nat). i < L.length g.vars ==> L.nth g'.vars i == L.nth g.vars i))
          (ensures tm_ren_ok id_ren g g')

(** * The judgements *)

val occ_typing_ren_tm (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t) (xi: ren) (g': ctx)
  : Pure (occ_typing sg g' om o t) (requires tm_ren_ok xi g g') (ensures fun _ -> True)

val typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (xi: ren) (g': ctx)
  : Pure (typing sg ln g' d (ren_tm xi e) t r) (requires tm_ren_ok xi g g')
    (ensures fun _ -> True)

val exps_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d r es ts) (xi: ren) (g': ctx)
  : Pure (exps_typing sg ln g' d r (ren_tm_exps xi es) ts)
         (requires tm_ren_ok xi g g')
         (ensures fun _ -> True)

val chain_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (xi: ren) (g': ctx)
  : Pure (chain_typing sg ln g' d r (ren_tm xi e)) (requires tm_ren_ok xi g g')
    (ensures fun _ -> True)

val binds_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (xi: ren) (g': ctx)
  : Pure (binds_typing sg ln g' (ren_tm_binds xi bs)) (requires tm_ren_ok xi g g')
    (ensures fun _ -> True)

val cells_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay) (xi: ren) (g': ctx)
  : Pure (cells_typing sg ln g' (ren_tm_cells xi cells) lay)
         (requires tm_ren_ok xi g g')
         (ensures fun _ -> True)

val match_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx)
  (h: match_typing sg ln g d r th om) (xi: ren) (g': ctx)
  : Pure (match_typing sg ln g' d r (ren_tm_exps xi th) om)
         (requires tm_ren_ok xi g g')
         (ensures fun _ -> True)

val dt_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d om dt t r) (xi: ren) (g': ctx)
  : Pure (dt_typing sg ln g' d om (ren_tm_dt xi dt) t r)
         (requires tm_ren_ok xi g g')
         (ensures fun _ -> True)

val ctor_brs_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ)
  (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (xi: ren) (g': ctx)
  : Pure (ctor_brs_typing sg ln g' d om o ks ss cs (ren_tm_brs xi bs) t r)
         (requires tm_ren_ok xi g g')
         (ensures fun _ -> True)

val lit_brs_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (xi: ren) (g': ctx)
  : Pure (lit_brs_typing sg ln g' d om lt (ren_tm_brs xi bs) t r)
         (requires tm_ren_ok xi g g')
         (ensures fun _ -> True)

val key_brs_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (xi: ren) (g': ctx)
  : Pure (key_brs_typing sg ln g' d om o kts (ren_tm_brs xi bs) t r)
         (requires tm_ren_ok xi g g')
         (ensures fun _ -> True)

val clauses_typing_ren_tm (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause)
  (h: clauses_typing sg ln g ei ts r b cs) (xi: ren) (g': ctx)
  : Pure (clauses_typing sg ln g' ei ts r b (ren_tm_cls xi cs))
         (requires tm_ren_ok xi g g')
         (ensures fun _ -> True)
