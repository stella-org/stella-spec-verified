(**
 * Weakening of the typing judgement (design §4.2, §4.3, §4.5).
 *
 * Each form is a corollary of a renaming lemma:
 *
 *   - an unused type variable, or a telescope of them, is the type
 *     renaming `↑m` (`Stella.Core.Typing.Rename.Ty`); it shifts the term,
 *     its type, its row and `Δ`;
 *   - an unused term variable, or a telescope of them, is the term
 *     renaming `↑m` (`Stella.Core.Typing.Rename.Tm`);
 *   - more hypotheses, more regions with the layouts of the old ones kept,
 *     and term variables added after the old ones are the identity term
 *     renaming. Adding a region to `regions` is how `Γ_R` grows when a
 *     region is opened (design §4.5);
 *   - more join points in `Δ` is the join renaming `↑m`
 *     (`Stella.Core.Typing.Join.typing_weaken_jp`, `typing_weaken_jps`),
 *     and join points appended behind `Δ` change nothing
 *     (`Stella.Core.Typing.Join.typing_jp_append`).
 *
 * `Γ_N` is a parameter of the judgement, not part of `Γ`, so extending it
 * is a lemma of its own (`typing_lctx_ext`): only `force` and `fill` read
 * it, at locations it already has, and new locations are allocated at its
 * end, so `ln @ ln'` agrees with `ln` on them.
 *
 * A term typed in a context with no term variables, a closed run-time
 * value in particular, stays typed under every extension of the
 * hypotheses and of the regions of its context, under any term variables
 * added, and under every extension of `Γ_N` (`typing_closed_ext`).
 *)
module Stella.Core.Typing.Weaken
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Entail
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Ty
open Stella.Core.Typing.Rename.Tm
module L = FStar.List.Tot

(** * Type variables *)

(** Composition of type renamings between contexts. *)
val ty_ren_ok_comp (xi zeta: ren) (g1 g2 g3: ctx)
  : Lemma (requires ty_ren_ok xi g1 g2 /\ ty_ren_ok zeta g2 g3)
          (ensures ty_ren_ok (fun i -> zeta (xi i)) g1 g3)

(** Entering `m` unused type binders is the renaming `↑m`. *)
val ty_ren_ok_shifts (g: ctx) (ks: list kind)
  : Lemma (ty_ren_ok (shift (L.length ks)) g (push_tvars g ks))

val typing_weaken_tvar (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ)
  (h: typing sg ln g d e t r) (k: kind)
  : Pure (typing sg ln (push_tvar g k) (ren_jctx (shift 1) d) (ren_ty_exp (shift 1) e)
            (ren_ty (shift 1) t) (ren_ty (shift 1) r))
         (requires sig_ok sg)
         (ensures fun _ -> True)

val typing_weaken_tvars (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (ks: list kind)
  : Pure (typing sg ln (push_tvars g ks) (ren_jctx (shift (L.length ks)) d)
            (ren_ty_exp (shift (L.length ks)) e) (ren_ty (shift (L.length ks)) t)
            (ren_ty (shift (L.length ks)) r))
         (requires sig_ok sg)
         (ensures fun _ -> True)

(** * Term variables *)

(** Composition of term renamings between contexts. *)
val tm_ren_ok_comp (xi zeta: ren) (g1 g2 g3: ctx)
  : Lemma (requires tm_ren_ok xi g1 g2 /\ tm_ren_ok zeta g2 g3)
          (ensures tm_ren_ok (fun i -> zeta (xi i)) g1 g3)

(** Binding `m` unused term variables is the renaming `↑m`. *)
val tm_ren_ok_shifts (g: ctx) (ts: list typ)
  : Lemma (tm_ren_ok (shift (L.length ts)) g (push_vars g ts))

val typing_weaken_var (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (t': typ)
  : typing sg ln (push_var g t') d (ren_tm (shift 1) e) t r

val typing_weaken_vars (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ)
  (h: typing sg ln g d e t r) (ts: list typ)
  : typing sg ln (push_vars g ts) d (ren_tm (shift (L.length ts)) e) t r

(** * Extending the context in place *)

(** `g'` has the hypotheses, the regions with their layouts, and the term
    variables of `g`, and possibly more of each; the term variables of `g`
    stand first. *)
let ctx_weaker (g g': ctx) : prop =
  ctx_ext g g' /\ layouts_ext g g' /\
  (forall (i: nat). i < L.length g.vars ==> L.nth g'.vars i == L.nth g.vars i)

val typing_weaken_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (g': ctx)
  : Pure (typing sg ln g' d e t r) (requires ctx_weaker g g') (ensures fun _ -> True)

(** Assumptions, and hypotheses in general. *)
val typing_weaken_assumps (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (cs: list constr)
  : typing sg ln (add_assumps g cs) d e t r

(** A fresh region with any layout, added to `regions` (`Γ_R`). *)
val typing_weaken_region (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (a: atom) (l: layout)
  : Pure (typing sg ln ({ g with regions = (a, l) :: g.regions }) d e t r)
         (requires ~(L.mem a (rdom g)))
         (ensures fun _ -> True)

val exps_typing_weaken_region (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (a: atom) (l: layout)
  : Pure (exps_typing sg ln ({ g with regions = (a, l) :: g.regions }) d r es ts)
         (requires ~(L.mem a (rdom g)))
         (ensures fun _ -> True)

val binds_typing_weaken_region (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (a: atom) (l: layout)
  : Pure (binds_typing sg ln ({ g with regions = (a, l) :: g.regions }) bs)
         (requires ~(L.mem a (rdom g)))
         (ensures fun _ -> True)

val cells_typing_weaken_region (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp))
  (#lay: layout) (h: cells_typing sg ln g cells lay) (a: atom) (l: layout)
  : Pure (cells_typing sg ln ({ g with regions = (a, l) :: g.regions }) cells lay)
         (requires ~(L.mem a (rdom g)))
         (ensures fun _ -> True)

val dt_typing_weaken_region (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (a: atom) (l: layout)
  : Pure (dt_typing sg ln ({ g with regions = (a, l) :: g.regions }) d om dt t r)
         (requires ~(L.mem a (rdom g)))
         (ensures fun _ -> True)

(** `ctx_weaker` is reflexive, and holds again under a term binder, a
    telescope of them, and a region entered on both sides. *)
val ctx_weaker_refl (g: ctx) : Lemma (ctx_weaker g g)

val ctx_weaker_push_var (g g': ctx) (t: typ)
  : Lemma (requires ctx_weaker g g') (ensures ctx_weaker (push_var g t) (push_var g' t))

val ctx_weaker_push_vars (g g': ctx) (ts: list typ)
  : Lemma (requires ctx_weaker g g') (ensures ctx_weaker (push_vars g ts) (push_vars g' ts))

val ctx_weaker_enter_region (g g': ctx) (a: atom) (l: layout)
  : Lemma (requires ctx_weaker g g')
          (ensures ctx_weaker (enter_region g a l) (enter_region g' a l) /\
                   (~(L.mem a (rdom g')) ==> ~(L.mem a (rdom g))))

(** The side conditions the rules check in `g` hold in `g'`: kinding,
    keys, entailment, the closed kinding in the regions, and the layout of
    every region. *)
val ctx_weaker_facts (sg: sig) (g g': ctx)
  : Lemma (requires ctx_weaker g g')
          (ensures (forall (t: typ) (k: kind). {:pattern check sg g' t k}
                      check sg g t k ==> check sg g' t k) /\
                   (forall (ts: list typ) (ks: list kind). {:pattern check_tys sg g' ts ks}
                      check_tys sg g ts ks ==> check_tys sg g' ts ks) /\
                   (forall (ts: list typ). {:pattern tys_ok sg g' ts}
                      tys_ok sg g ts ==> tys_ok sg g' ts) /\
                   (forall (k: key) (e: elt_kind). {:pattern key_ok sg g' k e}
                      key_ok sg g k e ==> key_ok sg g' k e) /\
                   (forall (c: constr). {:pattern entails (hyps g') c}
                      entails (hyps g) c ==> entails (hyps g') c) /\
                   (forall (t: typ) (k: kind). {:pattern check sg (closed_ctx g'.regions) t k}
                      check sg (closed_ctx g.regions) t k ==>
                      check sg (closed_ctx g'.regions) t k) /\
                   (forall (a: atom). {:pattern L.assoc a g'.regions}
                      Some? (L.assoc a g.regions) ==> L.assoc a g'.regions == L.assoc a g.regions))

(** The other judgements, in place. *)
val exps_typing_weaken_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (g': ctx)
  : Pure (exps_typing sg ln g' d r es ts) (requires ctx_weaker g g') (ensures fun _ -> True)

val chain_typing_weaken_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (g': ctx)
  : Pure (chain_typing sg ln g' d r e) (requires ctx_weaker g g') (ensures fun _ -> True)

val cells_typing_weaken_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp))
  (#lay: layout) (h: cells_typing sg ln g cells lay) (g': ctx)
  : Pure (cells_typing sg ln g' cells lay) (requires ctx_weaker g g') (ensures fun _ -> True)

val match_typing_weaken_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#th: list exp) (#om: octx) (h: match_typing sg ln g d r th om) (g': ctx)
  : Pure (match_typing sg ln g' d r th om) (requires ctx_weaker g g') (ensures fun _ -> True)

val dt_typing_weaken_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (g': ctx)
  : Pure (dt_typing sg ln g' d om dt t r) (requires ctx_weaker g g') (ensures fun _ -> True)

val clauses_typing_weaken_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info)
  (#ts: list typ) (#r #b: typ) (#cs: list clause) (h: clauses_typing sg ln g ei ts r b cs)
  (g': ctx)
  : Pure (clauses_typing sg ln g' ei ts r b cs) (requires ctx_weaker g g')
         (ensures fun _ -> True)

(** * The location context `Γ_N` *)

(** `ln'` has the locations of `ln` with their types. *)
let lctx_incl (ln ln': lctx) : prop =
  forall (nu: nat). Some? (L.nth ln nu) ==> L.nth ln' nu == L.nth ln nu

val lctx_incl_append (ln ln': lctx) : Lemma (lctx_incl ln (L.append ln ln'))

val typing_lctx_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (ln': lctx)
  : Pure (typing sg ln' g d e t r) (requires lctx_incl ln ln') (ensures fun _ -> True)

val exps_typing_lctx_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (ln': lctx)
  : Pure (exps_typing sg ln' g d r es ts) (requires lctx_incl ln ln') (ensures fun _ -> True)

val binds_typing_lctx_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (ln': lctx)
  : Pure (binds_typing sg ln' g bs) (requires lctx_incl ln ln') (ensures fun _ -> True)

val cells_typing_lctx_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp))
  (#lay: layout) (h: cells_typing sg ln g cells lay) (ln': lctx)
  : Pure (cells_typing sg ln' g cells lay) (requires lctx_incl ln ln') (ensures fun _ -> True)

val dt_typing_lctx_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (ln': lctx)
  : Pure (dt_typing sg ln' g d om dt t r) (requires lctx_incl ln ln') (ensures fun _ -> True)

(** * Closed terms *)

(** A term typed with no term variable in scope, under every extension of
    the hypotheses and regions of its context and of `Γ_N`. *)
val typing_closed_ext (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (ln': lctx) (g': ctx)
  : Pure (typing sg (L.append ln ln') g' d e t r)
         (requires g.vars == [] /\ ctx_ext g g' /\ layouts_ext g g')
         (ensures fun _ -> True)
