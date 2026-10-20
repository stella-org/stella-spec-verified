(**
 * Typing is preserved by a renaming of type variables (design §1.1, §2.3,
 * §4.2).
 *
 * A type renaming `ξ` goes from `Γ` to `Γ'` (`ty_ren_ok`) when it is a
 * kinding renaming (`Stella.Core.Kinding.Subst.ren_ok`: kinds of type
 * variables, hypotheses entailed, region domain included) that also maps
 * the types `Γ` stores: the term variable `i` of `Γ'` has the renamed type
 * of the term variable `i` of `Γ`, and the region `a` of `Γ'` has the
 * renamed layout of the region `a` of `Γ`. The condition is re-established
 * under every binder of the rules: a type binder with `ξ` lifted, a
 * telescope of them with `ξ` lifted past it, an assumption with its image
 * assumed, a term binder with its renamed type, and a region entered with
 * its renamed layout. The facts the region adds are mapped to facts of the
 * renamed context, because `ξ` keeps the kind `Row Effect` of each type
 * variable. No freshness is needed there.
 *
 * Every judgement is preserved, with every type of the derivation renamed:
 * the term (`ren_ty_exp`), its type and its row, `Δ` (`ren_jctx`) and `Ω`
 * (`ren_octx`). The theorems assume `sig_ok`: the declared types of `Σ`
 * that the rules instantiate (globals, constructor fields, operation
 * signatures, the remainder a chain's cursor reaches) are closed, so a
 * renaming commutes with their instantiation. The context needs no
 * well-formedness. The cofinite premise of `region` reads the atoms of the
 * term, which a type renaming keeps, so its excluded set only grows: an
 * atom outside the regions of `Γ'` and the atoms of the renamed body is
 * outside those of `Γ` and of the body (`ty_ren_ok_fresh`). The closed
 * types of `force`, `fill` and `region⟨a⟩` carry their own kinding premise
 * in `closed_ctx g.regions`, which every renaming fixes.
 *)
module Stella.Core.Typing.Rename.Ty
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
module L = FStar.List.Tot

(** * Renaming the contexts of the judgement *)

(** `Ω` with its types renamed. *)
let rec ren_octx (xi: ren) (om: octx) : Tot octx (decreases om) =
  match om with
  | [] -> []
  | (o, t) :: om -> (o, ren_ty xi t) :: ren_octx xi om

(** A join point's signature renamed. *)
let ren_jt (xi: ren) (jt: list typ & typ & typ) : list typ & typ & typ =
  match jt with
  | (ts, t, r) -> (ren_tys xi ts, ren_ty xi t, ren_ty xi r)

(** `Δ` with its types renamed. *)
let rec ren_jctx (xi: ren) (d: jctx) : Tot jctx (decreases d) =
  match d with
  | [] -> []
  | jt :: d -> ren_jt xi jt :: ren_jctx xi d

(** * The context morphism *)

let ty_ren_ok (xi: ren) (g g': ctx) : prop =
  ren_ok xi g g' /\
  (forall (i: nat). {:pattern L.nth g.vars i}
     match L.nth g.vars i with
     | Some t -> L.nth g'.vars i == Some (ren_ty xi t)
     | None -> True) /\
  (forall (a: atom). {:pattern L.assoc a g.regions}
     match L.assoc a g.regions with
     | Some l -> L.assoc a g'.regions == Some (ren_layout xi l)
     | None -> True)

(** The condition reads `ξ` pointwise. *)
val ty_ren_ok_ext (xi xi': ren) (g g': ctx)
  : Lemma (requires ty_ren_ok xi g g' /\ (forall (i: nat). xi' i == xi i))
          (ensures ty_ren_ok xi' g g')

val ty_ren_ok_up (xi: ren) (g g': ctx) (k: kind)
  : Lemma (requires ty_ren_ok xi g g')
          (ensures ty_ren_ok (up_ren xi) (push_tvar g k) (push_tvar g' k))

(** The type binders of a clause, the last one index 0. *)
val ty_ren_ok_upn (xi: ren) (g g': ctx) (ks: list kind)
  : Lemma (requires ty_ren_ok xi g g')
          (ensures ty_ren_ok (upn_ren (L.length ks) xi) (push_tvars g ks) (push_tvars g' ks))

val ty_ren_ok_assumps (xi: ren) (g g': ctx) (cs: list constr)
  : Lemma (requires ty_ren_ok xi g g')
          (ensures ty_ren_ok xi (add_assumps g cs) (add_assumps g' (L.map (ren_constr xi) cs)))

val ty_ren_ok_assump (xi: ren) (g g': ctx) (c: constr)
  : Lemma (requires ty_ren_ok xi g g')
          (ensures ty_ren_ok xi (add_assump g c) (add_assump g' (ren_constr xi c)))

val ty_ren_ok_push_var (xi: ren) (g g': ctx) (t: typ)
  : Lemma (requires ty_ren_ok xi g g')
          (ensures ty_ren_ok xi (push_var g t) (push_var g' (ren_ty xi t)))

val ty_ren_ok_push_vars (xi: ren) (g g': ctx) (ts: list typ)
  : Lemma (requires ty_ren_ok xi g g')
          (ensures ty_ren_ok xi (push_vars g ts) (push_vars g' (ren_tys xi ts)))

val ty_ren_ok_enter_region (xi: ren) (g g': ctx) (a: atom) (l: layout)
  : Lemma (requires ty_ren_ok xi g g')
          (ensures ty_ren_ok xi (enter_region g a l) (enter_region g' a (ren_layout xi l)))

(** The excluded set of the cofinite premise grows. *)
val ty_ren_ok_fresh (xi: ren) (g g': ctx) (a: atom) (body: exp)
  : Lemma (requires ty_ren_ok xi g g' /\ ~(L.mem a (rdom g')) /\
                    ~(L.mem a (frn_exp (ren_ty_exp xi body))))
          (ensures ~(L.mem a (rdom g)) /\ ~(L.mem a (frn_exp body)))

(** Entering an unused type binder is the renaming `↑1`. *)
val ty_ren_ok_shift (g: ctx) (k: kind) : Lemma (ty_ren_ok (shift 1) g (push_tvar g k))

(** * The judgements *)

val occ_typing_ren_ty (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t) (xi: ren) (g': ctx)
  : Pure (occ_typing sg g' (ren_octx xi om) o (ren_ty xi t))
         (requires ty_ren_ok xi g g')
         (ensures fun _ -> True)

val typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d tl e t r) (xi: ren) (g': ctx)
  : Pure (typing sg ln g' (ren_jctx xi d) tl (ren_ty_exp xi e) (ren_ty xi t) (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

val exps_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d tl r es ts) (xi: ren) (g': ctx)
  : Pure (exps_typing sg ln g' (ren_jctx xi d) tl (ren_ty xi r) (ren_ty_exps xi es) (ren_tys xi ts))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

val chain_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (xi: ren) (g': ctx)
  : Pure (chain_typing sg ln g' (ren_jctx xi d) (ren_ty xi r) (ren_ty_exp xi e))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

val binds_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (xi: ren) (g': ctx)
  : Pure (binds_typing sg ln g' (ren_ty_binds xi bs))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

val cells_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay) (xi: ren) (g': ctx)
  : Pure (cells_typing sg ln g' (ren_ty_cells xi cells) (ren_layout xi lay))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

val match_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx)
  (h: match_typing sg ln g d r th om) (xi: ren) (g': ctx)
  : Pure (match_typing sg ln g' (ren_jctx xi d) (ren_ty xi r) (ren_ty_exps xi th) (ren_octx xi om))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

val dt_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d tl om dt t r) (xi: ren) (g': ctx)
  : Pure (dt_typing sg ln g' (ren_jctx xi d) tl (ren_octx xi om) (ren_ty_dt xi dt) (ren_ty xi t)
            (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

val ctor_brs_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ)
  (h: ctor_brs_typing sg ln g d tl om o ks ss cs bs t r) (xi: ren) (g': ctx)
  : Pure (ctor_brs_typing sg ln g' (ren_jctx xi d) tl (ren_octx xi om) o ks (ren_tys xi ss) cs
            (ren_ty_brs xi bs) (ren_ty xi t) (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

val lit_brs_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d tl om lt bs t r) (xi: ren) (g': ctx)
  : Pure (lit_brs_typing sg ln g' (ren_jctx xi d) tl (ren_octx xi om) (ren_ty xi lt)
            (ren_ty_brs xi bs) (ren_ty xi t) (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

val key_brs_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#tl: bool) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d tl om o kts bs t r) (xi: ren) (g': ctx)
  : Pure (key_brs_typing sg ln g' (ren_jctx xi d) tl (ren_octx xi om) o (ren_layout xi kts)
            (ren_ty_brs xi bs) (ren_ty xi t) (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True)

(** The clauses of a handler of `E τ̄`, `E` being the effect `q` of `Σ`
    whose parameters `τ̄` instantiate (the premise of `T_Handle` kinds
    `E τ̄`). The signatures of `E`'s operations are closed in its
    parameters and the operations' binders, which is what lets the
    instances commute with the renaming lifted past the binders. *)
val clauses_typing_ren_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause)
  (h: clauses_typing sg ln g ei ts r b cs) (q: qname) (xi: ren) (g': ctx)
  : Pure (clauses_typing sg ln g' ei (ren_tys xi ts) (ren_ty xi r) (ren_ty xi b) (ren_ty_cls xi cs))
         (requires sig_ok sg /\ ty_ren_ok xi g g' /\ sg.effects q == Some ei /\
                   L.length ts == L.length ei.eff_params)
         (ensures fun _ -> True)
