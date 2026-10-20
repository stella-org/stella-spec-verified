(**
 * Typing is preserved by a substitution of type variables (design §1.1,
 * §1.3, §2.2, §2.3, §4.2).
 *
 * A type substitution `σ` goes from `Γ` to `Γ'` (`ty_sub_ok`) when it is a
 * kinding substitution (`Stella.Core.Kinding.Subst.sub_ok`: each `σ i` has
 * the kind of `i` in `Γ'`, the hypotheses of `Γ` map to entailed ones, the
 * region domain is included), every substitute is locally closed for
 * regions (design §3.1), and `σ` maps the types `Γ` stores: the term
 * variable `i` of `Γ'` has the substituted type of the term variable `i`
 * of `Γ`, and the region `a` of `Γ'` has the substituted layout of the
 * region `a` of `Γ`. A substitute in the domain of `Γ` is kinded in `Γ'`,
 * so its atoms are regions of `Γ'` (`Stella.Core.Kinding.Facts.check_lc`).
 *
 * The condition is re-established under every binder of the rules: a type
 * binder with `σ` lifted, a telescope of them with `σ` lifted past it, an
 * assumption with its image assumed (no entailment is required, as in
 * `sub_ok_assumps`), a term binder with its substituted type, and a region
 * entered with its substituted layout. A fact `RegionKey a ∉ j` that the
 * region adds maps to `RegionKey a ∉ σ j`, which the facts of the region
 * entered in `Γ'` entail when `a` is not in scope in `Γ'`: `σ j` is a row
 * of kind `Row Effect` in `Γ'`, its tails are row variables of `Γ'`, each
 * of which the region gives a fact, and it names no region out of scope.
 * Reading the tails needs the type variables of `Γ'` to have quantifiable
 * kinds (`tvars_wf`): a variable of a kind `κ -> Row Effect` would make an
 * application a tail, which no fact covers.
 *
 * The cofinite premise of `region` reads the atoms of the term, which a
 * type substitution only adds to, so the excluded set of the substituted
 * term, `rdom Γ' ∪ frn(σ(body))`, includes that of the term,
 * `rdom Γ ∪ frn(body)` (`ty_sub_ok_fresh`). Opening a region commutes with
 * a substitution whose substitutes are locally closed
 * (`Stella.Core.Region.Lemmas.open_region_sub_ty_exp`).
 *
 * Every judgement is preserved, with every type of the derivation
 * substituted: the term (`sub_ty_exp`), its type and its row, `Δ`
 * (`sub_jctx`) and `Ω` (`sub_octx`). The theorems assume `sig_ok` and
 * `tvars_wf Γ'`, and nothing of `Γ`. Under `sig_ok` the declared types of
 * `Σ` that the rules instantiate are closed, so a substitution commutes
 * with their instances, and a constructor's fields at substituted
 * arguments are the substituted fields. The closed types of `force`,
 * `fill` and `region⟨a⟩` are kinded in `closed_ctx g.regions`, which every
 * substitution fixes.
 *)
module Stella.Core.Typing.Subst.Ty
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

(** * Substituting the contexts of the judgement *)

(** `Ω` with its types substituted. *)
let rec sub_octx (sigma: tsub) (om: octx) : Tot octx (decreases om) =
  match om with
  | [] -> []
  | (o, t) :: om -> (o, sub_ty sigma t) :: sub_octx sigma om

(** A join point's signature substituted. *)
let sub_jt (sigma: tsub) (jt: list typ & typ & typ) : list typ & typ & typ =
  match jt with
  | (ts, t, r) -> (sub_tys sigma ts, sub_ty sigma t, sub_ty sigma r)

(** `Δ` with its types substituted. *)
let rec sub_jctx (sigma: tsub) (d: jctx) : Tot jctx (decreases d) =
  match d with
  | [] -> []
  | jt :: d -> sub_jt sigma jt :: sub_jctx sigma d

(** * The context morphism *)

let ty_sub_ok (sg: sig) (sigma: tsub) (g g': ctx) : prop =
  sub_ok sg sigma g g' /\
  (forall (i: nat). lc_ty (sigma i)) /\
  (forall (i: nat). {:pattern L.nth g.vars i}
     match L.nth g.vars i with
     | Some t -> L.nth g'.vars i == Some (sub_ty sigma t)
     | None -> True) /\
  (forall (a: atom). {:pattern L.assoc a g.regions}
     match L.assoc a g.regions with
     | Some l -> L.assoc a g'.regions == Some (sub_layout sigma l)
     | None -> True)

(** The condition reads `σ` pointwise. *)
val ty_sub_ok_ext (sg: sig) (sigma sigma': tsub) (g g': ctx)
  : Lemma (requires ty_sub_ok sg sigma g g' /\ (forall (i: nat). sigma' i == sigma i))
          (ensures ty_sub_ok sg sigma' g g')

val ty_sub_ok_up (sg: sig) (sigma: tsub) (g g': ctx) (k: kind)
  : Lemma (requires ty_sub_ok sg sigma g g')
          (ensures ty_sub_ok sg (up_tsub sigma) (push_tvar g k) (push_tvar g' k))

(** The type binders of a clause, the last one index 0. *)
val ty_sub_ok_upn (sg: sig) (sigma: tsub) (g g': ctx) (ks: list kind)
  : Lemma (requires ty_sub_ok sg sigma g g')
          (ensures ty_sub_ok sg (upn_tsub (L.length ks) sigma) (push_tvars g ks) (push_tvars g' ks))

(** Assumptions, substituted on the other side and not discharged. *)
val ty_sub_ok_assumps (sg: sig) (sigma: tsub) (g g': ctx) (cs: list constr)
  : Lemma (requires ty_sub_ok sg sigma g g')
          (ensures ty_sub_ok sg sigma (add_assumps g cs) (add_assumps g' (L.map (sub_constr sigma) cs)))

val ty_sub_ok_assump (sg: sig) (sigma: tsub) (g g': ctx) (c: constr)
  : Lemma (requires ty_sub_ok sg sigma g g')
          (ensures ty_sub_ok sg sigma (add_assump g c) (add_assump g' (sub_constr sigma c)))

val ty_sub_ok_push_var (sg: sig) (sigma: tsub) (g g': ctx) (t: typ)
  : Lemma (requires ty_sub_ok sg sigma g g')
          (ensures ty_sub_ok sg sigma (push_var g t) (push_var g' (sub_ty sigma t)))

val ty_sub_ok_push_vars (sg: sig) (sigma: tsub) (g g': ctx) (ts: list typ)
  : Lemma (requires ty_sub_ok sg sigma g g')
          (ensures ty_sub_ok sg sigma (push_vars g ts) (push_vars g' (sub_tys sigma ts)))

(** A region entered with an atom out of the scope of `Γ'`. *)
val ty_sub_ok_enter_region (sg: sig) (sigma: tsub) (g g': ctx) (a: atom) (l: layout)
  : Lemma (requires tycons_wf sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g' /\
                    ~(L.mem a (rdom g')))
          (ensures ty_sub_ok sg sigma (enter_region g a l) (enter_region g' a (sub_layout sigma l)))

(** The excluded set of the cofinite premise grows. *)
val ty_sub_ok_fresh (sg: sig) (sigma: tsub) (g g': ctx) (a: atom) (body: exp)
  : Lemma (requires ty_sub_ok sg sigma g g' /\ ~(L.mem a (rdom g')) /\
                    ~(L.mem a (frn_exp (sub_ty_exp sigma body))))
          (ensures ~(L.mem a (rdom g)) /\ ~(L.mem a (frn_exp body)))

(** Instantiating the type variable a binder pushed, at a type of its
    kind. *)
val ty_sub_ok_subst1 (sg: sig) (g: ctx) (k: kind) (s: typ)
  : Lemma (requires check sg g s k) (ensures ty_sub_ok sg (scons s tvar) (push_tvar g k) g)

(** * The judgements *)

val occ_typing_sub_ty (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t) (sigma: tsub) (g': ctx)
  : Pure (occ_typing sg g' (sub_octx sigma om) o (sub_ty sigma t))
         (requires ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (sigma: tsub) (g': ctx)
  : Pure (typing sg ln g' (sub_jctx sigma d) (sub_ty_exp sigma e) (sub_ty sigma t) (sub_ty sigma r))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val exps_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ)
  (h: exps_typing sg ln g d r es ts) (sigma: tsub) (g': ctx)
  : Pure (exps_typing sg ln g' (sub_jctx sigma d) (sub_ty sigma r) (sub_ty_exps sigma es)
            (sub_tys sigma ts))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val chain_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (sigma: tsub) (g': ctx)
  : Pure (chain_typing sg ln g' (sub_jctx sigma d) (sub_ty sigma r) (sub_ty_exp sigma e))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val binds_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (sigma: tsub) (g': ctx)
  : Pure (binds_typing sg ln g' (sub_ty_binds sigma bs))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val cells_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay) (sigma: tsub) (g': ctx)
  : Pure (cells_typing sg ln g' (sub_ty_cells sigma cells) (sub_layout sigma lay))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val match_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx)
  (h: match_typing sg ln g d r th om) (sigma: tsub) (g': ctx)
  : Pure (match_typing sg ln g' (sub_jctx sigma d) (sub_ty sigma r) (sub_ty_exps sigma th)
            (sub_octx sigma om))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val dt_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ)
  (h: dt_typing sg ln g d om dt t r) (sigma: tsub) (g': ctx)
  : Pure (dt_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma om) (sub_ty_dt sigma dt)
            (sub_ty sigma t) (sub_ty sigma r))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val ctor_brs_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ)
  (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (sigma: tsub) (g': ctx)
  : Pure (ctor_brs_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma om) o ks (sub_tys sigma ss)
            cs (sub_ty_brs sigma bs) (sub_ty sigma t) (sub_ty sigma r))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val lit_brs_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (sigma: tsub) (g': ctx)
  : Pure (lit_brs_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma om) (sub_ty sigma lt)
            (sub_ty_brs sigma bs) (sub_ty sigma t) (sub_ty sigma r))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

val key_brs_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (sigma: tsub) (g': ctx)
  : Pure (key_brs_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma om) o
            (sub_layout sigma kts) (sub_ty_brs sigma bs) (sub_ty sigma t) (sub_ty sigma r))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g')
         (ensures fun _ -> True)

(** The clauses of a handler of `E τ̄`, `E` being the effect `q` of `Σ`
    whose parameters `τ̄` instantiate. The signatures of `E`'s operations
    are closed in its parameters and the operations' binders, so their
    instances commute with the substitution lifted past the binders. *)
val clauses_typing_sub_ty (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause)
  (h: clauses_typing sg ln g ei ts r b cs) (q: qname) (sigma: tsub) (g': ctx)
  : Pure (clauses_typing sg ln g' ei (sub_tys sigma ts) (sub_ty sigma r) (sub_ty sigma b)
            (sub_ty_cls sigma cs))
         (requires sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g' /\ sg.effects q == Some ei /\
                   L.length ts == L.length ei.eff_params)
         (ensures fun _ -> True)

(** * Instantiating one type variable *)

(** The body of `Λ (a : κ)`, typed under the binder (`T_TyLam`), at a
    type `s` of kind `κ`: the shape the preservation of type application
    reads. *)
val typing_subst1 (#sg: sig) (#ln: lctx) (#g: ctx) (#k: kind) (#d: jctx) (#e: exp)
  (#t #r: typ)
  (h: typing sg ln (push_tvar g k) d e t r) (s: typ)
  : Pure (typing sg ln g (sub_jctx (scons s tvar) d) (subst1_ty_exp s e) (subst1_ty s t)
            (subst1_ty s r))
         (requires sig_ok sg /\ tvars_wf g /\ check sg g s k)
         (ensures fun _ -> True)

(** The body `v` of `Λ (a : κ). Λ (_ : C). v`, typed under both binders,
    at `s`: it is typed with `C[a := s]` assumed, not discharged. Cut
    discharges the assumption where it is entailed (design §2.2). *)
val typing_subst1_assump (#sg: sig) (#ln: lctx) (#g: ctx) (#k: kind) (#c: constr) (#d: jctx)
  (#e: exp) (#t #r: typ)
  (h: typing sg ln (add_assump (push_tvar g k) c) d e t r) (s: typ)
  : Pure (typing sg ln (add_assump g (sub_constr (scons s tvar) c)) (sub_jctx (scons s tvar) d)
            (subst1_ty_exp s e) (subst1_ty s t) (subst1_ty s r))
         (requires sig_ok sg /\ tvars_wf g /\ check sg g s k)
         (ensures fun _ -> True)
