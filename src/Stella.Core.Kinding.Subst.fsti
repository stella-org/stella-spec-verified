(**
 * Kinding is preserved by renaming, substitution, and kind instantiation
 * (spec 01 §Kinding; design §1.1, §1.2, §2.2, §2.3).
 *
 * ## Renaming and substitution
 *
 * Both go from a context `g` to a context `g'` under four conditions
 * (`ren_ok`, `sub_ok`):
 *
 *   - the kind variables are the same, `g'.nk = g.nk`;
 *   - every type variable of `g` is sent to a type variable of `g'` of the
 *     same kind (renaming), or to a type of that kind in `g'`
 *     (substitution);
 *   - the image of every hypothesis of `g` is *entailed* by the hypotheses
 *     of `g'`. Stated with entailment, one lemma covers renaming,
 *     weakening by more hypotheses, and cut;
 *   - the region domain grows, `rdom g ⊆ rdom g'` (`rdom_incl`). Every
 *     preservation lemma has this hypothesis, since a region element or a
 *     region key names a region in scope.
 *
 * Kinding changes the context in two ways, entering a type binder
 * (`push_tvar`) and assuming a constraint (`add_assump`). Both conditions
 * are re-established there: under a binder with the lifted renaming or
 * substitution (`ren_ok_up`, `sub_ok_up`), and under an assumption with
 * the image of the constraint assumed in `g'` (`ren_ok_assumps`,
 * `sub_ok_assumps`). Neither changes the region domain
 * (`Stella.Core.Context.rdom_push_tvar`, `rdom_add_assump`), so both keep
 * the inclusion (`rdom_incl_push_tvar`, `rdom_incl_add_assumps`).
 *
 * A synthesized kind is kept by a renaming but not by a substitution,
 * which may put row syntax where a variable stood; there the conclusion is
 * a `check`.
 *
 * ## Kind instantiation
 *
 * `kinst_ctx ks nk g` instantiates the kind variables of `g` everywhere,
 * types and kinds of type variables included (`Stella.Core.Context`).
 * The instance kinds are well-formed quantifiable kinds under the new
 * `nk` (`kinst_ok`), and `Σ` is well formed so that its constructor kinds
 * are closed under their own kind variables and its effect parameters
 * mention none.
 *)
module Stella.Core.Kinding.Subst
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
module L = FStar.List.Tot

(** * The conditions *)

(** `rdom g ⊆ rdom g'` *)
let rdom_incl (g g': ctx) : prop =
  forall (a: atom). {:pattern L.mem a (rdom g)} L.mem a (rdom g) ==> L.mem a (rdom g')

(** `ξ` sends the type variables of `g` to those of `g'`, kinds and
    hypotheses included. *)
let ren_ok (xi: ren) (g g': ctx) : prop =
  g'.nk == g.nk /\
  (forall (i: nat). {:pattern L.nth g.tvars i}
     i < L.length g.tvars ==> L.nth g'.tvars (xi i) == L.nth g.tvars i) /\
  (forall (h: constr). {:pattern L.mem h (hyps g)}
     L.mem h (hyps g) ==> entails (hyps g') (ren_constr xi h)) /\
  rdom_incl g g'

(** `σ` sends each type variable of `g` to a type of its kind in `g'`, and
    the hypotheses of `g` to entailed ones. *)
let sub_ok (sg: sig) (sigma: tsub) (g g': ctx) : prop =
  g'.nk == g.nk /\
  (forall (i: nat). {:pattern L.nth g.tvars i}
     match L.nth g.tvars i with
     | Some k -> check sg g' (sigma i) k
     | None -> True) /\
  (forall (h: constr). {:pattern L.mem h (hyps g)}
     L.mem h (hyps g) ==> entails (hyps g') (sub_constr sigma h)) /\
  rdom_incl g g'

(** `g'` extends `g`: the same variables, hypotheses entailing those of
    `g`, and more regions. *)
let ctx_ext (g g': ctx) : prop =
  g'.nk == g.nk /\ g'.tvars == g.tvars /\
  (forall (h: constr). {:pattern L.mem h (hyps g)} L.mem h (hyps g) ==> entails (hyps g') h) /\
  rdom_incl g g'

(** `ks` instantiates the kind variables of `g` with well-formed
    quantifiable kinds under `nk` kind variables. *)
let kinst_ok (ks: list kind) (nk: nat) (g: ctx) : prop = L.length ks == g.nk /\ qkinds_wf nk ks

(** A list of constraints is well formed exactly when each member is. *)
val constrs_ok_mem (sg: sig) (g: ctx) (cs: list constr)
  : Lemma (constrs_ok sg g cs <==> (forall (c: constr). L.mem c cs ==> constr_ok sg g c))

(** A key in scope stays in scope when the region domain grows. *)
val key_ok_rdom (sg: sig) (g g': ctx) (k: key) (e: elt_kind)
  : Lemma (requires rdom_incl g g' /\ key_ok sg g k e) (ensures key_ok sg g' k e)

(** The region-domain inclusion survives entering a type binder and
    assuming constraints, on both sides. *)
val rdom_incl_push_tvar (g g': ctx) (k k': kind)
  : Lemma (requires rdom_incl g g') (ensures rdom_incl (push_tvar g k) (push_tvar g' k'))

val rdom_incl_add_assumps (g g': ctx) (cs cs': list constr)
  : Lemma (requires rdom_incl g g') (ensures rdom_incl (add_assumps g cs) (add_assumps g' cs'))

(** * Renaming *)

val ren_ok_up (xi: ren) (g g': ctx) (k: kind)
  : Lemma (requires ren_ok xi g g') (ensures ren_ok (up_ren xi) (push_tvar g k) (push_tvar g' k))

val ren_ok_assumps (xi: ren) (g g': ctx) (cs: list constr)
  : Lemma (requires ren_ok xi g g')
          (ensures ren_ok xi (add_assumps g cs) (add_assumps g' (L.map (ren_constr xi) cs)))

val synth_kind_ren (sg: sig) (xi: ren) (g g': ctx) (t: typ)
  : Lemma (requires ren_ok xi g g' /\ Some? (synth_kind sg g t))
          (ensures synth_kind sg g' (ren_ty xi t) == synth_kind sg g t)

val check_ren (sg: sig) (xi: ren) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires ren_ok xi g g' /\ check sg g t k) (ensures check sg g' (ren_ty xi t) k)

val entry_ok_ren (sg: sig) (xi: ren) (g g': ctx) (en: entry) (e: elt_kind)
  : Lemma (requires ren_ok xi g g' /\ entry_ok sg g en e)
          (ensures entry_ok sg g' (ren_ent xi en) e)

val check_tys_ren (sg: sig) (xi: ren) (g g': ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires ren_ok xi g g' /\ check_tys sg g ts ks)
          (ensures check_tys sg g' (ren_tys xi ts) ks)

val constr_ok_ren (sg: sig) (xi: ren) (g g': ctx) (c: constr)
  : Lemma (requires ren_ok xi g g' /\ constr_ok sg g c) (ensures constr_ok sg g' (ren_constr xi c))

val constrs_ok_ren (sg: sig) (xi: ren) (g g': ctx) (cs: list constr)
  : Lemma (requires ren_ok xi g g' /\ constrs_ok sg g cs)
          (ensures constrs_ok sg g' (L.map (ren_constr xi) cs))

(** * Weakening *)

(** Entering an unrelated type binder is the renaming `↑1`. *)
val ren_ok_shift (g: ctx) (k: kind) : Lemma (ren_ok (shift 1) g (push_tvar g k))

val check_shift (sg: sig) (g: ctx) (k': kind) (t: typ) (k: kind)
  : Lemma (requires check sg g t k) (ensures check sg (push_tvar g k') (ren_ty (shift 1) t) k)

val constr_ok_shift (sg: sig) (g: ctx) (k': kind) (c: constr)
  : Lemma (requires constr_ok sg g c)
          (ensures constr_ok sg (push_tvar g k') (ren_constr (shift 1) c))

(** Extending a context is the renaming `id`. *)
val ren_ok_ext (g g': ctx) : Lemma (requires ctx_ext g g') (ensures ren_ok id_ren g g')

val ctx_ext_add_assumps (g: ctx) (cs: list constr) : Lemma (ctx_ext g (add_assumps g cs))

val ctx_ext_add_assump (g: ctx) (c: constr) : Lemma (ctx_ext g (add_assump g c))

val ctx_ext_enter_region (g: ctx) (a: atom) (l: layout) : Lemma (ctx_ext g (enter_region g a l))

val ctx_ext_push_var (g: ctx) (t: typ) : Lemma (ctx_ext g (push_var g t))

val check_weaken (sg: sig) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires ctx_ext g g' /\ check sg g t k) (ensures check sg g' t k)

val entry_ok_weaken (sg: sig) (g g': ctx) (en: entry) (e: elt_kind)
  : Lemma (requires ctx_ext g g' /\ entry_ok sg g en e) (ensures entry_ok sg g' en e)

val constr_ok_weaken (sg: sig) (g g': ctx) (c: constr)
  : Lemma (requires ctx_ext g g' /\ constr_ok sg g c) (ensures constr_ok sg g' c)

val constrs_ok_weaken (sg: sig) (g g': ctx) (cs: list constr)
  : Lemma (requires ctx_ext g g' /\ constrs_ok sg g cs) (ensures constrs_ok sg g' cs)

(** A type of a declaration of `Σ`, kinded with only its kind variables in
    scope, is kinded in every context with those kind variables. *)
val check_decl (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg (decl_ctx g.nk) t k) (ensures check sg g t k)

(** Cut for kinding (design §2.2 lemma 5): entailed assumptions can be
    dropped. *)
val check_cut (sg: sig) (g: ctx) (cs: list constr) (t: typ) (k: kind)
  : Lemma (requires check sg (add_assumps g cs) t k /\
                    (forall (c: constr). L.mem c cs ==> entails (hyps g) c))
          (ensures check sg g t k)

(** * Well-formed parts of a context *)

val tvars_wf_push_tvar (g: ctx) (k: kind)
  : Lemma (requires tvars_wf g /\ kind_wf g.nk k /\ qkind g.nk k) (ensures tvars_wf (push_tvar g k))

val wf_hyps_push_tvar (sg: sig) (g: ctx) (k: kind)
  : Lemma (requires wf_hyps sg g) (ensures wf_hyps sg (push_tvar g k))

val wf_hyps_add_assumps (sg: sig) (g: ctx) (cs: list constr)
  : Lemma (requires wf_hyps sg g /\ constrs_ok sg g cs) (ensures wf_hyps sg (add_assumps g cs))

val wf_hyps_add_assump (sg: sig) (g: ctx) (c: constr)
  : Lemma (requires wf_hyps sg g /\ constr_ok sg g c) (ensures wf_hyps sg (add_assump g c))

(** The facts a region adds are well formed. *)
val wf_hyps_enter_region (sg: sig) (g: ctx) (a: atom) (l: layout)
  : Lemma (requires wf_hyps sg g) (ensures wf_hyps sg (enter_region g a l))

(** * Substitution *)

val sub_ok_up (sg: sig) (sigma: tsub) (g g': ctx) (k: kind)
  : Lemma (requires sub_ok sg sigma g g')
          (ensures sub_ok sg (up_tsub sigma) (push_tvar g k) (push_tvar g' k))

val sub_ok_assumps (sg: sig) (sigma: tsub) (g g': ctx) (cs: list constr)
  : Lemma (requires sub_ok sg sigma g g')
          (ensures sub_ok sg sigma (add_assumps g cs) (add_assumps g' (L.map (sub_constr sigma) cs)))

val synth_kind_sub (sg: sig) (sigma: tsub) (g g': ctx) (t: typ)
  : Lemma (requires sub_ok sg sigma g g' /\ Some? (synth_kind sg g t))
          (ensures check sg g' (sub_ty sigma t) (Some?.v (synth_kind sg g t)))

val check_sub (sg: sig) (sigma: tsub) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires sub_ok sg sigma g g' /\ check sg g t k)
          (ensures check sg g' (sub_ty sigma t) k)

val entry_ok_sub (sg: sig) (sigma: tsub) (g g': ctx) (en: entry) (e: elt_kind)
  : Lemma (requires sub_ok sg sigma g g' /\ entry_ok sg g en e)
          (ensures entry_ok sg g' (sub_ent sigma en) e)

val check_tys_sub (sg: sig) (sigma: tsub) (g g': ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires sub_ok sg sigma g g' /\ check_tys sg g ts ks)
          (ensures check_tys sg g' (sub_tys sigma ts) ks)

val constr_ok_sub (sg: sig) (sigma: tsub) (g g': ctx) (c: constr)
  : Lemma (requires sub_ok sg sigma g g' /\ constr_ok sg g c)
          (ensures constr_ok sg g' (sub_constr sigma c))

val constrs_ok_sub (sg: sig) (sigma: tsub) (g g': ctx) (cs: list constr)
  : Lemma (requires sub_ok sg sigma g g' /\ constrs_ok sg g cs)
          (ensures constrs_ok sg g' (L.map (sub_constr sigma) cs))

(** * Instantiating one type variable

    Index 0 is the variable `push_tvar` adds, the one `ETyLam` and
    `TForall` bind. The assumptions of `push_tvar g k` are the shifted ones
    of `g`, which the instantiation sends back to themselves. *)

val sub_ok_subst1 (sg: sig) (g: ctx) (k: kind) (s: typ)
  : Lemma (requires check sg g s k) (ensures sub_ok sg (scons s tvar) (push_tvar g k) g)

val check_subst1 (sg: sig) (g: ctx) (k: kind) (s t: typ) (kt: kind)
  : Lemma (requires check sg (push_tvar g k) t kt /\ check sg g s k)
          (ensures check sg g (subst1_ty s t) kt)

(** Assumptions `cs` made inside the binder, which may mention index 0,
    are instantiated and stay assumptions. No entailment is required, so
    this is the shape a substitution lemma carries under `Λ(_ : C)`
    (design §2.2 lemma 3); `check_subst1_entailed` discharges them by cut
    (lemma 5). *)
val check_subst1_assumps (sg: sig) (g: ctx) (k: kind) (cs: list constr) (s t: typ) (kt: kind)
  : Lemma (requires check sg (add_assumps (push_tvar g k) cs) t kt /\ check sg g s k)
          (ensures check sg (add_assumps g (L.map (sub_constr (scons s tvar)) cs))
                     (subst1_ty s t) kt)

val check_subst1_entailed (sg: sig) (g: ctx) (k: kind) (cs: list constr) (s t: typ) (kt: kind)
  : Lemma (requires check sg (add_assumps (push_tvar g k) cs) t kt /\ check sg g s k /\
                    (forall (c: constr). L.mem c cs ==> entails (hyps g) (sub_constr (scons s tvar) c)))
          (ensures check sg g (subst1_ty s t) kt)

(** * Kind instantiation of kinds *)

val kinst_kind_wf (ks: list kind) (nk: nat) (k: kind)
  : Lemma (requires kind_wf (L.length ks) k /\ qkinds_wf nk ks) (ensures kind_wf nk (kinst_kind ks k))

val kinst_qkind (ks: list kind) (nk: nat) (k: kind)
  : Lemma (requires qkind (L.length ks) k /\ qkinds_wf nk ks) (ensures qkind nk (kinst_kind ks k))

val kinst_qkinds_wf (ks: list kind) (nk: nat) (kl: list kind)
  : Lemma (requires qkinds_wf (L.length ks) kl /\ qkinds_wf nk ks)
          (ensures qkinds_wf nk (kinst_kinds ks kl))

(** A kind with no kind variable is unchanged. *)
val kinst_kind_closed (ks: list kind) (k: kind)
  : Lemma (requires kind_wf 0 k) (ensures kinst_kind ks k == k)

val kinst_kinds_closed (ks: list kind) (kl: list kind)
  : Lemma (requires qkinds_wf 0 kl) (ensures kinst_kinds ks kl == kl)

(** Instantiations compose, on a kind whose variables `ks0` covers. *)
val kinst_kind_comp (ks ks0: list kind) (k: kind)
  : Lemma (requires kind_wf (L.length ks0) k)
          (ensures kinst_kind ks (kinst_kind ks0 k) == kinst_kind (kinst_kinds ks ks0) k)

(** * Kind instantiation of types *)

val synth_kind_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (t: typ)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ Some? (synth_kind sg g t))
          (ensures synth_kind sg (kinst_ctx ks nk g) (kinst_ty ks t) ==
                   Some (kinst_kind ks (Some?.v (synth_kind sg g t))))

val check_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ check sg g t k)
          (ensures check sg (kinst_ctx ks nk g) (kinst_ty ks t) (kinst_kind ks k))

val entry_ok_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (en: entry) (e: elt_kind)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ entry_ok sg g en e)
          (ensures entry_ok sg (kinst_ctx ks nk g) (kinst_ent ks en) e)

val check_tys_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (ts: list typ) (kl: list kind)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ check_tys sg g ts kl)
          (ensures check_tys sg (kinst_ctx ks nk g) (kinst_tys ks ts) (kinst_kinds ks kl))

val constr_ok_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (c: constr)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ constr_ok sg g c)
          (ensures constr_ok sg (kinst_ctx ks nk g) (kinst_constr ks c))

val constrs_ok_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (cs: list constr)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ constrs_ok sg g cs)
          (ensures constrs_ok sg (kinst_ctx ks nk g) (L.map (kinst_constr ks) cs))

val tvars_wf_kinst (ks: list kind) (nk: nat) (g: ctx)
  : Lemma (requires kinst_ok ks nk g /\ tvars_wf g) (ensures tvars_wf (kinst_ctx ks nk g))

val wf_hyps_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ wf_hyps sg g)
          (ensures wf_hyps sg (kinst_ctx ks nk g))

val kinst_decl_ctx (ks: list kind) (nk n: nat)
  : Lemma (kinst_ctx ks nk (decl_ctx n) == decl_ctx nk)

(** An instance of a type scheme `forall k̄. σ` of `Σ` at kinds of the
    context is a type of the context. *)
val scheme_inst (sg: sig) (g: ctx) (n: nat) (t: typ) (ks: list kind)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ scheme_ok sg n t /\ L.length ks == n /\
                    qkinds_wf g.nk ks)
          (ensures check sg g (kinst_ty ks t) KType)
