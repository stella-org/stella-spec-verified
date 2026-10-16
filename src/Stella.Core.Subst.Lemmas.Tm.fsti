(**
 * The σ-calculus of the term and join sorts, and how the three sorts of a
 * term commute.
 *
 * Families proved by induction on terms, in dependency order:
 *
 *   join sort      `ren_ren_jp`, `ren_id_jp`
 *   orthogonal     `sub_ty_ren_tm`   sub_ty_exp σ ∘ ren_tm ξ  = ren_tm ξ ∘ sub_ty_exp σ
 *                  `ren_jp_ren_tm`   ren_jp ζ ∘ ren_tm ξ      = ren_tm ξ ∘ ren_jp ζ
 *                  `sub_ty_ren_jp`   sub_ty_exp σ ∘ ren_jp ζ  = ren_jp ζ ∘ sub_ty_exp σ
 *   term sort      `rinst_tm`        ren_tm ξ = sub_tm (ξ >> EVar)
 *                  `sub_ren_tm`      sub ∘ ren
 *                  `ren_sub_tm`      ren ∘ sub
 *   cross-sort     `ren_jp_sub_tm`   ren_jp ζ (sub_tm τ e) = sub_tm (τ >> ren_jp ζ) (ren_jp ζ e)
 *                  `sub_ty_sub_tm`   sub_ty_exp σ (sub_tm τ e)
 *                                      = sub_tm (τ >> sub_ty_exp σ) (sub_ty_exp σ e)
 *   term sort      `sub_sub_tm`      sub ∘ sub
 *                  `sub_id_tm`       sub (EVar) = id
 *
 * The cross-sort laws are what lifting a term substitution under a type or
 * join binder needs (`tyup_esub`, `jup_esub`): `sub ∘ sub` at an `ETyLam`
 * meets `ren_ty_exp ↑1 (sub_tm τ v)`, which `sub_ty_sub_tm` turns into
 * `sub_tm (tyup_esub 1 τ) (ren_ty_exp ↑1 v)`. They are also what the
 * substitution lemma for `Λ` uses to push a type substitution through a term
 * substitution.
 *
 * As in `Stella.Core.Subst.Lemmas.Typ`, every hypothesis is pointwise.
 * A family over terms is a mutual induction over all term classes; the
 * interface exports its instances at `exp` and `dtree`.
 *)
module Stella.Core.Subst.Lemmas.Tm
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
module L = FStar.List.Tot

(** * Named compositions *)

(** `ξ >> EVar`, the substitution a term renaming stands for *)
let ren_esub (xi: ren) (i: nat) : exp = EVar (xi i)

(** * The join sort *)

val ren_ren_jp (xi: ren) (zeta: ren) (theta: ren) (e: exp)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp xi (ren_jp zeta e) == ren_jp theta e)

val ren_ren_jp_dt (xi: ren) (zeta: ren) (theta: ren) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp_dt xi (ren_jp_dt zeta dt) == ren_jp_dt theta dt)

val ren_id_jp (xi: ren) (e: exp)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp xi e == e)

val ren_id_jp_dt (xi: ren) (dt: dtree)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp_dt xi dt == dt)

val ren_jp_ext (xi xi': ren) (e: exp)
  : Lemma (requires forall (i: nat). xi i == xi' i) (ensures ren_jp xi e == ren_jp xi' e)

val ren_jp_id (e: exp) : Lemma (ren_jp id_ren e == e)

(** * Operations on different sorts commute *)

val sub_ty_ren_tm (sigma: tsub) (xi: ren) (e: exp)
  : Lemma (ensures sub_ty_exp sigma (ren_tm xi e) == ren_tm xi (sub_ty_exp sigma e))

val sub_ty_ren_tm_dt (sigma: tsub) (xi: ren) (dt: dtree)
  : Lemma (ensures sub_ty_dt sigma (ren_tm_dt xi dt) == ren_tm_dt xi (sub_ty_dt sigma dt))

val ren_jp_ren_tm (zeta: ren) (xi: ren) (e: exp)
  : Lemma (ensures ren_jp zeta (ren_tm xi e) == ren_tm xi (ren_jp zeta e))

val ren_jp_ren_tm_dt (zeta: ren) (xi: ren) (dt: dtree)
  : Lemma (ensures ren_jp_dt zeta (ren_tm_dt xi dt) == ren_tm_dt xi (ren_jp_dt zeta dt))

val sub_ty_ren_jp (sigma: tsub) (zeta: ren) (e: exp)
  : Lemma (ensures sub_ty_exp sigma (ren_jp zeta e) == ren_jp zeta (sub_ty_exp sigma e))

val sub_ty_ren_jp_dt (sigma: tsub) (zeta: ren) (dt: dtree)
  : Lemma (ensures sub_ty_dt sigma (ren_jp_dt zeta dt) == ren_jp_dt zeta (sub_ty_dt sigma dt))

val ren_ty_ren_tm (xi zeta: ren) (e: exp)
  : Lemma (ren_ty_exp xi (ren_tm zeta e) == ren_tm zeta (ren_ty_exp xi e))

val ren_ty_ren_jp (xi zeta: ren) (e: exp)
  : Lemma (ren_ty_exp xi (ren_jp zeta e) == ren_jp zeta (ren_ty_exp xi e))

(** * A term renaming is a substitution by variables *)

val rinst_tm (xi: ren) (sigma: esub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm xi e == sub_tm sigma e)

val rinst_tm_dt (xi: ren) (sigma: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm_dt xi dt == sub_tm_dt sigma dt)

val ren_tm_as_sub (xi: ren) (e: exp) : Lemma (ren_tm xi e == sub_tm (ren_esub xi) e)

(** * Substitution after renaming *)

val sub_ren_tm (sigma: esub) (xi: ren) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm sigma (ren_tm xi e) == sub_tm theta e)

val sub_ren_tm_dt (sigma: esub) (xi: ren) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm_dt sigma (ren_tm_dt xi dt) == sub_tm_dt theta dt)

(** `ren ξ (ren ζ e) == ren θ e` for `θ` pointwise `ζ >> ξ`. *)
val ren_ren_tm (xi zeta theta: ren) (e: exp)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_tm xi (ren_tm zeta e) == ren_tm theta e)

(** * Renaming after substitution *)

val ren_sub_tm (xi: ren) (sigma: esub) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm xi (sub_tm sigma e) == sub_tm theta e)

val ren_sub_tm_dt (xi: ren) (sigma: esub) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm_dt xi (sub_tm_dt sigma dt) == sub_tm_dt theta dt)

(** * A join renaming passes through a term substitution *)

val ren_jp_sub_tm (zeta: ren) (tau: esub) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp zeta (sub_tm tau e) == sub_tm theta (ren_jp zeta e))

val ren_jp_sub_tm_dt (zeta: ren) (tau: esub) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp_dt zeta (sub_tm_dt tau dt) == sub_tm_dt theta (ren_jp_dt zeta dt))

(** * A type substitution passes through a term substitution *)

val sub_ty_sub_tm (sigma: tsub) (tau: esub) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_exp sigma (sub_tm tau e) == sub_tm theta (sub_ty_exp sigma e))

val sub_ty_sub_tm_dt (sigma: tsub) (tau: esub) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_dt sigma (sub_tm_dt tau dt) == sub_tm_dt theta (sub_ty_dt sigma dt))

(** The renaming instance: `ren_ty_exp ξ (sub_tm τ e)
    == sub_tm (τ >> ren_ty_exp ξ) (ren_ty_exp ξ e)`. *)
val ren_ty_sub_tm (xi: ren) (tau theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == ren_ty_exp xi (tau i))
          (ensures ren_ty_exp xi (sub_tm tau e) == sub_tm theta (ren_ty_exp xi e))

(** * Substitution after substitution *)

val sub_sub_tm (tau: esub) (sigma: esub) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm tau (sub_tm sigma e) == sub_tm theta e)

val sub_sub_tm_dt (tau: esub) (sigma: esub) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm_dt tau (sub_tm_dt sigma dt) == sub_tm_dt theta dt)

(** * Substitution by variables *)

val sub_id_tm (sigma: esub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm sigma e == e)

val sub_id_tm_dt (sigma: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm_dt sigma dt == dt)

(** * Corollaries *)

val sub_tm_ext (sigma sigma': esub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == sigma' i)
          (ensures sub_tm sigma e == sub_tm sigma' e)

val ren_tm_ext (xi xi': ren) (e: exp)
  : Lemma (requires forall (i: nat). xi i == xi' i)
          (ensures ren_tm xi e == ren_tm xi' e)

val sub_tm_evar (e: exp) : Lemma (sub_tm evar e == e)

val ren_tm_id (e: exp) : Lemma (ren_tm id_ren e == e)

val ren_tm_shift0 (e: exp) : Lemma (ren_tm (shift 0) e == e)

val ren_jp_shift0 (e: exp) : Lemma (ren_jp (shift 0) e == e)
