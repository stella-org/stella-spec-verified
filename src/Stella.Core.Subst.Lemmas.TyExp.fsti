(**
 * The σ-calculus of the type sort lifted to terms: `ren_ty_exp` and
 * `sub_ty_exp`.
 *
 * Only three families are proved by induction on terms:
 *
 *   - `rinst_ty_exp`    a type renaming is a type substitution by variables;
 *   - `sub_sub_ty_exp`  substitution after substitution;
 *   - `sub_id_ty_exp`   substitution by variables (pointwise) is the identity.
 *
 * A family over terms is a mutual induction over all term classes; the
 * interface exports its instances at `exp` and `dtree`.
 *
 * A type substitution carries TYPES, so lifting it under a type binder is
 * entirely a matter of `Stella.Core.Subst.Lemmas.Typ` (`upn_sub_sub_ty`
 * etc.). Every other law (extensionality, the four compositions, the
 * identity renaming) follows from the three by rewriting renamings into
 * substitutions.
 *)
module Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
module L = FStar.List.Tot

(** * A renaming is a substitution by variables *)

val rinst_ty_exp (xi: ren) (sigma: tsub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_exp xi e == sub_ty_exp sigma e)

val rinst_ty_dt (xi: ren) (sigma: tsub) (dt: dtree)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_dt xi dt == sub_ty_dt sigma dt)

(** * Substitution after substitution *)

val sub_sub_ty_exp (tau: tsub) (sigma: tsub) (theta: tsub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_exp tau (sub_ty_exp sigma e) == sub_ty_exp theta e)

val sub_sub_ty_dt (tau: tsub) (sigma: tsub) (theta: tsub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_dt tau (sub_ty_dt sigma dt) == sub_ty_dt theta dt)

(** * Substitution by variables *)

val sub_id_ty_exp (sigma: tsub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_exp sigma e == e)

val sub_id_ty_dt (sigma: tsub) (dt: dtree)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_dt sigma dt == dt)

(** * Corollaries *)

val ren_ty_exp_as_sub (xi: ren) (e: exp)
  : Lemma (ren_ty_exp xi e == sub_ty_exp (ren_tsub xi) e)

val sub_ty_exp_ext (sigma sigma': tsub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == sigma' i)
          (ensures sub_ty_exp sigma e == sub_ty_exp sigma' e)

val ren_ty_exp_ext (xi xi': ren) (e: exp)
  : Lemma (requires forall (i: nat). xi i == xi' i)
          (ensures ren_ty_exp xi e == ren_ty_exp xi' e)

val sub_ty_exp_tvar (e: exp) : Lemma (sub_ty_exp tvar e == e)

val ren_ty_exp_id (e: exp) : Lemma (ren_ty_exp id_ren e == e)

val ren_ty_exp_shift0 (e: exp) : Lemma (ren_ty_exp (shift 0) e == e)

(** `ren ξ (ren ζ e) == ren θ e` for `θ` pointwise `ζ >> ξ`. *)
val ren_ren_ty_exp (xi zeta theta: ren) (e: exp)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_ty_exp xi (ren_ty_exp zeta e) == ren_ty_exp theta e)

(** `sub σ (ren ξ e) == sub θ e` for `θ` pointwise `ξ >> σ`. *)
val sub_ren_ty_exp (sigma: tsub) (xi: ren) (theta: tsub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_ty_exp sigma (ren_ty_exp xi e) == sub_ty_exp theta e)

(** `ren ξ (sub σ e) == sub θ e` for `θ` pointwise `σ >> ren ξ`. *)
val ren_sub_ty_exp (xi: ren) (sigma theta: tsub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_ty_exp xi (sub_ty_exp sigma e) == sub_ty_exp theta e)

(** Lifting a type substitution and shifting commute (the `up` step of the
    cross-sort laws in `Stella.Core.Subst.Lemmas.Tm`). *)
val sub_ty_exp_shift (m: nat) (sigma: tsub) (e: exp)
  : Lemma (ren_ty_exp (shift m) (sub_ty_exp sigma e)
           == sub_ty_exp (upn_tsub m sigma) (ren_ty_exp (shift m) e))

val ren_ty_exp_shift (m: nat) (xi: ren) (e: exp)
  : Lemma (ren_ty_exp (shift m) (ren_ty_exp xi e)
           == ren_ty_exp (upn_ren m xi) (ren_ty_exp (shift m) e))
