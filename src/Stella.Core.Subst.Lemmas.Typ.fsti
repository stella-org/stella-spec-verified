(**
 * The σ-calculus on types: renaming and parallel substitution of type
 * variables in `typ`, `entry`, `constr`, `list typ` and layouts.
 *
 * Every law is stated with POINTWISE hypotheses on the renamings and
 * substitutions involved (`forall i. θ i == …`), so that one lemma covers
 * extensionality as well: e.g. `ren_ren_ty ξ ζ θ t` is
 * `ren ξ (ren ζ t) == ren θ t` for ANY `θ` that agrees with `ζ >> ξ`
 * (`f >> g` is `fun i -> g (f i)`).
 *
 * The families come in dependency order:
 *
 *   1. ren ∘ ren, ren id
 *   2. ren = sub ∘ TVar ("rinst")
 *   3. sub ∘ ren
 *   4. ren ∘ sub          (its `up` lemma needs 1)
 *   5. sub ∘ sub          (its `up` lemma needs 3 and 4)
 *   6. sub TVar = id
 *
 * Each family mirrors the mutual recursion of the definitions, and each comes
 * with an `upn_*` lemma: lifting across `n` type binders preserves the
 * hypothesis of the family.
 *)
module Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Syntax
open Stella.Core.Subst
module L = FStar.List.Tot

(** * Named compositions

    The few compositions the `up` lemmas need, as named functions, so that
    two occurrences of one composition are the same SMT term. *)

(** `ξ >> ↑n` *)
let ren_shift (n: nat) (xi: ren) (k: nat) : nat = xi k + n

(** `ξ >> TVar`, the substitution a renaming stands for *)
let ren_tsub (xi: ren) (i: nat) : typ = TVar (xi i)

(** `σ >> ren_ty ↑n` *)
let tsub_shift (n: nat) (sigma: tsub) (k: nat) : typ = ren_ty (shift n) (sigma k)

(** * Lifting renamings *)

val upn_ren_comp (n: nat) (xi zeta theta: ren)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures forall (i: nat). upn_ren n theta i == upn_ren n xi (upn_ren n zeta i))

val upn_ren_id (n: nat) (xi: ren)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures forall (i: nat). upn_ren n xi i == i)

(** * Renaming after renaming *)

val ren_ren_ty (xi: ren) (zeta: ren) (theta: ren) (t: typ)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_ty xi (ren_ty zeta t) == ren_ty theta t)

val ren_ren_ent (xi: ren) (zeta: ren) (theta: ren) (en: entry)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_ent xi (ren_ent zeta en) == ren_ent theta en)

val ren_ren_constr (xi: ren) (zeta: ren) (theta: ren) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_constr xi (ren_constr zeta cn) == ren_constr theta cn)

val ren_ren_tys (xi: ren) (zeta: ren) (theta: ren) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_tys xi (ren_tys zeta ts) == ren_tys theta ts)

val ren_ren_layout (xi: ren) (zeta: ren) (theta: ren) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_layout xi (ren_layout zeta l) == ren_layout theta l)

(** * Renaming by the identity *)

val ren_id_ty (xi: ren) (t: typ)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_ty xi t == t)

val ren_id_ent (xi: ren) (en: entry)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_ent xi en == en)

val ren_id_constr (xi: ren) (cn: constr)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_constr xi cn == cn)

val ren_id_tys (xi: ren) (ts: list typ)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_tys xi ts == ts)

val ren_id_layout (xi: ren) (l: list (key & typ))
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_layout xi l == l)

(** * A renaming is a substitution by variables *)

val upn_rinst_ty (n: nat) (xi: ren) (sigma: tsub)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures forall (i: nat). upn_tsub n sigma i == TVar (upn_ren n xi i))

val rinst_ty (xi: ren) (sigma: tsub) (t: typ)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty xi t == sub_ty sigma t)

val rinst_ent (xi: ren) (sigma: tsub) (en: entry)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ent xi en == sub_ent sigma en)

val rinst_constr (xi: ren) (sigma: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_constr xi cn == sub_constr sigma cn)

val rinst_tys (xi: ren) (sigma: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_tys xi ts == sub_tys sigma ts)

val rinst_layout (xi: ren) (sigma: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_layout xi l == sub_layout sigma l)

(** * Substitution after renaming *)

val upn_sub_ren_ty (n: nat) (sigma: tsub) (xi: ren) (theta: tsub)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures forall (i: nat). upn_tsub n theta i == upn_tsub n sigma (upn_ren n xi i))

val sub_ren_ty (sigma: tsub) (xi: ren) (theta: tsub) (t: typ)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_ty sigma (ren_ty xi t) == sub_ty theta t)

val sub_ren_ent (sigma: tsub) (xi: ren) (theta: tsub) (en: entry)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_ent sigma (ren_ent xi en) == sub_ent theta en)

val sub_ren_constr (sigma: tsub) (xi: ren) (theta: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_constr sigma (ren_constr xi cn) == sub_constr theta cn)

val sub_ren_tys (sigma: tsub) (xi: ren) (theta: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tys sigma (ren_tys xi ts) == sub_tys theta ts)

val sub_ren_layout (sigma: tsub) (xi: ren) (theta: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_layout sigma (ren_layout xi l) == sub_layout theta l)

(** * Renaming after substitution *)

val upn_ren_sub_ty (n: nat) (xi: ren) (sigma theta: tsub)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures forall (i: nat).
             upn_tsub n theta i == ren_ty (upn_ren n xi) (upn_tsub n sigma i))

val ren_sub_ty (xi: ren) (sigma: tsub) (theta: tsub) (t: typ)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_ty xi (sub_ty sigma t) == sub_ty theta t)

val ren_sub_ent (xi: ren) (sigma: tsub) (theta: tsub) (en: entry)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_ent xi (sub_ent sigma en) == sub_ent theta en)

val ren_sub_constr (xi: ren) (sigma: tsub) (theta: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_constr xi (sub_constr sigma cn) == sub_constr theta cn)

val ren_sub_tys (xi: ren) (sigma: tsub) (theta: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_tys xi (sub_tys sigma ts) == sub_tys theta ts)

val ren_sub_layout (xi: ren) (sigma: tsub) (theta: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_layout xi (sub_layout sigma l) == sub_layout theta l)

(** * Substitution after substitution *)

val upn_sub_sub_ty (n: nat) (tau sigma theta: tsub)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures forall (i: nat).
             upn_tsub n theta i == sub_ty (upn_tsub n tau) (upn_tsub n sigma i))

val sub_sub_ty (tau: tsub) (sigma: tsub) (theta: tsub) (t: typ)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty tau (sub_ty sigma t) == sub_ty theta t)

val sub_sub_ent (tau: tsub) (sigma: tsub) (theta: tsub) (en: entry)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ent tau (sub_ent sigma en) == sub_ent theta en)

val sub_sub_constr (tau: tsub) (sigma: tsub) (theta: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_constr tau (sub_constr sigma cn) == sub_constr theta cn)

val sub_sub_tys (tau: tsub) (sigma: tsub) (theta: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_tys tau (sub_tys sigma ts) == sub_tys theta ts)

val sub_sub_layout (tau: tsub) (sigma: tsub) (theta: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_layout tau (sub_layout sigma l) == sub_layout theta l)

(** * Substitution by variables *)

val upn_sub_id_ty (n: nat) (sigma: tsub)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures forall (i: nat). upn_tsub n sigma i == TVar i)

val sub_id_ty (sigma: tsub) (t: typ)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty sigma t == t)

val sub_id_ent (sigma: tsub) (en: entry)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ent sigma en == en)

val sub_id_constr (sigma: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_constr sigma cn == cn)

val sub_id_tys (sigma: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_tys sigma ts == ts)

val sub_id_layout (sigma: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_layout sigma l == l)

(** * Corollaries with the function written out *)

(** Extensionality. *)
val ren_ty_ext (xi xi': ren) (t: typ)
  : Lemma (requires forall (i: nat). xi i == xi' i) (ensures ren_ty xi t == ren_ty xi' t)

val sub_ty_ext (sigma sigma': tsub) (t: typ)
  : Lemma (requires forall (i: nat). sigma i == sigma' i)
          (ensures sub_ty sigma t == sub_ty sigma' t)

val ren_ty_id (t: typ) : Lemma (ren_ty id_ren t == t)

val sub_ty_tvar (t: typ) : Lemma (sub_ty tvar t == t)

val ren_ty_as_sub (xi: ren) (t: typ) : Lemma (ren_ty xi t == sub_ty (ren_tsub xi) t)

(** `↑0` is the identity. *)
val ren_ty_shift0 (t: typ) : Lemma (ren_ty (shift 0) t == t)
