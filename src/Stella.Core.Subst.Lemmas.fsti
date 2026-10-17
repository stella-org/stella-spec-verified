(**
 * Facts about the derived cutoff-style operations of `Stella.Core.Subst`
 * (`shift_*`, `subst_*`, `subst1_*`) and kind instantiation:
 *
 *   - shifting by 0 is the identity, in each index sort;
 *   - substituting right after a shift by the substitution's width cancels
 *     (`subst c ss (shift c |ss| t) == t`), for types, types in terms and
 *     terms;
 *   - `subst1_*` is the one-element case of `subst_* 0`;
 *   - instantiating with the empty kind vector is the identity;
 *   - kind instantiation commutes with renaming and substitution of type
 *     variables on types: it changes kinds only, and both leave kinds
 *     alone.
 *
 * The shift and substitution facts are corollaries of the σ-calculus laws
 * in `Stella.Core.Subst.Lemmas.Typ`, `.TyExp` and `.Tm`. `kinst_*_nil` is
 * exported at kinds, at every type class, and at `exp` and `dtree`.
 *)
module Stella.Core.Subst.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Subst.Lemmas.Tm
module L = FStar.List.Tot

(** * Kind instantiation with no kinds *)

val kinst_kind_nil (k: kind) : Lemma (ensures kinst_kind [] k == k)

val kinst_kinds_nil (kl: list kind) : Lemma (ensures kinst_kinds [] kl == kl)

val kinst_ty_nil (t: typ) : Lemma (ensures kinst_ty [] t == t)

val kinst_ent_nil (en: entry) : Lemma (ensures kinst_ent [] en == en)

val kinst_constr_nil (cn: constr) : Lemma (ensures kinst_constr [] cn == cn)

val kinst_tys_nil (ts: list typ) : Lemma (ensures kinst_tys [] ts == ts)

val kinst_layout_nil (l: list (key & typ))
  : Lemma (ensures kinst_layout [] l == l)

val kinst_exp_nil (e: exp) : Lemma (ensures kinst_exp [] e == e)

val kinst_dt_nil (dt: dtree) : Lemma (ensures kinst_dt [] dt == dt)

(** * Kind instantiation commutes with renaming and substitution *)

val kinst_ren_ty (ks: list kind) (xi: ren) (t: typ)
  : Lemma (kinst_ty ks (ren_ty xi t) == ren_ty xi (kinst_ty ks t))

val kinst_ren_ent (ks: list kind) (xi: ren) (en: entry)
  : Lemma (kinst_ent ks (ren_ent xi en) == ren_ent xi (kinst_ent ks en))

val kinst_ren_constr (ks: list kind) (xi: ren) (cn: constr)
  : Lemma (kinst_constr ks (ren_constr xi cn) == ren_constr xi (kinst_constr ks cn))

val kinst_ren_tys (ks: list kind) (xi: ren) (ts: list typ)
  : Lemma (kinst_tys ks (ren_tys xi ts) == ren_tys xi (kinst_tys ks ts))

val kinst_ren_layout (ks: list kind) (xi: ren) (l: list (key & typ))
  : Lemma (kinst_layout ks (ren_layout xi l) == ren_layout xi (kinst_layout ks l))

(** `θ` is any substitution agreeing pointwise with `σ >> kinst_ty ks`. *)
val kinst_sub_ty (ks: list kind) (sigma theta: tsub) (t: typ)
  : Lemma (requires forall (i: nat). theta i == kinst_ty ks (sigma i))
          (ensures kinst_ty ks (sub_ty sigma t) == sub_ty theta (kinst_ty ks t))

val kinst_sub_ent (ks: list kind) (sigma theta: tsub) (en: entry)
  : Lemma (requires forall (i: nat). theta i == kinst_ty ks (sigma i))
          (ensures kinst_ent ks (sub_ent sigma en) == sub_ent theta (kinst_ent ks en))

val kinst_sub_constr (ks: list kind) (sigma theta: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == kinst_ty ks (sigma i))
          (ensures kinst_constr ks (sub_constr sigma cn) == sub_constr theta (kinst_constr ks cn))

val kinst_sub_tys (ks: list kind) (sigma theta: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == kinst_ty ks (sigma i))
          (ensures kinst_tys ks (sub_tys sigma ts) == sub_tys theta (kinst_tys ks ts))

val kinst_sub_layout (ks: list kind) (sigma theta: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == kinst_ty ks (sigma i))
          (ensures kinst_layout ks (sub_layout sigma l) == sub_layout theta (kinst_layout ks l))

(** * Shift by 0 *)

val shift_ty_zero (c: nat) (t: typ) : Lemma (shift_ty c 0 t == t)

val shift_ty_exp_zero (c: nat) (e: exp) : Lemma (shift_ty_exp c 0 e == e)

val shift_tm_zero (c: nat) (e: exp) : Lemma (shift_tm c 0 e == e)

val shift_jp_zero (c: nat) (e: exp) : Lemma (shift_jp c 0 e == e)

(** * Substitution cancels a shift *)

val subst_shift_ty (c: nat) (ss: list typ) (t: typ)
  : Lemma (subst_ty c ss (shift_ty c (L.length ss) t) == t)

val subst_shift_ty_exp (c: nat) (ss: list typ) (e: exp)
  : Lemma (subst_ty_exp c ss (shift_ty_exp c (L.length ss) e) == e)

val subst_shift_tm (c: nat) (vs: list exp) (e: exp)
  : Lemma (subst_tm c vs (shift_tm c (L.length vs) e) == e)

(** The single-variable instances: `τ[a := σ]` after weakening `τ` by `a`,
    and the same on terms. *)
val subst1_shift_ty (s t: typ) : Lemma (subst1_ty s (shift_ty 0 1 t) == t)

val subst1_shift_ty_exp (s: typ) (e: exp) : Lemma (subst1_ty_exp s (shift_ty_exp 0 1 e) == e)

val subst1_shift_tm (v e: exp) : Lemma (subst1_tm v (shift_tm 0 1 e) == e)

(** * Single substitution is the one-element simultaneous one *)

val subst1_ty_list (s t: typ) : Lemma (subst1_ty s t == subst_ty 0 [s] t)

val subst1_ty_exp_list (s: typ) (e: exp) : Lemma (subst1_ty_exp s e == subst_ty_exp 0 [s] e)

val subst1_tm_list (v e: exp) : Lemma (subst1_tm v e == subst_tm 0 [v] e)
