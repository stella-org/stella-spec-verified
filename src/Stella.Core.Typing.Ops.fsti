(**
 * The instances of operation signatures under the maps of the metatheory
 * (spec 05 §Effects; design §3.1).
 *
 * The argument and result types of an operation of `E (ā : κ̄)` are kinded
 * in the declaration context `·, ā : κ̄, b̄ : κ̄'` of `Σ` (`op_ok`): their
 * type variables are the effect's parameters and the operation's binders,
 * and they mention no kind variable and no region (`op_types_closed`). The
 * instances that `perform` reads, `op_inst τ̄ σ̄ τ = τ[ā := τ̄][b̄ := σ̄]`, and
 * that a clause reads under its `m` binders, `eff_inst m τ̄ τ = τ[ā := τ̄]`,
 * therefore commute with every map of the types of the term:
 *
 *   - a substitution or a renaming maps the instantiating types, and under
 *     a clause's binders is lifted past them;
 *   - a kind instantiation and a region map, which fix the signature's
 *     types, map the instantiating types.
 *)
module Stella.Core.Typing.Ops
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Kinding.Facts
open Stella.Core.Typing.Aux
module L = FStar.List.Tot

(** * The types of an operation *)

(** A type with `n` type variables in scope and no kind variable or
    region: every kind instantiation and region map fixes it. *)
let sig_closed (n: nat) (t: typ) : prop =
  tvs_below n t /\ (forall (ks: list kind). kinst_ty ks t == t) /\
  (forall (f: region_ref -> region_ref). rmap_ty f t == t)

val op_types_closed (sg: sig) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  : Lemma (requires effects_wf sg /\ sg.effects q == Some ei /\ op_of ei op == Some os)
          (ensures sig_closed (L.length os.binders + L.length ei.eff_params) os.arg /\
                   sig_closed (L.length os.binders + L.length ei.eff_params) os.res)

(** * `perform` *)

val op_inst_sub (sigma: tsub) (ts ss: list typ) (t: typ)
  : Lemma (requires tvs_below (L.length ss + L.length ts) t)
          (ensures sub_ty sigma (op_inst ts ss t) == op_inst (sub_tys sigma ts) (sub_tys sigma ss) t)

val op_inst_ren (xi: ren) (ts ss: list typ) (t: typ)
  : Lemma (requires tvs_below (L.length ss + L.length ts) t)
          (ensures ren_ty xi (op_inst ts ss t) == op_inst (ren_tys xi ts) (ren_tys xi ss) t)

val op_inst_kinst (ks: list kind) (ts ss: list typ) (t: typ)
  : Lemma (requires kinst_ty ks t == t)
          (ensures kinst_ty ks (op_inst ts ss t) == op_inst (kinst_tys ks ts) (kinst_tys ks ss) t)

val op_inst_rmap (f: region_ref -> region_ref) (ts ss: list typ) (t: typ)
  : Lemma (requires rmap_ty f t == t)
          (ensures rmap_ty f (op_inst ts ss t) == op_inst (rmap_tys f ts) (rmap_tys f ss) t)

(** * Clauses, under `m` binders *)

val eff_inst_sub (sigma: tsub) (m: nat) (ts: list typ) (t: typ)
  : Lemma (requires tvs_below (m + L.length ts) t)
          (ensures sub_ty (upn_tsub m sigma) (eff_inst m ts t) == eff_inst m (sub_tys sigma ts) t)

val eff_inst_ren (xi: ren) (m: nat) (ts: list typ) (t: typ)
  : Lemma (requires tvs_below (m + L.length ts) t)
          (ensures ren_ty (upn_ren m xi) (eff_inst m ts t) == eff_inst m (ren_tys xi ts) t)

val eff_inst_kinst (ks: list kind) (m: nat) (ts: list typ) (t: typ)
  : Lemma (requires kinst_ty ks t == t)
          (ensures kinst_ty ks (eff_inst m ts t) == eff_inst m (kinst_tys ks ts) t)

val eff_inst_rmap (f: region_ref -> region_ref) (m: nat) (ts: list typ) (t: typ)
  : Lemma (requires rmap_ty f t == t)
          (ensures rmap_ty f (eff_inst m ts t) == eff_inst m (rmap_tys f ts) t)
