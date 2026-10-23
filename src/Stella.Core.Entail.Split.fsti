(**
 * Entailment of Lacks and Disjoint constraints over the parts of a row
 * (design §2.1, §2.2).
 *
 *   - Known keys: in consistent hypotheses, an entailed `k ∉ ρ` says that
 *     `k` is not a known key of `ρ`, and an entailed `ρ1 # ρ2` says that
 *     `ρ1` and `ρ2` have no known key in common. Decomposing a constraint
 *     whose known part violates it fails, and only ex falso could entail
 *     it then. Inconsistent hypotheses entail every constraint
 *     (design §2.2 item 4), so these two facts need consistency.
 *   - Sub-rows: entailment of `k ∉ ρ` and of `ρ1 # ρ2` passes to sub-rows
 *     (`Stella.Core.Rows.Split.sub_row`), a known key of one side of an
 *     entailed `ρ1 # ρ2` is lacked by the other, and Lacks constraints
 *     combine over an extension at another key and over a union. These
 *     facts hold for every list of hypotheses: ex falso entails both
 *     their premises and their conclusions.
 *   - Cancellation under entailment: `Stella.Core.Rows.Split.ext_cancel`
 *     with its known-key premises read off entailed Lacks constraints in
 *     consistent hypotheses.
 *)
module Stella.Core.Entail.Split
open Stella.Core.Syntax
open Stella.Core.Rows
open Stella.Core.Rows.Split
open Stella.Core.Entail
module L = FStar.List.Tot

(** * Known keys in consistent hypotheses *)

val entails_lacks_known (hyps: list constr) (k: key) (r: typ)
  : Lemma (requires not (inconsistent hyps) /\ entails hyps (CLacks k r))
          (ensures not (L.mem k (known_keys r)))

val entails_disj_known (hyps: list constr) (r1 r2: typ) (k: key)
  : Lemma (requires not (inconsistent hyps) /\ entails hyps (CDisj r1 r2) /\
                    L.mem k (known_keys r1))
          (ensures not (L.mem k (known_keys r2)))

(** * Sub-rows *)

val entails_lacks_sub (hyps: list constr) (k: key) (r r': typ)
  : Lemma (requires entails hyps (CLacks k r) /\ sub_row r' r) (ensures entails hyps (CLacks k r'))

val entails_disj_sub (hyps: list constr) (r1 r2 r1' r2': typ)
  : Lemma (requires entails hyps (CDisj r1 r2) /\ sub_row r1' r1 /\ sub_row r2' r2)
          (ensures entails hyps (CDisj r1' r2'))

(** A known key of `ρ1` is lacked by `ρ2` when `ρ1 # ρ2`. *)
val entails_disj_lacks (hyps: list constr) (r1 r2: typ) (k: key)
  : Lemma (requires entails hyps (CDisj r1 r2) /\ L.mem k (known_keys r1))
          (ensures entails hyps (CLacks k r2))

(** A known key of `ρ2` is lacked by `ρ1` when `ρ1 # ρ2`. *)
val entails_disj_lacks_r (hyps: list constr) (r1 r2: typ) (k: key)
  : Lemma (requires entails hyps (CDisj r1 r2) /\ L.mem k (known_keys r2))
          (ensures entails hyps (CLacks k r1))

(** `k ∉ ρ` gives `k ∉ ( ent | ρ )` for an element at another key. *)
val entails_lacks_ext (hyps: list constr) (k: key) (en: entry) (r: typ)
  : Lemma (requires entails hyps (CLacks k r) /\ ent_key en <> k)
          (ensures entails hyps (CLacks k (TRowExt en r)))

(** `k ∉ ρ` and `k ∉ ρ3` give `k ∉ ρ ⊎ ρ3`. *)
val entails_lacks_union (hyps: list constr) (k: key) (r r3: typ)
  : Lemma (requires entails hyps (CLacks k r) /\ entails hyps (CLacks k r3))
          (ensures entails hyps (CLacks k (TRowUnion r r3)))

(** `( ent | ρ ) # ρ3` gives `ρ # ρ3` and `key(ent) ∉ ρ3`. With
    `key(ent) ∉ ρ` and `entails_lacks_union` these are the sharpness
    premises of `( ent | ρ ⊎ ρ3 )`, which is `( ent | ρ ) ⊎ ρ3`
    (`Stella.Core.Rows.Split.union_ext_l`). *)
val entails_disj_ext (hyps: list constr) (en: entry) (r r3: typ)
  : Lemma (requires entails hyps (CDisj (TRowExt en r) r3))
          (ensures entails hyps (CDisj r r3) /\ entails hyps (CLacks (ent_key en) r3))

(** * Cancellation under entailment *)

val ext_cancel_entails (hyps: list constr) (e e': entry) (r0 r1: typ)
  : Lemma (requires not (inconsistent hyps) /\
                    ty_eq (TRowExt e r0) (TRowExt e' r1) /\ ent_key e == ent_key e' /\
                    entails hyps (CLacks (ent_key e) r0) /\ entails hyps (CLacks (ent_key e) r1))
          (ensures ent_eq e e' /\ ty_eq r0 r1)

val ext_ty_cancel_entails (hyps: list constr) (k: key) (t t' r0 r1: typ)
  : Lemma (requires not (inconsistent hyps) /\
                    ty_eq (TRowExt (EntTy k t) r0) (TRowExt (EntTy k t') r1) /\
                    entails hyps (CLacks k r0) /\ entails hyps (CLacks k r1))
          (ensures ty_eq t t' /\ ty_eq r0 r1)

(** Cancellation across a swap: `( k : τ0 | ρ0 ) ≡ ( k' : τ1 | ρ1 )` with
    `ρ1 ≡ ( k : τ0 | ρd )`, `k ≠ k'` and `k` lacked by `ρ0` and `ρd`, gives
    `ρ0 ≡ ( k' : τ1 | ρd )`. *)
val ext_ty_cancel_swap (hyps: list constr) (k k': key) (t0 t1 r0 r1 rd: typ)
  : Lemma (requires not (inconsistent hyps) /\ k <> k' /\
                    ty_eq (TRowExt (EntTy k t0) r0) (TRowExt (EntTy k' t1) r1) /\
                    ty_eq r1 (TRowExt (EntTy k t0) rd) /\
                    entails hyps (CLacks k r0) /\ entails hyps (CLacks k rd))
          (ensures ty_eq r0 (TRowExt (EntTy k' t1) rd))
