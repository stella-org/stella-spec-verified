(**
 * Sharpness of kinded rows, and splitting a kinded row at a key (spec 02
 * §Sharpness; design §2.1–§2.3).
 *
 *   - Sharpness: in a context with consistent hypotheses, two canonical
 *     entries of a kinded row with the same key have the same payload, so
 *     the entry set is the graph of a finite map (design §2.1). The
 *     sharpness premises of row extension and row union are entailments,
 *     and an inconsistent context entails them all (design §2.2 item 4):
 *     there `( k : τ | k : τ' | () )` is kinded for any `τ`, `τ'` of kind
 *     `Type`, and has both entries at `k` (`ex_falso_unsharp`). A
 *     well-formed context may have inconsistent assumptions, so
 *     consistency is a premise of its own.
 *   - `row_drop k ρ` (`Stella.Core.Rows.Split`) of a row of kind `Row ε`
 *     has kind `Row ε` and lacks `k` when `k` is a known key of `ρ`, in
 *     every context.
 *   - Split: in a consistent context, a kinded row with the canonical
 *     entry of `ent` is `( ent | row_drop key(ent) ρ )`, with the rest
 *     kinded and lacking `key(ent)`. This holds at both row element kinds:
 *     a record or variant row (`Row Type`) and an effect row
 *     (`Row Effect`).
 *)
module Stella.Core.Kinding.Sharp
open Stella.Core.Syntax
open Stella.Core.Rows
open Stella.Core.Rows.Split
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
module L = FStar.List.Tot

(** * Sharpness *)

val check_sharp (sg: sig) (g: ctx) (r: typ) (e: elt_kind)
  : Lemma (requires check sg g r (KRow e) /\ not (inconsistent (hyps g)))
          (ensures forall (e1 e2: centry).
                     L.mem e1 (row_entries (canon r)) /\ L.mem e2 (row_entries (canon r)) /\
                     fst e1 == fst e2 ==> snd e1 == snd e2)

(** Ex falso: in an inconsistent context a kinded row may have two
    entries at one key. *)
val ex_falso_unsharp (sg: sig) (g: ctx) (k: key) (t t': typ)
  : Lemma (requires inconsistent (hyps g) /\ struct_key k /\ check sg g t KType /\
                    check sg g t' KType)
          (ensures (let r = TRowExt (EntTy k t) (TRowExt (EntTy k t') TRowEmpty) in
                    check sg g r (KRow EType) /\
                    L.mem (k, PTy (canon t)) (row_entries (canon r)) /\
                    L.mem (k, PTy (canon t')) (row_entries (canon r))))

(** * Dropping a key from a kinded row *)

val check_row_drop (sg: sig) (g: ctx) (k: key) (r: typ) (e: elt_kind)
  : Lemma (requires check sg g r (KRow e)) (ensures check sg g (row_drop k r) (KRow e))

val check_drop_lacks (sg: sig) (g: ctx) (k: key) (r: typ) (e: elt_kind)
  : Lemma (requires check sg g r (KRow e) /\ L.mem k (known_keys r))
          (ensures entails (hyps g) (CLacks k (row_drop k r)))

(** * Splitting a kinded row at a key *)

val check_split (sg: sig) (g: ctx) (en: entry) (r: typ) (e: elt_kind)
  : Lemma (requires check sg g r (KRow e) /\ not (inconsistent (hyps g)) /\
                    L.mem (canon_ent en) (row_entries (canon r)))
          (ensures ty_eq r (TRowExt en (row_drop (ent_key en) r)) /\
                   check sg g (row_drop (ent_key en) r) (KRow e) /\
                   entails (hyps g) (CLacks (ent_key en) (row_drop (ent_key en) r)))

(** The split of an effect row at its entry `(k, E τ̄)`, as `perform`
    reads it. *)
val check_split_eff (sg: sig) (g: ctx) (k: key) (q: qname) (ts: list typ) (r: typ)
  : Lemma (requires check sg g r (KRow EEffect) /\ not (inconsistent (hyps g)) /\
                    L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)))
          (ensures ent_key (EntEff (eff_label k) q ts) == k /\
                   ty_eq r (TRowExt (EntEff (eff_label k) q ts) (row_drop k r)) /\
                   check sg g (row_drop k r) (KRow EEffect) /\
                   entails (hyps g) (CLacks k (row_drop k r)))

(** The split of a record or variant row at `k : τ`. *)
val check_split_ty (sg: sig) (g: ctx) (k: key) (t r: typ)
  : Lemma (requires check sg g r (KRow EType) /\ not (inconsistent (hyps g)) /\
                    L.mem (k, PTy (canon t)) (row_entries (canon r)))
          (ensures ty_eq r (TRowExt (EntTy k t) (row_drop k r)) /\
                   check sg g (row_drop k r) (KRow EType) /\
                   entails (hyps g) (CLacks k (row_drop k r)))

(** The split at `k` of the rest of `( k' : τ1 | ρ1 ) ≡ ( k : τ0 | ρ0 )`,
    `k ≠ k'`, both sides kinded: `k : τ0` is an entry of `ρ1`
    (`Stella.Core.Rows.Split.ext_other_entry`), so
    `ρ1 ≡ ( k : τ0 | ρd )` with `ρd = row_drop k ρ1` kinded and lacking
    `k` and `k'`. *)
val check_split_ty_other (sg: sig) (g: ctx) (k k': key) (t0 t1 r0 r1: typ)
  : Lemma (requires not (inconsistent (hyps g)) /\ k <> k' /\
                    ty_eq (TRowExt (EntTy k t0) r0) (TRowExt (EntTy k' t1) r1) /\
                    check sg g (TRowExt (EntTy k t0) r0) (KRow EType) /\
                    check sg g r1 (KRow EType) /\ entails (hyps g) (CLacks k' r1))
          (ensures (let rd = row_drop k r1 in
                    ty_eq r1 (TRowExt (EntTy k t0) rd) /\
                    check sg g (TRowExt (EntTy k t0) rd) (KRow EType) /\
                    check sg g rd (KRow EType) /\
                    entails (hyps g) (CLacks k rd) /\ entails (hyps g) (CLacks k' rd) /\
                    entails (hyps g) (CLacks k r0) /\ check sg g t0 KType))
