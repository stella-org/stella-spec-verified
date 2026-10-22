(**
 * Splitting a row at a key, and cancelling a common entry (design §2.1).
 *
 *   - The canonical entries and tails of a row extension and of a row
 *     union, read as membership.
 *   - Sub-rows: `sub_row r' r` says that the known keys and the tails of
 *     `r'` are among those of `r`. Entailment is monotone along it
 *     (`Stella.Core.Entail.Split`).
 *   - `row_drop k ρ` removes every element with key `k` from the spine of
 *     extensions and unions of `ρ`. Its canonical entries are those of
 *     `canon ρ` whose key is not `k`, and its tails are those of
 *     `canon ρ`.
 *   - Split: a row whose only entry at `k` is `k : τ` is `( k : τ | ρ' )`
 *     with `ρ' = row_drop k ρ`. Uniqueness at `k` is a premise here; in a
 *     kinded row it follows from sharpness in a consistent context
 *     (`Stella.Core.Kinding.Sharp`). An effect entry `(k, E τ̄)` is split
 *     with the element its key determines (`eff_label`).
 *   - Cancellation: two extensions at a key that neither rest knows are
 *     equal only when their payloads and their rests are; the converse is
 *     `ty_eq_ext_cong` (`Stella.Core.Rows.Lemmas`).
 *
 * Every fact here is about canonical forms alone: none reads kinds or
 * entailment.
 *)
module Stella.Core.Rows.Split
open Stella.Core.Syntax
open Stella.Core.OrdSet
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
module L = FStar.List.Tot

(** * Entries and tails of extensions and unions *)

val mem_entries_ext (en: entry) (r: typ) (e: centry)
  : Lemma (L.mem e (row_entries (canon (TRowExt en r))) =
           (e = canon_ent en || L.mem e (row_entries (canon r))))

val tails_ext (en: entry) (r: typ) : Lemma (row_tails (canon (TRowExt en r)) == row_tails (canon r))

val mem_entries_union (a b: typ) (e: centry)
  : Lemma (L.mem e (row_entries (canon (TRowUnion a b))) =
           (L.mem e (row_entries (canon a)) || L.mem e (row_entries (canon b))))

val mem_tails_union (a b: typ) (c: ctyp)
  : Lemma (L.mem c (row_tails (canon (TRowUnion a b))) =
           (L.mem c (row_tails (canon a)) || L.mem c (row_tails (canon b))))

(** A type that is not a row former has no canonical entries, and is its
    own only tail. *)
val view_nonrow (t: typ)
  : Lemma (requires not (is_row_former t))
          (ensures row_entries (canon t) == [] /\ row_tails (canon t) == [canon t])

(** * Sub-rows *)

(** The known keys and the tails of `r'` are among those of `r`. *)
let sub_row (r' r: typ) : prop =
  (forall (k: key). L.mem k (known_keys r') ==> L.mem k (known_keys r)) /\
  (forall (c: ctyp). L.mem c (row_tails (canon r')) ==> L.mem c (row_tails (canon r)))

val sub_row_refl (r: typ) : Lemma (sub_row r r)

val sub_row_trans (r1 r2 r3: typ)
  : Lemma (requires sub_row r1 r2 /\ sub_row r2 r3) (ensures sub_row r1 r3)

val sub_row_ext (en: entry) (r: typ) : Lemma (sub_row r (TRowExt en r))

val sub_row_union_l (a b: typ) : Lemma (sub_row a (TRowUnion a b))

val sub_row_union_r (a b: typ) : Lemma (sub_row b (TRowUnion a b))

(** * Dropping a key *)

(** The entries of `es` whose key is not `k`, in order. *)
let rec ents_drop (k: key) (es: list centry) : Tot (list centry) (decreases es) =
  match es with
  | [] -> []
  | e :: es -> if fst e = k then ents_drop k es else e :: ents_drop k es

(** `ρ` with every element of key `k` removed from its spine of
    extensions and unions. Every other type, a tail included, is kept. *)
let rec row_drop (k: key) (t: typ) : Tot typ (decreases t) =
  match t with
  | TRowExt en r -> if ent_key en = k then row_drop k r else TRowExt en (row_drop k r)
  | TRowUnion a b -> TRowUnion (row_drop k a) (row_drop k b)
  | _ -> t

val mem_ents_drop (k: key) (es: list centry) (e: centry)
  : Lemma (L.mem e (ents_drop k es) = (fst e <> k && L.mem e es))

val row_drop_entries (k: key) (t: typ)
  : Lemma (row_entries (canon (row_drop k t)) == ents_drop k (row_entries (canon t)))

val row_drop_tails (k: key) (t: typ)
  : Lemma (row_tails (canon (row_drop k t)) == row_tails (canon t))

val mem_known_keys_drop (k k': key) (t: typ)
  : Lemma (L.mem k' (known_keys (row_drop k t)) = (k' <> k && L.mem k' (known_keys t)))

val sub_row_drop (k: key) (t: typ) : Lemma (sub_row (row_drop k t) t)

(** * Splitting a row at a key *)

(** A row whose only entry at `k` is `(k, p)` is that entry over the rest:
    the canonical form, with the entry given as a canonical entry. *)
val canon_split (k: key) (p: cpayload) (r: typ)
  : Lemma (requires L.mem (k, p) (row_entries (canon r)) /\
                    (forall (p': cpayload). L.mem (k, p') (row_entries (canon r)) ==> p' == p))
          (ensures canon r ==
                   nrow ((k, p) :: row_entries (canon (row_drop k r))) (row_tails (canon (row_drop k r))))

(** `ρ ≡ ( ent | row_drop key(ent) ρ )` when the entry of `ent` is the
    only entry of `ρ` at `key(ent)`. *)
val split_at (en: entry) (r: typ)
  : Lemma (requires L.mem (canon_ent en) (row_entries (canon r)) /\
                    (forall (p: cpayload).
                       L.mem (ent_key en, p) (row_entries (canon r)) ==> p == snd (canon_ent en)))
          (ensures ty_eq r (TRowExt en (row_drop (ent_key en) r)))

(** `ρ ≡ ( k : τ | row_drop k ρ )` when `k : τ` is the only entry of `ρ`
    at `k`. *)
val split_at_ty (k: key) (t r: typ)
  : Lemma (requires L.mem (k, PTy (canon t)) (row_entries (canon r)) /\
                    (forall (p: cpayload). L.mem (k, p) (row_entries (canon r)) ==> p == PTy (canon t)))
          (ensures ty_eq r (TRowExt (EntTy k t) (row_drop k r)))

(** The label of an effect element written at key `k`: `Some s` for the
    key `SymbolKey s` of a labelled element, `None` otherwise. *)
let eff_label (k: key) : option string =
  match k with
  | SymbolKey s -> Some s
  | _ -> None

(** A canonical effect entry `(k, E τ̄)` is that of the element
    `EntEff (eff_label k) E τ̄`: its key is `E` itself or a label. *)
val eff_entry_key (r: typ) (k: key) (q: qname) (cs: list ctyp)
  : Lemma (requires L.mem (k, PEff q cs) (row_entries (canon r)))
          (ensures eff_key (eff_label k) q == k)

(** `ρ ≡ ( k : E τ̄ | row_drop k ρ )`, written with the element of
    `eff_label k`, when `(k, E τ̄)` is the only entry of `ρ` at `k`. *)
val split_at_eff (k: key) (q: qname) (ts: list typ) (r: typ)
  : Lemma (requires L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)) /\
                    (forall (p: cpayload).
                       L.mem (k, p) (row_entries (canon r)) ==> p == PEff q (canon_tys ts)))
          (ensures ent_key (EntEff (eff_label k) q ts) == k /\
                   ty_eq r (TRowExt (EntEff (eff_label k) q ts) (row_drop k r)))

(** * Cancellation *)

(** `( ent | ρ0 ) ≡ ( ent' | ρ1 )` with a common key known to neither rest
    gives `ent ≡ ent'` and `ρ0 ≡ ρ1`. *)
val ext_cancel (e e': entry) (r0 r1: typ)
  : Lemma (requires ty_eq (TRowExt e r0) (TRowExt e' r1) /\ ent_key e == ent_key e' /\
                    not (L.mem (ent_key e) (known_keys r0)) /\
                    not (L.mem (ent_key e) (known_keys r1)))
          (ensures ent_eq e e' /\ ty_eq r0 r1)

val ext_ty_cancel (k: key) (t t' r0 r1: typ)
  : Lemma (requires ty_eq (TRowExt (EntTy k t) r0) (TRowExt (EntTy k t') r1) /\
                    not (L.mem k (known_keys r0)) /\ not (L.mem k (known_keys r1)))
          (ensures ty_eq t t' /\ ty_eq r0 r1)

(** * Extension under union *)

(** `( ent | ρ ) ⊎ ρ3 ≡ ( ent | ρ ⊎ ρ3 )`, from `ext_as_union` and
    `union_assoc` (`Stella.Core.Rows.Lemmas`). *)
val union_ext_l (en: entry) (r r3: typ)
  : Lemma (ty_eq (TRowUnion (TRowExt en r) r3) (TRowExt en (TRowUnion r r3)))
