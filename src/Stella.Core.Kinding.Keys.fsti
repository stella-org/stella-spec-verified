(**
 * The keys of the canonical entries of a kinded row (spec 01 §Row
 * elements; design §2).
 *
 * The canonical entries of a row are those of the elements on its spine of
 * extensions and unions, so the key of each is the key of an element the
 * row writes. In a kinded row that element is well formed: its key names
 * no region out of scope and no bound region, and in a row of kind
 * `Row Type` it is structural. A typing rule that reads a key out of
 * `canon ρ` (`perform`, a record occurrence, the branches of a
 * `switchKey`) therefore reads a key of the scope of its context.
 *)
module Stella.Core.Kinding.Keys
open Stella.Core.Syntax
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Facts
module L = FStar.List.Tot

(** Every key of `l` is structural. *)
let rec keys_struct (l: list key) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | k :: l -> struct_key k && keys_struct l

val keys_struct_mem (l: list key) (k: key)
  : Lemma (requires keys_struct l /\ L.mem k l) (ensures struct_key k)

(** The key of a canonical entry of a kinded row is a key of the context's
    scope, and a structural one in a `Row Type` row. *)
val row_entry_key (sg: sig) (g: ctx) (r: typ) (e: elt_kind) (k: key) (p: cpayload)
  : Lemma (requires check sg g r (KRow e) /\ L.mem (k, p) (row_entries (canon r)))
          (ensures lc_key 0 k /\ in_rdom (frn_key k) g /\ (e == EType ==> struct_key k))

(** The same, read off the row alone: the key is locally closed where the row
    is, and its atoms are atoms of the row. *)
val row_entry_key_scope (r: typ) (n: nat) (k: key) (p: cpayload) (b: atom)
  : Lemma (requires L.mem (k, p) (row_entries (canon r)))
          (ensures (lc_ty_at n r ==> lc_key n k) /\ (L.mem b (frn_key k) ==> L.mem b (frn_ty r)))

(** A structural key has no region reference, so every region map fixes
    it. *)
val rmap_key_struct (f: region_ref -> region_ref) (k: key)
  : Lemma (requires struct_key k) (ensures rmap_key f k == k /\ lc_key 0 k /\ frn_key k == [])
