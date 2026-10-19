(* Proof structure.

   By induction on the row, following `check` at a row kind. An extension
   contributes the entry of its element, whose key is the element's key
   (`canon_ent_key`), and the entries of its tail; a union, those of its
   two sides (`view_nrow`, `mem_norm`). A type that is no row former is
   kinded by synthesis and canonicalizes to no row, so it has no entry. *)
module Stella.Core.Kinding.Keys
open Stella.Core.Syntax
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.OrdSet
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Facts
module L = FStar.List.Tot

let rec keys_struct_mem l k =
  match l with
  | k' :: l' -> if k = k' then () else keys_struct_mem l' k

let entry_key (sg: sig) (g: ctx) (en: entry) (e: elt_kind)
  : Lemma (requires entry_ok sg g en e)
          (ensures lc_key 0 (ent_key en) /\ in_rdom (frn_key (ent_key en)) g /\
                   (e == EType ==> struct_key (ent_key en))) =
  match en with
  | EntTy _ _ -> ()
  | EntEff lbl _ _ -> (match lbl with Some _ -> () | None -> ())
  | EntRegion _ -> ()

let rec row_entry_key sg g r e k p =
  match r with
  | TRowEmpty -> ()
  | TRowExt en r' ->
    let v = view_row (canon r') in
    view_nrow (canon_ent en :: fst v) (snd v);
    assert (canon r == nrow (canon_ent en :: fst v) (snd v));
    assert (L.mem (k, p) (norm ord_centry (canon_ent en :: fst v)));
    mem_norm ord_centry (canon_ent en :: fst v) (k, p);
    canon_ent_key en;
    if (k, p) = canon_ent en then entry_key sg g en e
    else row_entry_key sg g r' e k p
  | TRowUnion r1 r2 ->
    let v1 = view_row (canon r1) in
    let v2 = view_row (canon r2) in
    view_nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2));
    assert (canon r == nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2)));
    mem_norm ord_centry (L.append (fst v1) (fst v2)) (k, p);
    FStar.List.Tot.Properties.append_mem (fst v1) (fst v2) (k, p);
    if L.mem (k, p) (fst v1) then row_entry_key sg g r1 e k p
    else row_entry_key sg g r2 e k p
  | _ -> canon_nonrow r

let entry_key_scope (en: entry) (n: nat) (b: atom)
  : Lemma ((lc_ent_at n en ==> lc_key n (ent_key en)) /\
           (L.mem b (frn_key (ent_key en)) ==> L.mem b (frn_ent en))) =
  match en with
  | EntTy _ _ -> ()
  | EntEff lbl _ _ -> (match lbl with Some _ -> () | None -> ())
  | EntRegion _ -> ()

let rec row_entry_key_scope r n k p b =
  match r with
  | TRowEmpty -> ()
  | TRowExt en r' ->
    let v = view_row (canon r') in
    view_nrow (canon_ent en :: fst v) (snd v);
    assert (canon r == nrow (canon_ent en :: fst v) (snd v));
    mem_norm ord_centry (canon_ent en :: fst v) (k, p);
    canon_ent_key en;
    if (k, p) = canon_ent en then entry_key_scope en n b
    else row_entry_key_scope r' n k p b
  | TRowUnion r1 r2 ->
    let v1 = view_row (canon r1) in
    let v2 = view_row (canon r2) in
    view_nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2));
    assert (canon r == nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2)));
    mem_norm ord_centry (L.append (fst v1) (fst v2)) (k, p);
    FStar.List.Tot.Properties.append_mem (fst v1) (fst v2) (k, p);
    if L.mem (k, p) (fst v1) then row_entry_key_scope r1 n k p b
    else row_entry_key_scope r2 n k p b
  | _ -> canon_nonrow r

let rmap_key_struct f k = ()
