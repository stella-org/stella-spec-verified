(* Proof structure.

   Each fact is an induction on the list. The keys of a split are entries
   of the split row (`key_split_branch`), which `row_entry_key` makes
   structural. *)
module Stella.Core.Typing.Keys
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Keys
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Scope
module L = FStar.List.Tot

let rec split_keys_struct (sg: sig) (g: ctx) (vr: typ) (kts0: list (key & typ)) (r': typ)
  (kts: list (key & typ))
  : Lemma (requires check sg g vr (KRow EType) /\ key_split vr kts0 r' /\
                    (forall (kt: key & typ). L.mem kt kts ==> L.mem kt kts0))
          (ensures keys_struct (L.map fst kts)) (decreases kts) =
  match kts with
  | [] -> ()
  | (k, t) :: kts' ->
    key_split_branch vr kts0 r' k t;
    row_entry_key sg g vr EType k (PTy (canon t));
    split_keys_struct sg g vr kts0 r' kts'

let key_split_keys_struct sg g vr kts r' = split_keys_struct sg g vr kts r' kts

let rec key_brs_typing_keys #sg #ln #g #d #om #o #kts #bs #t #r h =
  match h with
  | TKB_Nil _ -> ()
  | TKB_Cons _ _ h' -> key_brs_typing_keys h'

let rec ren_layout_keys xi l =
  match l with
  | [] -> ()
  | _ :: l' -> ren_layout_keys xi l'

let rec sub_layout_keys sigma l =
  match l with
  | [] -> ()
  | _ :: l' -> sub_layout_keys sigma l'

let rec kinst_layout_keys ks l =
  match l with
  | [] -> ()
  | _ :: l' -> kinst_layout_keys ks l'

let rec ren_ty_brs_labels #lb xi bs =
  match bs with
  | [] -> ()
  | _ :: bs' -> ren_ty_brs_labels xi bs'

let rec sub_ty_brs_labels #lb sigma bs =
  match bs with
  | [] -> ()
  | _ :: bs' -> sub_ty_brs_labels sigma bs'

let rec kinst_brs_labels #lb ks bs =
  match bs with
  | [] -> ()
  | _ :: bs' -> kinst_brs_labels ks bs'

let rec ren_tm_brs_labels #lb xi bs =
  match bs with
  | [] -> ()
  | _ :: bs' -> ren_tm_brs_labels xi bs'

let rec sub_tm_brs_labels #lb sigma bs =
  match bs with
  | [] -> ()
  | _ :: bs' -> sub_tm_brs_labels sigma bs'

let rec ren_jp_brs_labels #lb xi bs =
  match bs with
  | [] -> ()
  | _ :: bs' -> ren_jp_brs_labels xi bs'

let rec rmap_brs_labels #lb f d bs =
  match bs with
  | [] -> ()
  | _ :: bs' -> rmap_brs_labels f d bs'

let rec rmap_layout_keys f l =
  match l with
  | [] -> ()
  | (k, _) :: l' -> rmap_key_struct f k; rmap_layout_keys f l'

let rec rmap_kbrs_keys f d bs =
  match bs with
  | [] -> ()
  | (k, _) :: bs' -> rmap_key_struct (f d) k; rmap_kbrs_keys f d bs'

let rmap_occ_variant f o k = rmap_key_struct f k

let rmap_layout_row_keys sg g f l =
  layout_row_struct sg g l;
  rmap_layout_keys f l
