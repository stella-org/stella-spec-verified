(* Proof structure.

   By induction on the layouts. A cell type kinded in a closed context
   stays kinded when the closed context gains a region
   (`check_closed_mono`), so the layouts already in `Γ_R` stay well formed
   when it grows. *)
module Stella.Core.Typing.Runtime
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Keys
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing.Wf
module L = FStar.List.Tot

let rec rlayouts_regions_ok (sg: sig) (rs0 rs: list (atom & layout))
  : Lemma (requires rlayouts_ok sg rs0 rs)
          (ensures regions_ok sg (closed_ctx rs0) rs) (decreases rs) =
  match rs with
  | [] -> ()
  | _ :: rs' -> rlayouts_regions_ok sg rs0 rs'

let rctx_ok_wf_ctx sg rs = rlayouts_regions_ok sg rs rs

let rec rlayouts_assoc (sg: sig) (rs0 rs: list (atom & layout)) (a: atom) (l: layout)
  : Lemma (requires rlayouts_ok sg rs0 rs /\ L.assoc a rs == Some l)
          (ensures L.noRepeats (L.map fst l) /\ keys_struct (L.map fst l) /\
                   layout_ok sg (closed_ctx rs0) l) (decreases rs) =
  match rs with
  | (a', _) :: rs' ->
    if a = a' then layout_ok_keys_struct sg (closed_ctx rs0) l else rlayouts_assoc sg rs0 rs' a l

let rctx_ok_assoc sg rs a l = rlayouts_assoc sg rs rs a l

let rec layout_ok_closed_mono (sg: sig) (rs rs': list (atom & layout)) (l: layout)
  : Lemma (requires layout_ok sg (closed_ctx rs) l /\ regions_incl rs rs')
          (ensures layout_ok sg (closed_ctx rs') l) (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l' -> check_closed_mono sg rs rs' t KType; layout_ok_closed_mono sg rs rs' l'

let rec rlayouts_mono (sg: sig) (rs0 rs0' rs: list (atom & layout))
  : Lemma (requires rlayouts_ok sg rs0 rs /\ regions_incl rs0 rs0')
          (ensures rlayouts_ok sg rs0' rs) (decreases rs) =
  match rs with
  | [] -> ()
  | (_, l) :: rs' -> layout_ok_closed_mono sg rs0 rs0' l; rlayouts_mono sg rs0 rs0' rs'

let rctx_ok_extend sg rs a l =
  let rs' = (a, l) :: rs in
  assert (regions_incl rs rs');
  rlayouts_mono sg rs rs' rs;
  layout_ok_closed_mono sg rs rs' l

let rctx_ok_extend_row sg rs a l =
  layout_row_ok sg (closed_ctx rs) l;
  rctx_ok_extend sg rs a l

let lctx_ok_ren_ctx sg xi g ln =
  rdom_ren_ctx_types xi g;
  lctx_ok_rdom sg (ren_ctx_types xi g) g ln

let lctx_ok_sub_ctx sg sigma g ln =
  rdom_sub_ctx_types sigma g;
  lctx_ok_rdom sg (sub_ctx_types sigma g) g ln

let lctx_ok_kinst_ctx sg ks nk g ln =
  rdom_kinst_ctx ks nk g;
  lctx_ok_rdom sg (kinst_ctx ks nk g) g ln
