(* Proof structure.

   Each inversion strips the conversions (`strip_conv`) and matches the
   rule of the form; `T_Chain` and `T_VariantValue` are excluded by the
   form being no chain and no value. The lemmas on cells go down the
   derivation of the cells and the layout together: at the first cell of
   the key the layout's entry has that key too. *)
module Stella.Core.Typing.Region
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Inversion
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module V = Stella.Core.Value

(* * Inversions *)

let inv_region #sg #ln #g #d #lay #es #body #t #r h =
  let s = strip_conv h in
  match s.cf_h with
  | T_Region #_ #_ #_ #_ #_ #_ #_ #b #r0 _ _ hes hb ->
    { rg_b = b; rg_r = r0; rg_init = hes; rg_body = hb; rg_facts = () }
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let inv_region_open #sg #ln #g #d #a #cells #body #t #r h =
  let s = strip_conv h in
  match s.cf_h with
  | T_RegionOpen #_ #_ #_ #_ #_ #_ #_ #lay #b #r0 _ _ _ hc hb ->
    { ro_lay = lay; ro_b = b; ro_r = r0; ro_cells = hc; ro_body = hb; ro_facts = () }
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let region_open_typing #sg #ln #g #a #cells #body #t #r ro d cells' body' hc hb =
  T_RegionOpen #sg #ln #g #d #a #cells' #body' #ro.ro_lay #ro.ro_b #ro.ro_r () () () hc hb

let inv_read_cell #sg #ln #g #d #a #k #t #r h =
  let s = strip_conv h in
  match s.cf_h with
  | T_ReadCell #_ #_ #_ #_ #_ #_ #lay #t0 #_ _ _ _ -> { rd_lay = lay; rd_t = t0; rd_facts = () }
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let inv_write_cell #sg #ln #g #d #a #k #e #t #r h =
  let s = strip_conv h in
  match s.cf_h with
  | T_WriteCell #_ #_ #_ #_ #_ #_ #_ #lay #t0 #r0 _ _ hv ->
    { wr_lay = lay; wr_t = t0; wr_r = r0; wr_arg = hv; wr_facts = () }
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

(* * Cells *)

let rec cells_typing_assoc #sg #ln #g #cells #lay hc k v
  : Pure (t: typ & typing sg ln g [] v t TRowEmpty)
         (requires L.assoc k cells == Some v)
         (ensures fun (| t, _ |) -> L.assoc k lay == Some t /\ V.is_value sg v)
         (decreases hc) =
  match hc with
  | TC_Cons #_ #_ #_ #k' #v' #t' _ hv hrest ->
    if k' = k then begin
      let hv : typing sg ln g [] v t' TRowEmpty = hv in
      (| t', hv |)
    end
    else cells_typing_assoc hrest k v

let rec cells_typing_update #sg #ln #g #cells #lay hc k v t hv
  : Pure (cells_typing sg ln g (cells_update cells k v) lay)
         (requires L.assoc k lay == Some t /\ V.is_value sg v)
         (ensures fun _ -> True)
         (decreases hc) =
  match hc with
  | TC_Cons #_ #_ #_ #k' #v' #t' sqv hv' hrest ->
    if k' = k then begin
      let hv : typing sg ln g [] v t' TRowEmpty = hv in
      TC_Cons #sg #ln #g #k' #v () hv hrest
    end
    else TC_Cons #sg #ln #g #k' sqv hv' (cells_typing_update hrest k v t hv)

let rec init_cells_typing #sg #ln #g lay #vs h
  : Pure (cells_typing sg ln g (init_cells (L.map fst lay) vs) lay)
         (requires L.for_all (V.is_value sg) vs)
         (ensures fun _ -> True)
         (decreases lay) =
  match lay with
  | [] -> TC_Nil
  | (k, t) :: lay' ->
    (match h with
     | TE_Cons hv hrest -> TC_Cons #sg #ln #g #k () hv (init_cells_typing lay' hrest))

(* * Opening *)

let enter_closed rs a lay =
  assert_norm (region_facts a 0 [] == [])

let unit_typing sg ln g d r =
  assert_norm (kinst_ty [] t_unit == t_unit);
  assert_norm (qkinds_wf g.nk []);
  assert (global_type sg prim_unit_ctor == Some (0, t_unit));
  T_Global #sg #ln #g #d #prim_unit_ctor #[] #0 #t_unit #r () () ()
