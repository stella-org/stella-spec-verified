(* Proof structure.

   Closed contexts: kinding reads the regions of a context only through
   its region domain, so moving between closed contexts with the same or a
   larger domain is the identity renaming (`check_ren`). Into an arbitrary
   `g`, the kind variables of `g` are added first, by instantiating the
   kind variables of `closed_ctx rs`, of which there are none, with the
   empty vector (`check_kinst`). That a closed type is fixed by every type
   map is `check_tvs_below` at no type variable, and by every kind
   instantiation `check_kinst_fixed`.

   `switchKey` rows: the maps act on a branch row entry by entry. Each
   entry of a branch row joins the entries of its tail through `nrow`,
   whose members are those of its argument (`view_nrow`, `mem_norm`). *)
module Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Region
open Stella.Core.OrdSet
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Facts
open Stella.Core.Typing.Aux
module L = FStar.List.Tot
module V = Stella.Core.Value

(* Closed contexts. *)

let check_closed_mono sg rs rs' t k =
  assert (ren_ok id_ren (closed_ctx rs) (closed_ctx rs'));
  check_ren sg id_ren (closed_ctx rs) (closed_ctx rs') t k;
  ren_ty_id t

let check_closed_weaken sg rs g t k =
  let g0 = kinst_ctx [] g.nk (closed_ctx rs) in
  check_kinst sg [] g.nk (closed_ctx rs) t k;
  kinst_ty_nil t;
  kinst_kind_nil k;
  rdom_kinst_ctx [] g.nk (closed_ctx rs);
  assert (ren_ok id_ren g0 g);
  check_ren sg id_ren g0 g t k;
  ren_ty_id t

let check_closed_ctx sg g t k = check_closed_weaken sg g.regions g t k

let check_closed_ren sg rs t k xi =
  check_tvs_below sg (closed_ctx rs) t k;
  ren_ty_as_sub xi t;
  sub_tvs_below 0 (ren_tsub xi) t

let check_closed_sub sg rs t k sigma =
  check_tvs_below sg (closed_ctx rs) t k;
  sub_tvs_below 0 sigma t

let check_closed_kinst sg rs t k ks = check_kinst_fixed sg (closed_ctx rs) t k ks

let check_closed_lc sg rs t k = check_lc sg (closed_ctx rs) t k

(* Location contexts. *)

let rec lctx_ok_mono (sg: sig) (rs rs': list (atom & layout)) (ln: lctx)
  : Lemma (requires lctx_ok sg rs ln /\ regions_incl rs rs') (ensures lctx_ok sg rs' ln)
          (decreases ln) =
  match ln with
  | [] -> ()
  | t :: ln' -> check_closed_mono sg rs rs' t KType; lctx_ok_mono sg rs rs' ln'

let lctx_ok_rdom sg g g' ln =
  if lctx_ok sg g.regions ln then lctx_ok_mono sg g.regions g'.regions ln;
  if lctx_ok sg g'.regions ln then lctx_ok_mono sg g'.regions g.regions ln

let rec lctx_ok_nth (sg: sig) (rs: list (atom & layout)) (ln: lctx) (nu: nat) (t: typ)
  : Lemma (requires lctx_ok sg rs ln /\ L.nth ln nu == Some t)
          (ensures check sg (closed_ctx rs) t KType) (decreases ln) =
  match ln with
  | _ :: ln' -> if nu = 0 then () else lctx_ok_nth sg rs ln' (nu - 1) t

(* `switchKey` rows. *)

let rec brs_row_empty (kts: list (key & typ))
  : Lemma (ensures brs_row kts TRowEmpty == layout_row kts) (decreases kts) =
  match kts with
  | [] -> ()
  | _ :: kts' -> brs_row_empty kts'

let rec ren_brs_row (xi: ren) (kts: list (key & typ)) (r: typ)
  : Lemma (ensures ren_ty xi (brs_row kts r) == brs_row (ren_layout xi kts) (ren_ty xi r))
          (decreases kts) =
  match kts with
  | [] -> ()
  | _ :: kts' -> ren_brs_row xi kts' r

let rec sub_brs_row (sigma: tsub) (kts: list (key & typ)) (r: typ)
  : Lemma (ensures sub_ty sigma (brs_row kts r) == brs_row (sub_layout sigma kts) (sub_ty sigma r))
          (decreases kts) =
  match kts with
  | [] -> ()
  | _ :: kts' -> sub_brs_row sigma kts' r

let rec kinst_brs_row (ks: list kind) (kts: list (key & typ)) (r: typ)
  : Lemma (ensures kinst_ty ks (brs_row kts r) == brs_row (kinst_layout ks kts) (kinst_ty ks r))
          (decreases kts) =
  match kts with
  | [] -> ()
  | _ :: kts' -> kinst_brs_row ks kts' r

let rec rmap_brs_row (f: region_ref -> region_ref) (kts: list (key & typ)) (r: typ)
  : Lemma (ensures rmap_ty f (brs_row kts r) == brs_row (rmap_layout f kts) (rmap_ty f r))
          (decreases kts) =
  match kts with
  | [] -> ()
  | _ :: kts' -> rmap_brs_row f kts' r

let key_split_ren xi r kts r' = ty_eq_ren xi r (brs_row kts r'); ren_brs_row xi kts r'

let key_split_sub sigma r kts r' = ty_eq_sub sigma r (brs_row kts r'); sub_brs_row sigma kts r'

let key_split_kinst ks r kts r' = ty_eq_kinst ks r (brs_row kts r'); kinst_brs_row ks kts r'

let key_split_rmap f r kts r' = ty_eq_rmap f r (brs_row kts r'); rmap_brs_row f kts r'

let rec mem_brs_row_view (kts: list (key & typ)) (r: typ) (e: centry) (c: ctyp)
  : Lemma (ensures (L.mem e (row_entries (canon (brs_row kts r))) <==>
                    L.mem e (brs_entries kts) \/ L.mem e (row_entries (canon r))) /\
                   (L.mem c (row_tails (canon (brs_row kts r))) <==> L.mem c (row_tails (canon r))))
          (decreases kts) =
  match kts with
  | [] -> ()
  | (k, t) :: kts' ->
    let v = view_row (canon (brs_row kts' r)) in
    let es = (k, PTy (canon t)) :: fst v in
    assert (canon (brs_row kts r) == nrow es (snd v));
    view_nrow es (snd v);
    mem_norm ord_centry es e;
    mem_norm ord_ctyp (snd v) c;
    mem_brs_row_view kts' r e c

let mem_brs_row_entries kts r e = mem_brs_row_view kts r e (CRow [] [])

let mem_brs_row_tails kts r c = mem_brs_row_view kts r (SymbolKey "", PRegion (RBound 0)) c

let rec mem_brs_entries (kts: list (key & typ)) (k: key) (t: typ)
  : Lemma (requires L.mem (k, t) kts) (ensures L.mem (k, PTy (canon t)) (brs_entries kts))
          (decreases kts) =
  match kts with
  | (k', t') :: kts' -> if k = k' && t = t' then () else mem_brs_entries kts' k t

let rec brs_entries_keys (kts: list (key & typ)) (e: centry)
  : Lemma (requires L.mem e (brs_entries kts)) (ensures L.mem (fst e) (L.map fst kts))
          (decreases kts) =
  match kts with
  | (k', t') :: kts' -> if e = (k', PTy (canon t')) then () else brs_entries_keys kts' e

let key_split_entries r kts r' e = mem_brs_row_entries kts r' e

let key_split_tails r kts r' c = mem_brs_row_tails kts r' c

let key_split_branch r kts r' k t =
  mem_brs_entries kts k t;
  mem_brs_row_entries kts r' (k, PTy (canon t));
  mem_ckeys k (canon r)

let key_split_residual r kts r' e =
  mem_brs_row_entries kts r' e;
  if L.mem e (brs_entries kts) then brs_entries_keys kts e

let no_mem_nil (#a: eqtype) (l: list a)
  : Lemma (requires forall (x: a). ~(L.mem x l)) (ensures l == []) =
  match l with
  | [] -> ()
  | x :: _ -> assert (L.mem x l)

let key_split_exhaustive r kts =
  introduce forall (c: ctyp). ~(L.mem c (row_tails (canon r)))
  with mem_brs_row_tails kts TRowEmpty c;
  no_mem_nil (row_tails (canon r));
  introduce forall (e: centry).
    L.mem e (row_entries (canon r)) <==> L.mem e (brs_entries kts)
  with mem_brs_row_entries kts TRowEmpty e

let rec check_brs_row (sg: sig) (g: ctx) (kts: list (key & typ)) (r: typ)
  : Lemma (requires check sg g (brs_row kts r) (KRow EType))
          (ensures layout_ok sg g kts /\ check sg g r (KRow EType)) (decreases kts) =
  match kts with
  | [] -> ()
  | (k, t) :: kts' -> check_ext_ty sg g k t (brs_row kts' r); check_brs_row sg g kts' r

(* Variant values. *)

let rec variant_payload_view (k: key) (e: exp)
  : Lemma (ensures variant_payload k e ==
                   (match variant_view e with
                    | Some (k', v) -> if k' = k then Some v else None
                    | None -> None))
          (decreases e) =
  match e with
  | EWeaken _ _ e' -> variant_payload_view k e'
  | _ -> ()

let rec variant_view_value (sg: sig) (e: exp) (k: key) (v: exp)
  : Lemma (requires variant_view e == Some (k, v)) (ensures V.is_value sg e == V.is_value sg v)
          (decreases e) =
  match e with
  | EWeaken _ _ e' -> variant_view_value sg e' k v
  | _ -> ()

let rec variant_view_ren_ty (xi: ren) (e: exp)
  : Lemma (ensures variant_view (ren_ty_exp xi e) == map_view id (ren_ty_exp xi) (variant_view e))
          (decreases e) =
  match e with
  | EWeaken _ _ e' -> variant_view_ren_ty xi e'
  | _ -> ()

let rec variant_view_sub_ty (sigma: tsub) (e: exp)
  : Lemma (ensures variant_view (sub_ty_exp sigma e) ==
                   map_view id (sub_ty_exp sigma) (variant_view e))
          (decreases e) =
  match e with
  | EWeaken _ _ e' -> variant_view_sub_ty sigma e'
  | _ -> ()

let rec variant_view_kinst (ks: list kind) (e: exp)
  : Lemma (ensures variant_view (kinst_exp ks e) == map_view id (kinst_exp ks) (variant_view e))
          (decreases e) =
  match e with
  | EWeaken _ _ e' -> variant_view_kinst ks e'
  | _ -> ()

let rec variant_view_ren_tm (xi: ren) (e: exp)
  : Lemma (ensures variant_view (ren_tm xi e) == map_view id (ren_tm xi) (variant_view e))
          (decreases e) =
  match e with
  | EWeaken _ _ e' -> variant_view_ren_tm xi e'
  | _ -> ()

let rec variant_view_sub_tm (sigma: esub) (e: exp)
  : Lemma (requires Some? (variant_view e))
          (ensures variant_view (sub_tm sigma e) == map_view id (sub_tm sigma) (variant_view e))
          (decreases e) =
  match e with
  | EWeaken _ _ e' -> variant_view_sub_tm sigma e'
  | _ -> ()

let rec variant_view_rmap (f: nat -> region_ref -> region_ref) (d: nat) (e: exp)
  : Lemma (ensures variant_view (rmap_exp f d e) ==
                   map_view (rmap_key (f d)) (rmap_exp f d) (variant_view e))
          (decreases e) =
  match e with
  | EWeaken _ _ e' -> variant_view_rmap f d e'
  | _ -> ()
