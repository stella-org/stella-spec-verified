(**
 * Facts about the auxiliary definitions of the typing relation
 * (`Stella.Core.Typing.Aux`).
 *
 *   - Closed contexts. A type kinded in `closed_ctx rs` stays kinded when
 *     the region domain grows, and in every context `g` whose region domain
 *     holds that of `rs`, `closed_ctx g.regions` among them. It has no type
 *     variable and no kind variable, so every renaming, substitution and
 *     kind instantiation fixes it; it is locally closed, and its atoms are
 *     regions of `rs`.
 *   - Location contexts. `lctx_ok sg rs ln` reads `rs` only through its
 *     region domain, which no map of the types of a context changes
 *     (`Stella.Core.Context.rdom_*`), and every location type is fixed by
 *     every type map, so the typing rules read `Γ_N` unchanged under every
 *     binder.
 *   - `switchKey` rows. The branch row commutes with renaming, substitution,
 *     kind instantiation and region maps, so `key_split` is preserved by each
 *     of them with no kinding hypothesis. The canonical entries of a branch
 *     row are those of its branches and of its tail, which gives the key and
 *     the payload of each branch in the split row, and the entries the
 *     residual keeps. Kinding a branch row kinds its payloads and its tail.
 *   - Variant values. `variant_view` sees through `weaken`; a variant is a
 *     value exactly when its payload is. Renamings, type substitutions and
 *     kind instantiations act on the view's payload alone, region maps on
 *     its key as well, and a term substitution on the payload of a term that
 *     has a view.
 *)
module Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Typing.Aux
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Closed contexts *)

(** The region domain of `rs` is included in that of `rs'`. *)
let regions_incl (rs rs': list (atom & layout)) : prop =
  forall (a: atom). L.mem a (L.map fst rs) ==> L.mem a (L.map fst rs')

val check_closed_mono (sg: sig) (rs rs': list (atom & layout)) (t: typ) (k: kind)
  : Lemma (requires check sg (closed_ctx rs) t k /\ regions_incl rs rs')
          (ensures check sg (closed_ctx rs') t k)

(** Kinding in `closed_ctx rs` weakens to every context in whose scope the
    regions of `rs` are. *)
val check_closed_weaken (sg: sig) (rs: list (atom & layout)) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ check sg (closed_ctx rs) t k /\
                    regions_incl rs g.regions)
          (ensures check sg g t k)

val check_closed_ctx (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ check sg (closed_ctx g.regions) t k)
          (ensures check sg g t k)

val check_closed_ren (sg: sig) (rs: list (atom & layout)) (t: typ) (k: kind) (xi: ren)
  : Lemma (requires check sg (closed_ctx rs) t k) (ensures ren_ty xi t == t)

val check_closed_sub (sg: sig) (rs: list (atom & layout)) (t: typ) (k: kind) (sigma: tsub)
  : Lemma (requires check sg (closed_ctx rs) t k) (ensures sub_ty sigma t == t)

val check_closed_kinst (sg: sig) (rs: list (atom & layout)) (t: typ) (k: kind) (ks: list kind)
  : Lemma (requires check sg (closed_ctx rs) t k) (ensures kinst_ty ks t == t)

val check_closed_lc (sg: sig) (rs: list (atom & layout)) (t: typ) (k: kind)
  : Lemma (requires check sg (closed_ctx rs) t k)
          (ensures lc_ty t /\ (forall (a: atom). L.mem a (frn_ty t) ==> L.mem a (L.map fst rs)))

(** * Location contexts *)

val lctx_ok_mono (sg: sig) (rs rs': list (atom & layout)) (ln: lctx)
  : Lemma (requires lctx_ok sg rs ln /\ regions_incl rs rs') (ensures lctx_ok sg rs' ln)

(** The region domain of a context is all `lctx_ok` reads of it. *)
val lctx_ok_rdom (sg: sig) (g g': ctx) (ln: lctx)
  : Lemma (requires rdom g == rdom g') (ensures lctx_ok sg g.regions ln == lctx_ok sg g'.regions ln)

val lctx_ok_nth (sg: sig) (rs: list (atom & layout)) (ln: lctx) (nu: nat) (t: typ)
  : Lemma (requires lctx_ok sg rs ln /\ L.nth ln nu == Some t)
          (ensures check sg (closed_ctx rs) t KType)

(** * `switchKey` rows *)

val brs_row_empty (kts: list (key & typ)) : Lemma (brs_row kts TRowEmpty == layout_row kts)

val ren_brs_row (xi: ren) (kts: list (key & typ)) (r: typ)
  : Lemma (ren_ty xi (brs_row kts r) == brs_row (ren_layout xi kts) (ren_ty xi r))

val sub_brs_row (sigma: tsub) (kts: list (key & typ)) (r: typ)
  : Lemma (sub_ty sigma (brs_row kts r) == brs_row (sub_layout sigma kts) (sub_ty sigma r))

val kinst_brs_row (ks: list kind) (kts: list (key & typ)) (r: typ)
  : Lemma (kinst_ty ks (brs_row kts r) == brs_row (kinst_layout ks kts) (kinst_ty ks r))

val rmap_brs_row (f: region_ref -> region_ref) (kts: list (key & typ)) (r: typ)
  : Lemma (rmap_ty f (brs_row kts r) == brs_row (rmap_layout f kts) (rmap_ty f r))

val key_split_ren (xi: ren) (r: typ) (kts: list (key & typ)) (r': typ)
  : Lemma (requires key_split r kts r')
          (ensures key_split (ren_ty xi r) (ren_layout xi kts) (ren_ty xi r'))

val key_split_sub (sigma: tsub) (r: typ) (kts: list (key & typ)) (r': typ)
  : Lemma (requires key_split r kts r')
          (ensures key_split (sub_ty sigma r) (sub_layout sigma kts) (sub_ty sigma r'))

val key_split_kinst (ks: list kind) (r: typ) (kts: list (key & typ)) (r': typ)
  : Lemma (requires key_split r kts r')
          (ensures key_split (kinst_ty ks r) (kinst_layout ks kts) (kinst_ty ks r'))

val key_split_rmap (f: region_ref -> region_ref) (r: typ) (kts: list (key & typ)) (r': typ)
  : Lemma (requires key_split r kts r')
          (ensures key_split (rmap_ty f r) (rmap_layout f kts) (rmap_ty f r'))

(** The canonical entries `k̄ : canon τ̄` of the branches. *)
let rec brs_entries (kts: list (key & typ)) : Tot (list centry) (decreases kts) =
  match kts with
  | [] -> []
  | (k, t) :: kts -> (k, PTy (canon t)) :: brs_entries kts

(** The entries of a branch row are those of its branches and of its tail,
    and its tails are those of its tail. *)
val mem_brs_row_entries (kts: list (key & typ)) (r: typ) (e: centry)
  : Lemma (L.mem e (row_entries (canon (brs_row kts r))) <==>
           L.mem e (brs_entries kts) \/ L.mem e (row_entries (canon r)))

val mem_brs_row_tails (kts: list (key & typ)) (r: typ) (c: ctyp)
  : Lemma (L.mem c (row_tails (canon (brs_row kts r))) <==> L.mem c (row_tails (canon r)))

val mem_brs_entries (kts: list (key & typ)) (k: key) (t: typ)
  : Lemma (requires L.mem (k, t) kts) (ensures L.mem (k, PTy (canon t)) (brs_entries kts))

(** Every key of `brs_entries kts` is a key of `kts`. *)
val brs_entries_keys (kts: list (key & typ)) (e: centry)
  : Lemma (requires L.mem e (brs_entries kts)) (ensures L.mem (fst e) (L.map fst kts))

(** The split row has the entries of the branches and of the residual, and
    the tails of the residual. *)
val key_split_entries (r: typ) (kts: list (key & typ)) (r': typ) (e: centry)
  : Lemma (requires key_split r kts r')
          (ensures L.mem e (row_entries (canon r)) <==>
                   L.mem e (brs_entries kts) \/ L.mem e (row_entries (canon r')))

val key_split_tails (r: typ) (kts: list (key & typ)) (r': typ) (c: ctyp)
  : Lemma (requires key_split r kts r')
          (ensures L.mem c (row_tails (canon r)) <==> L.mem c (row_tails (canon r')))

(** Each branch's key and payload are an entry of the split row. *)
val key_split_branch (r: typ) (kts: list (key & typ)) (r': typ) (k: key) (t: typ)
  : Lemma (requires key_split r kts r' /\ L.mem (k, t) kts)
          (ensures L.mem (k, PTy (canon t)) (row_entries (canon r)) /\ L.mem k (known_keys r))

(** An entry of the split row at a key no branch takes is an entry of the
    residual. *)
val key_split_residual (r: typ) (kts: list (key & typ)) (r': typ) (e: centry)
  : Lemma (requires key_split r kts r' /\ L.mem e (row_entries (canon r)) /\
                    not (L.mem (fst e) (L.map fst kts)))
          (ensures L.mem e (row_entries (canon r')))

(** An exhaustive split: the row has no tail, and its entries are the
    branches'. *)
val key_split_exhaustive (r: typ) (kts: list (key & typ))
  : Lemma (requires key_split r kts TRowEmpty)
          (ensures row_tails (canon r) == [] /\
                   (forall (e: centry). L.mem e (row_entries (canon r)) <==> L.mem e (brs_entries kts)))

(** A kinded branch row has payloads of kind `Type` and a kinded tail. *)
val check_brs_row (sg: sig) (g: ctx) (kts: list (key & typ)) (r: typ)
  : Lemma (requires check sg g (brs_row kts r) (KRow EType))
          (ensures layout_ok sg g kts /\ check sg g r (KRow EType))

(** * Variant values *)

val variant_payload_view (k: key) (e: exp)
  : Lemma (variant_payload k e ==
           (match variant_view e with
            | Some (k', v) -> if k' = k then Some v else None
            | None -> None))

val variant_view_value (sg: sig) (e: exp) (k: key) (v: exp)
  : Lemma (requires variant_view e == Some (k, v)) (ensures V.is_value sg e == V.is_value sg v)

(** The view of a mapped term is the mapped view. *)
let map_view (fk: key -> key) (fe: exp -> exp) (o: option (key & exp)) : option (key & exp) =
  match o with
  | Some (k, v) -> Some (fk k, fe v)
  | None -> None

val variant_view_ren_ty (xi: ren) (e: exp)
  : Lemma (variant_view (ren_ty_exp xi e) == map_view id (ren_ty_exp xi) (variant_view e))

val variant_view_sub_ty (sigma: tsub) (e: exp)
  : Lemma (variant_view (sub_ty_exp sigma e) == map_view id (sub_ty_exp sigma) (variant_view e))

val variant_view_kinst (ks: list kind) (e: exp)
  : Lemma (variant_view (kinst_exp ks e) == map_view id (kinst_exp ks) (variant_view e))

val variant_view_ren_tm (xi: ren) (e: exp)
  : Lemma (variant_view (ren_tm xi e) == map_view id (ren_tm xi) (variant_view e))

(** A term substitution may replace a variable by a variant, so the view is
    kept only where there is one. *)
val variant_view_sub_tm (sigma: esub) (e: exp)
  : Lemma (requires Some? (variant_view e))
          (ensures variant_view (sub_tm sigma e) == map_view id (sub_tm sigma) (variant_view e))

val variant_view_rmap (f: nat -> region_ref -> region_ref) (d: nat) (e: exp)
  : Lemma (variant_view (rmap_exp f d e) == map_view (rmap_key (f d)) (rmap_exp f d) (variant_view e))
