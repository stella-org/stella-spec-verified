(**
 * The keys of `switchKey` branches and of layouts under the maps of the
 * metatheory (spec 04 §Decision trees, spec 05 §Regions).
 *
 * A `switchKey` names its keys three times: in the branches, in the split
 * `kts` of the variant row, and in the occurrences `o ? k` it adds to `Ω`.
 * `key_brs_typing` pairs the first two in order. The split row is kinded
 * as a `Row Type` row, so its keys, and with them the branch keys, are
 * structural; so are the keys of a layout, kinded as a row too.
 *
 *   - A renaming, a substitution and a kind instantiation map the types of
 *     a layout or a split and the trees of branches, never their keys or
 *     labels, so the distinctness premises of `switchKey`, `switchCtor`,
 *     `switchLit` and `region` are kept as they stand.
 *   - A region map maps keys too, but a structural key has no region
 *     reference, so it fixes the keys of a split, of the branches and of a
 *     layout, and the occurrence `o ? k` keeps its key.
 *
 * The split itself, `key_split`, is preserved by each map with no kinding
 * hypothesis (`Stella.Core.Typing.Aux.Lemmas.key_split_*`).
 *)
module Stella.Core.Typing.Keys
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Keys
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot

(** * Structural keys *)

(** The keys of a split of a kinded variant row are structural. *)
val key_split_keys_struct (sg: sig) (g: ctx) (vr: typ) (kts: list (key & typ)) (r': typ)
  : Lemma (requires check sg g vr (KRow EType) /\ key_split vr kts r')
          (ensures keys_struct (L.map fst kts))

(** The branches of a `switchKey` have the keys of the split, in order. *)
val key_brs_typing_keys (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r)
  : Lemma (L.map fst bs == L.map fst kts)

(** * Keys under renaming, substitution and kind instantiation *)

val ren_layout_keys (xi: ren) (l: list (key & typ)) : Lemma (L.map fst (ren_layout xi l) == L.map fst l)

val sub_layout_keys (sigma: tsub) (l: list (key & typ))
  : Lemma (L.map fst (sub_layout sigma l) == L.map fst l)

val kinst_layout_keys (ks: list kind) (l: list (key & typ))
  : Lemma (L.map fst (kinst_layout ks l) == L.map fst l)

val ren_ty_brs_labels (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Lemma (L.map fst (ren_ty_brs xi bs) == L.map fst bs)

val sub_ty_brs_labels (#lb: eqtype) (sigma: tsub) (bs: list (lb & dtree))
  : Lemma (L.map fst (sub_ty_brs sigma bs) == L.map fst bs)

val kinst_brs_labels (#lb: eqtype) (ks: list kind) (bs: list (lb & dtree))
  : Lemma (L.map fst (kinst_brs ks bs) == L.map fst bs)

val ren_tm_brs_labels (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Lemma (L.map fst (ren_tm_brs xi bs) == L.map fst bs)

val sub_tm_brs_labels (#lb: eqtype) (sigma: esub) (bs: list (lb & dtree))
  : Lemma (L.map fst (sub_tm_brs sigma bs) == L.map fst bs)

val ren_jp_brs_labels (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Lemma (L.map fst (ren_jp_brs xi bs) == L.map fst bs)

val rmap_brs_labels (#lb: eqtype) (f: nat -> region_ref -> region_ref) (d: nat)
  (bs: list (lb & dtree))
  : Lemma (L.map fst (rmap_brs f d bs) == L.map fst bs)

(** * Keys under region maps *)

(** A region map fixes structural keys: those of a layout or a split, and
    those of the branches of a `switchKey`. *)
val rmap_layout_keys (f: region_ref -> region_ref) (l: list (key & typ))
  : Lemma (requires keys_struct (L.map fst l)) (ensures L.map fst (rmap_layout f l) == L.map fst l)

val rmap_kbrs_keys (f: nat -> region_ref -> region_ref) (d: nat) (bs: list (key & dtree))
  : Lemma (requires keys_struct (L.map fst bs)) (ensures L.map fst (rmap_kbrs f d bs) == L.map fst bs)

(** The refinement `o ? k` of a branch at a structural key. *)
val rmap_occ_variant (f: region_ref -> region_ref) (o: occ) (k: key)
  : Lemma (requires struct_key k) (ensures rmap_occ f (OVariant o k) == OVariant (rmap_occ f o) k)

(** A layout kinded as a row keeps its keys under every region map. *)
val rmap_layout_row_keys (sg: sig) (g: ctx) (f: region_ref -> region_ref) (l: layout)
  : Lemma (requires check sg g (layout_row l) (KRow EType))
          (ensures L.map fst (rmap_layout f l) == L.map fst l)
