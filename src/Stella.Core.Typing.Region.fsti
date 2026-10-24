(**
 * Typing the redexes of the rules of regions and cells (spec 05
 * §Regions; spec 06 §Run-time forms, §Regions, §Cells).
 *
 * ## Inversions
 *
 * `region [ℓ] ( k̄ : σ̄ ) @ ( ē ) in e` is typed by `T_Region` alone up to
 * conversion (`inv_region`), `region⟨a⟩ θ in e` by `T_RegionOpen`
 * (`inv_region_open`), `readCell a.k` by `T_ReadCell` (`inv_read_cell`)
 * and `writeCell a.k e` by `T_WriteCell` (`inv_write_cell`): none of
 * them is a chain or a value. `T_RegionOpen` is rebuilt from its
 * premises with other cells and another body, typed as they were
 * (`region_open_typing`).
 *
 * ## Cells
 *
 * The cells `θ` of an open region are typed against its layout key by key,
 * in order (`cells_typing`), so the first cell of a key and the first entry
 * of that key in the layout stand at the same position. The value
 * `θ(k)` a read finds has the type of the entry (`cells_typing_assoc`),
 * and a write of a value of that type keeps the cells typed
 * (`cells_typing_update`). The initial values of a `region`, typed against
 * the layout's types, are the cells of its opening (`init_cells_typing`).
 *
 * ## Opening
 *
 * A closed context has no type variable, so entering a region adds no
 * fact: it is the closed context of `Γ_R` with the region added
 * (`enter_closed`). `Prim.Unit`, the reduct of a write, has the type
 * `Unit` that `writeCell` has (`unit_typing`).
 *)
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
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Inversions *)

(** The premises of `T_Region` for `region [ℓ] lay @ (ē) in e` at `τ ! ρ`:
    the answer type `rg_b ≡ τ` and the outer row `rg_r ≡ ρ`. *)
noeq type region_inv (sg: sig) (ln: lctx) (g: ctx) (lay: layout) (es: list exp) (body: exp)
  (t r: typ) = {
  rg_b: typ;
  rg_r: typ;
  rg_init: exps_typing sg ln g [] rg_r es (L.map snd lay);
  rg_body: (a: atom{~(L.mem a (rdom g)) /\ ~(L.mem a (frn_exp body))} ->
             typing sg ln (enter_region g a lay) [] (open_region a body) rg_b
               (TRowExt (EntRegion (RFree a)) rg_r));
  rg_facts: squash (check sg g (layout_row lay) (KRow EType) /\ L.noRepeats (L.map fst lay) /\
                    check sg g rg_b KType /\ check sg g rg_r (KRow EEffect) /\
                    ty_eq rg_b t /\ ty_eq rg_r r);
}

val inv_region (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#lay: layout) (#es: list exp)
  (#body: exp) (#t #r: typ) (h: typing sg ln g d (ERegion lay es body) t r)
  : Pure (region_inv sg ln g lay es body t r) (requires True) (ensures fun _ -> True)

(** The premises of `T_RegionOpen` for `region⟨a⟩ θ in e` at `τ ! ρ`: the
    layout `ro_lay` of `a`, the answer type `ro_b ≡ τ` and the outer row
    `ro_r ≡ ρ`. *)
noeq type region_open_inv (sg: sig) (ln: lctx) (g: ctx) (a: atom) (cells: list (key & exp))
  (body: exp) (t r: typ) = {
  ro_lay: layout;
  ro_b: typ;
  ro_r: typ;
  ro_cells: cells_typing sg ln g cells ro_lay;
  ro_body: typing sg ln g [] body ro_b (TRowExt (EntRegion (RFree a)) ro_r);
  ro_facts: squash (L.assoc a g.regions == Some ro_lay /\
                    check sg (closed_ctx g.regions) ro_b KType /\
                    check sg (closed_ctx g.regions) ro_r (KRow EEffect) /\
                    ~(L.mem a (frn_ty ro_b @ frn_ty ro_r)) /\
                    ty_eq ro_b t /\ ty_eq ro_r r);
}

val inv_region_open (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#a: atom)
  (#cells: list (key & exp)) (#body: exp) (#t #r: typ)
  (h: typing sg ln g d (ERegionOpen a cells body) t r)
  : Pure (region_open_inv sg ln g a cells body t r) (requires True) (ensures fun _ -> True)

(** `T_RegionOpen` from its premises, with other cells and another body
    typed as they were, under any `Δ`. *)
val region_open_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#a: atom) (#cells: list (key & exp))
  (#body: exp) (#t #r: typ) (ro: region_open_inv sg ln g a cells body t r) (d: jctx)
  (cells': list (key & exp)) (body': exp)
  (hc: cells_typing sg ln g cells' ro.ro_lay)
  (hb: typing sg ln g [] body' ro.ro_b (TRowExt (EntRegion (RFree a)) ro.ro_r))
  : typing sg ln g d (ERegionOpen a cells' body') ro.ro_b ro.ro_r

(** The premises of `T_ReadCell` for `readCell a.k` at `τ ! ρ`: the layout
    `rd_lay` of `a` has the entry `k : rd_t`, `rd_t ≡ τ`. *)
noeq type read_inv (sg: sig) (g: ctx) (a: atom) (k: key) (t: typ) = {
  rd_lay: layout;
  rd_t: typ;
  rd_facts: squash (L.assoc a g.regions == Some rd_lay /\ L.assoc k rd_lay == Some rd_t /\
                    ty_eq rd_t t);
}

val inv_read_cell (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#a: atom) (#k: key) (#t #r: typ)
  (h: typing sg ln g d (EReadCell (RFree a) k) t r)
  : Pure (read_inv sg g a k t) (requires True) (ensures fun _ -> True)

(** The premises of `T_WriteCell` for `writeCell a.k e` at `τ ! ρ`: the
    layout `wr_lay` of `a` has the entry `k : wr_t`, `e` has the type
    `wr_t` at the row `wr_r ≡ ρ`, and `Unit ≡ τ`. *)
noeq type write_inv (sg: sig) (ln: lctx) (g: ctx) (a: atom) (k: key) (e: exp) (t r: typ) = {
  wr_lay: layout;
  wr_t: typ;
  wr_r: typ;
  wr_arg: typing sg ln g [] e wr_t wr_r;
  wr_facts: squash (L.assoc a g.regions == Some wr_lay /\ L.assoc k wr_lay == Some wr_t /\
                    ty_eq t_unit t /\ ty_eq wr_r r);
}

val inv_write_cell (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#a: atom) (#k: key) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d (EWriteCell (RFree a) k e) t r)
  : Pure (write_inv sg ln g a k e t r) (requires True) (ensures fun _ -> True)

(** * Cells *)

(** The first cell of the key `k` holds a value of the type of the first
    entry of `k` in the layout. *)
val cells_typing_assoc (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp))
  (#lay: layout) (hc: cells_typing sg ln g cells lay) (k: key) (v: exp)
  : Pure (t: typ & typing sg ln g [] v t TRowEmpty)
         (requires L.assoc k cells == Some v)
         (ensures fun (| t, _ |) -> L.assoc k lay == Some t /\ V.is_value sg v)

(** `θ[k ↦ v]`, for a value `v` of the type of the entry of `k`. *)
val cells_typing_update (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp))
  (#lay: layout) (hc: cells_typing sg ln g cells lay) (k: key) (v: exp) (t: typ)
  (hv: typing sg ln g [] v t TRowEmpty)
  : Pure (cells_typing sg ln g (cells_update cells k v) lay)
         (requires L.assoc k lay == Some t /\ V.is_value sg v)
         (ensures fun _ -> True)

(** `( k̄ ↦ v̄ )` for initial values `v̄` typed against the layout's types. *)
val init_cells_typing (#sg: sig) (#ln: lctx) (#g: ctx) (lay: layout) (#vs: list exp)
  (h: exps_typing sg ln g [] TRowEmpty vs (L.map snd lay))
  : Pure (cells_typing sg ln g (init_cells (L.map fst lay) vs) lay)
         (requires L.for_all (V.is_value sg) vs)
         (ensures fun _ -> True)

(** * Opening *)

(** Entering a region in the closed context of `Γ_R` gives the closed
    context of `Γ_R` with the region. *)
val enter_closed (rs: list (atom & layout)) (a: atom) (lay: layout)
  : Lemma (enter_region (closed_ctx rs) a lay == closed_ctx ((a, lay) :: rs) /\
           { closed_ctx rs with regions = (a, lay) :: (closed_ctx rs).regions } ==
           closed_ctx ((a, lay) :: rs))

(** `Prim.Unit : Unit`, under any `Δ`, at every kinded row. *)
val unit_typing (sg: sig) (ln: lctx) (g: ctx) (d: jctx) (r: typ)
  : Pure (typing sg ln g d unit_exp t_unit r)
         (requires sig_ok sg /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True)
