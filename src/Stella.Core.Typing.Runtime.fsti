(**
 * The run-time region context `Γ_R` (design §4.5; spec 06 §Regions).
 *
 * `Γ_R` stands at the start of every context of a run-time term
 * (`Stella.Core.Context`), so its layouts are read by `readCell`,
 * `writeCell` and `region⟨a⟩` wherever they stand. `rctx_ok sg rs` says
 * that it is well formed:
 *
 *   - its region names are distinct;
 *   - the keys of each layout are distinct;
 *   - each layout is well formed in `closed_ctx rs` (`layout_ok`): its
 *     keys are structural and its cell types have kind `Type`.
 *
 * The last is what `wf_ctx` asks of the layouts of a context, so
 * `closed_ctx rs` is a well-formed context (`rctx_ok_wf_ctx`); the two
 * distinctness conditions are the stronger run-time invariant.
 *
 * Every region a reduction creates is opened from a `region` whose layout
 * is kinded as a row in that closed context and has distinct keys, so
 * `Γ_R` stays well formed when such a region is added with a fresh name
 * (`rctx_ok_extend_row`).
 *)
module Stella.Core.Typing.Runtime
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Keys
open Stella.Core.Typing.Aux
module L = FStar.List.Tot

(** Every layout of `rs` has distinct keys and is well formed in
    `closed_ctx rs0`. *)
let rec rlayouts_ok (sg: sig) (rs0 rs: list (atom & layout)) : Tot bool (decreases rs) =
  match rs with
  | [] -> true
  | (_, l) :: rs ->
    L.noRepeats (L.map fst l) && layout_ok sg (closed_ctx rs0) l && rlayouts_ok sg rs0 rs

let rctx_ok (sg: sig) (rs: list (atom & layout)) : bool =
  L.noRepeats (L.map fst rs) && rlayouts_ok sg rs rs

(** A well-formed `Γ_R` is a well-formed closed context. *)
val rctx_ok_wf_ctx (sg: sig) (rs: list (atom & layout))
  : Lemma (requires rctx_ok sg rs) (ensures wf_ctx sg (closed_ctx rs))

(** The layout of a region of a well-formed `Γ_R`: distinct keys, a well
    formed layout, and so structural keys. *)
val rctx_ok_assoc (sg: sig) (rs: list (atom & layout)) (a: atom) (l: layout)
  : Lemma (requires rctx_ok sg rs /\ L.assoc a rs == Some l)
          (ensures L.noRepeats (L.map fst l) /\ keys_struct (L.map fst l) /\
                   layout_ok sg (closed_ctx rs) l)

(** Adding a region with a fresh name and a layout of `closed_ctx rs`. *)
val rctx_ok_extend (sg: sig) (rs: list (atom & layout)) (a: atom) (l: layout)
  : Lemma (requires rctx_ok sg rs /\ ~(L.mem a (L.map fst rs)) /\ L.noRepeats (L.map fst l) /\
                    layout_ok sg (closed_ctx rs) l)
          (ensures rctx_ok sg ((a, l) :: rs))

(** The same, for a layout kinded as a row in `closed_ctx rs`, as a
    `region` has it. *)
val rctx_ok_extend_row (sg: sig) (rs: list (atom & layout)) (a: atom) (l: layout)
  : Lemma (requires rctx_ok sg rs /\ ~(L.mem a (L.map fst rs)) /\ L.noRepeats (L.map fst l) /\
                    check sg (closed_ctx rs) (layout_row l) (KRow EType))
          (ensures rctx_ok sg ((a, l) :: rs))

(** `lctx_ok` reads the regions of a context only, which no map of the
    context's types changes. *)
val lctx_ok_ren_ctx (sg: sig) (xi: ren) (g: ctx) (ln: lctx)
  : Lemma (lctx_ok sg (ren_ctx_types xi g).regions ln == lctx_ok sg g.regions ln)

val lctx_ok_sub_ctx (sg: sig) (sigma: tsub) (g: ctx) (ln: lctx)
  : Lemma (lctx_ok sg (sub_ctx_types sigma g).regions ln == lctx_ok sg g.regions ln)

val lctx_ok_kinst_ctx (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (ln: lctx)
  : Lemma (lctx_ok sg (kinst_ctx ks nk g).regions ln == lctx_ok sg g.regions ln)
