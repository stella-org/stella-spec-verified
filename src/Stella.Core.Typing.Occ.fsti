(**
 * Occurrences of the values of a `match`, and the branches a dispatch
 * selects (spec 06 §Pattern matching; spec 05 §Occurrence typing, §Join
 * points and decision trees; design §2.1, §6.1).
 *
 * `match θ dt` types `dt` under an `Ω` that the values `θ` justify
 * (`match_typing`), and a dispatch of `dt` reads `θ(o)` (`proj`) at its
 * occurrence `o`:
 *
 *   - Soundness of occurrences: an occurrence `o` typed in `Ω` at `τ` has a
 *     value `θ(o)` of type `τ` (`occ_sound`). An entry of `Ω` is justified
 *     by `match_typing`, and a record field by the canonical form of the
 *     record (`Stella.Core.Typing.Canonical.canonical_record_field`), which
 *     reads the payload of the field's entry through sharpness and so needs
 *     consistent hypotheses.
 *   - Branch selection: the branch a dispatch takes, `branch l bs`
 *     (`Stella.Core.Semantics.Step`), is typed under the `Ω` its typing
 *     rule gives it: the fields `o ! C . j ↦ τ_j` of the constructor, the
 *     payload `o ? k ↦ τ` of the key, or `Ω` itself for a literal.
 *   - Exhaustiveness: a `switchCtor` with no default has a branch for every
 *     constructor of its data type, and a `switchKey` with no default one
 *     for every key of its variant row, whose split has the residual `()`.
 *   - Defaults: in the default of a `switchKey`, the value `θ(o)` has the
 *     variant type `Variant ρ'` at the residual `ρ'` of the split, its key
 *     being none of the branches' (`T_VariantValue`).
 *   - Building `match_typing`: for the scrutinees of a `case`, for the
 *     fields of a constructor value, for the payload of a variant value, and
 *     for the concatenation of two occurrence contexts.
 *)
module Stella.Core.Typing.Occ
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * Projections of values *)

(** A projection of values is a value: a field of a constructor chain, a
    field of a record, or the payload of a variant. *)
val proj_value (sg: sig) (th: list exp) (o: occ) (v: exp)
  : Lemma (requires L.for_all (V.is_value sg) th /\ proj sg th o == Some v)
          (ensures V.is_value sg v)

(** The payload of a variant value at the key of its view. *)
val variant_payload_of_view (k: key) (v w: exp)
  : Lemma (requires variant_view v == Some (k, w)) (ensures variant_payload k v == Some w)

(** * Soundness of occurrences *)

(** An entry `o ↦ τ` of `Ω`, the most recent one at `o`, is justified by a
    value `θ(o)` of type `τ`. *)
val match_typing_lookup (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (hm: match_typing sg ln g d r th om) (o: occ) (t: typ)
  : Pure (v: exp & typing sg ln g d v t r)
         (requires L.assoc o om == Some t)
         (ensures fun (| v, _ |) -> proj sg th o == Some v)

(** `Ω ⊢ o : τ` gives a value `θ(o)` of type `τ`, at the row of `θ` and
    under no join point. *)
val occ_sound (#sg: sig) (#ln: lctx) (#g: ctx) (#r: typ) (#th: list exp) (#om: octx)
  (#o: occ) (#t_o: typ)
  (hm: match_typing sg ln g [] r th om) (ho: occ_typing sg g om o t_o)
  : Pure (v: exp & typing sg ln g [] v t_o r)
         (requires sig_ok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   L.for_all (V.is_value sg) th)
         (ensures fun (| v, _ |) -> proj sg th o == Some v /\ V.is_value sg v)

(** * Branch selection *)

(** The branch of a `switchCtor` at the constructor `c` names a constructor
    of the data type, and is typed with the fields of `c` at the instance
    added to `Ω`. *)
val ctor_brs_select (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#o: occ)
  (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree)) (#t #r: typ)
  (hb: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (c: qname) (dt: dtree)
  : Pure (fs: list typ & dt_typing sg ln g d (L.append (field_occs o c 0 fs) om) dt t r)
         (requires branch (Some c) bs == Some dt)
         (ensures fun (| fs, _ |) -> L.mem c cs /\ ctor_fields sg c ks ss == Some fs)

(** The branch of a `switchLit` at the literal `c` is typed under `Ω`, and
    `c` has the literal type of the dispatch. *)
val lit_brs_select (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#lt: typ)
  (#bs: list (lit & dtree)) (#t #r: typ)
  (hb: lit_brs_typing sg ln g d om lt bs t r) (c: lit) (dt: dtree)
  : Pure (dt_typing sg ln g d om dt t r)
         (requires branch (Some c) bs == Some dt)
         (ensures fun _ -> ty_eq (lit_type c) lt)

(** The branch of a `switchKey` at the key `k` has the payload type `pt`
    of `k` in the split, a type of kind `Type`, and is typed with
    `o ? k ↦ pt` added to `Ω`. *)
val key_brs_select (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#o: occ)
  (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (hb: key_brs_typing sg ln g d om o kts bs t r) (k: key) (dt: dtree)
  : Pure (pt: typ & dt_typing sg ln g d ((OVariant o k, pt) :: om) dt t r)
         (requires branch (Some k) bs == Some dt)
         (ensures fun (| pt, _ |) -> L.assoc k kts == Some pt /\ L.mem (k, pt) kts /\
                                    check sg g pt KType)

(** The payload `w` of a variant value of type `Variant vr` at a key `k`
    with the payload type `pt` in a split of `vr` has the type `pt`, at the
    row of the value and under no join point. In a consistent context the
    entries of `vr` at `k` have one payload (sharpness). *)
val variant_payload_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t_o #r: typ)
  (h: typing sg ln g d v t_o r) (vr: typ) (kts: list (key & typ)) (vr': typ) (k: key) (w: exp)
  (pt: typ)
  : Pure (typing sg ln g [] w pt r)
         (requires sig_ok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   ty_eq t_o (t_variant vr) /\ check sg g vr (KRow EType) /\
                   key_split vr kts vr' /\ L.mem (k, pt) kts /\ check sg g pt KType /\
                   variant_view v == Some (k, w))
         (ensures fun _ -> True)

(** * Exhaustiveness *)

(** A `switchCtor` with no default names every constructor of `cs`. *)
val ctor_brs_exhaustive (cs: list qname) (bs: list (qname & dtree)) (c: qname)
  : Lemma (requires (forall (c': qname). L.mem c' cs ==> L.mem c' (L.map fst bs)) /\ L.mem c cs)
          (ensures Some? (branch (Some c) bs))

(** A split with the residual `()` has a branch key for every entry of the
    row. *)
val key_split_exhaustive_key (vr: typ) (kts: list (key & typ)) (k: key) (p: cpayload)
  : Lemma (requires key_split vr kts TRowEmpty /\ L.mem (k, p) (row_entries (canon vr)))
          (ensures L.mem k (L.map fst kts))

(** A `switchKey` with no default has a branch at the key of every entry of
    its variant row. *)
val key_brs_exhaustive (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#o: occ)
  (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (hb: key_brs_typing sg ln g d om o kts bs t r) (vr: typ) (k: key) (p: cpayload)
  : Lemma (requires key_split vr kts TRowEmpty /\ L.mem (k, p) (row_entries (canon vr)))
          (ensures Some? (branch (Some k) bs))

(** * Defaults *)

(** In the default of a `switchKey` on `o : Variant vr`, whose branches
    split `vr` with the residual `vr'`, the value `θ(o)` has the type
    `Variant vr'`: its key is none of the branches', so its entry is one
    of `vr'` (`T_VariantValue`). *)
val key_default_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t_o #r: typ)
  (#d': jctx) (#om: octx) (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree))
  (#t #r': typ)
  (h: typing sg ln g d v t_o r) (hb: key_brs_typing sg ln g d' om o kts bs t r')
  (vr vr': typ)
  : Pure (typing sg ln g [] v (t_variant vr') r)
         (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v /\ ty_eq t_o (t_variant vr) /\
                   check sg g vr (KRow EType) /\ key_split vr kts vr' /\
                   check sg g vr' (KRow EType) /\ branch (carrier_key v) bs == None)
         (ensures fun _ -> True)

(** * Building `match_typing` *)

(** The scrutinees of a `case` justify `{ s_i ↦ τ_i }`. *)
val match_typing_scrut (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#ts: list typ) (h: exps_typing sg ln g d r th ts)
  : match_typing sg ln g d r th (scrut_occs 0 ts)

(** The fields of a constructor value `θ(o) = C [[κ̄]] ᾱ`, typed at `τ̄`,
    justify `{ o ! C . j ↦ τ_j }`. *)
val match_typing_fields (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (o: occ) (v: exp) (c: qname) (ks: list kind) (args: list spine_arg) (#fs: list typ)
  (hf: exps_typing sg ln g d r (value_args args) fs)
  : Pure (match_typing sg ln g d r th (field_occs o c 0 fs))
         (requires proj sg th o == Some v /\ decompose_global_app v == Some (c, ks, args) /\
                   is_ctor sg c)
         (ensures fun _ -> True)

(** The payload `w` of a variant value `θ(o)`, typed at `τ`, justifies
    `o ? k ↦ τ`. *)
val match_typing_variant (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (hm: match_typing sg ln g d r th om) (o: occ) (v: exp) (k: key) (#w: exp)
  (#pt: typ) (hw: typing sg ln g d w pt r)
  : Pure (match_typing sg ln g d r th ((OVariant o k, pt) :: om))
         (requires proj sg th o == Some v /\ variant_view v == Some (k, w))
         (ensures fun _ -> True)

val match_typing_append (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om1 #om2: octx) (h1: match_typing sg ln g d r th om1) (h2: match_typing sg ln g d r th om2)
  : match_typing sg ln g d r th (L.append om1 om2)
