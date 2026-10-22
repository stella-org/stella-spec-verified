(**
 * Canonical forms: the run-time values of each class of type (spec 06
 * §Values, §Opaque values, §Pattern matching; spec 05 §Typing a chain;
 * design §2.1).
 *
 * A typed run-time value (`Stella.Core.Value.is_value`) whose type is equal
 * to one of the types the elimination forms read has the form of its
 * class:
 *
 *   - a function type `τ1 -{ρ}-> τ2`: a λ, an `openEff [ρ'] v`, or a chain
 *     whose cursor remainder is a function type, which is an unsaturated
 *     chain of a constructor or a foreign;
 *   - `forall (a : κ). σ`: a `Λ`, or a chain whose cursor remainder is a
 *     `forall`; `C => σ`: a constraint `Λ`, or a chain whose cursor
 *     remainder is a constrained type;
 *   - `Record ρ`: `{}` or `extend k v1 v2`, and at a key whose entry `ρ`
 *     holds, the field of the record has the payload type of the entry;
 *   - `Variant ρ`: a variant value, `inject k [ρ0] w` under any number of
 *     `weaken`s, and there is none at `Variant ()`;
 *   - a type constructor of class literal: a literal of that type, so a
 *     `Boolean` is `true` or `false`;
 *   - an instance `T [[κ̄]] σ̄` of a data type `T`: a chain headed by a
 *     constructor of `T`, at the kinds `κ̄`, whose fields at `σ̄` are
 *     defined;
 *   - an application of a type constructor of class opaque: `opaque ω [τ]`.
 *
 * The classes are told apart by the head of the canonical form of the
 * type. `canon` keeps the structure of applications, constructors and
 * quantifiers, so a type equal to an application of a type constructor
 * `q` has the head `q`, and one equal to a `forall` or a constrained type
 * has none. `Σ` records one class per type constructor, `prim_wf` gives the
 * names of `Prim` their classes, and the function class belongs to
 * `Function` alone, so a function type a chain's cursor reads is a
 * `t_fun`. A constructor's saturated remainder is an instance of its owner,
 * a data type that lists it (`ctor_owner_listed`), and a foreign's chain at
 * a saturated remainder is a redex, no value.
 *
 * Each lemma takes a derivation at any `Δ` and any row. The record field
 * reads the payload of the entry through sharpness (design §2.1), which
 * needs consistent hypotheses: an inconsistent context kinds a row with
 * two entries at one key (`Stella.Core.Kinding.Sharp.ex_falso_unsharp`).
 * The context of a closed run-time term is consistent
 * (`Stella.Core.Typing.Closed.closed_ctx_consistent`).
 *)
module Stella.Core.Typing.Canonical
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

(** * Constructors and their owners *)

(** A constructor is listed by its owner, whose class is `TcData cs`: the
    converse of `Stella.Core.Sig.Wf.ctor_of_data`. *)
val ctor_owner_listed (sg: sig) (c: qname) (ci: ctor_info) (cs: list qname)
  : Lemma (requires ctors_ok sg /\ sg.ctors c == Some ci /\ has_class sg ci.ct_owner (TcData cs))
          (ensures L.mem c cs)

(** * The opaque class *)

(** The types the elimination forms read are of no opaque class: an arrow,
    a record, a variant and a Boolean, by `prim_wf`, and an instance of a
    data type. *)
val prim_not_opaque (sg: sig) (a rho b rr: typ)
  : Lemma (requires prim_wf sg)
          (ensures not (opaque_type sg (t_fun a rho b)) /\ not (opaque_type sg (t_record rr)) /\
                   not (opaque_type sg (t_variant rr)) /\ not (opaque_type sg t_bool))

val data_not_opaque (sg: sig) (tq: qname) (ks: list kind) (ss: list typ) (cs: list qname)
  : Lemma (requires has_class sg tq (TcData cs))
          (ensures not (opaque_type sg (tapps (TCon tq ks) ss)))

(** * Abstractions *)

(** A value of a function type is a λ, an `openEff`, or a chain whose
    cursor remainder `σ` is a function type, its instance `θ(σ)` being
    equal to the type of the value. *)
val canonical_fun (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (a rho b: typ)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ ty_eq t (t_fun a rho b))
          (ensures ELam? v \/ EOpenEff? v \/
                   (V.value_head sg v /\
                    (match chain_cursor sg v with
                     | Some (s, th) -> Some? (as_function sg s) /\ ty_eq t (sub_ty th s)
                     | None -> False)))

(** A value of a `forall` type is a `Λ`, or a chain whose cursor remainder
    is a `forall`. *)
val canonical_forall (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (k: kind) (s0: typ)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ ty_eq t (TForall k s0))
          (ensures ETyLam? v \/
                   (V.value_head sg v /\
                    (match chain_cursor sg v with
                     | Some (s, th) -> TForall? s /\ ty_eq t (sub_ty th s)
                     | None -> False)))

(** A value of a constrained type is a constraint `Λ`, or a chain whose
    cursor remainder is a constrained type. *)
val canonical_constr (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (c: constr) (s0: typ)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ ty_eq t (TConstr c s0))
          (ensures ECLam? v \/
                   (V.value_head sg v /\
                    (match chain_cursor sg v with
                     | Some (s, th) -> TConstr? s /\ ty_eq t (sub_ty th s)
                     | None -> False)))

(** * Records *)

val canonical_record (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (rr: typ)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ ty_eq t (t_record rr))
          (ensures v == ERecEmpty \/ EExtend? v)

(** The field at `k` of a record value of type `Record rr`, `rr` a kinded
    row with the entry `k : pt`, is a value of type `pt`, at the row of the
    record and under no join point. In a consistent context the entries of
    `rr` at `k` have one payload (sharpness), so the field of the `extend`
    at `k` has the type `pt`. *)
val canonical_record_field (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (rr: typ) (k: key) (pt: typ)
  : Pure (w: exp & typing sg ln g [] w pt r)
         (requires sig_ok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\ V.is_value sg v /\
                   ty_eq t (t_record rr) /\ check sg g rr (KRow EType) /\ check sg g pt KType /\
                   L.mem (k, PTy (canon pt)) (row_entries (canon rr)))
         (ensures fun (| w, _ |) -> record_field k v == Some w /\ V.is_value sg w)

(** * Variants *)

(** A value of a variant type has a variant view: its key and payload are
    those of the `inject` under its `weaken`s. *)
val canonical_variant (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (rr: typ)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ ty_eq t (t_variant rr))
          (ensures Some? (variant_view v) /\ Some? (carrier_key v))

(** No value has the type `Variant ()`: the key of its view would be an
    entry of the empty row. *)
val canonical_variant_empty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (rr: typ)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v /\ ty_eq t (t_variant rr) /\
                    ty_eq rr TRowEmpty)
          (ensures False)

(** * Literals *)

(** A value of the type `lq`, a type constructor of class literal, is a
    literal of that type. *)
val canonical_lit (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (lq: qname)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ ty_eq t (TCon lq []) /\
                    has_class sg lq (TcIntrinsic ClsLiteral))
          (ensures (match v with
                    | ELit c -> ty_eq (lit_type c) (TCon lq []) /\ lit_of v == Some c
                    | _ -> False))

(** A value of type `Boolean` is `true` or `false`. *)
val canonical_bool (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ ty_eq t t_bool)
          (ensures v == bool_lit true \/ v == bool_lit false)

(** * Data types *)

(** A value of the instance `T [[κ̄]] σ̄` of a data type `T` whose
    constructors are `cs` is a chain `C [[κ̄]] ᾱ` of a constructor `C` of
    `cs`, at the kinds `κ̄`, and the fields of `C` at `σ̄` are defined: the
    premises of `Stella.Core.Typing.Ctor.ctor_value_fields_typing`. *)
val canonical_data (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (tq: qname) (ks: list kind) (ss: list typ) (cs: list qname)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ ty_eq t (tapps (TCon tq ks) ss) /\
                    has_class sg tq (TcData cs))
          (ensures (match ctor_head sg v, decompose_global_app v with
                    | Some c, Some (c', ks', _) ->
                      c' == c /\ ks' == ks /\ is_ctor sg c /\ L.mem c cs /\
                      Some? (ctor_fields sg c ks ss)
                    | _ -> False))

(** * Opaque types *)

(** A value of an application of a type constructor of class opaque is an
    `opaque ω [τ]`. *)
val canonical_opaque (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (t': typ)
  : Lemma (requires sig_ok sg /\ V.is_value sg v /\ ty_eq t t' /\ opaque_type sg t')
          (ensures EOpaque? v)
