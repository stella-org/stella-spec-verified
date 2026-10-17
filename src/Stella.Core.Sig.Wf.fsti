(**
 * Well-formedness of the global signature `Σ`: the kinding conditions on
 * its entries (spec 01 §Kinds, §Kind schemes; spec 05 §Contexts).
 *
 *   - A type constructor's kind is a well-formed quantifiable kind under its
 *     kind variables and produces `Type`.
 *   - An effect's parameter kinds are well-formed quantifiable kinds with no
 *     kind variable. Each operation's binder kinds are too, and its argument
 *     and result types have kind `Type` under the effect's parameters and,
 *     inside them, the operation's binders (design §3.1).
 *   - The type of a data constructor, a foreign, and a top-level value has
 *     kind `Type` under its kind variables, with no type variable in scope.
 *
 * Each class of entry has its own condition, so that a fact needing only
 * one of them assumes only that one.
 *)
module Stella.Core.Sig.Wf
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
module L = FStar.List.Tot

(** * Entries *)

let tycon_ok (ti: tycon_info) : bool =
  kind_wf ti.tc_nk ti.tc_kind && qkind ti.tc_nk ti.tc_kind && result ti.tc_kind = KType

let op_ok (sg: sig) (params: list kind) (os: op_sig) : bool =
  let g = push_tvars (push_tvars (decl_ctx 0) params) os.binders in
  qkinds_wf 0 os.binders && check sg g os.arg KType && check sg g os.res KType

let rec ops_ok (sg: sig) (params: list kind) (ops: list (opname & op_sig))
  : Tot bool (decreases ops) =
  match ops with
  | [] -> true
  | (_, os) :: ops -> op_ok sg params os && ops_ok sg params ops

let effect_ok (sg: sig) (ei: effect_info) : bool =
  qkinds_wf 0 ei.eff_params && ops_ok sg ei.eff_params ei.eff_ops

(** A type scheme `forall k̄. σ` with `n = |k̄|`. *)
let scheme_ok (sg: sig) (n: nat) (t: typ) : bool = check sg (decl_ctx n) t KType

(** * The signature *)

let tycons_wf (sg: sig) : prop =
  forall (q: qname). match sg.tycons q with Some ti -> tycon_ok ti | None -> True

let effects_wf (sg: sig) : prop =
  forall (q: qname). match sg.effects q with Some ei -> effect_ok sg ei | None -> True

let ctors_wf (sg: sig) : prop =
  forall (q: qname). match sg.ctors q with Some ci -> scheme_ok sg ci.ct_nk ci.ct_ty | None -> True

let foreigns_wf (sg: sig) : prop =
  forall (q: qname).
    match sg.foreigns q with Some fi -> scheme_ok sg fi.fr_nk fi.fr_ty | None -> True

let values_wf (sg: sig) : prop =
  forall (q: qname). match sg.values q with Some vi -> scheme_ok sg vi.vl_nk vi.vl_ty | None -> True

let sig_wf (sg: sig) : prop =
  tycons_wf sg /\ effects_wf sg /\ ctors_wf sg /\ foreigns_wf sg /\ values_wf sg
