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
 *   - A name is at most one of a data constructor, a foreign, and a
 *     top-level value (`globals_disjoint`).
 *   - The operations of an effect have distinct names, so that `op_of`
 *     finds the one declaration of a name and a handler covers it by name.
 *
 * Separately, `prim_wf` says that `Σ` records the names of `Prim` that
 * the typing rules mention (`Stella.Core.Prim`) as the rules assume them.
 * `sig_ok` is the conjunction of the two, the assumption on `Σ` of the
 * typing relation's metatheory.
 *
 * Each class of entry has its own condition, so that a fact needing only
 * one of them assumes only that one.
 *)
module Stella.Core.Sig.Wf
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
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

let rec op_names (ops: list (opname & op_sig)) : Tot (list opname) (decreases ops) =
  match ops with
  | [] -> []
  | (op, _) :: ops -> op :: op_names ops

let effect_ok (sg: sig) (ei: effect_info) : bool =
  qkinds_wf 0 ei.eff_params && L.noRepeats (op_names ei.eff_ops) &&
  ops_ok sg ei.eff_params ei.eff_ops

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

(** Every name is recorded in at most one of the value-level tables, so a
    global is a data constructor, a foreign, or a top-level value, and never
    two of them. *)
let globals_disjoint (sg: sig) : prop =
  forall (q: qname).
    (Some? (sg.ctors q) ==> None? (sg.foreigns q) /\ None? (sg.values q)) /\
    (Some? (sg.foreigns q) ==> None? (sg.values q))

let sig_wf (sg: sig) : prop =
  tycons_wf sg /\ effects_wf sg /\ ctors_wf sg /\ foreigns_wf sg /\ values_wf sg /\
  globals_disjoint sg

(** * The names of `Prim` *)

(** `Σ` records the type constructor `q` with no kind variable, the kind
    `k`, and the class `c`. *)
let prim_tycon (sg: sig) (q: qname) (k: kind) (c: tycon_class) : bool =
  match sg.tycons q with
  | Some ti -> ti.tc_nk = 0 && ti.tc_kind = k && ti.tc_class = c
  | None -> false

(** The intrinsic class `c` belongs to the type constructor `q0` alone, so
    that a function, record or variant type is an application of the one
    constructor the rules name. *)
let class_unique (sg: sig) (c: canon_class) (q0: qname) : prop =
  forall (q: qname).
    (match sg.tycons q with Some ti -> ti.tc_class = TcIntrinsic c | None -> false) ==> q == q0

(** `Σ` records each name of `Prim` with its kind and class:

      Function                           : Type -> Row Effect -> Type -> Type   function
      Record, Variant                    : Row Type -> Type                     record, variant
      Int, Number, String, Char, Boolean : Type                                 literal
      IO                                 : Type -> Type                         opaque
      Unit                               : Type                                 data

    none with a kind variable. `Unit`'s only constructor is `Prim.Unit :
    Unit`, of tag 0 and arity 0. The function, record and variant classes
    belong to `Function`, `Record` and `Variant` alone. *)
let prim_wf (sg: sig) : prop =
  prim_tycon sg prim_function (KArrow KType (KArrow (KRow EEffect) (KArrow KType KType)))
    (TcIntrinsic ClsFunction) /\
  prim_tycon sg prim_record (KArrow (KRow EType) KType) (TcIntrinsic ClsRecord) /\
  prim_tycon sg prim_variant (KArrow (KRow EType) KType) (TcIntrinsic ClsVariant) /\
  prim_tycon sg prim_int KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_number KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_string KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_char KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_boolean KType (TcIntrinsic ClsLiteral) /\
  prim_tycon sg prim_io (KArrow KType KType) (TcIntrinsic ClsOpaque) /\
  prim_tycon sg prim_unit KType (TcData [prim_unit_ctor]) /\
  sg.ctors prim_unit_ctor ==
    Some ({ ct_owner = prim_unit; ct_tag = 0; ct_arity = 0; ct_nk = 0; ct_ty = t_unit }) /\
  class_unique sg ClsFunction prim_function /\
  class_unique sg ClsRecord prim_record /\
  class_unique sg ClsVariant prim_variant

(** The assumption on `Σ` of the typing relation's metatheory. *)
let sig_ok (sg: sig) : prop = sig_wf sg /\ prim_wf sg
