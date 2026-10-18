(**
 * The global signature `Σ` (design §4.1; spec 05 §Contexts).
 *
 * `Σ` is a record of lookup functions keyed by qualified names, one per
 * class of declaration. It is a parameter of every judgement and never
 * changes during checking. A kind scheme `forall k̄. κ` or a type scheme
 * `forall k̄. σ` is stored as the number of its kind variables together with
 * its body, in which `KVar i` is the `i`-th kind variable in written order
 * (spec 01 §Kind schemes).
 *
 * The kinding conditions on the entries are in `Stella.Core.Sig.Wf`.
 *)
module Stella.Core.Sig
open Stella.Core.Syntax
module L = FStar.List.Tot

(** * Type constructors *)

(** The canonical-value class of an intrinsic type constructor: how the
    values of a type with no data constructors are formed (spec 06 §Opaque
    values). *)
type canon_class =
  | ClsLiteral        (** a literal: `Int`, `Number`, `String`, `Char`, `Boolean` *)
  | ClsFunction       (** `λ`, an unsaturated application chain, `openEff`: `Function` *)
  | ClsRecord         (** `{}`, `extend`: `Record` *)
  | ClsVariant        (** `inject`, `weaken`: `Variant` *)
  | ClsOpaque         (** `opaque ω [τ]`: `IO` and every other intrinsic *)

(** Whether a type constructor is intrinsic or a data type. *)
type tycon_class =
  | TcIntrinsic : canon_class -> tycon_class
  | TcData      : ctors: list qname -> tycon_class    (** its data constructors *)

(** `T : forall k̄. κ`, with `tc_nk = |k̄|`. *)
type tycon_info = {
  tc_nk    : nat;
  tc_kind  : kind;
  tc_class : tycon_class;
}

(** * Effects *)

(** The signature `forall (b̄ : κ̄'). σ ->* τ` of an operation of an effect
    `E (ā : κ̄)`. `arg` (`σ`) and `res` (`τ`) stand under the operation's
    binders `b̄` and, outside them, the effect's parameters `ā`; the last
    binder of each telescope is index 0 (design §3.1). *)
type op_sig = {
  binders : list kind;
  arg     : typ;
  res     : typ;
}

(** `E (ā : κ̄) { op : σ }`. An effect constructor binds no kind variable
    (spec 01 §Kind schemes), so `eff_params` mentions none. *)
type effect_info = {
  eff_params : list kind;
  eff_ops    : list (opname & op_sig);
}

(** The signature of the operation `op` of an effect. *)
let op_of (ei: effect_info) (op: opname) : option op_sig = L.assoc op ei.eff_ops

(** * Data constructors, foreigns, and top-level values *)

(** `Ctor : forall k̄. σ`. `ct_owner` is the data type `Ctor` builds a value
    of, `ct_tag` tells it apart from the other constructors of that type
    (spec 04 §Decision trees), and `ct_arity` is its number of value
    arguments. *)
type ctor_info = {
  ct_owner : qname;
  ct_tag   : nat;
  ct_arity : nat;
  ct_nk    : nat;
  ct_ty    : typ;
}

(** `foreign f : forall k̄. σ`. `fr_observ_none` holds when the declaration
    asserts `#observ(none)` (spec 06 §Conformance of the global
    environment). *)
type foreign_info = {
  fr_nk          : nat;
  fr_ty          : typ;
  fr_observ_none : bool;
}

(** `M.x : forall k̄. σ` *)
type value_info = {
  vl_nk : nat;
  vl_ty : typ;
}

(** * The signature *)

noeq type sig = {
  tycons   : qname -> option tycon_info;
  effects  : qname -> option effect_info;
  ctors    : qname -> option ctor_info;
  foreigns : qname -> option foreign_info;
  values   : qname -> option value_info;
}
