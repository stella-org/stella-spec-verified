(**
 * The names of `Prim` that the typing rules mention, and the types built
 * from them (spec 05 §Basic rules, §Records and variants).
 *
 * Core has no syntax for arrows, records, variants or the literal types:
 * they are applications of type constructors of the reserved module `Prim`.
 * The typing rules name those constructors through the constants below and
 * read nothing of `Σ` for it. That `Σ` records each name with the kind and
 * the canonical-value class the rules assume of it is the condition
 * `Stella.Core.Sig.Wf.prim_wf`.
 *)
module Stella.Core.Prim
open Stella.Core.Syntax

(** * Names *)

(** `Prim.s` *)
let prim (s: string) : qname = { qmod = ["Prim"]; qid = s }

(** `Function τ1 ρ τ2`, written `τ1 -{ρ}-> τ2`. *)
let prim_function : qname = prim "Function"

let prim_record : qname = prim "Record"

let prim_variant : qname = prim "Variant"

(** The literal types. *)
let prim_int : qname = prim "Int"

let prim_number : qname = prim "Number"

let prim_string : qname = prim "String"

let prim_char : qname = prim "Char"

let prim_boolean : qname = prim "Boolean"

(** The data type `Unit`, and its only constructor `Prim.Unit`, which has the
    same qualified name in the table of constructors. `Unit` is not a
    literal type (spec 05 §Basic rules). *)
let prim_unit : qname = prim "Unit"

let prim_unit_ctor : qname = prim "Unit"

(** The intrinsic `IO`, of class opaque (spec 03 §`IO` is not an effect). *)
let prim_io : qname = prim "IO"

(** * Types *)

(** `litType(c)` (spec 05 §Basic rules). *)
let lit_type (c: lit) : typ =
  match c with
  | LInt _ -> TCon prim_int []
  | LNumber _ -> TCon prim_number []
  | LString _ -> TCon prim_string []
  | LChar _ -> TCon prim_char []
  | LBool _ -> TCon prim_boolean []

(** `τ1 -{ρ}-> τ2` *)
let t_fun (t1 r t2: typ) : typ = fun_ty prim_function t1 r t2

(** `Record ρ` *)
let t_record (r: typ) : typ = TApp (TCon prim_record []) r

(** `Variant ρ` *)
let t_variant (r: typ) : typ = TApp (TCon prim_variant []) r

let t_unit : typ = TCon prim_unit []

let t_bool : typ = TCon prim_boolean []
