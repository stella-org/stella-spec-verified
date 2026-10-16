(* The proof of `canon_number_idem` and the decidable-equality checks of
   `Stella.Core.Syntax`. *)
module Stella.Core.Syntax
module U64 = FStar.UInt64
module I32 = FStar.Int32

let canon_number_idem (b: U64.t)
  : Lemma (canon_number (canon_number b) == canon_number b)
  = assert_norm (is_nan_bits canonical_nan)

(* Every syntactic class is an eqtype, as computational type equality
   (design §2) needs. Each ascription fails to check if a change to the AST
   loses decidable equality, e.g. through a function field. *)
let _ : eqtype = kind
let _ : eqtype = key
let _ : eqtype = typ
let _ : eqtype = entry
let _ : eqtype = constr
let _ : eqtype = lit
let _ : eqtype = exp
let _ : eqtype = dtree
let _ : eqtype = handler
