(* The hypotheses of a context with no fact and no assumption are the
   empty list. *)
module Stella.Core.Typing.Closed
open Stella.Core.Syntax
open Stella.Core.Context
open Stella.Core.Entail
open Stella.Core.Typing.Aux

let no_hyps_consistent g = assert (hyps g == [])

let closed_ctx_consistent rs = no_hyps_consistent (closed_ctx rs)
