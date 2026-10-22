(**
 * Consistency of the contexts a closed run-time term is typed in.
 *
 * A closed run-time term is typed in `closed_ctx rs`, and the definition
 * of a top-level value in `decl_ctx nk` with the regions of `Γ_R` in scope
 * (`Stella.Core.Typing.Kinst.decl_rctx`). Neither context has a fact or an
 * assumption, so its hypotheses are consistent and entailment there is no
 * ex falso: a lemma that asks `not (inconsistent (hyps g))`, such as those
 * of `Stella.Core.Entail.Split`, applies to them.
 *)
module Stella.Core.Typing.Closed
open Stella.Core.Syntax
open Stella.Core.Context
open Stella.Core.Entail
open Stella.Core.Typing.Aux

(** A context with no fact and no assumption has consistent hypotheses. *)
val no_hyps_consistent (g: ctx)
  : Lemma (requires g.facts == [] /\ g.assumps == []) (ensures not (inconsistent (hyps g)))

(** `closed_ctx rs`, the context of a closed run-time term, has consistent
    hypotheses. *)
val closed_ctx_consistent (rs: list (atom & layout))
  : Lemma (not (inconsistent (hyps (closed_ctx rs))))
