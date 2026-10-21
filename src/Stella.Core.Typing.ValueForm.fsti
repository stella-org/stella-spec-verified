(**
 * The static value restriction implies the run-time value predicate
 * (spec 04 §Value forms; spec 06 §Values).
 *
 * `Stella.Core.Typing.Aux.value_form` is the restriction that `T_TyLam`
 * and `T_CLam` put on the body of a `Λ` and a constraint `Λ`;
 * `Stella.Core.Value.is_value` is the value grammar that evaluation stops
 * at. The second grammar contains the first, form by form: literals, `λ`,
 * `{}`, `Λ`, constraint `Λ`, `extend` and `inject` are values of both,
 * and a constructor chain whose value arguments are value forms
 * (`ctor_chain_form`) is a global application chain headed by a data
 * constructor (`value_head`) whose value arguments are values
 * (`chain_values`). A constructor heads a value whether its chain is
 * saturated or not, so no arity is read.
 *
 * The implication is syntactic. Both grammars ask `Σ` the same question
 * of the head of a chain, whether `global_scheme` classifies it as a
 * constructor, so it holds for every `Σ`, well formed or not.
 *)
module Stella.Core.Typing.ValueForm
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Typing.Aux
module V = Stella.Core.Value

(** A constructor chain is a run-time value chain headed by a constructor. *)
val ctor_chain_form_value (sg: sig) (e: exp)
  : Lemma (requires ctor_chain_form sg e)
          (ensures V.value_head sg e /\ V.chain_values sg e)

val value_form_is_value (sg: sig) (e: exp)
  : Lemma (requires value_form sg e) (ensures V.is_value sg e)
