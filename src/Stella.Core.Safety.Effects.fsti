(**
 * Effect safety (spec 06 §Properties; design §7).
 *
 *     steps sg G R N e R' N' e'      G ⊢ N; e →* N'; e'
 *
 * `steps` is the reflexive-transitive closure of `step` through terms: each
 * step goes to a term (`CTerm`), and a step to a fault ends a reduction
 * sequence, so it is no part of one.
 *
 * **Effect safety.** A closed program typed at the row `()` never reaches
 * `Ev_k[perform k.op [σ̄] v]` with no handler of key `k` enclosing the hole
 * (`unhandled_perform`, `effect_safety`). The proof composes two results:
 *
 *   - typing is preserved along the sequence (`steps_preservation`), one
 *     step at a time by `Stella.Core.Safety.Preservation.preservation`, at
 *     the same `Γ_R`, `Γ_N`, type and row `()`;
 *   - a term typed at `()` is no unhandled `perform`
 *     (`Stella.Core.Safety.Progress.Eff.unhandled_perform_untypable`):
 *     through `Ev_k` the entry the `perform` reads is one of `()`.
 *
 * A sequence may still reach a handled `perform`, which its clause then
 * reduces; only a `perform` that escapes every handler of its key is
 * excluded.
 *
 * The premises are those of preservation: a well-formed `Σ`, well-formed
 * run-time contexts and a conforming `G`. Effect safety is about typing
 * alone, so coverage (`covers`) and the preconditions (`pre_ok`) are not
 * among them. Those decide whether a term steps, and the statement is
 * about the terms a sequence reaches, however it ends.
 * Coverage preservation (`Stella.Core.Safety.Covers.preservation_covers`)
 * is a separate result, used to chain Progress along a sequence.
 *
 * The theorem is about the reduction relation as it stands: the pure head
 * rules and the rules of operations and handlers. None of these opens a
 * region, allocates a location or touches the store, so `Γ_R` and `Γ_N`
 * are the same along a sequence. Stages 7 and 8 add the rules of regions,
 * cells and recursive bindings, which extend `Γ_R` and `Γ_N`, and Effect
 * safety is established again for the relation they give.
 *)
module Stella.Core.Safety.Effects
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
open Stella.Core.Safety.Progress.Eff

(** * Reduction sequences *)

(** `G ⊢ N; e →* N'; e'`, through terms, with `R` and `R'` the region
    names allocated before and after. *)
noeq type steps (sg: sig) (gi: genv)
  : list atom -> store -> exp -> list atom -> store -> exp -> Type =
  (** No step. *)
  | Steps_Refl :
      #ra:list atom -> #st:store -> #e:exp ->
      steps sg gi ra st e ra st e

  (** A step to a term, then a sequence from it. *)
  | Steps_Step :
      #ra:list atom -> #st:store -> #e:exp ->
      #ra1:list atom -> #st1:store -> #e1:exp ->
      #ra':list atom -> #st':store -> #e':exp ->
      step sg gi ra st e ra1 st1 (CTerm e1) ->
      steps sg gi ra1 st1 e1 ra' st' e' ->
      steps sg gi ra st e ra' st' e'

(** * Preservation along a sequence *)

(** Every term of a sequence from a closed program has the program's type
    at the row `()`, under no join point. *)
val steps_preservation (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (#t: typ)
  (h: typing sg ln (closed_ctx rs) [] e t TRowEmpty)
  (s: steps sg gi ra st e ra' st' e')
  : Ghost (typing sg ln (closed_ctx rs) [] e' t TRowEmpty)
          (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi)
          (ensures fun _ -> True)

(** The same, for `typed`. `Γ_N = ln` and `Γ_R = rs` occur in the
    hypotheses alone, so they are explicit. *)
val steps_typed (#sg: sig) (#gi: genv) (ln: lctx) (rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (t: typ) (s: steps sg gi ra st e ra' st' e')
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    typed sg ln (closed_ctx rs) e t)
          (ensures typed sg ln (closed_ctx rs) e' t)

(** * Effect safety *)

(** Effect safety (spec 06 §Properties): no reduction sequence from a
    closed program typed `Γ_R; Γ_N; · ⊢ e : τ ! ()` reaches a term
    `Ev_k[perform k.op [σ̄] v]` in which no handler of key `k` encloses the
    hole. *)
val effect_safety (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (#t: typ)
  (h: typing sg ln (closed_ctx rs) [] e t TRowEmpty)
  (s: steps sg gi ra st e ra' st' e')
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi)
          (ensures ~(unhandled_perform sg e'))

(** Effect safety, for `typed`. *)
val effect_safety_typed (#sg: sig) (#gi: genv) (ln: lctx) (rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (t: typ) (s: steps sg gi ra st e ra' st' e')
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    typed sg ln (closed_ctx rs) e t)
          (ensures ~(unhandled_perform sg e'))
