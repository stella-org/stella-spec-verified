(**
 * Preservation (spec 06 §Properties; design §7).
 *
 * A closed run-time term `e` is typed in `closed_ctx rs`, the context of
 * the regions `rs = Γ_R` alone, under the store typing `ln = Γ_N`. When
 * `G ⊢ N; e → N'; e'` steps to a term, `e'` has the derivation's type, row
 * and `Δ`:
 *
 *     Γ_R; Γ_N; Δ ⊢ e : τ ! ρ   and   e → e'   give   Γ_R; Γ_N; Δ ⊢ e' : τ ! ρ
 *
 * The theorem covers the steps that use no rule of regions and cells
 * (`Stella.Core.Semantics.Step.stage6_step`): the pure rules and the
 * rules of operations and handlers, at the root or under any evaluation
 * frame.
 *
 * The hypotheses are the part of the premises of spec 06 §Properties
 * that does not concern the store: a well-formed `Σ` (`sig_ok`),
 * well-formed run-time contexts (`rctx_ok`, `lctx_ok`), and a global
 * environment that conforms at them (`genv_ok`). The rest of the spec's
 * premises are left out, so the statement is stronger than the spec's:
 *
 *   - the store typing `⊢ N : Γ_N`, with the facts relating `R` to `Γ_R`.
 *     None of these rules reads or writes the store, allocates a location,
 *     or opens a region, so none needs them, and `Γ_R` and `Γ_N` are the
 *     same on both sides of a step;
 *   - that the term respects the preconditions of the foreigns it calls
 *     (`Stella.Core.Semantics.Step.pre_ok`). The rule for a saturated
 *     foreign chain has the precondition of its call as a premise of its
 *     own, so a step that calls a foreign already has it.
 *
 * `Δ`, `τ` and `ρ` are arbitrary. A step under an evaluation frame is a
 * step of the frame's hole, which stands at a `Δ` and a row of its own
 * (`Stella.Core.Typing.Plug.plug1_typing`): under `letjoin` the hole has a
 * join point in front of `Δ`, under `openEffC` its row is the operand
 * row, under `handle` the row with the handled element, under an open
 * region the row with the region, and under `fill` the row `()`. At the
 * root of a program `Δ = []` and `ρ = ()` (`preservation_typed`).
 *
 * A rule of operations and handlers rewrites
 * `handle Ev_k[perform k.op [σ̄] v] with h` to the body of the clause for
 * `op` with `b̄ := σ̄` and `x := v`: a `full` clause's body with the
 * continuation for `k`, a `fast` clause's body bound by a `let` around
 * the handler reinstalled. The `perform` reads in its row an element of
 * key `k`, which through `Ev_k` is an element of the row of the handled
 * computation; that row is sharp, so the element is the handler's own,
 * and the `perform` is typed at the instance the clause is typed at
 * (`Stella.Core.Typing.Eff`). The continuation and the `let` rebuild the
 * `handle` around `Ev_k[y]`, typed as the redex was with `y` at the type
 * of the `perform`.
 *
 * The reduct of each head rule is typed from the derivation of its redex
 * alone, except for two rules that read `G`. The unfolding of a top-level
 * value `M.x [[κ̄]]` takes the definition's derivation from condition (2)
 * of conformance, and a saturated foreign chain the derivation of the
 * adapter's value from condition (3). Conformance asserts that such a
 * derivation exists, so the derivation of the reduct is computed in the
 * `Ghost` effect: it is a proof object, and nothing runs it.
 *)
module Stella.Core.Safety.Preservation
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Step

(** A step to a term that uses no rule of regions and cells keeps the
    type, the row and the `Δ` of a derivation of a closed run-time term. *)
val preservation (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (#d: jctx) (#t #r: typ)
  (h: typing sg ln (closed_ctx rs) d e t r)
  (s: step sg gi ra st e ra' st' (CTerm e'))
  : Ghost (typing sg ln (closed_ctx rs) d e' t r)
          (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    stage6_step s)
          (ensures fun _ -> True)

(** At the root of a program: a closed term typed at `τ`, under no join
    point and at the row `()`, steps to a term of the same type, by a step
    that uses no rule of regions and cells. `Γ_N = ln`
    and `Γ_R = rs` occur in the hypotheses alone, so they are explicit. *)
val preservation_typed (#sg: sig) (#gi: genv) (ln: lctx) (rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (t: typ) (s: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    stage6_step s /\ typed sg ln (closed_ctx rs) e t)
          (ensures typed sg ln (closed_ctx rs) e' t)
