(**
 * Coverage is preserved by a step (spec 06 §Coverage, §Properties;
 * design §7).
 *
 * `G covers e` (`Stella.Core.Semantics.Env.covers`) is what Progress needs
 * of the term, and Preservation carries it: when `G ⊢ N; e → N'; e'`
 * steps to a term and `G` covers `e`, `G` covers `e'`. This is a theorem
 * of its own, with coverage as an extra premise:
 * `Stella.Core.Safety.Preservation` keeps typing whether or not the term
 * is covered (spec 06 §Properties).
 *
 * Each rule keeps coverage for the reason spec 06 §Properties gives:
 *
 *   - a definition unfolded from `G` is covered by condition (1) of
 *     conformance (`genv_ok_covered`), and kind instantiation keeps its
 *     global names (`Stella.Core.Semantics.Covers.covers_kinst`);
 *   - a value a foreign returns is covered relative to its arguments by
 *     condition (3) (`outcome_ok`), and the arguments of a covered chain
 *     are covered (`covers_value_args`, `covers_relative_covers`). The
 *     condition speaks of typed calls, so the statement takes the
 *     derivation of the term;
 *   - every other rule substitutes, rearranges, or moves what the term
 *     already holds, and a kind or a type it substitutes carries no global
 *     name (`Stella.Core.Semantics.Covers`). A rule of operations and
 *     handlers builds its reduct from the handled computation, the
 *     `perform`'s argument, the handler and one of its clauses, each
 *     covered when the redex is, and the continuation and the reinstalled
 *     `handle` hold the context renamed, with a variable in its hole.
 *
 * The hypotheses are those of `Stella.Core.Safety.Preservation.preservation`,
 * plus the coverage of the term.
 *)
module Stella.Core.Safety.Covers
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Step

(** A step to a term keeps the coverage of a closed run-time term typed
    under conforming contexts. *)
val preservation_covers (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (#d: jctx) (#t #r: typ)
  (h: typing sg ln (closed_ctx rs) d e t r)
  (s: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    covers sg gi e)
          (ensures covers sg gi e')
