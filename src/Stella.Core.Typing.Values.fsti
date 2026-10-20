(**
 * Ambient independence of values (spec 05 §Basic rules; spec 06 §Values).
 *
 * A run-time value (`Stella.Core.Value.is_value`) performs no effect and
 * jumps nowhere: wherever it is typed, it has the same type under every
 * `Δ` and at every well-kinded ambient row (`value_typing`). The rule
 * that types a value form checks the ambient row and reads it nowhere
 * else, and reads `Δ` nowhere; its subterms are values again, and
 * `T_Conv` and `T_VariantValue` keep the term. A chain derived by the
 * ordinary application rules, in which the arrow's row is the ambient
 * row, is first re-derived by `chain_typing`
 * (`Stella.Core.Typing.Chain.chain_normal`), whose value arguments are
 * typed at the ambient row of the chain, and so at any.
 *
 * The new derivation is computed, so that a proof by induction on a
 * derivation can use it in place of the one it has.
 *)
module Stella.Core.Typing.Values
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot
module V = Stella.Core.Value

(** A typed value has its type under every `Δ` and at every kinded row. *)
val value_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (d': jctx) (r': typ)
  : Pure (typing sg ln g d' v t r')
         (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v /\ check sg g r' (KRow EEffect))
         (ensures fun _ -> True)

(** The arguments of a typed chain whose value arguments are values are
    well formed at every kinded row and `Δ`. *)
val value_chain_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (hc: chain_typing sg ln g d r e) (d': jctx) (r': typ)
  : Pure (chain_typing sg ln g d' r' e)
         (requires sig_ok sg /\ wf_ctx sg g /\ V.chain_values sg e /\ check sg g r' (KRow EEffect))
         (ensures fun _ -> True)

(** A list of values, such as the scrutinee values of a `match`. *)
val values_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#es: list exp)
  (#ts: list typ) (h: exps_typing sg ln g d r es ts) (d': jctx) (r': typ)
  : Pure (exps_typing sg ln g d' r' es ts)
         (requires sig_ok sg /\ wf_ctx sg g /\ L.for_all (V.is_value sg) es /\
                   check sg g r' (KRow EEffect))
         (ensures fun _ -> True)

(** The occurrences that the values of a `match` justify are justified at
    every kinded row and `Δ`. *)
val values_match_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (h: match_typing sg ln g d r th om) (d': jctx) (r': typ)
  : Pure (match_typing sg ln g d' r' th om)
         (requires sig_ok sg /\ wf_ctx sg g /\ L.for_all (V.is_value sg) th /\
                   check sg g r' (KRow EEffect))
         (ensures fun _ -> True)

(** `value_typing` as a statement. *)
val value_typing_exists (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp)
  (#t #r: typ) (h: typing sg ln g d v t r) (d': jctx) (r': typ)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v /\ check sg g r' (KRow EEffect))
          (ensures exists (h': typing sg ln g d' v t r'). True)
