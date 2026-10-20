(**
 * The instances of the substitution lemma of term variables that the
 * reduction rules use (spec 06 §Ordinary reduction, §Join points,
 * §Pattern matching, §Operations and handlers; design §3.1).
 *
 * Each substitutes run-time values for the innermost term variables of a
 * context, the values typed in the context outside them, at any row and
 * any `Δ`. The substituted term keeps the type, the row and the `Δ` of
 * the original (`Stella.Core.Typing.Subst.Tm`):
 *
 *   - one value for one binder, `e[x := v]` (`subst1_tm`): the body of a
 *     `λ` (β), the body of a `let`, the tree under a decision tree's
 *     `bind`;
 *   - values `v̄`, written in order, for a telescope `x̄ : τ̄`: the last
 *     binder is index 0 (design §3.1), so index `i` takes the `i`-th value
 *     from the end, `sub_tm (list_esub (L.rev v̄))`. A `jump` hands its
 *     arguments to the parameters of its join point so; a `full` clause
 *     binds `x`, then `k`, and a `fast` clause `x` alone.
 *
 * β is the exception to the last: it concludes under any `Δ`, which the
 * caller picks as the `Δ` of the redex. The body of a `λ` is typed under
 * no join point, so neither it nor its contractum mentions a free join
 * index (`Stella.Core.Typing.Join.typing_jp_nil`).
 *)
module Stella.Core.Typing.Subst.Tm.Inst
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Wf
module L = FStar.List.Tot
module V = Stella.Core.Value

(** `e[x := v]`, `e` typed under `x : τ1`. *)
val typing_subst1_value (#sg: sig) (#ln: lctx) (#g: ctx) (#t1: typ) (#d: jctx)
  (#e: exp) (#t #r: typ) (h: typing sg ln (push_var g t1) d e t r)
  (#d0: jctx) (#v: exp) (#r0: typ) (hv: typing sg ln g d0 v t1 r0)
  : Pure (typing sg ln g d (subst1_tm v e) t r)
         (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True)

(** β: `(λ (x : τ1) / ρ'. e) v → e[x := v]`. The body is typed at its own
    row `ρ'` under no join point; the contractum is typed at `ρ'` under
    the `Δ` of the redex, `d`, whatever it is. *)
val typing_beta (#sg: sig) (#ln: lctx) (#g: ctx) (#t1: typ) (#body: exp) (#t2 #r': typ)
  (hb: typing sg ln (push_var g t1) [] body t2 r')
  (#d0: jctx) (#v: exp) (#r0: typ) (hv: typing sg ln g d0 v t1 r0) (d: jctx)
  : Pure (typing sg ln g d (subst1_tm v body) t2 r')
         (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True)

(** `let x : τ1 = v in e → e[x := v]`, at the `Δ` and the row of the
    `let`. The bound value is typed under no join point, as the bound side
    of a `let` is. *)
val typing_let_value (#sg: sig) (#ln: lctx) (#g: ctx) (#t1: typ) (#d: jctx)
  (#e2: exp) (#t #r: typ) (h2: typing sg ln (push_var g t1) d e2 t r)
  (#v: exp) (hv: typing sg ln g [] v t1 r)
  : Pure (typing sg ln g d (subst1_tm v e2) t r)
         (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True)

(** `e[x̄ := v̄]`, `e` typed under the telescope `x̄ : τ̄` and `v̄ : τ̄`. *)
val typing_subst_values (#sg: sig) (#ln: lctx) (#g: ctx) (#ts: list typ) (#d: jctx)
  (#e: exp) (#t #r: typ) (h: typing sg ln (push_vars g ts) d e t r)
  (#d0: jctx) (#r0: typ) (#vs: list exp) (hvs: exps_typing sg ln g d0 r0 vs ts)
  : Pure (typing sg ln g d (sub_tm (list_esub (L.rev vs)) e) t r)
         (requires sig_ok sg /\ wf_ctx sg g /\ L.for_all (V.is_value sg) vs)
         (ensures fun _ -> True)

(** `bind y o dt` with `θ(o) = v`: the tree with `v` for `y`, under the same
    `Ω`. *)
val dt_typing_bind_value (#sg: sig) (#ln: lctx) (#g: ctx) (#t_o: typ) (#d: jctx)
  (#om: octx) (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln (push_var g t_o) d om dt t r)
  (#d0: jctx) (#v: exp) (#r0: typ) (hv: typing sg ln g d0 v t_o r0)
  : Pure (dt_typing sg ln g d om (sub_tm_dt (scons v evar) dt) t r)
         (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v /\ octx_ok sg g om)
         (ensures fun _ -> True)
