(**
 * Progress for the pure fragment, one step (spec 06 §Properties; design §7).
 *
 * A closed well-typed term of the stage-5 fragment (`stage5_frag`) is a
 * value or takes a step, to a term or to a fault, when `G` covers it
 * (`covers`), conforms to `Σ` (`genv_ok`), and the term respects the
 * preconditions of the foreigns it is about to call (`pre_ok`). Every
 * step of the fragment is a pure head rule under an evaluation context
 * (`Stella.Core.Semantics.Step`). No such rule reads or writes `R` or the
 * store, so a step leaves both as they are
 * (`Stella.Core.Semantics.Step.step_term_shape`, `step_fault_shape`), and
 * the theorems need no store typing (`progress_top`). An unfolded
 * definition or a foreign's result may hold a form outside the fragment,
 * so the fragment is not closed under reduction, and the statement is
 * about one step.
 *
 * ## Join points
 *
 * Under a non-empty `Δ` a well-typed term has a third outcome: it is a
 * `jump` to a join point bound outside it, standing in a tail context `Tl`
 * of `letjoin` continuations (`tl_frames`) with value arguments. The jump
 * refers to its target by the index `n`; the `|Tl|` join points of `Tl`
 * come first, so `n` names the join point at `n - |Tl|` of `Δ`
 * (`Stella.Core.Typing.Plug.tl_typing`). `progress_in` states progress
 * under any `Δ` and at any row with this outcome. A `letjoin` whose
 * continuation is such a jump to its own join point, `n = |Tl|`, takes the
 * join rule (spec 06 §Join points); a jump past it is one more `letjoin`
 * frame of `Tl`. At the root `Δ = []`, so no jump is left (`progress_top`).
 *
 * The row is arbitrary: no rule of the fragment reads it, and the hole of
 * `openEffC` stands at a row of its own.
 *
 * ## What the premises give
 *
 *   - Canonical forms (`Stella.Core.Typing.Canonical`) give each
 *     elimination form at a value its redex, and rule out the stuck ones:
 *     `absurd` has no value to eliminate, a record of a type holding a
 *     key is an `extend`, a `guard` reads a Boolean literal, and a
 *     dispatch with no default meets a constructor or a key it names.
 *   - The values of a `match` justify its occurrences, so every
 *     projection a dispatch reads is defined
 *     (`Stella.Core.Typing.Occ.occ_sound`).
 *   - `covers` gives a top-level value its definition and a foreign its
 *     entry.
 *   - `pre_ok` gives the call of a saturated foreign chain its
 *     precondition, and condition (3) of `genv_ok`, read at `rs` and `ln`
 *     (`genv_ok_foreign`), gives the adapter's outcome at that typed
 *     call. `genv_ok_foreign` reads the condition at well-formed contexts
 *     only, so the theorems assume `rctx_ok` and `lctx_ok` as well.
 *)
module Stella.Core.Safety.Progress
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
module L = FStar.List.Tot
module V = Stella.Core.Value

(** * The statements *)

(** The outcomes of progress at the root: `e` is a value, or
    `G ⊢ N; e → N'; c` for some `R'`, `N'` and configuration `c`. *)
noeq type progress (sg: sig) (gi: genv) (ra: list atom) (st: store) (e: exp) =
  | PValue : squash (V.is_value sg e) -> progress sg gi ra st e
  | PStep  : ra': list atom -> st': store -> c: config ->
             step sg gi ra st e ra' st' c -> progress sg gi ra st e

(** The outcomes of progress under the join context `d`: those of
    `progress`, or `e` is `Tl[jump n (v̄)]` with `Tl = fs` a tail context,
    `v̄` values, and `n` naming a join point of `d`, the one at
    `n - |Tl|`. *)
noeq type pin (sg: sig) (gi: genv) (ra: list atom) (st: store) (d: jctx) (e: exp) =
  | PIValue : squash (V.is_value sg e) -> pin sg gi ra st d e
  | PIStep  : ra': list atom -> st': store -> c: config ->
              step sg gi ra st e ra' st' c -> pin sg gi ra st d e
  | PIJump  : fs: list frame -> n: nat -> vs: list exp ->
              squash (e == plug fs (EJump n vs) /\ tl_frames fs /\ L.for_all (V.is_value sg) vs /\
                      L.length fs <= n /\ n < L.length fs + L.length d) -> pin sg gi ra st d e

(** Progress under any `Δ` and at any row, for a term of the stage-5
    fragment typed in the context `closed_ctx rs` of a closed run-time
    term, under the premises of `progress_top`. The proof is by induction
    on the term: each form either has a subterm in an evaluation position
    that is no value, whose outcome is lifted through the frame, or is a
    value, a redex of a pure head rule, or a `jump` with value
    arguments. *)
val progress_in (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#d: jctx) (#e: exp) (#t #r: typ) (h: typing sg ln (closed_ctx rs) d e t r)
  (ra: list atom) (st: store)
  : Pure (pin sg gi ra st d e)
         (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                   stage5_frag e /\ covers sg gi e /\ pre_ok sg gi e)
         (ensures fun _ -> True)

(** Progress (spec 06 §Properties), for the stage-5 fragment and one step:
    a term typed `Γ_R; Γ_N; · ⊢ e : τ ! ()` under a well-formed `Σ`,
    `Γ_R = rs` and `Γ_N = ln`, covered by a conforming `G` and respecting
    the preconditions, is a value or steps.

    The premises are the part of the premises of spec 06 §Properties that
    does not concern the store, with `pre_ok`, the condition for one step,
    in place of the premise that the term respects the preconditions. The
    store typing `⊢ N : Γ_N` and the facts relating `R` to `Γ_R` are not
    among them, and `R` and the store are arbitrary.

    `genv_ok` and `lctx_ok` serve the foreign rule alone: condition (3)
    gives the adapter's outcome at a saturated call inside its
    precondition, which is the one premise of that rule the term and `G`'s
    coverage do not give. `rctx_ok` serves that rule too, and makes
    `closed_ctx rs` a well-formed context
    (`Stella.Core.Typing.Runtime.rctx_ok_wf_ctx`), which the lemmas that
    split a derivation at a frame and read canonical forms ask for. *)
val progress_top (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#e: exp) (#t: typ) (h: typing sg ln (closed_ctx rs) [] e t TRowEmpty)
  (ra: list atom) (st: store)
  : Pure (progress sg gi ra st e)
         (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                   stage5_frag e /\ covers sg gi e /\ pre_ok sg gi e)
         (ensures fun _ -> True)
