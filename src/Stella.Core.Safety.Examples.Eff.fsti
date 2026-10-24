(**
 * The safety theorems at the rules of operations and handlers (spec 06
 * §Operations and handlers, §Properties): preservation
 * (`Stella.Core.Safety.Preservation`, `Stella.Core.Safety.Covers`),
 * progress (`Stella.Core.Safety.Progress`) and Effect safety
 * (`Stella.Core.Safety.Effects`).
 *
 * The signature is `Stella.Core.Semantics.Examples.Eff.eff_sig`, which is
 * well formed (`eff_sig_ok`). The global environment is the empty one,
 * which conforms at every pair of run-time contexts (`empty_genv_ok`),
 * and the run-time contexts are empty. The steps are those of
 * `Stella.Core.Semantics.Examples.Eff`, taken in that environment, which
 * no rule of operations and handlers reads. No step allocates a region
 * name, so the run-time contexts after each step are empty as well
 * (`Stella.Core.Safety.Preservation.rdom_in_nil`).
 *
 *   - A `full` clause resuming once:
 *     `handle (perform Console.log "hi") with h_once : Unit ! ()` steps to
 *     `K Prim.Unit`, typed at `Unit ! ()` by `preservation`.
 *   - A `fast` clause:
 *     `handle (perform Console.log "hi") with h_fast : Unit ! ()` steps to
 *     `let y : Unit = Prim.Unit in handle y with h_fast`, typed at
 *     `Unit ! ()` by `preservation`.
 *   - A continuation that leaves its clause. The handler `h_reify` has the
 *     answer type `β = Unit -{()}-> Unit`, the return clause
 *     `return (x : Unit) -> λ (u : Unit) / (). x`, and the clause
 *     `full log (x : String, k : Unit -{()}-> β) -> λ (u : Unit) / (). k u u`,
 *     which returns the continuation wrapped in a λ instead of resuming.
 *     The program `(handle (perform Console.log "hi") with h_reify) Prim.Unit`
 *     applies the handler's answer outside the handler:
 *
 *         (handle (perform Console.log "hi") with h_reify) Prim.Unit
 *       → (λ (u : Unit) / (). K u u) Prim.Unit
 *       → K Prim.Unit Prim.Unit
 *
 *     with `K = λ (y : Unit) / (). handle y with h_reify`. The continuation
 *     is applied after the `handle` it came from has been removed, and it
 *     reinstalls the handler. The program is typed at `Unit`, and so is
 *     each term of the sequence (`preservation_typed`); each is covered by
 *     the environment (`preservation_covers`).
 *
 * Progress and Effect safety:
 *
 *   - `progress_top` applied to the derivations of
 *     `handle (perform Console.log "hi") with h_once` and of
 *     `reify_prog` gives each a step. Both programs are in the stage-6
 *     fragment, covered by the empty environment, and respect every
 *     precondition, since the empty environment has no foreign entry
 *     (`empty_genv_pre_ok`). The `perform` of each is an outcome of
 *     progress under the `handle`, which takes the `full` rule.
 *   - `effect_safety` applied to the run of `reify_prog` in two steps:
 *     no term of it is an unhandled `perform`. `reify_prog` holds a
 *     `perform` in an evaluation position, under a handler of its key.
 *)
module Stella.Core.Safety.Examples.Eff
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
open Stella.Core.Sig.Examples
open Stella.Core.Semantics.Examples
open Stella.Core.Semantics.Examples.Eff
open Stella.Core.Safety.Progress.Eff
open Stella.Core.Safety.Progress
open Stella.Core.Safety.Effects

(** The premises of preservation hold at `eff_sig`, the empty run-time
    contexts and the empty environment. *)
val eff_premises : unit
  -> Lemma (sig_ok eff_sig /\ rctx_ok eff_sig [] /\ lctx_ok eff_sig [] [] /\
            genv_ok eff_sig [] [] empty_genv)

(** * A `full` clause resuming once *)

val full_once_typing : typing eff_sig [] (closed_ctx []) [] (EHandle log_hi h_once) t_unit TRowEmpty

val full_once_step_e :
  step eff_sig empty_genv [] [] (EHandle log_hi h_once) [] [] (CTerm (EApp (cont_unit h_once) unit_v))

val full_once_reduct_typing : unit
  -> GTot (typing eff_sig [] (closed_ctx []) [] (EApp (cont_unit h_once) unit_v) t_unit TRowEmpty)

(** * A `fast` clause *)

val fast_typing : typing eff_sig [] (closed_ctx []) [] (EHandle log_hi h_fast) t_unit TRowEmpty

val fast_step_e :
  step eff_sig empty_genv [] [] (EHandle log_hi h_fast) [] []
    (CTerm (ELet t_unit unit_v (EHandle (EVar 0) h_fast)))

val fast_reduct_typing : unit
  -> GTot (typing eff_sig [] (closed_ctx []) [] (ELet t_unit unit_v (EHandle (EVar 0) h_fast))
             t_unit TRowEmpty)

(** * A continuation that leaves its clause *)

(** `β = Unit -{()}-> Unit` *)
let reify_ty : typ = t_fun t_unit TRowEmpty t_unit

(** `k : Unit -{()}-> β` *)
let reify_kt : typ = t_fun t_unit TRowEmpty reify_ty

(** `λ (u : Unit) / (). k u u`, under `x` and `k`: `u` is index 0, `k`
    index 1. *)
let reify_body : exp = ELam t_unit TRowEmpty (EApp (EApp (EVar 1) (EVar 0)) (EVar 0))

let h_reify : handler =
  { h_ent = console_ent; h_ret_ty = t_unit; h_ret = ELam t_unit TRowEmpty (EVar 1);
    h_clauses = [CFull "log" 0 t_string reify_kt reify_body] }

(** `(handle (perform Console.log "hi") with h_reify) Prim.Unit` *)
let reify_prog : exp = EApp (EHandle log_hi h_reify) unit_v

(** `K = λ (y : Unit) / (). handle y with h_reify` *)
let cont_reify : exp = ELam t_unit TRowEmpty (EHandle (EVar 0) h_reify)

(** `(λ (u : Unit) / (). K u u) Prim.Unit` *)
let reify_1 : exp = EApp (ELam t_unit TRowEmpty (EApp (EApp cont_reify (EVar 0)) (EVar 0))) unit_v

(** `K Prim.Unit Prim.Unit` *)
let reify_2 : exp = EApp (EApp cont_reify unit_v) unit_v

val reify_prog_typing : typing eff_sig [] (closed_ctx []) [] reify_prog t_unit TRowEmpty

(** The `full` rule, under the frame `[] Prim.Unit`. *)
val reify_step_1 : step eff_sig empty_genv [] [] reify_prog [] [] (CTerm reify_1)

(** β, applying the continuation's wrapper. *)
val reify_step_2 : step eff_sig empty_genv [] [] reify_1 [] [] (CTerm reify_2)

val reify_preserved : unit
  -> Lemma (typed eff_sig [] (closed_ctx []) reify_prog t_unit /\
            typed eff_sig [] (closed_ctx []) reify_1 t_unit /\
            typed eff_sig [] (closed_ctx []) reify_2 t_unit /\
            covers eff_sig empty_genv reify_1 /\ covers eff_sig empty_genv reify_2)

(** * Progress *)

(** The empty environment has no foreign entry, so every term respects
    the preconditions under it. *)
val empty_genv_pre_ok (sg: sig) (e: exp) : Lemma (pre_ok sg empty_genv e)

(** The premises of `progress_top` on the two programs. *)
val handled_terms_ok : unit
  -> Lemma (stage6_frag (EHandle log_hi h_once) /\ covers eff_sig empty_genv (EHandle log_hi h_once) /\
            stage6_frag reify_prog /\ covers eff_sig empty_genv reify_prog)

let full_once_progress : progress eff_sig empty_genv [] [] (EHandle log_hi h_once) =
  eff_premises ();
  handled_terms_ok ();
  empty_genv_pre_ok eff_sig (EHandle log_hi h_once);
  progress_top full_once_typing [] []

let reify_progress : progress eff_sig empty_genv [] [] reify_prog =
  eff_premises ();
  handled_terms_ok ();
  empty_genv_pre_ok eff_sig reify_prog;
  progress_top reify_prog_typing [] []

(** Neither program is a value, so progress gives each a step. *)
val handled_progress_steps : unit -> Lemma (PStep? full_once_progress /\ PStep? reify_progress)

(** * Effect safety *)

(** The run `reify_prog → reify_1 → reify_2`, and its prefixes. *)
let reify_run_0 : steps eff_sig empty_genv [] [] reify_prog [] [] reify_prog = Steps_Refl

let reify_run_1 : steps eff_sig empty_genv [] [] reify_prog [] [] reify_1 =
  Steps_Step reify_step_1 Steps_Refl

let reify_run_2 : steps eff_sig empty_genv [] [] reify_prog [] [] reify_2 =
  Steps_Step reify_step_1 (Steps_Step reify_step_2 Steps_Refl)

(** No term of the run is an unhandled `perform` (`effect_safety`). *)
val reify_effect_safe : unit
  -> Lemma (~(unhandled_perform eff_sig reify_prog) /\ ~(unhandled_perform eff_sig reify_1) /\
            ~(unhandled_perform eff_sig reify_2))
