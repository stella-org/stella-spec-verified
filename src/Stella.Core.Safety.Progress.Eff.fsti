(**
 * A `perform` in an `Ev_k`, handled and unhandled (spec 06 §Operations
 * and handlers, §Evaluation contexts, §Properties; design §7).
 *
 * The term `Ev_k[perform k.op [σ̄] v]` (`ev_k k fs`, `frames_ok sg fs`) is
 * an additional outcome of progress under a row other than `()`
 * (`Stella.Core.Safety.Progress.PIPerform`). Two facts decide what becomes
 * of it.
 *
 *   - **Handled.** Under `handle _ with h`, `h` of key `k`, it is a redex
 *     of an effect rule (`handled_perform_redex`). The `perform` reads in
 *     its row an entry of key `k`, which through `Ev_k` is an entry of the
 *     row `( E τ̄ | ρ )` of the handled computation. That row is sharp, so
 *     the entry is the handler's own `E τ̄`
 *     (`Stella.Core.Typing.Eff.handled_entry`), and `op` is an operation
 *     of `E`. The clauses cover the operations of `E` (`clauses_cover`),
 *     so `clause_of op` finds the clause, which binds as many types as the
 *     operation does and so as many as the `perform` writes. A `fast`
 *     clause gives the rule `EH_Fast`. A `full` clause gives `EH_Full`
 *     once its continuation type `κ`, instantiated at `σ̄`, is read as a
 *     function type: `TCL_Full` kinds `κ` at `Type` and makes it equal to
 *     a function type, and a type of kind `Type` equal to a function type
 *     is one syntactically (`kinded_fun_as_function`). The kinding rules out a row former,
 *     which may equal a type of any shape.
 *   - **Unhandled.** At the row `()` it is untypable
 *     (`unhandled_perform_untypable`): through `Ev_k` every effect entry
 *     of key `k` in the hole's row is one of the outer row
 *     (`Stella.Core.Typing.Eff.plug_typing`), the `perform` reads such an
 *     entry in the hole's row, and `()` has none. Effect safety (spec 06
 *     §Properties) rests on this lemma, and it leaves no `perform` at the
 *     root of progress.
 *)
module Stella.Core.Safety.Progress.Eff
open Stella.Core.Syntax
open Stella.Core.Rows
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
module V = Stella.Core.Value

(** A type of kind `Type` equal to a function type is a function type:
    `as_function` reads it. *)
val kinded_fun_as_function (sg: sig) (g: ctx) (t a r b: typ)
  : Lemma (requires prim_wf sg /\ check sg g t KType /\ ty_eq t (t_fun a r b))
          (ensures Some? (as_function sg t))

(** `Ev_k[perform k.op [σ̄] v]`: a `perform` whose key no `handle` frame
    of the evaluation context `fs` handles. *)
let unhandled_perform (sg: sig) (e: exp) : prop =
  exists (fs: list frame) (k: key) (op: opname) (ss: list typ) (v: exp).
    e == plug fs (EPerform k op ss v) /\ ev_k k fs /\ frames_ok sg fs

(** `handle Ev_k[perform k.op [σ̄] v] with h`, `h` of key `k`, typed in
    `closed_ctx rs`, is the redex of a rule of operations and handlers. *)
val handled_perform_redex (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#d: jctx) (#fs: list frame) (#k: key) (#op: opname) (#ss: list typ) (#v: exp)
  (#hd: handler) (#t #r: typ)
  (h: typing sg ln (closed_ctx rs) d (EHandle (plug fs (EPerform k op ss v)) hd) t r)
  : Pure (c: config & eff_head sg gi (EHandle (plug fs (EPerform k op ss v)) hd) c)
         (requires sig_ok sg /\ rctx_ok sg rs /\ frames_ok sg fs /\ ev_k k fs /\
                   V.is_value sg v /\ handler_key hd == k)
         (ensures fun _ -> True)

(** No term typed at the row `()`, under any `Δ`, in a well-formed
    context, is `Ev_k[perform k.op [σ̄] v]`, whatever its argument. *)
val unhandled_perform_untypable (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t: typ)
  (h: typing sg ln g d e t TRowEmpty)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g) (ensures ~(unhandled_perform sg e))
