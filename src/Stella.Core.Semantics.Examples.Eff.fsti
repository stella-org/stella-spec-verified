(**
 * Steps of the rules of operations and handlers
 * (`Stella.Core.Semantics.Step.eff_head`; spec 06 §Operations and
 * handlers, §Where a handler finishes, §Evaluation contexts).
 *
 * The signature `eff_sig` is `Stella.Core.Semantics.Examples.ex_sig` with
 * one more effect, whose operation has a type binder:
 *
 *     effect Poly { poly : forall (b : Type). b ->* b }
 *
 * beside `Console { log : String ->* Unit }`. The environment is
 * `ex_genv`; no rule here reads it.
 *
 * Every handler of `Console` here except `h_z` (below) has the return
 * clause `return (x : Unit) -> idu x`, with `idu = λ (u : Unit) / (). u`,
 * and one clause for `log`. These handlers are closed, and shifting a
 * closed handler past the binder of the continuation
 * (`ren_handler (shift 1)`) leaves it as it is, so a continuation rebuilds
 * such a handler unchanged.
 *
 *   - The return clause: `handle Prim.Unit with h  →  idu Prim.Unit`.
 *   - A `full` clause resuming once, `full log (x, k) -> k Prim.Unit`:
 *     `handle (perform Console.log "hi") with h  →  K Prim.Unit` with the
 *     continuation `K = λ (y : Unit) / (). handle y with h`, its
 *     annotation read from the clause's `k : Unit -{()}-> Unit`.
 *   - A `full` clause resuming twice, `full log (x, k) -> k (k Prim.Unit)`:
 *     the step gives `K (K Prim.Unit)`, one function value applied twice.
 *     The inner application then steps, giving
 *     `K (handle Prim.Unit with h)` with the handler reinstalled by the
 *     continuation.
 *   - A `fast` clause, `fast log (x) -> Prim.Unit`:
 *     `handle (perform Console.log "hi") with h  →
 *     let y : Unit = Prim.Unit in handle y with h`, the `let` annotated
 *     with the instantiated result type `Unit`.
 *   - Two handlers of one key: in
 *     `handle (handle (perform Console.log "hi") with h_in) with h_out` the
 *     inner one answers, by a step under the frame `handle [] with h_out`.
 *     The outer one is not reached: the context between it and the
 *     `perform` holds a `handle` of the key `Console`, so it is no `Ev_k`.
 *   - A handler of another key on the way: `h_aux` handles the labelled
 *     element `aux : Console`, of key `aux`, so
 *     `handle (handle (perform Console.log "hi") with h_aux) with h` is
 *     answered by `h` through `Ev_k = handle [] with h_aux`, and the
 *     continuation rebuilds both handlers:
 *     `λ (y : Unit) / (). handle (handle y with h_aux) with h`.
 *   - A context under a binder: the term
 *     `handle (let w : Unit = perform Console.log "hi" in z) with h_z`
 *     has a free variable `z` (index 0 outside, index 1 in the body of the
 *     `let`), and `h_z`'s return clause mentions it too (index 1 under
 *     its binder). In the continuation they stand under one more binder,
 *     so the `let` body is `EVar 2` and the return clause `EVar 2`, while
 *     the hole is the parameter `EVar 0`.
 *   - An operation with a type binder: for
 *     `full poly [b] (x : b, k : b -{()}-> Int) -> let y : b = x in k y`,
 *     `perform Poly.poly [Int] 5` instantiates the continuation type
 *     `κ = b -{()}-> Int` to `Int -{()}-> Int`, which annotates the
 *     continuation, and the body becomes `let y : Int = 5 in K y`. The `fast` clause
 *     `fast poly [b] (x : b) -> x` gives `let y : Int = 5 in handle y with h`,
 *     the `let` annotated with `b[b := Int] = Int`.
 *)
module Stella.Core.Semantics.Examples.Eff
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Sig.Examples
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Ctx.Ren
open Stella.Core.Semantics.Step
open Stella.Core.Semantics.Examples
module L = FStar.List.Tot

(** * The signature *)

let poly_q : qname = base "Poly"

(** `poly : forall (b : Type). b ->* b` *)
let poly_sig : op_sig = { binders = [KType]; arg = TVar 0; res = TVar 0 }

let poly_info : effect_info = { eff_params = []; eff_ops = [("poly", poly_sig)] }

let eff_effects (q: qname) : option effect_info =
  if q = poly_q then Some poly_info else good_effects q

let eff_sig : sig = { ex_sig with effects = eff_effects }

(** * Terms *)

let console_q : qname = base "Console"

(** The element `Console` and its key. *)
let console_ent : entry = EntEff None console_q []

let console_key : key = EffectKey console_q

(** `Prim.Unit` *)
let unit_v : exp = EGlobal prim_unit_ctor []

(** `"hi"` *)
let hi : exp = ELit (LString [104; 105])

(** `perform Console.log "hi"` *)
let log_hi : exp = EPerform console_key "log" [] hi

(** `λ (u : Unit) / (). u` *)
let idu : exp = ELam t_unit TRowEmpty (EVar 0)

(** `{ handles ent ; return (x : Unit) -> idu x ; c }` *)
let console_handler (ent: entry) (c: clause) : handler =
  { h_ent = ent; h_ret_ty = t_unit; h_ret = EApp idu (EVar 0); h_clauses = [c] }

(** `k : Unit -{()}-> Unit`, the continuation type of a `full` clause for
    `log` in a handler at the row `()` with the answer type `Unit`. *)
let log_kt : typ = t_fun t_unit TRowEmpty t_unit

(** `λ (y : Unit) / (). handle y with h`, `h` closed. *)
let cont_unit (h: handler) : exp = ELam t_unit TRowEmpty (EHandle (EVar 0) h)

(** * The return clause *)

(** `full log (x : String, k : Unit -{()}-> Unit) -> k Prim.Unit` *)
let h_once : handler =
  console_handler console_ent (CFull "log" 0 t_string log_kt (EApp (EVar 0) unit_v))

val return_step :
  step eff_sig ex_genv [] [] (EHandle unit_v h_once) [] [] (CTerm (EApp idu unit_v))

(** * A `full` clause resuming once *)

val full_once_step :
  step eff_sig ex_genv [] [] (EHandle log_hi h_once) [] [] (CTerm (EApp (cont_unit h_once) unit_v))

(** * A `full` clause resuming twice *)

(** `full log (x : String, k : Unit -{()}-> Unit) -> k (k Prim.Unit)` *)
let h_twice : handler =
  console_handler console_ent
    (CFull "log" 0 t_string log_kt (EApp (EVar 0) (EApp (EVar 0) unit_v)))

(** `K (K Prim.Unit)` *)
let twice_reduct : exp = EApp (cont_unit h_twice) (EApp (cont_unit h_twice) unit_v)

val full_twice_step :
  step eff_sig ex_genv [] [] (EHandle log_hi h_twice) [] [] (CTerm twice_reduct)

(** The inner application resumes first, the argument before the function,
    and reinstalls the handler. *)
val twice_resume_step :
  step eff_sig ex_genv [] [] twice_reduct [] []
    (CTerm (EApp (cont_unit h_twice) (EHandle unit_v h_twice)))

(** * A `fast` clause *)

(** `fast log (x : String) -> Prim.Unit` *)
let h_fast : handler = console_handler console_ent (CFast "log" 0 t_string unit_v)

val fast_step :
  step eff_sig ex_genv [] [] (EHandle log_hi h_fast) [] []
    (CTerm (ELet t_unit unit_v (EHandle (EVar 0) h_fast)))

(** * Two handlers of one key *)

let h_in : handler = h_once

let h_out : handler = h_fast

let nested_same : exp = EHandle (EHandle log_hi h_in) h_out

(** The inner handler answers, under the outer one. *)
val nested_same_step :
  step eff_sig ex_genv [] [] nested_same [] []
    (CTerm (EHandle (EApp (cont_unit h_in) unit_v) h_out))

(** The context from the outer handler to the `perform` is no `Ev_k`. *)
val nested_outer_excluded : unit -> Lemma (~(ev_k console_key [FHandle h_in]))

(** * A handler of another key on the way *)

(** `aux : Console`, of key `aux` *)
let aux_ent : entry = EntEff (Some "aux") console_q []

let h_aux : handler = console_handler aux_ent (CFast "log" 0 t_string unit_v)

let crossing : exp = EHandle (EHandle log_hi h_aux) h_once

val crossing_ev_k : unit -> Lemma (handler_key h_aux <> console_key /\ ev_k console_key [FHandle h_aux])

val crossing_step :
  step eff_sig ex_genv [] [] crossing [] []
    (CTerm (EApp (ELam t_unit TRowEmpty (EHandle (EHandle (EVar 0) h_aux) h_once)) unit_v))

(** * A context under a binder *)

(** `h_once` with the return clause `return (x : Unit) -> z`, `z` free. *)
let h_z : handler = { h_once with h_ret = EVar 1 }

(** `let w : Unit = [] in z` *)
let let_z : frame = FLet t_unit (EVar 1)

let under_let : exp = EHandle (plug1 let_z log_hi) h_z

(** Past the binder of `y`, `z` is index 2 in both. *)
val under_let_shift : unit
  -> Lemma (ren_frames (shift 1) [let_z] == [FLet t_unit (EVar 2)] /\
           ren_handler (shift 1) h_z == { h_z with h_ret = EVar 2 })

val under_let_step :
  step eff_sig ex_genv [] [] under_let [] []
    (CTerm (EApp (ELam t_unit TRowEmpty
                    (EHandle (ELet t_unit (EVar 0) (EVar 2)) { h_z with h_ret = EVar 2 }))
                 unit_v))

(** * An operation with a type binder *)

let poly_ent : entry = EntEff None poly_q []

let poly_key : key = EffectKey poly_q

(** `perform Poly.poly [Int] 5` *)
let poly_5 : exp = EPerform poly_key "poly" [t_int] (lit_int 5l)

(** `k : b -{()}-> Int`, under the binder `b` (type index 0). *)
let poly_kt : typ = t_fun (TVar 0) TRowEmpty t_int

(** `full poly [b] (x : b, k : b -{()}-> Int) -> let y : b = x in k y`; in
    the body of the `let`, `y` is index 0, `k` index 1 and `x` index 2. *)
let h_poly : handler =
  { h_ent = poly_ent; h_ret_ty = t_int; h_ret = EVar 0;
    h_clauses = [CFull "poly" 1 (TVar 0) poly_kt (ELet (TVar 0) (EVar 1) (EApp (EVar 1) (EVar 0)))] }

(** `κ[b := Int] = Int -{()}-> Int`, and its parts. *)
val poly_kt_inst : unit
  -> Lemma (sub_ty (binders_tsub [t_int]) poly_kt == t_fun t_int TRowEmpty t_int /\
           as_function eff_sig (sub_ty (binders_tsub [t_int]) poly_kt) ==
             Some (t_int, TRowEmpty, t_int))

(** `K = λ (y : Int) / (). handle y with h_poly` *)
let cont_poly : exp = ELam t_int TRowEmpty (EHandle (EVar 0) h_poly)

val poly_full_step :
  step eff_sig ex_genv [] [] (EHandle poly_5 h_poly) [] []
    (CTerm (ELet t_int (lit_int 5l) (EApp cont_poly (EVar 0))))

(** `fast poly [b] (x : b) -> x` *)
let h_poly_fast : handler =
  { h_ent = poly_ent; h_ret_ty = t_int; h_ret = EVar 0;
    h_clauses = [CFast "poly" 1 (TVar 0) (EVar 0)] }

val poly_fast_step :
  step eff_sig ex_genv [] [] (EHandle poly_5 h_poly_fast) [] []
    (CTerm (ELet t_int (lit_int 5l) (EHandle (EVar 0) h_poly_fast)))
