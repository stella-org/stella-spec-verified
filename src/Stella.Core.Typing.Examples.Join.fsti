(**
 * The join-point discipline of `Stella.Core.Typing` on small terms, over
 * `Stella.Core.Typing.Examples.ex_sig`.
 *
 *   - A β-redex whose λ body is `letjoin j () : Int = 1 in jump j ()`,
 *     standing on the bound side of a `let`, and its contractum, where the
 *     `letjoin` itself stands there, have the same type: a `letjoin` and
 *     the `jump`s to it type wherever the `letjoin` stands.
 *   - A `jump` to an outer join point from a non-tail position has no
 *     type: from the definition of a join point defined on the bound side
 *     of a `let`, and from an application argument, for every `Γ` and `Δ`.
 *   - A `jump` to an outer join point from tail-transparent positions, the
 *     definition of a `letjoin` in a continuation, the body of a `let` and
 *     a leaf of a decision tree, has a type.
 *)
module Stella.Core.Typing.Examples.Join
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Prim
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Examples

let lit_int (n: Int32.t) : exp = ELit (LInt n)

(** `Prim.Unit` *)
let unit_v : exp = EGlobal prim_unit_ctor []

(** * A local join point on the bound side of a `let` *)

(** `letjoin j () : Int = 1 in jump j ()` *)
let local_join : exp = ELetJoin [] t_int (lit_int 1l) (EJump 0 [])

(** `let y : Int = (λ (_ : Unit) / (). letjoin j () : Int = 1 in jump j ()) Prim.Unit in y` *)
let beta_redex : exp = ELet t_int (EApp (ELam t_unit TRowEmpty local_join) unit_v) (EVar 0)

(** `let y : Int = (letjoin j () : Int = 1 in jump j ()) in y`, the
    contractum of the application. *)
let beta_contractum : exp = ELet t_int local_join (EVar 0)

(** The λ body does not mention its parameter, so the substitution of β
    leaves it as it is. *)
val beta_body_inst : unit -> Lemma (subst1_tm unit_v local_join == local_join)

val beta_redex_typing : typing ex_sig [] (decl_ctx 0) [] beta_redex t_int TRowEmpty

val beta_contractum_typing : typing ex_sig [] (decl_ctx 0) [] beta_contractum t_int TRowEmpty

(** * Jumps to an outer join point from a non-tail position *)

(** `letjoin j0 () : Int = 1 in
       let y : Int = (letjoin j1 () : Int = jump j0 () in jump j1 ()) in y`.
    The bound side of the `let` starts with no join point, so the
    definition of `j1` has `j1` alone in scope. *)
let jump_from_inner : exp =
  ELetJoin [] t_int (lit_int 1l)
    (ELet t_int (ELetJoin [] t_int (EJump 1 []) (EJump 0 [])) (EVar 0))

val jump_from_inner_untypable (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#t #r: typ)
  (h: typing sg ln g d jump_from_inner t r)
  : Lemma False

(** A `jump` as the argument of an application, whatever the function,
    `Γ` and `Δ`. *)
val jump_in_arg_untypable (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#t #r: typ)
  (f: exp) (j: nat) (es: list exp)
  (h: typing sg ln g d (EApp f (EJump j es)) t r)
  : Lemma False

(** `letjoin j () : Int = 1 in (λ (x : Int) / (). x) (jump j ())` *)
let jump_from_arg : exp =
  ELetJoin [] t_int (lit_int 1l) (EApp (ELam t_int TRowEmpty (EVar 0)) (EJump 0 []))

val jump_from_arg_untypable (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#t #r: typ)
  (h: typing sg ln g d jump_from_arg t r)
  : Lemma False

(** * Jumps to an outer join point from tail-transparent positions *)

(** `letjoin j0 () : Int = 1 in
       letjoin j1 (x : Int) : Int = jump j0 () in
       let y : Int = 2 in
       case () of guard true (leaf (jump j1 (y))) (leaf (jump j0 ()))` *)
let jump_from_tail : exp =
  ELetJoin [] t_int (lit_int 1l)
    (ELetJoin [t_int] t_int (EJump 1 [])
       (ELet t_int (lit_int 2l)
          (ECase [] (DGuard (ELit (LBool true)) (DLeaf (EJump 0 [EVar 0])) (DLeaf (EJump 1 []))))))

val jump_from_tail_typing : typing ex_sig [] (decl_ctx 0) [] jump_from_tail t_int TRowEmpty
