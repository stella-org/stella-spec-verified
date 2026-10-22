(**
 * Steps of `Stella.Core.Semantics.Step` on small terms, and an environment
 * that conforms.
 *
 * The signature `ex_sig` is `Stella.Core.Sig.Examples.good_sig` with one
 * more foreign, `boom : Int -> Int`, which carries no `#observ(none)` and so
 * may fault, and one top-level value, `one : Int`. It satisfies `sig_ok`
 * (`ex_sig_ok`). The environment `ex_genv` defines `one` as `1` and
 * implements
 *
 *   - `length`, whose ABI precondition is that its argument is a value
 *     list built from `Cons` and `Nil`, as the number of elements of that
 *     list, saturated at `2^31 - 1`; it returns `None` off its
 *     precondition;
 *   - `boom`, whose precondition is `True`, which faults with an ABI fault
 *     on every argument.
 *
 * `ex_genv` conforms to `ex_sig` at every pair of run-time contexts
 * (`ex_genv_ok`), and all the premises of preservation hold at once with
 * one region and one location (`premises_inhabited`).
 *
 * The steps:
 *
 *   - β: `(λ (x : Int) / (). x) 1  →  1`;
 *   - the argument before the function (D35):
 *     `(λ (x : Int) / (). x) ((λ (y : Int) / (). y) 2)  →  (λ (x : Int) / (). x) 2`;
 *   - the join rule through a tail context of length 0,
 *     `letjoin j (x : Int) : Int = x in jump 0 (1)  →  letjoin … in 1`;
 *   - the join rule through a tail context of length 1, where the
 *     definition jumps to its own join point, so the shift past `Tl` is
 *     visible: `letjoin j (x : Int) : Int = jump 0 (x) in
 *     (letjoin j' () : Int = 0 in jump 1 (5))` steps to the same term with
 *     `jump 1 (5)` in the hole, the shifted index `1` again naming `j`;
 *   - unfolding a top-level value: `one  →  1`;
 *   - a foreign call with a value outcome: `length [Int] (Cons [Int] 1
 *     (Nil [Int]))  →  1`;
 *   - a foreign call with an ABI fault: `boom 0  →  fault φ`;
 *   - the fault propagated through a frame: `let x : Int = boom 0 in x  →
 *     fault φ`;
 *   - a `switchKey` default: the scrutinee `inject y [( x : Int )] true`
 *     injects no key the branches name, so `match θ (switchKey s_0 { x ->
 *     leaf 0 } default -> leaf 1)  →  match θ (leaf 1)`.
 *
 * The preconditions: `let n : Int = length [Int] (Cons [Int] 1 (Nil
 * [Int])) in n` respects them (`length_let_pre_ok`), the call standing in
 * the evaluation position of the `let`; `length [Int] 0` does not
 * (`length_lit_not_pre_ok`), and has no step (`length_lit_no_step`).
 *
 * And an environment with no definition, no implementation and no
 * satisfiable precondition conforms at every pair of run-time contexts.
 *)
module Stella.Core.Semantics.Examples
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Runtime
open Stella.Core.Sig.Examples
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module I32 = FStar.Int32
module V = Stella.Core.Value

(** * The signature *)

(** `boom : Int -> Int`, with no `#observ(none)` *)
let boom_info : foreign_info =
  { fr_nk = 0; fr_ty = t_fun t_int TRowEmpty t_int; fr_observ_none = false }

(** `one : Int` *)
let one_info : value_info = { vl_nk = 0; vl_ty = t_int }

let ex_sig : sig =
  { good_sig with
    foreigns = (fun q -> if q = base "boom" then Some boom_info else good_foreigns q);
    values = (fun q -> if q = base "one" then Some one_info else None) }

val ex_sig_ok : unit -> Lemma (sig_ok ex_sig)

(** * The environment *)

(** The number of elements of a list `Cons [τ] v1 (… (Nil [τ]))`. *)
let rec list_len (e: exp) : Tot (option nat) (decreases e) =
  match e with
  | ETyApp (EGlobal q []) _ -> if q = base "Nil" then Some 0 else None
  | EApp (EApp (ETyApp (EGlobal q []) _) _) tl ->
    if q = base "Cons"
    then (match list_len tl with Some n -> Some (n + 1) | None -> None)
    else None
  | _ -> None

(** The precondition of `length`: one argument, a value list built from
    `Cons` and `Nil`. *)
let length_pre (vs: list exp) : prop =
  match vs with
  | [l] -> V.is_value ex_sig l /\ Some? (list_len l)
  | _ -> False

(** `n`, or `2^31 - 1` if `n` is larger. *)
let clamp31 (n: nat) : m: nat{m < pow2 31} = if n < pow2 31 then n else pow2 31 - 1

(** `δ_length`: the number of elements as an `Int`, saturated at
    `2^31 - 1`, on a list built from `Cons` and `Nil`; nothing on any other
    argument. *)
let length_impl (vs: list exp) : option foreign_outcome =
  match vs with
  | [l] ->
    (match list_len l with
     | Some n -> Some (FOVal (ELit (LInt (I32.int_to_t (clamp31 n)))))
     | None -> None)
  | _ -> None

(** The ABI fault `boom` raises. *)
let boom_fault : abi_fault = AbiFault 42

(** `δ_boom`: a fault on every argument. *)
let boom_impl (vs: list exp) : option foreign_outcome = Some (FOFault boom_fault)

let lit_int (n: I32.t) : exp = ELit (LInt n)

let ex_genv : genv = {
  gvals = (fun q -> if q = base "one" then Some (lit_int 1l) else None);
  gimpl = (fun q ->
    if q = base "length" then Some length_impl
    else if q = base "boom" then Some boom_impl
    else None);
  gpre = (fun q vs ->
    if q = base "length" then length_pre vs
    else if q = base "boom" then True
    else False);
}

(** `ex_genv` conforms at every pair of run-time contexts. *)
val ex_genv_ok (ln: lctx) (rs: list (atom & layout)) : Lemma (genv_ok ex_sig ln rs ex_genv)

(** One region `3`, with one cell `c : Int`, and one location of type
    `Int`. *)
let rs1 : list (atom & layout) = [(3, [(SymbolKey "c", t_int)])]

let ln1 : lctx = [t_int]

(** The premises of preservation hold together: `Σ`, `Γ_R` and `Γ_N` are
    well formed and `G` conforms. *)
val premises_inhabited : unit
  -> Lemma (sig_ok ex_sig /\ rctx_ok ex_sig rs1 /\ lctx_ok ex_sig rs1 ln1 /\
            genv_ok ex_sig ln1 rs1 ex_genv)

(** * Terms *)

(** `λ (x : Int) / (). x` *)
let id_int : exp = ELam t_int TRowEmpty (EVar 0)

(** * β *)

let beta_redex : exp = EApp id_int (lit_int 1l)

val beta_step : step ex_sig ex_genv [] [] beta_redex [] [] (CTerm (lit_int 1l))

(** The argument is evaluated first, under the frame `id_int Ev`. *)
let arg_first : exp = EApp id_int (EApp id_int (lit_int 2l))

val arg_first_step : step ex_sig ex_genv [] [] arg_first [] [] (CTerm (EApp id_int (lit_int 2l)))

(** * Join points *)

(** `letjoin j (x : Int) : Int = x in jump 0 (1)` *)
let join0 : exp = ELetJoin [t_int] t_int (EVar 0) (EJump 0 [lit_int 1l])

val join0_step :
  step ex_sig ex_genv [] [] join0 [] [] (CTerm (ELetJoin [t_int] t_int (EVar 0) (lit_int 1l)))

(** `jump j (x)` in the definition of `j` *)
let self_jump : exp = EJump 0 [EVar 0]

(** `letjoin j' () : Int = 0 in e` *)
let inner_join (e: exp) : exp = ELetJoin [] t_int (lit_int 0l) e

(** `letjoin j (x : Int) : Int = jump j (x) in (letjoin j' () : Int = 0 in jump j (5))`,
    the jump to `j` in the hole of `Tl = letjoin j' … in []` written with
    the index 1. *)
let join1 : exp = ELetJoin [t_int] t_int self_jump (inner_join (EJump 1 [lit_int 5l]))

(** The definition `jump 0 (x)` lands in the hole shifted past `j'`, as
    `jump 1 (5)`. *)
val join1_step : step ex_sig ex_genv [] [] join1 [] [] (CTerm join1)

(** * Top-level values *)

(** `one` *)
let one_ref : exp = EGlobal (base "one") []

val unfold_step : step ex_sig ex_genv [] [] one_ref [] [] (CTerm (lit_int 1l))

(** * Foreign calls *)

let int_list1 : exp =
  EApp (EApp (ETyApp (EGlobal (base "Cons") []) t_int) (lit_int 1l))
       (ETyApp (EGlobal (base "Nil") []) t_int)

(** `length [Int] (Cons [Int] 1 (Nil [Int]))` *)
let length_call : exp = EApp (ETyApp (EGlobal (base "length") []) t_int) int_list1

val length_call_redex : unit -> Lemma (V.foreign_redex ex_sig length_call)

val length_step :
  step ex_sig ex_genv [] [] length_call [] [] (CTerm (ELit (LInt (I32.int_to_t 1))))

(** `boom 0` *)
let boom_call : exp = EApp (EGlobal (base "boom") []) (lit_int 0l)

val boom_step : step ex_sig ex_genv [] [] boom_call [] [] (CFault (FAbi boom_fault))

(** `let x : Int = boom 0 in x` *)
let boom_let : exp = ELet t_int boom_call (EVar 0)

val boom_let_step : step ex_sig ex_genv [] [] boom_let [] [] (CFault (FAbi boom_fault))

(** * Preconditions *)

(** `let n : Int = length [Int] (Cons [Int] 1 (Nil [Int])) in n` *)
let length_let : exp = ELet t_int length_call (EVar 0)

val length_let_pre_ok : unit -> Lemma (pre_ok ex_sig ex_genv length_let)

(** `length [Int] 0`, a saturated chain of values whose argument is no
    list *)
let length_lit : exp = EApp (ETyApp (EGlobal (base "length") []) t_int) (lit_int 0l)

val length_lit_not_pre_ok : unit -> Lemma (~(pre_ok ex_sig ex_genv length_lit))

(** Outside the precondition of `length` the call has no step. *)
val length_lit_no_step (#ra: list atom) (#st: store) (#ra': list atom) (#st': store) (#c: config)
  (h: step ex_sig ex_genv ra st length_lit ra' st' c)
  : Lemma False

(** * A `switchKey` default *)

(** `inject y [( x : Int )] true` *)
let inj_y : exp = EInject (SymbolKey "y") (TRowExt (EntTy (SymbolKey "x") t_int) TRowEmpty)
                    (ELit (LBool true))

(** `switchKey s_0 { x -> leaf 0 } default -> leaf 1` *)
let key_tree : dtree =
  DSwitchKey (OScrut 0) [(SymbolKey "x", DLeaf (lit_int 0l))] (Some (DLeaf (lit_int 1l)))

val switch_key_default_step :
  step ex_sig ex_genv [] [] (EMatch [inj_y] key_tree) [] []
    (CTerm (EMatch [inj_y] (DLeaf (lit_int 1l))))

(** * Conformance of the empty environment *)

let empty_genv : genv =
  { gvals = (fun _ -> None); gimpl = (fun _ -> None); gpre = (fun _ _ -> False) }

val empty_genv_ok (sg: sig) (ln: lctx) (rs: list (atom & layout))
  : Lemma (genv_ok sg ln rs empty_genv)
