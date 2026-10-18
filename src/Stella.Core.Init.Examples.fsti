(**
 * The groups of spec 10 §The rule, judged by `Stella.Core.Init`.
 *
 * A refused group is refused by a derivation of `reads_imm` for a member
 * written at or after the right-hand side that reads it. An admitted group
 * is admitted by showing that no such derivation exists.
 *
 * The signature `ex_sig` declares, in a module `Ex`:
 *
 *   - `Function`, the function type constructor, and the data types
 *     `Int`, `String`, `Unit`, `Pair` and `List`;
 *   - the constructors `Tuple : forall a b. a -> b -> Pair a b`,
 *     `Cons : forall a. a -> List a -> List a` and `Unit : Unit`;
 *   - the foreign `add : Int -> Int -> Int`.
 *
 * `snd` is a top-level value outside every group here, which `Σ` does not
 * declare, so applying it is a default application. A group's members are
 * written in the order shown; the comments on the right-hand sides name the
 * variables, a de Bruijn index counting the binders between it and its
 * member (design §3.1).
 *)
module Stella.Core.Init.Examples
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Init
module L = FStar.List.Tot
module I32 = FStar.Int32

(** * The signature *)

let ex (s: string) : qname = { qmod = ["Ex"]; qid = s }

let ty (s: string) : typ = TCon (ex s) []

let arr (t1 t2: typ) : typ = fun_ty (ex "Function") t1 TRowEmpty t2

let data (cs: list string) : tycon_info =
  { tc_nk = 0; tc_kind = KType; tc_class = TcData (L.map ex cs) }

let ex_tycons (q: qname) : option tycon_info =
  if q = ex "Function" then
    Some { tc_nk = 0;
           tc_kind = KArrow KType (KArrow (KRow EEffect) (KArrow KType KType));
           tc_class = TcIntrinsic ClsFunction }
  else if q = ex "Int" || q = ex "String" then
    Some { tc_nk = 0; tc_kind = KType; tc_class = TcIntrinsic ClsLiteral }
  else if q = ex "Unit" then Some (data ["Unit"])
  else if q = ex "Pair" then
    Some { tc_nk = 0; tc_kind = KArrow KType (KArrow KType KType); tc_class = TcData [ex "Tuple"] }
  else if q = ex "List" then
    Some { tc_nk = 0; tc_kind = KArrow KType KType; tc_class = TcData [ex "Cons"] }
  else None

let ex_ctors (q: qname) : option ctor_info =
  if q = ex "Tuple" then
    Some { ct_owner = ex "Pair"; ct_tag = 0; ct_arity = 2; ct_nk = 0;
           ct_ty = TForall KType (TForall KType
                     (arr (TVar 1) (arr (TVar 0) (TApp (TApp (ty "Pair") (TVar 1)) (TVar 0))))) }
  else if q = ex "Cons" then
    Some { ct_owner = ex "List"; ct_tag = 0; ct_arity = 2; ct_nk = 0;
           ct_ty = TForall KType (arr (TVar 0) (arr (TApp (ty "List") (TVar 0))
                                                    (TApp (ty "List") (TVar 0)))) }
  else if q = ex "Unit" then
    Some { ct_owner = ex "Unit"; ct_tag = 0; ct_arity = 0; ct_nk = 0; ct_ty = ty "Unit" }
  else None

let ex_foreigns (q: qname) : option foreign_info =
  if q = ex "add" then
    Some { fr_nk = 0; fr_ty = arr (ty "Int") (arr (ty "Int") (ty "Int")); fr_observ_none = true }
  else None

let ex_sig : sig = {
  tycons = ex_tycons;
  effects = (fun _ -> None);
  ctors = ex_ctors;
  foreigns = ex_foreigns;
  values = (fun _ -> None);
}

(** * Terms *)

let int (n: I32.t) : exp = ELit (LInt n)

(** `Tuple a b`, i.e. `Ex.Tuple [Int] [τ] a b`. *)
let tuple (t: typ) (a b: exp) : exp =
  EApp (EApp (ETyApp (ETyApp (EGlobal (ex "Tuple") []) (ty "Int")) t) a) b

(** `Cons a b`, i.e. `Ex.Cons [Int] a b`. *)
let cons (a b: exp) : exp = EApp (EApp (ETyApp (EGlobal (ex "Cons") []) (ty "Int")) a) b

let unit_v : exp = EGlobal (ex "Unit") []

let lam (t: typ) (b: exp) : exp = ELam t TRowEmpty b

(** `{ next: e }` *)
let next_rec (e: exp) : exp = EExtend (SymbolKey "next") e ERecEmpty

(** A local group, its members in written order, every one annotated `τ`. *)
let group_of (t: typ) (rs: list exp) : list (typ & exp) = L.map (fun r -> (t, r)) rs

(** * Refused: `x = Tuple 1 x` and `x = x`, each reading itself *)

let tuple_self_rhs : exp = tuple (ty "Pair") (int 1l) (EVar 0)        (* Tuple 1 x *)
let tuple_self : list (typ & exp) = group_of (ty "Pair") [tuple_self_rhs]

val tuple_self_reads
  : reads_imm ex_sig (local_group tuple_self) (member_env 1) [] tuple_self_rhs 0

val tuple_self_refused : unit -> Lemma (~ (init_safe_letrec ex_sig tuple_self))

let self_rhs : exp = EVar 0                                           (* x *)
let self : list (typ & exp) = group_of (ty "Int") [self_rhs]

val self_reads : reads_imm ex_sig (local_group self) (member_env 1) [] self_rhs 0

val self_refused : unit -> Lemma (~ (init_safe_letrec ex_sig self))

(** The top-level `x = Tuple 1 x`, `x` a global. *)
let top_tuple_self_rhs : exp = tuple (ty "Pair") (int 1l) (EGlobal (ex "x") [])
let top_tuple_self : list (qname & exp) = [(ex "x", top_tuple_self_rhs)]

val top_tuple_self_reads
  : reads_imm ex_sig (top_group top_tuple_self) [] [] top_tuple_self_rhs 0

val top_tuple_self_refused : unit -> Lemma (~ (init_safe_top ex_sig top_tuple_self))

(** * Admitted: `fibAnd = Tuple "fib" (\n -> … snd fibAnd …)` *)

(** `snd fibAnd n` under `\n`, `fibAnd` being `fib_ref`. *)
let fib_body (fib_ref: exp) : exp = EApp (EApp (EGlobal (ex "snd") []) fib_ref) (EVar 0)

let fib_rhs (fib_ref: exp) : exp =
  tuple (arr (ty "Int") (ty "Int")) (ELit (LString [102; 105; 98])) (lam (ty "Int") (fib_body fib_ref))

let fib_and : list (typ & exp) = group_of (ty "Pair") [fib_rhs (EVar 1)]   (* n = 0, fibAnd = 1 *)

val fib_and_safe : unit -> Lemma (init_safe_letrec ex_sig fib_and)

let top_fib_and : list (qname & exp) = [(ex "fibAnd", fib_rhs (EGlobal (ex "fibAnd") []))]

val top_fib_and_safe : unit -> Lemma (init_safe_top ex_sig top_fib_and)

(** * Admitted: `a = { next: \_ -> b }; b = { next: \_ -> a }` *)

let next_ab : list (typ & exp) =
  group_of (ty "Int")
    [next_rec (lam (ty "Unit") (EVar 1));      (* _ = 0, b = 1, a = 2 *)
     next_rec (lam (ty "Unit") (EVar 2))]

val next_ab_safe : unit -> Lemma (init_safe_letrec ex_sig next_ab)

(** * Refused at `ys` in `xs`: `xs = Cons 1 ys; ys = Cons 2 xs` *)

let cons_xs_rhs : exp = cons (int 1l) (EVar 0)                        (* ys = 0, xs = 1 *)
let cons_cycle : list (typ & exp) =
  group_of (TApp (ty "List") (ty "Int")) [cons_xs_rhs; cons (int 2l) (EVar 1)]

val cons_cycle_reads
  : reads_imm ex_sig (local_group cons_cycle) (member_env 2) [] cons_xs_rhs 1

val cons_cycle_refused : unit -> Lemma (~ (init_safe_letrec ex_sig cons_cycle))

(** * Refused: `x = (\_ -> x) ()`, at `x` inside the λ through the application *)

let apply_self_rhs : exp = EApp (lam (ty "Unit") (EVar 1)) unit_v     (* _ = 0, x = 1 *)
let apply_self : list (typ & exp) = group_of (ty "Int") [apply_self_rhs]

val apply_self_reads
  : reads_imm ex_sig (local_group apply_self) (member_env 1) [] apply_self_rhs 0

val apply_self_refused : unit -> Lemma (~ (init_safe_letrec ex_sig apply_self))

(** * Refused: `a = { next: \_ -> b }; b = (select next a) Prim.Unit`, at `b`
    inside `a`'s closure through the application in `b` *)

let select_b_rhs : exp = EApp (ESelect (SymbolKey "next") (EVar 1)) unit_v   (* b = 0, a = 1 *)
let select_ab : list (typ & exp) =
  group_of (ty "Int") [next_rec (lam (ty "Unit") (EVar 1)); select_b_rhs]

val select_ab_reads
  : reads_imm ex_sig (local_group select_ab) (member_env 2) [] select_b_rhs 1

val select_ab_refused : unit -> Lemma (~ (init_safe_letrec ex_sig select_ab))

(** * Refused in `a`: `a = g 1; g x = c x; c y = a + y`, `a` calling `g`,
    which reads `c`, written after `a`, and through it `a` itself *)

let call_a_rhs : exp = EApp (EVar 1) (int 1l)                          (* c = 0, g = 1, a = 2 *)
let call_chain : list (typ & exp) =
  group_of (ty "Int")
    [call_a_rhs;
     lam (ty "Int") (EApp (EVar 1) (EVar 0));                          (* x = 0, c = 1 *)
     lam (ty "Int") (EApp (EApp (EGlobal (ex "add") []) (EVar 3)) (EVar 0))]
                                                                       (* y = 0, a = 3 *)

val call_chain_reads_c
  : reads_imm ex_sig (local_group call_chain) (member_env 3) [] call_a_rhs 2

val call_chain_reads_a
  : reads_imm ex_sig (local_group call_chain) (member_env 3) [] call_a_rhs 0

val call_chain_refused : unit -> Lemma (~ (init_safe_letrec ex_sig call_chain))

(** * The order of what is read: `g x = f x; f = g` is admitted, and
    `f = g; g x = f x` is not *)

let g_then_f : list (typ & exp) =
  group_of (ty "Int") [lam (ty "Int") (EApp (EVar 1) (EVar 0)); EVar 1]   (* f = 0, g = 1 *)

val g_then_f_safe : unit -> Lemma (init_safe_letrec ex_sig g_then_f)

let f_then_g : list (typ & exp) =
  group_of (ty "Int") [EVar 0; lam (ty "Int") (EApp (EVar 2) (EVar 0))]   (* g = 0, f = 1 *)

val f_then_g_reads : reads_imm ex_sig (local_group f_then_g) (member_env 2) [] (EVar 0) 1

val f_then_g_refused : unit -> Lemma (~ (init_safe_letrec ex_sig f_then_g))
