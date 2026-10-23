(**
 * Steps of `Stella.Core.Semantics.Step` on small terms, environments that
 * conform, and environments that do not.
 *
 * The signature `ex_sig` is `Stella.Core.Sig.Examples.good_sig` with five
 * more foreigns and two top-level values:
 *
 *     foreign boom  : Int -> Int                 (no #observ(none))
 *     foreign pure  : forall (a : Type). a -> IO a
 *     foreign mkNil : forall (a : Type). Unit -> List a     (no #observ(none))
 *     foreign ident : forall (a : Type). a -> a
 *     foreign leak  : Unit -> Task
 *     one     : Int
 *     missing : Unit
 *
 * `boom` and `mkNil` carry no `#observ(none)`, the other three do. It
 * satisfies `sig_ok` (`ex_sig_ok`). `mkNil` is an example of the semantic
 * model, as in spec 06 §An ABI precondition is where condition (3) stops
 * asking, and not of the host boundary, which D44 keeps a user constructor
 * away from.
 *
 * ## A conforming environment
 *
 * `ex_genv` defines `one` as `1`, defines nothing for `missing`, and has
 * an entry for `length`, `boom`, `pure`, `mkNil` and `ident`, none for
 * `leak`. Each entry is a typed adapter, an erased function and an erased
 * precondition:
 *
 *   - `length`: the precondition is that the erased argument is a list
 *     built from `Cons` and `Nil`; both functions give its number of
 *     elements, saturated at `2^31 - 1`, as an `Int` literal;
 *   - `boom`: no precondition; both functions fault, with the same fault;
 *   - `pure`: the adapter gives `opaque ω [IO τ]` at the instance `⟨ · ; τ ⟩`
 *     and the erased function `opaque ω`, one payload `ω` at every instance.
 *     The payload stands for the action the drive loop runs, which Core does
 *     not represent;
 *   - `mkNil`: the adapter gives `Nil [τ]` at the instance `⟨ · ; τ ⟩` and
 *     the erased function `Nil`;
 *   - `ident`: both functions return their argument.
 *
 * `ex_genv` conforms to `ex_sig` at every pair of run-time contexts
 * (`ex_genv_ok`): each adapter's outcome erases to its erased function's,
 * and is typed at the cursor instance of the call. All the premises of
 * preservation hold at once with one region and one location
 * (`premises_inhabited`).
 *
 * ## Steps
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
 *   - a foreign call with an ABI fault: `boom 0  →  fault φ`, and the fault
 *     propagated through a frame: `let x : Int = boom 0 in x  →  fault φ`;
 *   - one foreign at two instances: `pure [List Int] (Nil [Int])  →
 *     opaque ω [IO (List Int)]` and `pure [List String] (Nil [String])  →
 *     opaque ω [IO (List String)]`. The arguments erase alike, the two
 *     reducts differ in their annotation alone, and both erase to
 *     `opaque ω`, the erased function's outcome (`pure_erasure`);
 *   - a constructor value built from the instance: `mkNil [Int] Prim.Unit
 *     →  Nil [Int]`, whose erasure `Nil` is the erased function's outcome;
 *   - an identity on a closure naming a global `G` does not define:
 *     `ident [Unit -> Unit] (λ (u : Unit) / (). missing)  →
 *     λ (u : Unit) / (). missing`. The result is not covered by `G`, and is
 *     covered relative to the argument (`ident_relative`), which is what
 *     condition (3) asks;
 *   - a `switchKey` default: the scrutinee `inject y [( x : Int )] true`
 *     injects no key the branches name, so `match θ (switchKey s_0 { x ->
 *     leaf 0 } default -> leaf 1)  →  match θ (leaf 1)`.
 *
 * ## Preconditions
 *
 * `let n : Int = length [Int] (Cons [Int] 1 (Nil [Int])) in n` respects
 * them (`length_let_pre_ok`), the call standing in the evaluation position
 * of the `let`; `length [Int] 0` does not (`length_lit_not_pre_ok`), and has
 * no step (`length_lit_no_step`).
 *
 * ## Environments that do not conform
 *
 *   - `bad_nil_genv er` replaces the entry of `mkNil` by an adapter that
 *     gives `Nil [Int]` at `⟨ · ; Int ⟩` and a fault at every other
 *     instance, each of which a call of `mkNil` may have on its own, with
 *     any erased function `er`. Its two calls `mkNil [Int] Prim.Unit` and
 *     `mkNil [String] Prim.Unit` have the same erased argument and outcomes
 *     that erase differently, so whatever `er` is, one of them breaks
 *     erasure coherence (`bad_nil_not_ok`);
 *   - `leak_genv` gives `leak` an entry whose outcome is
 *     `MkTask (λ (u : Unit) / (Console). missing)`, a value of type `Task`
 *     (`leaked_typed`) that names a global `G` does not define and the
 *     argument `Prim.Unit` does not name, so it is not covered relative to
 *     the argument (`leak_not_ok`).
 *
 * And an environment with no definition and no foreign entry conforms at
 * every pair of run-time contexts.
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
open Stella.Core.Erase
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module I32 = FStar.Int32
module V = Stella.Core.Value

(** * The signature *)

(** `IO τ` *)
let io_ty (t: typ) : typ = TApp (TCon prim_io []) t

(** `Task` *)
let task_ty : typ = TCon (base "Task") []

(** `boom : Int -> Int`, with no `#observ(none)` *)
let boom_info : foreign_info =
  { fr_nk = 0; fr_ty = t_fun t_int TRowEmpty t_int; fr_observ_none = false }

(** `pure : forall (a : Type). a -> IO a` *)
let pure_info : foreign_info =
  { fr_nk = 0; fr_ty = TForall KType (t_fun (TVar 0) TRowEmpty (io_ty (TVar 0)));
    fr_observ_none = true }

(** `mkNil : forall (a : Type). Unit -> List a`, with no `#observ(none)` *)
let mknil_info : foreign_info =
  { fr_nk = 0; fr_ty = TForall KType (t_fun t_unit TRowEmpty (list_ty (TVar 0)));
    fr_observ_none = false }

(** `ident : forall (a : Type). a -> a` *)
let ident_info : foreign_info =
  { fr_nk = 0; fr_ty = TForall KType (t_fun (TVar 0) TRowEmpty (TVar 0)); fr_observ_none = true }

(** `leak : Unit -> Task` *)
let leak_info : foreign_info =
  { fr_nk = 0; fr_ty = t_fun t_unit TRowEmpty task_ty; fr_observ_none = true }

(** `one : Int` *)
let one_info : value_info = { vl_nk = 0; vl_ty = t_int }

(** `missing : Unit` *)
let missing_info : value_info = { vl_nk = 0; vl_ty = t_unit }

let ex_foreigns (q: qname) : option foreign_info =
  if q = base "boom" then Some boom_info
  else if q = base "pure" then Some pure_info
  else if q = base "mkNil" then Some mknil_info
  else if q = base "ident" then Some ident_info
  else if q = base "leak" then Some leak_info
  else good_foreigns q

let ex_values (q: qname) : option value_info =
  if q = base "one" then Some one_info
  else if q = base "missing" then Some missing_info
  else None

let ex_sig : sig = { good_sig with foreigns = ex_foreigns; values = ex_values }

val ex_sig_ok : unit -> Lemma (sig_ok ex_sig)

(** * The environment *)

let lit_int (n: I32.t) : exp = ELit (LInt n)

(** `n`, or `2^31 - 1` if `n` is larger. *)
let clamp31 (n: nat) : m: nat{m < pow2 31} = if n < pow2 31 then n else pow2 31 - 1

(** The `Int` literal of `n`, saturated at `2^31 - 1`. *)
let len_lit (n: nat) : lit = LInt (I32.int_to_t (clamp31 n))

(** The number of elements of an erased list `Cons w1 (… Nil)`. *)
let rec ulist_len (w: uexp) : Tot (option nat) (decreases w) =
  match w with
  | UGlobal q -> if q = base "Nil" then Some 0 else None
  | UApp (UApp (UGlobal q) _) tl ->
    if q = base "Cons"
    then (match ulist_len tl with Some n -> Some (n + 1) | None -> None)
    else None
  | _ -> None

(** `Pᶜ_length`: one erased argument, a list built from `Cons` and `Nil`. *)
let length_pre (ws: list uexp) : prop =
  match ws with
  | [w] -> Some? (ulist_len w)
  | _ -> False

(** `δᵤ_length`: the number of elements as an `Int`, on a list; nothing on
    any other argument. *)
let length_erased (ws: list uexp) : option uoutcome =
  match ws with
  | [w] -> (match ulist_len w with Some n -> Some (UOVal (ULit (len_lit n))) | None -> None)
  | _ -> None

(** `δᵀ_length`: the same literal, read off the erasure of the argument. *)
let length_adapt (xi: chain_inst) (vs: list exp) : option foreign_outcome =
  match vs with
  | [l] -> (match ulist_len (erase l) with Some n -> Some (FOVal (ELit (len_lit n))) | None -> None)
  | _ -> None

let length_entry : foreign_entry =
  { fe_adapt = length_adapt; fe_erased = length_erased; fe_pre = length_pre }

(** The ABI fault `boom` raises. *)
let boom_fault : abi_fault = AbiFault 42

let boom_entry : foreign_entry = {
  fe_adapt = (fun _ _ -> Some (FOFault boom_fault));
  fe_erased = (fun _ -> Some (UOFault boom_fault));
  fe_pre = (fun _ -> True);
}

(** The payload `ω` of every action `pure` returns. *)
let pure_payload : nat = 7

(** `δᵀ_pure(⟨ · ; τ ⟩, v) = opaque ω [IO τ]` *)
let pure_adapt (xi: chain_inst) (vs: list exp) : option foreign_outcome =
  match xi.inst_types, vs with
  | [t], [_] -> Some (FOVal (EOpaque pure_payload (io_ty t)))
  | _ -> None

(** `δᵤ_pure(w) = opaque ω` *)
let pure_erased (ws: list uexp) : option uoutcome =
  match ws with
  | [_] -> Some (UOVal (UOpaque pure_payload))
  | _ -> None

let pure_entry : foreign_entry =
  { fe_adapt = pure_adapt; fe_erased = pure_erased; fe_pre = (fun _ -> True) }

(** `Nil [τ]` *)
let nil_at (t: typ) : exp = ETyApp (EGlobal (base "Nil") []) t

(** `δᵀ_mkNil(⟨ · ; τ ⟩, Prim.Unit) = Nil [τ]` *)
let mknil_adapt (xi: chain_inst) (vs: list exp) : option foreign_outcome =
  match xi.inst_types, vs with
  | [t], [_] -> Some (FOVal (nil_at t))
  | _ -> None

(** `δᵤ_mkNil(Prim.Unit) = Nil` *)
let mknil_erased (ws: list uexp) : option uoutcome =
  match ws with
  | [_] -> Some (UOVal (UGlobal (base "Nil")))
  | _ -> None

let mknil_entry : foreign_entry =
  { fe_adapt = mknil_adapt; fe_erased = mknil_erased; fe_pre = (fun _ -> True) }

let ident_entry : foreign_entry = {
  fe_adapt = (fun _ vs -> match vs with [v] -> Some (FOVal v) | _ -> None);
  fe_erased = (fun ws -> match ws with [w] -> Some (UOVal w) | _ -> None);
  fe_pre = (fun _ -> True);
}

let ex_genv : genv = {
  gvals = (fun q -> if q = base "one" then Some (lit_int 1l) else None);
  gforeign = (fun q ->
    if q = base "length" then Some length_entry
    else if q = base "boom" then Some boom_entry
    else if q = base "pure" then Some pure_entry
    else if q = base "mkNil" then Some mknil_entry
    else if q = base "ident" then Some ident_entry
    else None);
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
  EApp (EApp (ETyApp (EGlobal (base "Cons") []) t_int) (lit_int 1l)) (nil_at t_int)

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

(** * One foreign at two instances *)

(** `pure [τ] v` *)
let pure_call (t: typ) (v: exp) : exp = EApp (ETyApp (EGlobal (base "pure") []) t) v

(** `opaque ω [IO τ]` *)
let pure_result (t: typ) : exp = EOpaque pure_payload (io_ty t)

(** `pure [List Int] (Nil [Int])  →  opaque ω [IO (List Int)]` *)
val pure_int_step :
  step ex_sig ex_genv [] [] (pure_call (list_ty t_int) (nil_at t_int)) [] []
    (CTerm (pure_result (list_ty t_int)))

(** `pure [List String] (Nil [String])  →  opaque ω [IO (List String)]` *)
val pure_string_step :
  step ex_sig ex_genv [] [] (pure_call (list_ty t_string) (nil_at t_string)) [] []
    (CTerm (pure_result (list_ty t_string)))

(** The two calls have arguments that erase alike, and reducts that differ
    and erase alike, to the erased function's outcome on those
    arguments. *)
val pure_erasure : unit
  -> Lemma (erase (nil_at t_int) == erase (nil_at t_string) /\
            ~(pure_result (list_ty t_int) == pure_result (list_ty t_string)) /\
            erase (pure_result (list_ty t_int)) == erase (pure_result (list_ty t_string)) /\
            pure_erased [erase (nil_at t_int)] ==
              Some (erase_outcome (FOVal (pure_result (list_ty t_int)))))

(** * A constructor value built from the instance *)

(** `Prim.Unit` *)
let unit_val : exp = EGlobal prim_unit_ctor []

(** `mkNil [τ] Prim.Unit` *)
let mknil_call (t: typ) : exp = EApp (ETyApp (EGlobal (base "mkNil") []) t) unit_val

(** `mkNil [Int] Prim.Unit  →  Nil [Int]` *)
val mknil_step : step ex_sig ex_genv [] [] (mknil_call t_int) [] [] (CTerm (nil_at t_int))

(** The reduct erases to the erased function's outcome. *)
val mknil_erasure : unit
  -> Lemma (mknil_erased (L.map erase [unit_val]) == Some (erase_outcome (FOVal (nil_at t_int))))

(** * Coverage relative to the arguments *)

(** `λ (u : Unit) / (). missing` *)
let thunk : exp = ELam t_unit TRowEmpty (EGlobal (base "missing") [])

(** `ident [Unit -> Unit] (λ (u : Unit) / (). missing)` *)
let ident_call : exp =
  EApp (ETyApp (EGlobal (base "ident") []) (t_fun t_unit TRowEmpty t_unit)) thunk

val ident_step : step ex_sig ex_genv [] [] ident_call [] [] (CTerm thunk)

(** The result names `missing`, which `G` does not define, so `G` does not
    cover it; it is covered relative to the argument. *)
val ident_relative : unit
  -> Lemma (~(covers ex_sig ex_genv thunk) /\ covers_relative ex_sig ex_genv [thunk] thunk)

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

(** * An adapter that reads the instance for more than annotations *)

(** The fault the adapter below gives off `Int`. *)
let nil_fault : abi_fault = AbiFault 0

(** `Nil [Int]` at `⟨ · ; Int ⟩`, a fault at every other instance. *)
let bad_nil_adapt (xi: chain_inst) (vs: list exp) : option foreign_outcome =
  match xi.inst_types, vs with
  | [t], [_] -> if t = t_int then Some (FOVal (nil_at t_int)) else Some (FOFault nil_fault)
  | _ -> None

(** `ex_genv` with that adapter for `mkNil`, beside the erased function
    `er`. *)
let bad_nil_genv (er: list uexp -> option uoutcome) : genv =
  { ex_genv with
    gforeign = (fun q ->
      if q = base "mkNil"
      then Some { fe_adapt = bad_nil_adapt; fe_erased = er; fe_pre = (fun _ -> True) }
      else ex_genv.gforeign q) }

(** No erased function makes it conform. *)
val bad_nil_not_ok (er: list uexp -> option uoutcome)
  : Lemma (~(genv_ok ex_sig [] [] (bad_nil_genv er)))

(** * An adapter whose outcome is not covered *)

(** `MkTask (λ (u : Unit) / (Console). missing)` *)
let leaked : exp =
  EApp (EGlobal (base "MkTask") []) (ELam t_unit console_row (EGlobal (base "missing") []))

let leak_entry : foreign_entry = {
  fe_adapt = (fun _ vs -> match vs with [_] -> Some (FOVal leaked) | _ -> None);
  fe_erased = (fun ws -> match ws with [_] -> Some (UOVal (erase leaked)) | _ -> None);
  fe_pre = (fun _ -> True);
}

(** `ex_genv` with an entry for `leak`. *)
let leak_genv : genv =
  { ex_genv with
    gforeign = (fun q -> if q = base "leak" then Some leak_entry else ex_genv.gforeign q) }

(** The outcome is a value of the result type `Task`. *)
val leaked_typed : unit
  -> Lemma (V.is_value ex_sig leaked /\ typed ex_sig [] (closed_ctx []) leaked task_ty)

(** It is not covered relative to the argument, so `leak_genv` does not
    conform. *)
val leak_not_ok : unit -> Lemma (~(genv_ok ex_sig [] [] leak_genv))

(** * Conformance of the empty environment *)

let empty_genv : genv = { gvals = (fun _ -> None); gforeign = (fun _ -> None) }

val empty_genv_ok (sg: sig) (ln: lctx) (rs: list (atom & layout))
  : Lemma (genv_ok sg ln rs empty_genv)
