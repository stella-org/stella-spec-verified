(**
 * Signatures against `Stella.Core.Sig.Wf.sig_ok`.
 *
 * `good_sig` is a realistic `Σ`: every name of `Prim`, the data types
 *
 *     data List (a : Type) = Nil | Cons a (List a)
 *     data Proxy [[k]] (a : k) = MkProxy
 *     data Task = MkTask (Unit -{Console}-> Unit)
 *
 * the effect `Console { log : String ->* Unit }`, and the pure foreign
 * `length : forall (a : Type). List a -> Int`. It satisfies `sig_ok`.
 *
 * Each `bad_*` signature changes `good_sig` in one place, and `sig_ok`
 * rejects it:
 *
 *   - `bad_result`: a data type `T : Type -> Type` with the constructor
 *     `C : forall a. a -> T Int`, whose result is not `T a`;
 *   - `bad_absent`: `List` lists a constructor `Snoc` that `Σ` lacks;
 *   - `bad_unlisted`: a constructor `Extra` owned by `List` that `List`
 *     does not list;
 *   - `bad_arity`: `Cons` declares arity 1;
 *   - `bad_tag`: `Nil` and `Cons` share the tag 0;
 *   - `bad_ctor_effect`: `Cons : forall a. a -{Console}-> List a -> List a`;
 *   - `bad_foreign_effect`: the foreign `print : String -{Console}-> Unit`;
 *   - `bad_foreign_arg`: the foreign `apply : (Int -{Console}-> Int) -> Int`,
 *     whose effectful arrow is in an argument.
 *)
module Stella.Core.Sig.Examples
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
module L = FStar.List.Tot

(** * Names and types *)

let base (s: string) : qname = { qmod = ["Base"]; qid = s }

let t_int : typ = TCon prim_int []

let t_string : typ = TCon prim_string []

let list_ty (t: typ) : typ = TApp (TCon (base "List") []) t

(** The row `( Console )` *)
let console_row : typ = TRowExt (EntEff None (base "Console") []) TRowEmpty

(** * The signature *)

(** The names of `Prim`, as `prim_wf` requires them. *)
let prim_tycons (q: qname) : option tycon_info =
  if q = prim_function then
    Some { tc_nk = 0;
           tc_kind = KArrow KType (KArrow (KRow EEffect) (KArrow KType KType));
           tc_class = TcIntrinsic ClsFunction }
  else if q = prim_record then
    Some { tc_nk = 0; tc_kind = KArrow (KRow EType) KType; tc_class = TcIntrinsic ClsRecord }
  else if q = prim_variant then
    Some { tc_nk = 0; tc_kind = KArrow (KRow EType) KType; tc_class = TcIntrinsic ClsVariant }
  else if q = prim_int || q = prim_number || q = prim_string || q = prim_char ||
          q = prim_boolean then
    Some { tc_nk = 0; tc_kind = KType; tc_class = TcIntrinsic ClsLiteral }
  else if q = prim_io then
    Some { tc_nk = 0; tc_kind = KArrow KType KType; tc_class = TcIntrinsic ClsOpaque }
  else if q = prim_unit then
    Some { tc_nk = 0; tc_kind = KType; tc_class = TcData [prim_unit_ctor] }
  else None

let list_info : tycon_info =
  { tc_nk = 0; tc_kind = KArrow KType KType; tc_class = TcData [base "Nil"; base "Cons"] }

(** `Proxy : forall k. k -> Type` *)
let proxy_info : tycon_info =
  { tc_nk = 1; tc_kind = KArrow (KVar 0) KType; tc_class = TcData [base "MkProxy"] }

(** `Task : Type`, a data type whose field is an effectful function *)
let task_info : tycon_info = { tc_nk = 0; tc_kind = KType; tc_class = TcData [base "MkTask"] }

let good_tycons (q: qname) : option tycon_info =
  if q = base "List" then Some list_info
  else if q = base "Task" then Some task_info
  else if q = base "Proxy" then Some proxy_info
  else prim_tycons q

let unit_info : ctor_info =
  { ct_owner = prim_unit; ct_tag = 0; ct_arity = 0; ct_nk = 0; ct_ty = t_unit }

(** `Nil : forall (a : Type). List a` *)
let nil_info : ctor_info =
  { ct_owner = base "List"; ct_tag = 0; ct_arity = 0; ct_nk = 0;
    ct_ty = TForall KType (list_ty (TVar 0)) }

(** `Cons : forall (a : Type). a -> List a -> List a` *)
let cons_ty : typ =
  TForall KType (t_fun (TVar 0) TRowEmpty (t_fun (list_ty (TVar 0)) TRowEmpty (list_ty (TVar 0))))

let cons_info : ctor_info =
  { ct_owner = base "List"; ct_tag = 1; ct_arity = 2; ct_nk = 0; ct_ty = cons_ty }

(** `MkProxy : forall k. forall (a : k). Proxy [[k]] a` *)
let mkproxy_info : ctor_info =
  { ct_owner = base "Proxy"; ct_tag = 0; ct_arity = 0; ct_nk = 1;
    ct_ty = TForall (KVar 0) (TApp (TCon (base "Proxy") [KVar 0]) (TVar 0)) }

(** `MkTask : (Unit -{Console}-> Unit) -> Task`. Only the arrows of a
    constructor's spine are pure; a field may hold an effectful function. *)
let mktask_info : ctor_info =
  { ct_owner = base "Task"; ct_tag = 0; ct_arity = 1; ct_nk = 0;
    ct_ty = t_fun (t_fun t_unit console_row t_unit) TRowEmpty (TCon (base "Task") []) }

let good_ctors (q: qname) : option ctor_info =
  if q = prim_unit_ctor then Some unit_info
  else if q = base "Nil" then Some nil_info
  else if q = base "Cons" then Some cons_info
  else if q = base "MkProxy" then Some mkproxy_info
  else if q = base "MkTask" then Some mktask_info
  else None

(** `log : String ->* Unit` *)
let console_info : effect_info =
  { eff_params = []; eff_ops = [("log", { binders = []; arg = t_string; res = t_unit })] }

let good_effects (q: qname) : option effect_info =
  if q = base "Console" then Some console_info else None

(** `length : forall (a : Type). List a -> Int` *)
let length_info : foreign_info =
  { fr_nk = 0; fr_ty = TForall KType (t_fun (list_ty (TVar 0)) TRowEmpty t_int);
    fr_observ_none = true }

let good_foreigns (q: qname) : option foreign_info =
  if q = base "length" then Some length_info else None

let good_sig : sig = {
  tycons = good_tycons;
  effects = good_effects;
  ctors = good_ctors;
  foreigns = good_foreigns;
  values = (fun _ -> None);
}

val good_sig_ok : unit -> Lemma (sig_ok good_sig)

(** * Rejected signatures *)

(** `T : Type -> Type` with `C : forall a. a -> T Int` *)
let t_info : tycon_info = { tc_nk = 0; tc_kind = KArrow KType KType; tc_class = TcData [base "C"] }

let c_info : ctor_info =
  { ct_owner = base "T"; ct_tag = 0; ct_arity = 1; ct_nk = 0;
    ct_ty = TForall KType (t_fun (TVar 0) TRowEmpty (TApp (TCon (base "T") []) t_int)) }

let bad_result : sig =
  { good_sig with
    tycons = (fun q -> if q = base "T" then Some t_info else good_tycons q);
    ctors = (fun q -> if q = base "C" then Some c_info else good_ctors q) }

val bad_result_rejected : unit -> Lemma (~(sig_ok bad_result))

(** `List` lists `Snoc`, which is no constructor. *)
let list_snoc_info : tycon_info =
  { list_info with tc_class = TcData [base "Nil"; base "Cons"; base "Snoc"] }

let bad_absent : sig =
  { good_sig with
    tycons = (fun q -> if q = base "List" then Some list_snoc_info else good_tycons q) }

val bad_absent_rejected : unit -> Lemma (~(sig_ok bad_absent))

(** `Extra : forall a. List a`, owned by `List`, which does not list it. *)
let extra_info : ctor_info = { nil_info with ct_tag = 2 }

let bad_unlisted : sig =
  { good_sig with ctors = (fun q -> if q = base "Extra" then Some extra_info else good_ctors q) }

val bad_unlisted_rejected : unit -> Lemma (~(sig_ok bad_unlisted))

let cons_arity_info : ctor_info = { cons_info with ct_arity = 1 }

let bad_arity : sig =
  { good_sig with ctors = (fun q -> if q = base "Cons" then Some cons_arity_info else good_ctors q) }

val bad_arity_rejected : unit -> Lemma (~(sig_ok bad_arity))

let cons_tag_info : ctor_info = { cons_info with ct_tag = 0 }

let bad_tag : sig =
  { good_sig with ctors = (fun q -> if q = base "Cons" then Some cons_tag_info else good_ctors q) }

val bad_tag_rejected : unit -> Lemma (~(sig_ok bad_tag))

(** `Cons : forall a. a -{Console}-> List a -> List a` *)
let cons_effect_info : ctor_info =
  { cons_info with
    ct_ty = TForall KType (t_fun (TVar 0) console_row
                             (t_fun (list_ty (TVar 0)) TRowEmpty (list_ty (TVar 0)))) }

let bad_ctor_effect : sig =
  { good_sig with ctors = (fun q -> if q = base "Cons" then Some cons_effect_info else good_ctors q) }

val bad_ctor_effect_rejected : unit -> Lemma (~(sig_ok bad_ctor_effect))

(** `print : String -{Console}-> Unit` *)
let print_info : foreign_info =
  { fr_nk = 0; fr_ty = t_fun t_string console_row t_unit; fr_observ_none = false }

let bad_foreign_effect : sig =
  { good_sig with
    foreigns = (fun q -> if q = base "print" then Some print_info else good_foreigns q) }

val bad_foreign_effect_rejected : unit -> Lemma (~(sig_ok bad_foreign_effect))

(** `apply : (Int -{Console}-> Int) -> Int` *)
let apply_info : foreign_info =
  { fr_nk = 0; fr_ty = t_fun (t_fun t_int console_row t_int) TRowEmpty t_int; fr_observ_none = false }

let bad_foreign_arg : sig =
  { good_sig with
    foreigns = (fun q -> if q = base "apply" then Some apply_info else good_foreigns q) }

val bad_foreign_arg_rejected : unit -> Lemma (~(sig_ok bad_foreign_arg))
