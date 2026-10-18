(**
 * Derivations of `Stella.Core.Typing` for three small terms, over a
 * signature `ex_sig` holding just what they use.
 *
 *   - the identity `λ (x : Int) / (). x`;
 *   - `select x (extend x 1 {})`;
 *   - `toMaybe` of spec 08 §Effects, the handler interpreting `Partial`
 *     into `Maybe` with a `full` clause that drops its continuation.
 *
 * `ex_sig` declares:
 *
 *   - in `Prim`, every name of `Stella.Core.Prim`, as `prim_wf` requires
 *     (`ex_prim_wf`);
 *   - in `Prelude`, the data type `Maybe (a : Type) = Nothing | Just a` and
 *     the effect `Partial` with `abort : forall (b : Type). Unit ->* b`.
 *)
module Stella.Core.Typing.Examples
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot

(** * The signature *)

let prelude (s: string) : qname = { qmod = ["Prelude"]; qid = s }

let t_int : typ = TCon prim_int []

let maybe_ty (t: typ) : typ = TApp (TCon (prelude "Maybe") []) t

let ex_tycons (q: qname) : option tycon_info =
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
  else if q = prelude "Maybe" then
    Some { tc_nk = 0; tc_kind = KArrow KType KType;
           tc_class = TcData [prelude "Nothing"; prelude "Just"] }
  else None

(** `Nothing : forall (a : Type). Maybe a` *)
let nothing_ty : typ = TForall KType (maybe_ty (TVar 0))

(** `Just : forall (a : Type). a -> Maybe a` *)
let just_ty : typ = TForall KType (t_fun (TVar 0) TRowEmpty (maybe_ty (TVar 0)))

let ex_ctors (q: qname) : option ctor_info =
  if q = prim_unit_ctor then
    Some { ct_owner = prim_unit; ct_tag = 0; ct_arity = 0; ct_nk = 0; ct_ty = t_unit }
  else if q = prelude "Nothing" then
    Some { ct_owner = prelude "Maybe"; ct_tag = 0; ct_arity = 0; ct_nk = 0; ct_ty = nothing_ty }
  else if q = prelude "Just" then
    Some { ct_owner = prelude "Maybe"; ct_tag = 1; ct_arity = 1; ct_nk = 0; ct_ty = just_ty }
  else None

(** `abort : forall (b : Type). Unit ->* b` *)
let abort_sig : op_sig = { binders = [KType]; arg = t_unit; res = TVar 0 }

let partial_info : effect_info = { eff_params = []; eff_ops = [("abort", abort_sig)] }

let ex_effects (q: qname) : option effect_info =
  if q = prelude "Partial" then Some partial_info else None

let ex_sig : sig = {
  tycons = ex_tycons;
  effects = ex_effects;
  ctors = ex_ctors;
  foreigns = (fun _ -> None);
  values = (fun _ -> None);
}

(** * The identity *)

(** `λ (x : Int) / (). x` *)
let id_exp : exp = ELam t_int TRowEmpty (EVar 0)

val id_typing : typing ex_sig [] (decl_ctx 0) [] true id_exp (t_fun t_int TRowEmpty t_int) TRowEmpty

(** * A record *)

let key_x : key = SymbolKey "x"

(** `select x (extend x 1 {})` *)
let select_exp : exp = ESelect key_x (EExtend key_x (ELit (LInt 1l)) ERecEmpty)

val select_typing : typing ex_sig [] (decl_ctx 0) [] true select_exp t_int TRowEmpty

(** * A handler *)

let partial_key : key = EffectKey (prelude "Partial")

(** The element `Partial` *)
let partial_ent : entry = EntEff None (prelude "Partial") []

(** `Partial ∉ e`, `e` being type index 0. *)
let lacks_partial : constr = CLacks partial_key (TVar 0)

(** Under `e : Row Effect` and `a : Type`, `a` being type index 0:

      thunk : Unit -{ ( Partial | e ) }-> a *)
let thunk_ty : typ = t_fun t_unit (TRowExt partial_ent (TVar 1)) (TVar 0)

(** The handler of `toMaybe`, under `e`, `a` and `thunk`:

      { handles Partial
      ; return (x : a) -> ( openEff [e] ( Prelude.Just [a] ) ) x
      ; full abort [b] (_ : Unit, k : b -{e}-> Maybe a) -> Prelude.Nothing [a] }

    Under the clause's binder `b`, `b`, `a` and `e` are type indices 0, 1
    and 2. *)
let to_maybe_handler : handler = {
  h_ent = partial_ent;
  h_ret_ty = TVar 0;
  h_ret = EApp (EOpenEff (TVar 1) (ETyApp (EGlobal (prelude "Just") []) (TVar 0))) (EVar 0);
  h_clauses = [CFull "abort" 1 t_unit (t_fun (TVar 0) (TVar 2) (maybe_ty (TVar 1)))
                 (ETyApp (EGlobal (prelude "Nothing") []) (TVar 1))];
}

(** `handle ( thunk Prim.Unit ) with …` *)
let to_maybe_handle : exp = EHandle (EApp (EVar 0) (EGlobal prim_unit_ctor [])) to_maybe_handler

(** `Λ (e : Row Effect). Λ (_ : Partial ∉ e). Λ (a : Type).
       λ (thunk : Unit -{ ( Partial | e ) }-> a) / e. handle …` *)
let to_maybe : exp =
  ETyLam (KRow EEffect)
    (ECLam lacks_partial (ETyLam KType (ELam thunk_ty (TVar 1) to_maybe_handle)))

(** `forall (e : Row Effect). Partial ∉ e => forall (a : Type).
       ( Unit -{ ( Partial | e ) }-> a ) -{e}-> Maybe a` *)
let to_maybe_ty : typ =
  TForall (KRow EEffect)
    (TConstr lacks_partial (TForall KType (t_fun thunk_ty (TVar 1) (maybe_ty (TVar 0)))))

val to_maybe_typing : typing ex_sig [] (decl_ctx 0) [] true to_maybe to_maybe_ty TRowEmpty

(** * The names of `Prim` *)

val ex_prim_wf : unit -> Lemma (prim_wf ex_sig)
