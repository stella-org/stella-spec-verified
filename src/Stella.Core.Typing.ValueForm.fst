module Stella.Core.Typing.ValueForm
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Typing.Aux
module V = Stella.Core.Value

(* Mutual induction following `value_form` / `ctor_chain_form`, with the
   same measure. `value_head` alone does not carry over from `f` to
   `EApp f v` (a foreign head reads the arguments), so the induction
   carries `ctor_headed`: `decompose_global_app` keeps the head of `f`,
   and a constructor head makes `value_head` true whatever the arguments. *)

let ctor_headed (sg: sig) (e: exp) : bool =
  match decompose_global_app e with
  | Some (q, _, _) -> is_ctor sg q
  | None -> false

let rec value_form_is_value' (sg: sig) (e: exp)
  : Lemma (requires value_form sg e) (ensures V.is_value sg e) (decreases %[e; 1]) =
  match e with
  | ELit _ | ELam _ _ _ | ERecEmpty -> ()
  | ETyLam _ v | ECLam _ v | EInject _ _ v -> value_form_is_value' sg v
  | EExtend _ v1 v2 -> value_form_is_value' sg v1; value_form_is_value' sg v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ctor_chain_form_value' sg e

and ctor_chain_form_value' (sg: sig) (e: exp)
  : Lemma (requires ctor_chain_form sg e)
          (ensures ctor_headed sg e /\ V.value_head sg e /\ V.chain_values sg e)
          (decreases %[e; 0]) =
  match e with
  | EGlobal _ _ -> ()
  | EApp f v -> ctor_chain_form_value' sg f; value_form_is_value' sg v
  | ETyApp f _ | ECApp f -> ctor_chain_form_value' sg f

let ctor_chain_form_value sg e = ctor_chain_form_value' sg e

let value_form_is_value sg e = value_form_is_value' sg e
