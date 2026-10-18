module Stella.Core.Spine
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Sig
module L = FStar.List.Tot

let as_function_fun_ty (sg: sig) (q: qname) (t1 r t2: typ)
  : Lemma (requires is_function_tycon sg q)
          (ensures as_function sg (fun_ty q t1 r t2) == Some (t1, r, t2)) =
  ()

let rec cursor_snoc (sg: sig) (t: typ) (th: tsub) (args: list spine_arg) (a: spine_arg)
  : Lemma (ensures cursor sg t th (L.append args [a]) ==
                   (match cursor sg t th args with
                    | Some (t', th') -> cursor_step sg t' th' a
                    | None -> None))
          (decreases args) =
  match args with
  | [] -> (match cursor_step sg t th a with Some _ -> () | None -> ())
  | b :: args ->
    match cursor_step sg t th b with
    | Some (t', th') -> cursor_snoc sg t' th' args a
    | None -> ()

(* `scons s tvar` undoes the shift of `up_tsub`, so composing it after
   `up_tsub θ` gives `scons s θ` pointwise. *)
let cursor_instance_forall (s: typ) (th: tsub) (body: typ)
  : Lemma (subst1_ty s (sub_ty (up_tsub th) body) == sub_ty (scons s th) body) =
  let aux (i: nat)
    : Lemma (scons s th i == sub_ty (scons s tvar) (up_tsub th i)) =
    if i = 0 then ()
    else begin
      sub_ren_ty (scons s tvar) (shift 1) tvar (th (i - 1));
      sub_ty_tvar (th (i - 1))
    end
  in
  FStar.Classical.forall_intro aux;
  sub_sub_ty (scons s tvar) (up_tsub th) (scons s th) body

let saturated_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (saturated sg (kinst_ty ks t) == saturated sg t) =
  match t with
  | TApp (TApp (TApp (TCon _ kl) _) _) _ ->
    (match kl with [] -> () | _ :: _ -> ())
  | _ -> ()
