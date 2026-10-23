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

let spine_cursor_snoc (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg) (a: spine_arg)
  : Lemma (spine_cursor sg q ks (L.append args [a]) ==
           (match spine_cursor sg q ks args with
            | Some (t', th') -> cursor_step sg t' th' a
            | None -> None)) =
  match global_scheme sg q with
  | Some (_, nk, t) -> if L.length ks = nk then cursor_snoc sg (kinst_ty ks t) tvar args a
  | None -> ()

let chain_cursor_global (sg: sig) (q: qname) (ks: list kind) = ()

let chain_cursor_apply_arg (sg: sig) (e: exp) (a: spine_arg) =
  decompose_apply_arg e a;
  let Some (q, ks, args) = decompose_global_app e in
  spine_cursor_snoc sg q ks args a

let decompose_prefix (e: exp) (a: spine_arg) = ()

(* One unfolding of `sub_ty` per application node. *)
let as_function_sub (sg: sig) (sigma: tsub) (t t1 r t2: typ) =
  let TApp (TApp (TApp (TCon q _) _) _) _ = t in
  let f = TCon q [] in
  assert (sub_ty sigma f == f);
  assert (sub_ty sigma (TApp f t1) == TApp f (sub_ty sigma t1));
  assert (sub_ty sigma (TApp (TApp f t1) r) == TApp (TApp f (sub_ty sigma t1)) (sub_ty sigma r))

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

let rec decompose_sub_ty_exp (sigma: tsub) (e: exp)
  : Lemma (ensures decompose_global_app (sub_ty_exp sigma e) ==
                   (match decompose_global_app e with
                    | Some (q, ks, args) -> Some (q, ks, L.map (sub_arg sigma) args)
                    | None -> None))
          (decreases e) =
  match e with
  | EApp f v ->
    decompose_sub_ty_exp sigma f;
    (match decompose_global_app f with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (sub_arg sigma) args [SVal v]
     | None -> ())
  | ETyApp f t ->
    decompose_sub_ty_exp sigma f;
    (match decompose_global_app f with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (sub_arg sigma) args [STy t]
     | None -> ())
  | ECApp f ->
    decompose_sub_ty_exp sigma f;
    (match decompose_global_app f with
     | Some (_, _, args) -> FStar.List.Tot.Properties.map_append (sub_arg sigma) args [SConstr]
     | None -> ())
  | _ -> ()

let rec decompose_sub_tm (sigma: esub) (e: exp)
  : Lemma (requires Some? (decompose_global_app e))
          (ensures (let Some (q, ks, args) = decompose_global_app e in
                    decompose_global_app (sub_tm sigma e) ==
                    Some (q, ks, L.map (sub_tm_arg sigma) args)))
          (decreases e) =
  match e with
  | EApp f v ->
    decompose_sub_tm sigma f;
    let Some (_, _, args) = decompose_global_app f in
    FStar.List.Tot.Properties.map_append (sub_tm_arg sigma) args [SVal v]
  | ETyApp f t ->
    decompose_sub_tm sigma f;
    let Some (_, _, args) = decompose_global_app f in
    FStar.List.Tot.Properties.map_append (sub_tm_arg sigma) args [STy t]
  | ECApp f ->
    decompose_sub_tm sigma f;
    let Some (_, _, args) = decompose_global_app f in
    FStar.List.Tot.Properties.map_append (sub_tm_arg sigma) args [SConstr]
  | _ -> ()

let rec cursor_sub_tm_args (sg: sig) (sigma: esub) (t: typ) (th: tsub) (args: list spine_arg)
  : Lemma (ensures cursor sg t th (L.map (sub_tm_arg sigma) args) == cursor sg t th args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: args' ->
    match cursor_step sg t th a with
    | Some (t', th') -> cursor_sub_tm_args sg sigma t' th' args'
    | None -> ()

let chain_cursor_sub_tm (sg: sig) (sigma: esub) (e: exp) =
  decompose_sub_tm sigma e;
  let Some (q, ks, args) = decompose_global_app e in
  match global_scheme sg q with
  | Some (_, nk, t) -> if L.length ks = nk then cursor_sub_tm_args sg sigma (kinst_ty ks t) tvar args
  | None -> ()

(* `kinst_ty` is unfolded one application node at a time. *)
let saturated_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (saturated sg (kinst_ty ks t) == saturated sg t) =
  match t with
  | TApp f t2 ->
    assert (kinst_ty ks t == TApp (kinst_ty ks f) (kinst_ty ks t2));
    (match f with
     | TApp g r ->
       assert (kinst_ty ks f == TApp (kinst_ty ks g) (kinst_ty ks r));
       (match g with
        | TApp h t1 ->
          assert (kinst_ty ks g == TApp (kinst_ty ks h) (kinst_ty ks t1));
          (match h with
           | TCon _ kl -> (match kl with [] -> () | _ :: _ -> ())
           | _ -> ())
        | _ -> ())
     | _ -> ())
  | _ -> ()
