(* Proof structure.

   Every lemma is an equation between lists built by `L.map`. The maps of
   a context commute with entering a type binder by the σ-calculus laws
   (`Stella.Core.Subst.Lemmas.Typ`) and by the commutation of kind
   instantiation with renaming (`Stella.Core.Subst.Lemmas`), applied to
   every element through `map_comm`. *)
module Stella.Core.Context
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

(* Lists. *)

let rec map_comm (#a #b #c #d: Type) (f: b -> c) (g: a -> b) (f': d -> c) (g': a -> d)
  (l: list a)
  : Lemma (requires forall (x: a). f (g x) == f' (g' x))
          (ensures L.map f (L.map g l) == L.map f' (L.map g' l)) (decreases l) =
  match l with
  | [] -> ()
  | _ :: tl -> map_comm f g f' g' tl

let rec map_cancel (#a #b: Type) (f: b -> a) (g: a -> b) (l: list a)
  : Lemma (requires forall (x: a). f (g x) == x) (ensures L.map f (L.map g l) == l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: tl -> map_cancel f g tl

let rec map_fst_keep (#b: Type) (f: (atom & b) -> (atom & b)) (l: list (atom & b))
  : Lemma (requires forall (x: atom & b). fst (f x) == fst x)
          (ensures L.map fst (L.map f l) == L.map fst l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: tl -> map_fst_keep f tl

(* The region domain. *)

let rdom_ren_ctx_types xi g = map_fst_keep (ren_region xi) g.regions

let rdom_sub_ctx_types sigma g = map_fst_keep (sub_region sigma) g.regions

let rdom_kinst_ctx ks nk g = map_fst_keep (kinst_region ks) g.regions

let rdom_push_tvar g k = map_fst_keep (ren_region (shift 1)) g.regions

let rdom_add_assumps g cs = ()

let rdom_add_assump g c = ()

let rdom_enter_region g a l = ()

(* The hypotheses. *)

let hyps_ren_ctx_types xi g = LP.map_append (ren_constr xi) g.facts g.assumps

let hyps_sub_ctx_types sigma g = LP.map_append (sub_constr sigma) g.facts g.assumps

let hyps_kinst_ctx ks nk g = LP.map_append (kinst_constr ks) g.facts g.assumps

let hyps_push_tvar g k = LP.map_append (ren_constr (shift 1)) g.facts g.assumps

let mem_hyps_add_assumps g cs h =
  LP.append_mem g.facts (L.append cs g.assumps) h;
  LP.append_mem cs g.assumps h;
  LP.append_mem g.facts g.assumps h

(* Entering a binder and assuming a constraint. *)

let push_tvar_ren g k = ()

let add_assump_assumps g c = ()

let ren_ctx_types_push_tvar xi g k =
  let th = ren_shift 1 xi in
  let f = ren_constr (up_ren xi) in
  let s = ren_constr (shift 1) in
  introduce forall (c: constr). f (s c) == s (ren_constr xi c)
  with (ren_ren_constr (up_ren xi) (shift 1) th c; ren_ren_constr (shift 1) xi th c);
  map_comm f s s (ren_constr xi) g.facts;
  map_comm f s s (ren_constr xi) g.assumps;
  introduce forall (r: atom & layout).
    ren_region (up_ren xi) (ren_region (shift 1) r) == ren_region (shift 1) (ren_region xi r)
  with (ren_ren_layout (up_ren xi) (shift 1) th (snd r);
        ren_ren_layout (shift 1) xi th (snd r));
  map_comm (ren_region (up_ren xi)) (ren_region (shift 1)) (ren_region (shift 1)) (ren_region xi)
    g.regions;
  introduce forall (t: typ).
    ren_ty (up_ren xi) (ren_ty (shift 1) t) == ren_ty (shift 1) (ren_ty xi t)
  with (ren_ren_ty (up_ren xi) (shift 1) th t; ren_ren_ty (shift 1) xi th t);
  map_comm (ren_ty (up_ren xi)) (ren_ty (shift 1)) (ren_ty (shift 1)) (ren_ty xi) g.vars

let sub_ctx_types_push_tvar sigma g k =
  let th = tsub_shift 1 sigma in
  let f = sub_constr (up_tsub sigma) in
  let s = ren_constr (shift 1) in
  introduce forall (c: constr). f (s c) == s (sub_constr sigma c)
  with (sub_ren_constr (up_tsub sigma) (shift 1) th c; ren_sub_constr (shift 1) sigma th c);
  map_comm f s s (sub_constr sigma) g.facts;
  map_comm f s s (sub_constr sigma) g.assumps;
  introduce forall (r: atom & layout).
    sub_region (up_tsub sigma) (ren_region (shift 1) r) ==
    ren_region (shift 1) (sub_region sigma r)
  with (sub_ren_layout (up_tsub sigma) (shift 1) th (snd r);
        ren_sub_layout (shift 1) sigma th (snd r));
  map_comm (sub_region (up_tsub sigma)) (ren_region (shift 1)) (ren_region (shift 1))
    (sub_region sigma) g.regions;
  introduce forall (t: typ).
    sub_ty (up_tsub sigma) (ren_ty (shift 1) t) == ren_ty (shift 1) (sub_ty sigma t)
  with (sub_ren_ty (up_tsub sigma) (shift 1) th t; ren_sub_ty (shift 1) sigma th t);
  map_comm (sub_ty (up_tsub sigma)) (ren_ty (shift 1)) (ren_ty (shift 1)) (sub_ty sigma) g.vars

let kinst_ctx_push_tvar ks nk g k =
  let s = ren_constr (shift 1) in
  introduce forall (c: constr). kinst_constr ks (s c) == s (kinst_constr ks c)
  with kinst_ren_constr ks (shift 1) c;
  map_comm (kinst_constr ks) s s (kinst_constr ks) g.facts;
  map_comm (kinst_constr ks) s s (kinst_constr ks) g.assumps;
  introduce forall (r: atom & layout).
    kinst_region ks (ren_region (shift 1) r) == ren_region (shift 1) (kinst_region ks r)
  with kinst_ren_layout ks (shift 1) (snd r);
  map_comm (kinst_region ks) (ren_region (shift 1)) (ren_region (shift 1)) (kinst_region ks)
    g.regions;
  introduce forall (t: typ). kinst_ty ks (ren_ty (shift 1) t) == ren_ty (shift 1) (kinst_ty ks t)
  with kinst_ren_ty ks (shift 1) t;
  map_comm (kinst_ty ks) (ren_ty (shift 1)) (ren_ty (shift 1)) (kinst_ty ks) g.vars

let ren_ctx_types_add_assumps xi g cs = LP.map_append (ren_constr xi) cs g.assumps

let sub_ctx_types_add_assumps sigma g cs = LP.map_append (sub_constr sigma) cs g.assumps

let kinst_ctx_add_assumps ks nk g cs = LP.map_append (kinst_constr ks) cs g.assumps

let sub1_push_tvar s g k =
  let sg = scons s tvar in
  introduce forall (c: constr). sub_constr sg (ren_constr (shift 1) c) == c
  with (sub_ren_constr sg (shift 1) tvar c; sub_id_constr tvar c);
  map_cancel (sub_constr sg) (ren_constr (shift 1)) g.facts;
  map_cancel (sub_constr sg) (ren_constr (shift 1)) g.assumps;
  introduce forall (r: atom & layout). sub_region sg (ren_region (shift 1) r) == r
  with (sub_ren_layout sg (shift 1) tvar (snd r); sub_id_layout tvar (snd r));
  map_cancel (sub_region sg) (ren_region (shift 1)) g.regions;
  introduce forall (t: typ). sub_ty sg (ren_ty (shift 1) t) == t
  with (sub_ren_ty sg (shift 1) tvar t; sub_id_ty tvar t);
  map_cancel (sub_ty sg) (ren_ty (shift 1)) g.vars
