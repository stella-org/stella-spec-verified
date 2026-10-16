(* Each family is one mutual induction over the classes of the definition.
   Its `upn_*` lemma, proved first, re-establishes the hypothesis under type
   binders. *)
module Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Syntax
open Stella.Core.Subst
module L = FStar.List.Tot

let upn_ren_comp (n: nat) (xi zeta theta: ren)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures forall (i: nat). upn_ren n theta i == upn_ren n xi (upn_ren n zeta i)) = ()

let upn_ren_id (n: nat) (xi: ren)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures forall (i: nat). upn_ren n xi i == i) = ()

let rec ren_ren_ty (xi: ren) (zeta: ren) (theta: ren) (t: typ)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_ty xi (ren_ty zeta t) == ren_ty theta t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> ren_ren_ty xi zeta theta t1; ren_ren_ty xi zeta theta t2
  | TForall _ t ->
    upn_ren_comp 1 xi zeta theta; ren_ren_ty (up_ren xi) (up_ren zeta) (up_ren theta) t
  | TConstr cn t -> ren_ren_constr xi zeta theta cn; ren_ren_ty xi zeta theta t
  | TRowExt en t -> ren_ren_ent xi zeta theta en; ren_ren_ty xi zeta theta t
  | TRowUnion t1 t2 -> ren_ren_ty xi zeta theta t1; ren_ren_ty xi zeta theta t2

and ren_ren_ent (xi: ren) (zeta: ren) (theta: ren) (en: entry)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_ent xi (ren_ent zeta en) == ren_ent theta en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> ren_ren_ty xi zeta theta t
  | EntEff _ _ ts -> ren_ren_tys xi zeta theta ts

and ren_ren_constr (xi: ren) (zeta: ren) (theta: ren) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_constr xi (ren_constr zeta cn) == ren_constr theta cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> ren_ren_ty xi zeta theta t
  | CDisj t1 t2 -> ren_ren_ty xi zeta theta t1; ren_ren_ty xi zeta theta t2

and ren_ren_tys (xi: ren) (zeta: ren) (theta: ren) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_tys xi (ren_tys zeta ts) == ren_tys theta ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> ren_ren_ty xi zeta theta t; ren_ren_tys xi zeta theta ts

and ren_ren_layout (xi: ren) (zeta: ren) (theta: ren) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_layout xi (ren_layout zeta l) == ren_layout theta l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> ren_ren_ty xi zeta theta t; ren_ren_layout xi zeta theta l

let rec ren_id_ty (xi: ren) (t: typ)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_ty xi t == t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> ren_id_ty xi t1; ren_id_ty xi t2
  | TForall _ t -> upn_ren_id 1 xi; ren_id_ty (up_ren xi) t
  | TConstr cn t -> ren_id_constr xi cn; ren_id_ty xi t
  | TRowExt en t -> ren_id_ent xi en; ren_id_ty xi t
  | TRowUnion t1 t2 -> ren_id_ty xi t1; ren_id_ty xi t2

and ren_id_ent (xi: ren) (en: entry)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_ent xi en == en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> ren_id_ty xi t
  | EntEff _ _ ts -> ren_id_tys xi ts

and ren_id_constr (xi: ren) (cn: constr)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_constr xi cn == cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> ren_id_ty xi t
  | CDisj t1 t2 -> ren_id_ty xi t1; ren_id_ty xi t2

and ren_id_tys (xi: ren) (ts: list typ)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_tys xi ts == ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> ren_id_ty xi t; ren_id_tys xi ts

and ren_id_layout (xi: ren) (l: list (key & typ))
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_layout xi l == l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> ren_id_ty xi t; ren_id_layout xi l

let upn_rinst_ty (n: nat) (xi: ren) (sigma: tsub)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures forall (i: nat). upn_tsub n sigma i == TVar (upn_ren n xi i)) = ()

let rec rinst_ty (xi: ren) (sigma: tsub) (t: typ)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty xi t == sub_ty sigma t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> rinst_ty xi sigma t1; rinst_ty xi sigma t2
  | TForall _ t -> upn_rinst_ty 1 xi sigma; rinst_ty (up_ren xi) (up_tsub sigma) t
  | TConstr cn t -> rinst_constr xi sigma cn; rinst_ty xi sigma t
  | TRowExt en t -> rinst_ent xi sigma en; rinst_ty xi sigma t
  | TRowUnion t1 t2 -> rinst_ty xi sigma t1; rinst_ty xi sigma t2

and rinst_ent (xi: ren) (sigma: tsub) (en: entry)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ent xi en == sub_ent sigma en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> rinst_ty xi sigma t
  | EntEff _ _ ts -> rinst_tys xi sigma ts

and rinst_constr (xi: ren) (sigma: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_constr xi cn == sub_constr sigma cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> rinst_ty xi sigma t
  | CDisj t1 t2 -> rinst_ty xi sigma t1; rinst_ty xi sigma t2

and rinst_tys (xi: ren) (sigma: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_tys xi ts == sub_tys sigma ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> rinst_ty xi sigma t; rinst_tys xi sigma ts

and rinst_layout (xi: ren) (sigma: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_layout xi l == sub_layout sigma l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> rinst_ty xi sigma t; rinst_layout xi sigma l

let upn_sub_ren_ty (n: nat) (sigma: tsub) (xi: ren) (theta: tsub)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures forall (i: nat). upn_tsub n theta i == upn_tsub n sigma (upn_ren n xi i)) = ()

let rec sub_ren_ty (sigma: tsub) (xi: ren) (theta: tsub) (t: typ)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_ty sigma (ren_ty xi t) == sub_ty theta t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> sub_ren_ty sigma xi theta t1; sub_ren_ty sigma xi theta t2
  | TForall _ t ->
    upn_sub_ren_ty 1 sigma xi theta; sub_ren_ty (up_tsub sigma) (up_ren xi) (up_tsub theta) t
  | TConstr cn t -> sub_ren_constr sigma xi theta cn; sub_ren_ty sigma xi theta t
  | TRowExt en t -> sub_ren_ent sigma xi theta en; sub_ren_ty sigma xi theta t
  | TRowUnion t1 t2 -> sub_ren_ty sigma xi theta t1; sub_ren_ty sigma xi theta t2

and sub_ren_ent (sigma: tsub) (xi: ren) (theta: tsub) (en: entry)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_ent sigma (ren_ent xi en) == sub_ent theta en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> sub_ren_ty sigma xi theta t
  | EntEff _ _ ts -> sub_ren_tys sigma xi theta ts

and sub_ren_constr (sigma: tsub) (xi: ren) (theta: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_constr sigma (ren_constr xi cn) == sub_constr theta cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> sub_ren_ty sigma xi theta t
  | CDisj t1 t2 -> sub_ren_ty sigma xi theta t1; sub_ren_ty sigma xi theta t2

and sub_ren_tys (sigma: tsub) (xi: ren) (theta: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tys sigma (ren_tys xi ts) == sub_tys theta ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> sub_ren_ty sigma xi theta t; sub_ren_tys sigma xi theta ts

and sub_ren_layout (sigma: tsub) (xi: ren) (theta: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_layout sigma (ren_layout xi l) == sub_layout theta l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> sub_ren_ty sigma xi theta t; sub_ren_layout sigma xi theta l

let upn_ren_sub_ty (n: nat) (xi: ren) (sigma theta: tsub)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures forall (i: nat).
             upn_tsub n theta i == ren_ty (upn_ren n xi) (upn_tsub n sigma i)) =
  introduce forall (i: nat). upn_tsub n theta i == ren_ty (upn_ren n xi) (upn_tsub n sigma i)
  with if i < n then () else begin
    ren_ren_ty (shift n) xi (ren_shift n xi) (sigma (i - n));
    ren_ren_ty (upn_ren n xi) (shift n) (ren_shift n xi) (sigma (i - n))
  end

let rec ren_sub_ty (xi: ren) (sigma: tsub) (theta: tsub) (t: typ)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_ty xi (sub_ty sigma t) == sub_ty theta t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> ren_sub_ty xi sigma theta t1; ren_sub_ty xi sigma theta t2
  | TForall _ t ->
    upn_ren_sub_ty 1 xi sigma theta; ren_sub_ty (up_ren xi) (up_tsub sigma) (up_tsub theta) t
  | TConstr cn t -> ren_sub_constr xi sigma theta cn; ren_sub_ty xi sigma theta t
  | TRowExt en t -> ren_sub_ent xi sigma theta en; ren_sub_ty xi sigma theta t
  | TRowUnion t1 t2 -> ren_sub_ty xi sigma theta t1; ren_sub_ty xi sigma theta t2

and ren_sub_ent (xi: ren) (sigma: tsub) (theta: tsub) (en: entry)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_ent xi (sub_ent sigma en) == sub_ent theta en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> ren_sub_ty xi sigma theta t
  | EntEff _ _ ts -> ren_sub_tys xi sigma theta ts

and ren_sub_constr (xi: ren) (sigma: tsub) (theta: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_constr xi (sub_constr sigma cn) == sub_constr theta cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> ren_sub_ty xi sigma theta t
  | CDisj t1 t2 -> ren_sub_ty xi sigma theta t1; ren_sub_ty xi sigma theta t2

and ren_sub_tys (xi: ren) (sigma: tsub) (theta: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_tys xi (sub_tys sigma ts) == sub_tys theta ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> ren_sub_ty xi sigma theta t; ren_sub_tys xi sigma theta ts

and ren_sub_layout (xi: ren) (sigma: tsub) (theta: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_layout xi (sub_layout sigma l) == sub_layout theta l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> ren_sub_ty xi sigma theta t; ren_sub_layout xi sigma theta l

let upn_sub_sub_ty (n: nat) (tau sigma theta: tsub)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures forall (i: nat).
             upn_tsub n theta i == sub_ty (upn_tsub n tau) (upn_tsub n sigma i)) =
  introduce forall (i: nat). upn_tsub n theta i == sub_ty (upn_tsub n tau) (upn_tsub n sigma i)
  with if i < n then () else begin
    ren_sub_ty (shift n) tau (tsub_shift n tau) (sigma (i - n));
    sub_ren_ty (upn_tsub n tau) (shift n) (tsub_shift n tau) (sigma (i - n))
  end

let rec sub_sub_ty (tau: tsub) (sigma: tsub) (theta: tsub) (t: typ)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty tau (sub_ty sigma t) == sub_ty theta t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> sub_sub_ty tau sigma theta t1; sub_sub_ty tau sigma theta t2
  | TForall _ t ->
    upn_sub_sub_ty 1 tau sigma theta; sub_sub_ty (up_tsub tau) (up_tsub sigma) (up_tsub theta) t
  | TConstr cn t -> sub_sub_constr tau sigma theta cn; sub_sub_ty tau sigma theta t
  | TRowExt en t -> sub_sub_ent tau sigma theta en; sub_sub_ty tau sigma theta t
  | TRowUnion t1 t2 -> sub_sub_ty tau sigma theta t1; sub_sub_ty tau sigma theta t2

and sub_sub_ent (tau: tsub) (sigma: tsub) (theta: tsub) (en: entry)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ent tau (sub_ent sigma en) == sub_ent theta en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> sub_sub_ty tau sigma theta t
  | EntEff _ _ ts -> sub_sub_tys tau sigma theta ts

and sub_sub_constr (tau: tsub) (sigma: tsub) (theta: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_constr tau (sub_constr sigma cn) == sub_constr theta cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> sub_sub_ty tau sigma theta t
  | CDisj t1 t2 -> sub_sub_ty tau sigma theta t1; sub_sub_ty tau sigma theta t2

and sub_sub_tys (tau: tsub) (sigma: tsub) (theta: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_tys tau (sub_tys sigma ts) == sub_tys theta ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> sub_sub_ty tau sigma theta t; sub_sub_tys tau sigma theta ts

and sub_sub_layout (tau: tsub) (sigma: tsub) (theta: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_layout tau (sub_layout sigma l) == sub_layout theta l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> sub_sub_ty tau sigma theta t; sub_sub_layout tau sigma theta l

let upn_sub_id_ty (n: nat) (sigma: tsub)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures forall (i: nat). upn_tsub n sigma i == TVar i) = ()

let rec sub_id_ty (sigma: tsub) (t: typ)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty sigma t == t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> sub_id_ty sigma t1; sub_id_ty sigma t2
  | TForall _ t -> upn_sub_id_ty 1 sigma; sub_id_ty (up_tsub sigma) t
  | TConstr cn t -> sub_id_constr sigma cn; sub_id_ty sigma t
  | TRowExt en t -> sub_id_ent sigma en; sub_id_ty sigma t
  | TRowUnion t1 t2 -> sub_id_ty sigma t1; sub_id_ty sigma t2

and sub_id_ent (sigma: tsub) (en: entry)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ent sigma en == en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> sub_id_ty sigma t
  | EntEff _ _ ts -> sub_id_tys sigma ts

and sub_id_constr (sigma: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_constr sigma cn == cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> sub_id_ty sigma t
  | CDisj t1 t2 -> sub_id_ty sigma t1; sub_id_ty sigma t2

and sub_id_tys (sigma: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_tys sigma ts == ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> sub_id_ty sigma t; sub_id_tys sigma ts

and sub_id_layout (sigma: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_layout sigma l == l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> sub_id_ty sigma t; sub_id_layout sigma l

let ren_ty_ext (xi xi': ren) (t: typ)
  : Lemma (requires forall (i: nat). xi i == xi' i) (ensures ren_ty xi t == ren_ty xi' t) =
  ren_ren_ty xi' id_ren xi t; ren_id_ty id_ren t

let sub_ty_ext (sigma sigma': tsub) (t: typ)
  : Lemma (requires forall (i: nat). sigma i == sigma' i)
          (ensures sub_ty sigma t == sub_ty sigma' t) =
  sub_sub_ty sigma' tvar sigma t; sub_id_ty tvar t

let ren_ty_id (t: typ) : Lemma (ren_ty id_ren t == t) = ren_id_ty id_ren t

let sub_ty_tvar (t: typ) : Lemma (sub_ty tvar t == t) = sub_id_ty tvar t

let ren_ty_as_sub (xi: ren) (t: typ) : Lemma (ren_ty xi t == sub_ty (ren_tsub xi) t) =
  rinst_ty xi (ren_tsub xi) t

let ren_ty_shift0 (t: typ) : Lemma (ren_ty (shift 0) t == t) = ren_id_ty (shift 0) t
