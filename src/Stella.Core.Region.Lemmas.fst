(* Each family is one mutual induction over the classes of the definition; for
   terms the interface exports the `exp` and `dtree` instances. The helpers
   before a family re-establish its hypothesis under binders. *)
module Stella.Core.Region.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
module L = FStar.List.Tot

let rec lc_mono_ty (n: nat) (m: nat) (t: typ)
  : Lemma (requires n <= m /\ lc_ty_at n t)
          (ensures lc_ty_at m t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> lc_mono_ty n m t1; lc_mono_ty n m t2
  | TForall _ t -> lc_mono_ty n m t
  | TConstr cn t -> lc_mono_constr n m cn; lc_mono_ty n m t
  | TRowExt en t -> lc_mono_ent n m en; lc_mono_ty n m t
  | TRowUnion t1 t2 -> lc_mono_ty n m t1; lc_mono_ty n m t2

and lc_mono_ent (n: nat) (m: nat) (en: entry)
  : Lemma (requires n <= m /\ lc_ent_at n en)
          (ensures lc_ent_at m en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> lc_mono_ty n m t
  | EntEff _ _ ts -> lc_mono_tys n m ts

and lc_mono_constr (n: nat) (m: nat) (cn: constr)
  : Lemma (requires n <= m /\ lc_constr_at n cn)
          (ensures lc_constr_at m cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> lc_mono_ty n m t
  | CDisj t1 t2 -> lc_mono_ty n m t1; lc_mono_ty n m t2

and lc_mono_tys (n: nat) (m: nat) (ts: list typ)
  : Lemma (requires n <= m /\ lc_tys_at n ts)
          (ensures lc_tys_at m ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> lc_mono_ty n m t; lc_mono_tys n m ts

and lc_mono_layout (n: nat) (m: nat) (l: list (key & typ))
  : Lemma (requires n <= m /\ lc_layout_at n l)
          (ensures lc_layout_at m l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> lc_mono_ty n m t; lc_mono_layout n m l

let rec lc_ren_ty (n: nat) (xi: ren) (t: typ)
  : Lemma (ensures lc_ty_at n (ren_ty xi t) == lc_ty_at n t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> lc_ren_ty n xi t1; lc_ren_ty n xi t2
  | TForall _ t -> lc_ren_ty n (up_ren xi) t
  | TConstr cn t -> lc_ren_constr n xi cn; lc_ren_ty n xi t
  | TRowExt en t -> lc_ren_ent n xi en; lc_ren_ty n xi t
  | TRowUnion t1 t2 -> lc_ren_ty n xi t1; lc_ren_ty n xi t2

and lc_ren_ent (n: nat) (xi: ren) (en: entry)
  : Lemma (ensures lc_ent_at n (ren_ent xi en) == lc_ent_at n en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> lc_ren_ty n xi t
  | EntEff _ _ ts -> lc_ren_tys n xi ts

and lc_ren_constr (n: nat) (xi: ren) (cn: constr)
  : Lemma (ensures lc_constr_at n (ren_constr xi cn) == lc_constr_at n cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> lc_ren_ty n xi t
  | CDisj t1 t2 -> lc_ren_ty n xi t1; lc_ren_ty n xi t2

and lc_ren_tys (n: nat) (xi: ren) (ts: list typ)
  : Lemma (ensures lc_tys_at n (ren_tys xi ts) == lc_tys_at n ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> lc_ren_ty n xi t; lc_ren_tys n xi ts

and lc_ren_layout (n: nat) (xi: ren) (l: list (key & typ))
  : Lemma (ensures lc_layout_at n (ren_layout xi l) == lc_layout_at n l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> lc_ren_ty n xi t; lc_ren_layout n xi l

let lc_upn_tsub (n m: nat) (sigma: tsub)
  : Lemma (requires forall (i: nat). lc_ty_at n (sigma i))
          (ensures forall (i: nat). lc_ty_at n (upn_tsub m sigma i)) =
  introduce forall (i: nat). lc_ty_at n (upn_tsub m sigma i)
  with if i < m then () else lc_ren_ty n (shift m) (sigma (i - m))

let rec lc_sub_ty (n: nat) (sigma: tsub) (t: typ)
  : Lemma (requires lc_ty_at n t /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_ty_at n (sub_ty sigma t))
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> lc_sub_ty n sigma t1; lc_sub_ty n sigma t2
  | TForall _ t -> lc_upn_tsub n 1 sigma; lc_sub_ty n (up_tsub sigma) t
  | TConstr cn t -> lc_sub_constr n sigma cn; lc_sub_ty n sigma t
  | TRowExt en t -> lc_sub_ent n sigma en; lc_sub_ty n sigma t
  | TRowUnion t1 t2 -> lc_sub_ty n sigma t1; lc_sub_ty n sigma t2

and lc_sub_ent (n: nat) (sigma: tsub) (en: entry)
  : Lemma (requires lc_ent_at n en /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_ent_at n (sub_ent sigma en))
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> lc_sub_ty n sigma t
  | EntEff _ _ ts -> lc_sub_tys n sigma ts

and lc_sub_constr (n: nat) (sigma: tsub) (cn: constr)
  : Lemma (requires lc_constr_at n cn /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_constr_at n (sub_constr sigma cn))
          (decreases cn) =
  match cn with
  | CLacks _ t -> lc_sub_ty n sigma t
  | CDisj t1 t2 -> lc_sub_ty n sigma t1; lc_sub_ty n sigma t2

and lc_sub_tys (n: nat) (sigma: tsub) (ts: list typ)
  : Lemma (requires lc_tys_at n ts /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_tys_at n (sub_tys sigma ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> lc_sub_ty n sigma t; lc_sub_tys n sigma ts

and lc_sub_layout (n: nat) (sigma: tsub) (l: list (key & typ))
  : Lemma (requires lc_layout_at n l /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_layout_at n (sub_layout sigma l))
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> lc_sub_ty n sigma t; lc_sub_layout n sigma l

let rec rmap_ren_ty (g: region_ref -> region_ref) (xi: ren) (t: typ)
  : Lemma (ensures rmap_ty g (ren_ty xi t) == ren_ty xi (rmap_ty g t))
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> rmap_ren_ty g xi t1; rmap_ren_ty g xi t2
  | TForall _ t -> rmap_ren_ty g (up_ren xi) t
  | TConstr cn t -> rmap_ren_constr g xi cn; rmap_ren_ty g xi t
  | TRowExt en t -> rmap_ren_ent g xi en; rmap_ren_ty g xi t
  | TRowUnion t1 t2 -> rmap_ren_ty g xi t1; rmap_ren_ty g xi t2

and rmap_ren_ent (g: region_ref -> region_ref) (xi: ren) (en: entry)
  : Lemma (ensures rmap_ent g (ren_ent xi en) == ren_ent xi (rmap_ent g en))
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> rmap_ren_ty g xi t
  | EntEff _ _ ts -> rmap_ren_tys g xi ts

and rmap_ren_constr (g: region_ref -> region_ref) (xi: ren) (cn: constr)
  : Lemma (ensures rmap_constr g (ren_constr xi cn) == ren_constr xi (rmap_constr g cn))
          (decreases cn) =
  match cn with
  | CLacks _ t -> rmap_ren_ty g xi t
  | CDisj t1 t2 -> rmap_ren_ty g xi t1; rmap_ren_ty g xi t2

and rmap_ren_tys (g: region_ref -> region_ref) (xi: ren) (ts: list typ)
  : Lemma (ensures rmap_tys g (ren_tys xi ts) == ren_tys xi (rmap_tys g ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> rmap_ren_ty g xi t; rmap_ren_tys g xi ts

and rmap_ren_layout (g: region_ref -> region_ref) (xi: ren) (l: list (key & typ))
  : Lemma (ensures rmap_layout g (ren_layout xi l) == ren_layout xi (rmap_layout g l))
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> rmap_ren_ty g xi t; rmap_ren_layout g xi l

let rmap_upn_tsub (m: nat) (g: region_ref -> region_ref) (sigma theta: tsub)
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures forall (i: nat). upn_tsub m theta i == rmap_ty g (upn_tsub m sigma i)) =
  introduce forall (i: nat). upn_tsub m theta i == rmap_ty g (upn_tsub m sigma i)
  with if i < m then () else rmap_ren_ty g (shift m) (sigma (i - m))

let rec rmap_sub_ty (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (t: typ)
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_ty g (sub_ty sigma t) == sub_ty theta (rmap_ty g t))
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> rmap_sub_ty g sigma theta t1; rmap_sub_ty g sigma theta t2
  | TForall _ t -> rmap_upn_tsub 1 g sigma theta; rmap_sub_ty g (up_tsub sigma) (up_tsub theta) t
  | TConstr cn t -> rmap_sub_constr g sigma theta cn; rmap_sub_ty g sigma theta t
  | TRowExt en t -> rmap_sub_ent g sigma theta en; rmap_sub_ty g sigma theta t
  | TRowUnion t1 t2 -> rmap_sub_ty g sigma theta t1; rmap_sub_ty g sigma theta t2

and rmap_sub_ent (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (en: entry)
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_ent g (sub_ent sigma en) == sub_ent theta (rmap_ent g en))
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> rmap_sub_ty g sigma theta t
  | EntEff _ _ ts -> rmap_sub_tys g sigma theta ts

and rmap_sub_constr (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (cn: constr)
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_constr g (sub_constr sigma cn) == sub_constr theta (rmap_constr g cn))
          (decreases cn) =
  match cn with
  | CLacks _ t -> rmap_sub_ty g sigma theta t
  | CDisj t1 t2 -> rmap_sub_ty g sigma theta t1; rmap_sub_ty g sigma theta t2

and rmap_sub_tys (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (ts: list typ)
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_tys g (sub_tys sigma ts) == sub_tys theta (rmap_tys g ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> rmap_sub_ty g sigma theta t; rmap_sub_tys g sigma theta ts

and rmap_sub_layout (g: region_ref -> region_ref) (sigma: tsub) (theta: tsub) (l: list (key & typ))
  : Lemma (requires forall (i: nat). theta i == rmap_ty g (sigma i))
          (ensures rmap_layout g (sub_layout sigma l) == sub_layout theta (rmap_layout g l))
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> rmap_sub_ty g sigma theta t; rmap_sub_layout g sigma theta l

let rec open_close_ty (a: atom) (d: nat) (t: typ)
  : Lemma (requires lc_ty_at d t)
          (ensures rmap_ty (open_rr a d) (rmap_ty (close_rr a d) t) == t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> open_close_ty a d t1; open_close_ty a d t2
  | TForall _ t -> open_close_ty a d t
  | TConstr cn t -> open_close_constr a d cn; open_close_ty a d t
  | TRowExt en t -> open_close_ent a d en; open_close_ty a d t
  | TRowUnion t1 t2 -> open_close_ty a d t1; open_close_ty a d t2

and open_close_ent (a: atom) (d: nat) (en: entry)
  : Lemma (requires lc_ent_at d en)
          (ensures rmap_ent (open_rr a d) (rmap_ent (close_rr a d) en) == en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> open_close_ty a d t
  | EntEff _ _ ts -> open_close_tys a d ts

and open_close_constr (a: atom) (d: nat) (cn: constr)
  : Lemma (requires lc_constr_at d cn)
          (ensures rmap_constr (open_rr a d) (rmap_constr (close_rr a d) cn) == cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> open_close_ty a d t
  | CDisj t1 t2 -> open_close_ty a d t1; open_close_ty a d t2

and open_close_tys (a: atom) (d: nat) (ts: list typ)
  : Lemma (requires lc_tys_at d ts)
          (ensures rmap_tys (open_rr a d) (rmap_tys (close_rr a d) ts) == ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> open_close_ty a d t; open_close_tys a d ts

and open_close_layout (a: atom) (d: nat) (l: list (key & typ))
  : Lemma (requires lc_layout_at d l)
          (ensures rmap_layout (open_rr a d) (rmap_layout (close_rr a d) l) == l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> open_close_ty a d t; open_close_layout a d l

let close_open_rr (a: atom) (d: nat) (r: region_ref)
  : Lemma (requires not (L.mem a (frn_rr r))) (ensures close_rr a d (open_rr a d r) == r) = ()

let close_open_key (a: atom) (d: nat) (k: key)
  : Lemma (requires not (L.mem a (frn_key k)))
          (ensures rmap_key (close_rr a d) (rmap_key (open_rr a d) k) == k) = ()

let rec close_open_ty (a: atom) (d: nat) (t: typ)
  : Lemma (requires not (L.mem a (frn_ty t)))
          (ensures rmap_ty (close_rr a d) (rmap_ty (open_rr a d) t) == t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> close_open_ty a d t1; close_open_ty a d t2
  | TForall _ t -> close_open_ty a d t
  | TConstr cn t -> close_open_constr a d cn; close_open_ty a d t
  | TRowExt en t -> close_open_ent a d en; close_open_ty a d t
  | TRowUnion t1 t2 -> close_open_ty a d t1; close_open_ty a d t2

and close_open_ent (a: atom) (d: nat) (en: entry)
  : Lemma (requires not (L.mem a (frn_ent en)))
          (ensures rmap_ent (close_rr a d) (rmap_ent (open_rr a d) en) == en)
          (decreases en) =
  match en with
  | EntTy k t -> close_open_key a d k; close_open_ty a d t
  | EntEff _ _ ts -> close_open_tys a d ts
  | EntRegion r -> close_open_rr a d r

and close_open_constr (a: atom) (d: nat) (cn: constr)
  : Lemma (requires not (L.mem a (frn_constr cn)))
          (ensures rmap_constr (close_rr a d) (rmap_constr (open_rr a d) cn) == cn)
          (decreases cn) =
  match cn with
  | CLacks k t -> close_open_key a d k; close_open_ty a d t
  | CDisj t1 t2 -> close_open_ty a d t1; close_open_ty a d t2

and close_open_tys (a: atom) (d: nat) (ts: list typ)
  : Lemma (requires not (L.mem a (frn_tys ts)))
          (ensures rmap_tys (close_rr a d) (rmap_tys (open_rr a d) ts) == ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> close_open_ty a d t; close_open_tys a d ts

and close_open_layout (a: atom) (d: nat) (l: list (key & typ))
  : Lemma (requires not (L.mem a (frn_layout l)))
          (ensures rmap_layout (close_rr a d) (rmap_layout (open_rr a d) l) == l)
          (decreases l) =
  match l with
  | [] -> ()
  | (k, t) :: l -> close_open_key a d k; close_open_ty a d t; close_open_layout a d l

let rec lc_open_ty (a: atom) (d: nat) (t: typ)
  : Lemma (requires lc_ty_at (d + 1) t)
          (ensures lc_ty_at d (rmap_ty (open_rr a d) t))
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> lc_open_ty a d t1; lc_open_ty a d t2
  | TForall _ t -> lc_open_ty a d t
  | TConstr cn t -> lc_open_constr a d cn; lc_open_ty a d t
  | TRowExt en t -> lc_open_ent a d en; lc_open_ty a d t
  | TRowUnion t1 t2 -> lc_open_ty a d t1; lc_open_ty a d t2

and lc_open_ent (a: atom) (d: nat) (en: entry)
  : Lemma (requires lc_ent_at (d + 1) en)
          (ensures lc_ent_at d (rmap_ent (open_rr a d) en))
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> lc_open_ty a d t
  | EntEff _ _ ts -> lc_open_tys a d ts

and lc_open_constr (a: atom) (d: nat) (cn: constr)
  : Lemma (requires lc_constr_at (d + 1) cn)
          (ensures lc_constr_at d (rmap_constr (open_rr a d) cn))
          (decreases cn) =
  match cn with
  | CLacks _ t -> lc_open_ty a d t
  | CDisj t1 t2 -> lc_open_ty a d t1; lc_open_ty a d t2

and lc_open_tys (a: atom) (d: nat) (ts: list typ)
  : Lemma (requires lc_tys_at (d + 1) ts)
          (ensures lc_tys_at d (rmap_tys (open_rr a d) ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> lc_open_ty a d t; lc_open_tys a d ts

and lc_open_layout (a: atom) (d: nat) (l: list (key & typ))
  : Lemma (requires lc_layout_at (d + 1) l)
          (ensures lc_layout_at d (rmap_layout (open_rr a d) l))
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> lc_open_ty a d t; lc_open_layout a d l

let rec open_lc_ty (a: atom) (d: nat) (t: typ)
  : Lemma (requires lc_ty_at d t)
          (ensures rmap_ty (open_rr a d) t == t)
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 -> open_lc_ty a d t1; open_lc_ty a d t2
  | TForall _ t -> open_lc_ty a d t
  | TConstr cn t -> open_lc_constr a d cn; open_lc_ty a d t
  | TRowExt en t -> open_lc_ent a d en; open_lc_ty a d t
  | TRowUnion t1 t2 -> open_lc_ty a d t1; open_lc_ty a d t2

and open_lc_ent (a: atom) (d: nat) (en: entry)
  : Lemma (requires lc_ent_at d en)
          (ensures rmap_ent (open_rr a d) en == en)
          (decreases en) =
  match en with
  | EntRegion _ -> ()
  | EntTy _ t -> open_lc_ty a d t
  | EntEff _ _ ts -> open_lc_tys a d ts

and open_lc_constr (a: atom) (d: nat) (cn: constr)
  : Lemma (requires lc_constr_at d cn)
          (ensures rmap_constr (open_rr a d) cn == cn)
          (decreases cn) =
  match cn with
  | CLacks _ t -> open_lc_ty a d t
  | CDisj t1 t2 -> open_lc_ty a d t1; open_lc_ty a d t2

and open_lc_tys (a: atom) (d: nat) (ts: list typ)
  : Lemma (requires lc_tys_at d ts)
          (ensures rmap_tys (open_rr a d) ts == ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> open_lc_ty a d t; open_lc_tys a d ts

and open_lc_layout (a: atom) (d: nat) (l: list (key & typ))
  : Lemma (requires lc_layout_at d l)
          (ensures rmap_layout (open_rr a d) l == l)
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> open_lc_ty a d t; open_lc_layout a d l

let rec lc_mono_occ (n m: nat) (o: occ)
  : Lemma (requires n <= m /\ lc_occ_at n o) (ensures lc_occ_at m o) (decreases o) =
  match o with
  | OScrut _ -> ()
  | OCtor o _ _ | ORecord o _ | OVariant o _ -> lc_mono_occ n m o

let rec lc_open_occ (a: atom) (d: nat) (o: occ)
  : Lemma (requires lc_occ_at (d + 1) o) (ensures lc_occ_at d (rmap_occ (open_rr a d) o))
          (decreases o) =
  match o with
  | OScrut _ -> ()
  | OCtor o _ _ | ORecord o _ | OVariant o _ -> lc_open_occ a d o

let rec open_lc_occ (a: atom) (d: nat) (o: occ)
  : Lemma (requires lc_occ_at d o) (ensures rmap_occ (open_rr a d) o == o) (decreases o) =
  match o with
  | OScrut _ -> ()
  | OCtor o _ _ | ORecord o _ | OVariant o _ -> open_lc_occ a d o

let rec open_close_occ (a: atom) (d: nat) (o: occ)
  : Lemma (requires lc_occ_at d o)
          (ensures rmap_occ (open_rr a d) (rmap_occ (close_rr a d) o) == o) (decreases o) =
  match o with
  | OScrut _ -> ()
  | OCtor o _ _ | ORecord o _ | OVariant o _ -> open_close_occ a d o

let rec close_open_occ (a: atom) (d: nat) (o: occ)
  : Lemma (requires not (L.mem a (frn_occ o)))
          (ensures rmap_occ (close_rr a d) (rmap_occ (open_rr a d) o) == o) (decreases o) =
  match o with
  | OScrut _ -> ()
  | OCtor o _ _ -> close_open_occ a d o
  | ORecord o k | OVariant o k -> close_open_occ a d o; close_open_key a d k

let rec lc_mono_exp (n: nat) (m: nat) (e: exp)
  : Lemma (requires n <= m /\ lc_exp_at n e)
          (ensures lc_exp_at m e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> lc_mono_ty n m t; lc_mono_ty n m r; lc_mono_exp n m b
  | EApp e1 e2 -> lc_mono_exp n m e1; lc_mono_exp n m e2
  | ETyLam _ b -> lc_mono_exp n m b
  | ETyApp b t -> lc_mono_exp n m b; lc_mono_ty n m t
  | ECLam cn b -> lc_mono_constr n m cn; lc_mono_exp n m b
  | ECApp b -> lc_mono_exp n m b
  | ELet t e1 e2 -> lc_mono_ty n m t; lc_mono_exp n m e1; lc_mono_exp n m e2
  | ELetRec bs b -> lc_mono_binds n m bs; lc_mono_exp n m b
  | ECase es dt -> lc_mono_exps n m es; lc_mono_dt n m dt
  | ELetJoin ts t e1 e2 ->
    lc_mono_tys n m ts; lc_mono_ty n m t; lc_mono_exp n m e1; lc_mono_exp n m e2
  | EJump _ es -> lc_mono_exps n m es
  | EExtend _ e1 e2 -> lc_mono_exp n m e1; lc_mono_exp n m e2
  | ESelect _ b -> lc_mono_exp n m b
  | ERestrict _ b -> lc_mono_exp n m b
  | EUpdate _ e1 e2 -> lc_mono_exp n m e1; lc_mono_exp n m e2
  | EMerge e1 e2 -> lc_mono_exp n m e1; lc_mono_exp n m e2
  | EInject _ t b -> lc_mono_ty n m t; lc_mono_exp n m b
  | EWeaken _ t b -> lc_mono_ty n m t; lc_mono_exp n m b
  | EAbsurd t b -> lc_mono_ty n m t; lc_mono_exp n m b
  | EPerform _ _ ts b -> lc_mono_tys n m ts; lc_mono_exp n m b
  | EHandle b h ->
    lc_mono_exp n m b; lc_mono_ent n m h.h_ent; lc_mono_ty n m h.h_ret_ty; lc_mono_exp n m h.h_ret;
    lc_mono_cls n m h.h_clauses
  | EOpenEff t b -> lc_mono_ty n m t; lc_mono_exp n m b
  | ERegion l es b -> lc_mono_layout n m l; lc_mono_exps n m es; lc_mono_exp (n + 1) (m + 1) b
  | EWriteCell _ _ b -> lc_mono_exp n m b
  | EMatch th dt -> lc_mono_exps n m th; lc_mono_dt n m dt
  | EOpenEffC t b -> lc_mono_ty n m t; lc_mono_exp n m b
  | EFill _ b -> lc_mono_exp n m b
  | ERegionOpen _ th b -> lc_mono_cells n m th; lc_mono_exp n m b
  | EOpaque _ t -> lc_mono_ty n m t

and lc_mono_exps (n: nat) (m: nat) (es: list exp)
  : Lemma (requires n <= m /\ lc_exps_at n es)
          (ensures lc_exps_at m es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> lc_mono_exp n m e; lc_mono_exps n m es

and lc_mono_binds (n: nat) (m: nat) (bs: list (typ & exp))
  : Lemma (requires n <= m /\ lc_binds_at n bs)
          (ensures lc_binds_at m bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> lc_mono_ty n m t; lc_mono_exp n m e; lc_mono_binds n m bs

and lc_mono_cells (n: nat) (m: nat) (th: list (key & exp))
  : Lemma (requires n <= m /\ lc_cells_at n th)
          (ensures lc_cells_at m th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> lc_mono_exp n m e; lc_mono_cells n m th

and lc_mono_dt (n: nat) (m: nat) (dt: dtree)
  : Lemma (requires n <= m /\ lc_dt_at n dt)
          (ensures lc_dt_at m dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> lc_mono_exp n m e
  | DBind o dt -> lc_mono_occ n m o; lc_mono_dt n m dt
  | DSwitchCtor o bs df -> lc_mono_occ n m o; lc_mono_brs n m bs; lc_mono_odt n m df
  | DSwitchLit o bs df -> lc_mono_occ n m o; lc_mono_brs n m bs; lc_mono_dt n m df
  | DSwitchKey o bs df -> lc_mono_occ n m o; lc_mono_kbrs n m bs; lc_mono_odt n m df
  | DGuard e dt1 dt2 -> lc_mono_exp n m e; lc_mono_dt n m dt1; lc_mono_dt n m dt2

and lc_mono_odt (n: nat) (m: nat) (df: option dtree)
  : Lemma (requires n <= m /\ lc_odt_at n df)
          (ensures lc_odt_at m df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> lc_mono_dt n m dt

and lc_mono_brs (#lb: eqtype) (n: nat) (m: nat) (bs: list (lb & dtree))
  : Lemma (requires n <= m /\ lc_brs_at n bs)
          (ensures lc_brs_at m bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_mono_dt n m dt; lc_mono_brs n m bs

and lc_mono_kbrs (n: nat) (m: nat) (bs: list (key & dtree))
  : Lemma (requires n <= m /\ lc_kbrs_at n bs)
          (ensures lc_kbrs_at m bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_mono_dt n m dt; lc_mono_kbrs n m bs

and lc_mono_cls (n: nat) (m: nat) (cs: list clause)
  : Lemma (requires n <= m /\ lc_cls_at n cs)
          (ensures lc_cls_at m cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt b :: cs ->
    lc_mono_ty n m s; lc_mono_ty n m kt; lc_mono_exp n m b; lc_mono_cls n m cs
  | CFast _ _ s b :: cs -> lc_mono_ty n m s; lc_mono_exp n m b; lc_mono_cls n m cs

let rec lc_open_exp (a: atom) (d: nat) (e: exp)
  : Lemma (requires lc_exp_at (d + 1) e)
          (ensures lc_exp_at d (rmap_exp (open_rr a) d e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> lc_open_ty a d t; lc_open_ty a d r; lc_open_exp a d b
  | EApp e1 e2 -> lc_open_exp a d e1; lc_open_exp a d e2
  | ETyLam _ b -> lc_open_exp a d b
  | ETyApp b t -> lc_open_exp a d b; lc_open_ty a d t
  | ECLam cn b -> lc_open_constr a d cn; lc_open_exp a d b
  | ECApp b -> lc_open_exp a d b
  | ELet t e1 e2 -> lc_open_ty a d t; lc_open_exp a d e1; lc_open_exp a d e2
  | ELetRec bs b -> lc_open_binds a d bs; lc_open_exp a d b
  | ECase es dt -> lc_open_exps a d es; lc_open_dt a d dt
  | ELetJoin ts t e1 e2 ->
    lc_open_tys a d ts; lc_open_ty a d t; lc_open_exp a d e1; lc_open_exp a d e2
  | EJump _ es -> lc_open_exps a d es
  | EExtend _ e1 e2 -> lc_open_exp a d e1; lc_open_exp a d e2
  | ESelect _ b -> lc_open_exp a d b
  | ERestrict _ b -> lc_open_exp a d b
  | EUpdate _ e1 e2 -> lc_open_exp a d e1; lc_open_exp a d e2
  | EMerge e1 e2 -> lc_open_exp a d e1; lc_open_exp a d e2
  | EInject _ t b -> lc_open_ty a d t; lc_open_exp a d b
  | EWeaken _ t b -> lc_open_ty a d t; lc_open_exp a d b
  | EAbsurd t b -> lc_open_ty a d t; lc_open_exp a d b
  | EPerform _ _ ts b -> lc_open_tys a d ts; lc_open_exp a d b
  | EHandle b h ->
    lc_open_exp a d b; lc_open_ent a d h.h_ent; lc_open_ty a d h.h_ret_ty; lc_open_exp a d h.h_ret;
    lc_open_cls a d h.h_clauses
  | EOpenEff t b -> lc_open_ty a d t; lc_open_exp a d b
  | ERegion l es b -> lc_open_layout a d l; lc_open_exps a d es; lc_open_exp a (d + 1) b
  | EWriteCell _ _ b -> lc_open_exp a d b
  | EMatch th dt -> lc_open_exps a d th; lc_open_dt a d dt
  | EOpenEffC t b -> lc_open_ty a d t; lc_open_exp a d b
  | EFill _ b -> lc_open_exp a d b
  | ERegionOpen _ th b -> lc_open_cells a d th; lc_open_exp a d b
  | EOpaque _ t -> lc_open_ty a d t

and lc_open_exps (a: atom) (d: nat) (es: list exp)
  : Lemma (requires lc_exps_at (d + 1) es)
          (ensures lc_exps_at d (rmap_exps (open_rr a) d es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> lc_open_exp a d e; lc_open_exps a d es

and lc_open_binds (a: atom) (d: nat) (bs: list (typ & exp))
  : Lemma (requires lc_binds_at (d + 1) bs)
          (ensures lc_binds_at d (rmap_binds (open_rr a) d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> lc_open_ty a d t; lc_open_exp a d e; lc_open_binds a d bs

and lc_open_cells (a: atom) (d: nat) (th: list (key & exp))
  : Lemma (requires lc_cells_at (d + 1) th)
          (ensures lc_cells_at d (rmap_cells (open_rr a) d th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> lc_open_exp a d e; lc_open_cells a d th

and lc_open_dt (a: atom) (d: nat) (dt: dtree)
  : Lemma (requires lc_dt_at (d + 1) dt)
          (ensures lc_dt_at d (rmap_dt (open_rr a) d dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> lc_open_exp a d e
  | DBind o dt -> lc_open_occ a d o; lc_open_dt a d dt
  | DSwitchCtor o bs df -> lc_open_occ a d o; lc_open_brs a d bs; lc_open_odt a d df
  | DSwitchLit o bs df -> lc_open_occ a d o; lc_open_brs a d bs; lc_open_dt a d df
  | DSwitchKey o bs df -> lc_open_occ a d o; lc_open_kbrs a d bs; lc_open_odt a d df
  | DGuard e dt1 dt2 -> lc_open_exp a d e; lc_open_dt a d dt1; lc_open_dt a d dt2

and lc_open_odt (a: atom) (d: nat) (df: option dtree)
  : Lemma (requires lc_odt_at (d + 1) df)
          (ensures lc_odt_at d (rmap_odt (open_rr a) d df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> lc_open_dt a d dt

and lc_open_brs (#lb: eqtype) (a: atom) (d: nat) (bs: list (lb & dtree))
  : Lemma (requires lc_brs_at (d + 1) bs)
          (ensures lc_brs_at d (rmap_brs (open_rr a) d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_open_dt a d dt; lc_open_brs a d bs

and lc_open_kbrs (a: atom) (d: nat) (bs: list (key & dtree))
  : Lemma (requires lc_kbrs_at (d + 1) bs)
          (ensures lc_kbrs_at d (rmap_kbrs (open_rr a) d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_open_dt a d dt; lc_open_kbrs a d bs

and lc_open_cls (a: atom) (d: nat) (cs: list clause)
  : Lemma (requires lc_cls_at (d + 1) cs)
          (ensures lc_cls_at d (rmap_cls (open_rr a) d cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt b :: cs ->
    lc_open_ty a d s; lc_open_ty a d kt; lc_open_exp a d b; lc_open_cls a d cs
  | CFast _ _ s b :: cs -> lc_open_ty a d s; lc_open_exp a d b; lc_open_cls a d cs

let rec open_lc_exp (a: atom) (d: nat) (e: exp)
  : Lemma (requires lc_exp_at d e)
          (ensures rmap_exp (open_rr a) d e == e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> open_lc_ty a d t; open_lc_ty a d r; open_lc_exp a d b
  | EApp e1 e2 -> open_lc_exp a d e1; open_lc_exp a d e2
  | ETyLam _ b -> open_lc_exp a d b
  | ETyApp b t -> open_lc_exp a d b; open_lc_ty a d t
  | ECLam cn b -> open_lc_constr a d cn; open_lc_exp a d b
  | ECApp b -> open_lc_exp a d b
  | ELet t e1 e2 -> open_lc_ty a d t; open_lc_exp a d e1; open_lc_exp a d e2
  | ELetRec bs b -> open_lc_binds a d bs; open_lc_exp a d b
  | ECase es dt -> open_lc_exps a d es; open_lc_dt a d dt
  | ELetJoin ts t e1 e2 ->
    open_lc_tys a d ts; open_lc_ty a d t; open_lc_exp a d e1; open_lc_exp a d e2
  | EJump _ es -> open_lc_exps a d es
  | EExtend _ e1 e2 -> open_lc_exp a d e1; open_lc_exp a d e2
  | ESelect _ b -> open_lc_exp a d b
  | ERestrict _ b -> open_lc_exp a d b
  | EUpdate _ e1 e2 -> open_lc_exp a d e1; open_lc_exp a d e2
  | EMerge e1 e2 -> open_lc_exp a d e1; open_lc_exp a d e2
  | EInject _ t b -> open_lc_ty a d t; open_lc_exp a d b
  | EWeaken _ t b -> open_lc_ty a d t; open_lc_exp a d b
  | EAbsurd t b -> open_lc_ty a d t; open_lc_exp a d b
  | EPerform _ _ ts b -> open_lc_tys a d ts; open_lc_exp a d b
  | EHandle b h ->
    open_lc_exp a d b; open_lc_ent a d h.h_ent; open_lc_ty a d h.h_ret_ty; open_lc_exp a d h.h_ret;
    open_lc_cls a d h.h_clauses
  | EOpenEff t b -> open_lc_ty a d t; open_lc_exp a d b
  | ERegion l es b -> open_lc_layout a d l; open_lc_exps a d es; open_lc_exp a (d + 1) b
  | EWriteCell _ _ b -> open_lc_exp a d b
  | EMatch th dt -> open_lc_exps a d th; open_lc_dt a d dt
  | EOpenEffC t b -> open_lc_ty a d t; open_lc_exp a d b
  | EFill _ b -> open_lc_exp a d b
  | ERegionOpen _ th b -> open_lc_cells a d th; open_lc_exp a d b
  | EOpaque _ t -> open_lc_ty a d t

and open_lc_exps (a: atom) (d: nat) (es: list exp)
  : Lemma (requires lc_exps_at d es)
          (ensures rmap_exps (open_rr a) d es == es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> open_lc_exp a d e; open_lc_exps a d es

and open_lc_binds (a: atom) (d: nat) (bs: list (typ & exp))
  : Lemma (requires lc_binds_at d bs)
          (ensures rmap_binds (open_rr a) d bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> open_lc_ty a d t; open_lc_exp a d e; open_lc_binds a d bs

and open_lc_cells (a: atom) (d: nat) (th: list (key & exp))
  : Lemma (requires lc_cells_at d th)
          (ensures rmap_cells (open_rr a) d th == th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> open_lc_exp a d e; open_lc_cells a d th

and open_lc_dt (a: atom) (d: nat) (dt: dtree)
  : Lemma (requires lc_dt_at d dt)
          (ensures rmap_dt (open_rr a) d dt == dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> open_lc_exp a d e
  | DBind o dt -> open_lc_occ a d o; open_lc_dt a d dt
  | DSwitchCtor o bs df -> open_lc_occ a d o; open_lc_brs a d bs; open_lc_odt a d df
  | DSwitchLit o bs df -> open_lc_occ a d o; open_lc_brs a d bs; open_lc_dt a d df
  | DSwitchKey o bs df -> open_lc_occ a d o; open_lc_kbrs a d bs; open_lc_odt a d df
  | DGuard e dt1 dt2 -> open_lc_exp a d e; open_lc_dt a d dt1; open_lc_dt a d dt2

and open_lc_odt (a: atom) (d: nat) (df: option dtree)
  : Lemma (requires lc_odt_at d df)
          (ensures rmap_odt (open_rr a) d df == df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> open_lc_dt a d dt

and open_lc_brs (#lb: eqtype) (a: atom) (d: nat) (bs: list (lb & dtree))
  : Lemma (requires lc_brs_at d bs)
          (ensures rmap_brs (open_rr a) d bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> open_lc_dt a d dt; open_lc_brs a d bs

and open_lc_kbrs (a: atom) (d: nat) (bs: list (key & dtree))
  : Lemma (requires lc_kbrs_at d bs)
          (ensures rmap_kbrs (open_rr a) d bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> open_lc_dt a d dt; open_lc_kbrs a d bs

and open_lc_cls (a: atom) (d: nat) (cs: list clause)
  : Lemma (requires lc_cls_at d cs)
          (ensures rmap_cls (open_rr a) d cs == cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt b :: cs ->
    open_lc_ty a d s; open_lc_ty a d kt; open_lc_exp a d b; open_lc_cls a d cs
  | CFast _ _ s b :: cs -> open_lc_ty a d s; open_lc_exp a d b; open_lc_cls a d cs

let rec open_close_exp (a: atom) (d: nat) (e: exp)
  : Lemma (requires lc_exp_at d e)
          (ensures rmap_exp (open_rr a) d (rmap_exp (close_rr a) d e) == e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> open_close_ty a d t; open_close_ty a d r; open_close_exp a d b
  | EApp e1 e2 -> open_close_exp a d e1; open_close_exp a d e2
  | ETyLam _ b -> open_close_exp a d b
  | ETyApp b t -> open_close_exp a d b; open_close_ty a d t
  | ECLam cn b -> open_close_constr a d cn; open_close_exp a d b
  | ECApp b -> open_close_exp a d b
  | ELet t e1 e2 -> open_close_ty a d t; open_close_exp a d e1; open_close_exp a d e2
  | ELetRec bs b -> open_close_binds a d bs; open_close_exp a d b
  | ECase es dt -> open_close_exps a d es; open_close_dt a d dt
  | ELetJoin ts t e1 e2 ->
    open_close_tys a d ts; open_close_ty a d t; open_close_exp a d e1; open_close_exp a d e2
  | EJump _ es -> open_close_exps a d es
  | EExtend _ e1 e2 -> open_close_exp a d e1; open_close_exp a d e2
  | ESelect _ b -> open_close_exp a d b
  | ERestrict _ b -> open_close_exp a d b
  | EUpdate _ e1 e2 -> open_close_exp a d e1; open_close_exp a d e2
  | EMerge e1 e2 -> open_close_exp a d e1; open_close_exp a d e2
  | EInject _ t b -> open_close_ty a d t; open_close_exp a d b
  | EWeaken _ t b -> open_close_ty a d t; open_close_exp a d b
  | EAbsurd t b -> open_close_ty a d t; open_close_exp a d b
  | EPerform _ _ ts b -> open_close_tys a d ts; open_close_exp a d b
  | EHandle b h ->
    open_close_exp a d b; open_close_ent a d h.h_ent; open_close_ty a d h.h_ret_ty;
    open_close_exp a d h.h_ret; open_close_cls a d h.h_clauses
  | EOpenEff t b -> open_close_ty a d t; open_close_exp a d b
  | ERegion l es b -> open_close_layout a d l; open_close_exps a d es; open_close_exp a (d + 1) b
  | EWriteCell _ _ b -> open_close_exp a d b
  | EMatch th dt -> open_close_exps a d th; open_close_dt a d dt
  | EOpenEffC t b -> open_close_ty a d t; open_close_exp a d b
  | EFill _ b -> open_close_exp a d b
  | ERegionOpen _ th b -> open_close_cells a d th; open_close_exp a d b
  | EOpaque _ t -> open_close_ty a d t

and open_close_exps (a: atom) (d: nat) (es: list exp)
  : Lemma (requires lc_exps_at d es)
          (ensures rmap_exps (open_rr a) d (rmap_exps (close_rr a) d es) == es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> open_close_exp a d e; open_close_exps a d es

and open_close_binds (a: atom) (d: nat) (bs: list (typ & exp))
  : Lemma (requires lc_binds_at d bs)
          (ensures rmap_binds (open_rr a) d (rmap_binds (close_rr a) d bs) == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> open_close_ty a d t; open_close_exp a d e; open_close_binds a d bs

and open_close_cells (a: atom) (d: nat) (th: list (key & exp))
  : Lemma (requires lc_cells_at d th)
          (ensures rmap_cells (open_rr a) d (rmap_cells (close_rr a) d th) == th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> open_close_exp a d e; open_close_cells a d th

and open_close_dt (a: atom) (d: nat) (dt: dtree)
  : Lemma (requires lc_dt_at d dt)
          (ensures rmap_dt (open_rr a) d (rmap_dt (close_rr a) d dt) == dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> open_close_exp a d e
  | DBind o dt -> open_close_occ a d o; open_close_dt a d dt
  | DSwitchCtor o bs df -> open_close_occ a d o; open_close_brs a d bs; open_close_odt a d df
  | DSwitchLit o bs df -> open_close_occ a d o; open_close_brs a d bs; open_close_dt a d df
  | DSwitchKey o bs df -> open_close_occ a d o; open_close_kbrs a d bs; open_close_odt a d df
  | DGuard e dt1 dt2 -> open_close_exp a d e; open_close_dt a d dt1; open_close_dt a d dt2

and open_close_odt (a: atom) (d: nat) (df: option dtree)
  : Lemma (requires lc_odt_at d df)
          (ensures rmap_odt (open_rr a) d (rmap_odt (close_rr a) d df) == df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> open_close_dt a d dt

and open_close_brs (#lb: eqtype) (a: atom) (d: nat) (bs: list (lb & dtree))
  : Lemma (requires lc_brs_at d bs)
          (ensures rmap_brs (open_rr a) d (rmap_brs (close_rr a) d bs) == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> open_close_dt a d dt; open_close_brs a d bs

and open_close_kbrs (a: atom) (d: nat) (bs: list (key & dtree))
  : Lemma (requires lc_kbrs_at d bs)
          (ensures rmap_kbrs (open_rr a) d (rmap_kbrs (close_rr a) d bs) == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> open_close_dt a d dt; open_close_kbrs a d bs

and open_close_cls (a: atom) (d: nat) (cs: list clause)
  : Lemma (requires lc_cls_at d cs)
          (ensures rmap_cls (open_rr a) d (rmap_cls (close_rr a) d cs) == cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt b :: cs ->
    open_close_ty a d s; open_close_ty a d kt; open_close_exp a d b; open_close_cls a d cs
  | CFast _ _ s b :: cs -> open_close_ty a d s; open_close_exp a d b; open_close_cls a d cs

let rec close_open_exp (a: atom) (d: nat) (e: exp)
  : Lemma (requires not (L.mem a (frn_exp e)))
          (ensures rmap_exp (close_rr a) d (rmap_exp (open_rr a) d e) == e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EForce _ -> ()
  | ELam t r b -> close_open_ty a d t; close_open_ty a d r; close_open_exp a d b
  | EApp e1 e2 -> close_open_exp a d e1; close_open_exp a d e2
  | ETyLam _ b -> close_open_exp a d b
  | ETyApp b t -> close_open_exp a d b; close_open_ty a d t
  | ECLam cn b -> close_open_constr a d cn; close_open_exp a d b
  | ECApp b -> close_open_exp a d b
  | ELet t e1 e2 -> close_open_ty a d t; close_open_exp a d e1; close_open_exp a d e2
  | ELetRec bs b -> close_open_binds a d bs; close_open_exp a d b
  | ECase es dt -> close_open_exps a d es; close_open_dt a d dt
  | ELetJoin ts t e1 e2 ->
    close_open_tys a d ts; close_open_ty a d t; close_open_exp a d e1; close_open_exp a d e2
  | EJump _ es -> close_open_exps a d es
  | EExtend k e1 e2 -> close_open_key a d k; close_open_exp a d e1; close_open_exp a d e2
  | ESelect k b -> close_open_key a d k; close_open_exp a d b
  | ERestrict k b -> close_open_key a d k; close_open_exp a d b
  | EUpdate k e1 e2 -> close_open_key a d k; close_open_exp a d e1; close_open_exp a d e2
  | EMerge e1 e2 -> close_open_exp a d e1; close_open_exp a d e2
  | EInject k t b -> close_open_key a d k; close_open_ty a d t; close_open_exp a d b
  | EWeaken k t b -> close_open_key a d k; close_open_ty a d t; close_open_exp a d b
  | EAbsurd t b -> close_open_ty a d t; close_open_exp a d b
  | EPerform k _ ts b -> close_open_key a d k; close_open_tys a d ts; close_open_exp a d b
  | EHandle b h ->
    close_open_exp a d b; close_open_ent a d h.h_ent; close_open_ty a d h.h_ret_ty;
    close_open_exp a d h.h_ret; close_open_cls a d h.h_clauses
  | EOpenEff t b -> close_open_ty a d t; close_open_exp a d b
  | ERegion l es b -> close_open_layout a d l; close_open_exps a d es; close_open_exp a (d + 1) b
  | EReadCell r k -> close_open_rr a d r; close_open_key a d k
  | EWriteCell r k b -> close_open_rr a d r; close_open_key a d k; close_open_exp a d b
  | EMatch th dt -> close_open_exps a d th; close_open_dt a d dt
  | EOpenEffC t b -> close_open_ty a d t; close_open_exp a d b
  | EFill _ b -> close_open_exp a d b
  | ERegionOpen _ th b -> close_open_cells a d th; close_open_exp a d b
  | EOpaque _ t -> close_open_ty a d t

and close_open_exps (a: atom) (d: nat) (es: list exp)
  : Lemma (requires not (L.mem a (frn_exps es)))
          (ensures rmap_exps (close_rr a) d (rmap_exps (open_rr a) d es) == es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> close_open_exp a d e; close_open_exps a d es

and close_open_binds (a: atom) (d: nat) (bs: list (typ & exp))
  : Lemma (requires not (L.mem a (frn_binds bs)))
          (ensures rmap_binds (close_rr a) d (rmap_binds (open_rr a) d bs) == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> close_open_ty a d t; close_open_exp a d e; close_open_binds a d bs

and close_open_cells (a: atom) (d: nat) (th: list (key & exp))
  : Lemma (requires not (L.mem a (frn_cells th)))
          (ensures rmap_cells (close_rr a) d (rmap_cells (open_rr a) d th) == th)
          (decreases th) =
  match th with
  | [] -> ()
  | (k, e) :: th -> close_open_key a d k; close_open_exp a d e; close_open_cells a d th

and close_open_dt (a: atom) (d: nat) (dt: dtree)
  : Lemma (requires not (L.mem a (frn_dt dt)))
          (ensures rmap_dt (close_rr a) d (rmap_dt (open_rr a) d dt) == dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> close_open_exp a d e
  | DBind o dt -> close_open_occ a d o; close_open_dt a d dt
  | DSwitchCtor o bs df -> close_open_occ a d o; close_open_brs a d bs; close_open_odt a d df
  | DSwitchLit o bs df -> close_open_occ a d o; close_open_brs a d bs; close_open_dt a d df
  | DSwitchKey o bs df -> close_open_occ a d o; close_open_kbrs a d bs; close_open_odt a d df
  | DGuard e dt1 dt2 -> close_open_exp a d e; close_open_dt a d dt1; close_open_dt a d dt2

and close_open_odt (a: atom) (d: nat) (df: option dtree)
  : Lemma (requires not (L.mem a (frn_odt df)))
          (ensures rmap_odt (close_rr a) d (rmap_odt (open_rr a) d df) == df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> close_open_dt a d dt

and close_open_brs (#lb: eqtype) (a: atom) (d: nat) (bs: list (lb & dtree))
  : Lemma (requires not (L.mem a (frn_brs bs)))
          (ensures rmap_brs (close_rr a) d (rmap_brs (open_rr a) d bs) == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> close_open_dt a d dt; close_open_brs a d bs

and close_open_kbrs (a: atom) (d: nat) (bs: list (key & dtree))
  : Lemma (requires not (L.mem a (frn_kbrs bs)))
          (ensures rmap_kbrs (close_rr a) d (rmap_kbrs (open_rr a) d bs) == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (k, dt) :: bs -> close_open_key a d k; close_open_dt a d dt; close_open_kbrs a d bs

and close_open_cls (a: atom) (d: nat) (cs: list clause)
  : Lemma (requires not (L.mem a (frn_cls cs)))
          (ensures rmap_cls (close_rr a) d (rmap_cls (open_rr a) d cs) == cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt b :: cs ->
    close_open_ty a d s; close_open_ty a d kt; close_open_exp a d b; close_open_cls a d cs
  | CFast _ _ s b :: cs -> close_open_ty a d s; close_open_exp a d b; close_open_cls a d cs

let lc_open_region (a: atom) (e: exp)
  : Lemma (requires lc_exp_at 1 e) (ensures lc_exp (open_region a e)) =
  lc_open_exp a 0 e

let close_open_region (a: atom) (e: exp)
  : Lemma (requires not (L.mem a (frn_exp e))) (ensures close_region a (open_region a e) == e) =
  close_open_exp a 0 e

let open_close_region (a: atom) (e: exp)
  : Lemma (requires lc_exp e) (ensures open_region a (close_region a e) == e) =
  open_close_exp a 0 e

let rec rmap_ren_tm (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (e: exp)
  : Lemma (ensures rmap_exp f d (ren_tm xi e) == ren_tm xi (rmap_exp f d e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> rmap_ren_tm f d (up_ren xi) b
  | EApp e1 e2 -> rmap_ren_tm f d xi e1; rmap_ren_tm f d xi e2
  | ETyLam _ b -> rmap_ren_tm f d xi b
  | ETyApp b _ -> rmap_ren_tm f d xi b
  | ECLam _ b -> rmap_ren_tm f d xi b
  | ECApp b -> rmap_ren_tm f d xi b
  | ELet _ e1 e2 -> rmap_ren_tm f d xi e1; rmap_ren_tm f d (up_ren xi) e2
  | ELetRec bs b ->
    rmap_ren_tm_binds f d (upn_ren (L.length bs) xi) bs;
    rmap_ren_tm f d (upn_ren (L.length bs) xi) b
  | ECase es dt -> rmap_ren_tm_exps f d xi es; rmap_ren_tm_dt f d xi dt
  | ELetJoin ts _ e1 e2 -> rmap_ren_tm f d (upn_ren (L.length ts) xi) e1; rmap_ren_tm f d xi e2
  | EJump _ es -> rmap_ren_tm_exps f d xi es
  | EExtend _ e1 e2 -> rmap_ren_tm f d xi e1; rmap_ren_tm f d xi e2
  | ESelect _ b -> rmap_ren_tm f d xi b
  | ERestrict _ b -> rmap_ren_tm f d xi b
  | EUpdate _ e1 e2 -> rmap_ren_tm f d xi e1; rmap_ren_tm f d xi e2
  | EMerge e1 e2 -> rmap_ren_tm f d xi e1; rmap_ren_tm f d xi e2
  | EInject _ _ b -> rmap_ren_tm f d xi b
  | EWeaken _ _ b -> rmap_ren_tm f d xi b
  | EAbsurd _ b -> rmap_ren_tm f d xi b
  | EPerform _ _ _ b -> rmap_ren_tm f d xi b
  | EHandle b h ->
    rmap_ren_tm f d xi b; rmap_ren_tm f d (up_ren xi) h.h_ret; rmap_ren_tm_cls f d xi h.h_clauses
  | EOpenEff _ b -> rmap_ren_tm f d xi b
  | ERegion _ es b -> rmap_ren_tm_exps f d xi es; rmap_ren_tm f (d + 1) xi b
  | EWriteCell _ _ b -> rmap_ren_tm f d xi b
  | EMatch th dt -> rmap_ren_tm_exps f d xi th; rmap_ren_tm_dt f d xi dt
  | EOpenEffC _ b -> rmap_ren_tm f d xi b
  | EFill _ b -> rmap_ren_tm f d xi b
  | ERegionOpen _ th b -> rmap_ren_tm_cells f d xi th; rmap_ren_tm f d xi b

and rmap_ren_tm_exps (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (es: list exp)
  : Lemma (ensures rmap_exps f d (ren_tm_exps xi es) == ren_tm_exps xi (rmap_exps f d es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> rmap_ren_tm f d xi e; rmap_ren_tm_exps f d xi es

and rmap_ren_tm_binds (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures rmap_binds f d (ren_tm_binds xi bs) == ren_tm_binds xi (rmap_binds f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> rmap_ren_tm f d xi e; rmap_ren_tm_binds f d xi bs

and rmap_ren_tm_cells (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (th: list (key & exp))
  : Lemma (ensures rmap_cells f d (ren_tm_cells xi th) == ren_tm_cells xi (rmap_cells f d th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> rmap_ren_tm f d xi e; rmap_ren_tm_cells f d xi th

and rmap_ren_tm_dt (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures rmap_dt f d (ren_tm_dt xi dt) == ren_tm_dt xi (rmap_dt f d dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> rmap_ren_tm f d xi e
  | DBind _ dt -> rmap_ren_tm_dt f d (up_ren xi) dt
  | DSwitchCtor _ bs df -> rmap_ren_tm_brs f d xi bs; rmap_ren_tm_odt f d xi df
  | DSwitchLit _ bs df -> rmap_ren_tm_brs f d xi bs; rmap_ren_tm_dt f d xi df
  | DSwitchKey _ bs df -> rmap_ren_tm_kbrs f d xi bs; rmap_ren_tm_odt f d xi df
  | DGuard e dt1 dt2 -> rmap_ren_tm f d xi e; rmap_ren_tm_dt f d xi dt1; rmap_ren_tm_dt f d xi dt2

and rmap_ren_tm_odt (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (df: option dtree)
  : Lemma (ensures rmap_odt f d (ren_tm_odt xi df) == ren_tm_odt xi (rmap_odt f d df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> rmap_ren_tm_dt f d xi dt

and rmap_ren_tm_brs (#lb: eqtype) (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren)
    (bs: list (lb & dtree))
  : Lemma (ensures rmap_brs f d (ren_tm_brs xi bs) == ren_tm_brs xi (rmap_brs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_ren_tm_dt f d xi dt; rmap_ren_tm_brs f d xi bs

and rmap_ren_tm_kbrs (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren)
    (bs: list (key & dtree))
  : Lemma (ensures rmap_kbrs f d (ren_tm_brs xi bs) == ren_tm_brs xi (rmap_kbrs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_ren_tm_dt f d xi dt; rmap_ren_tm_kbrs f d xi bs

and rmap_ren_tm_cls (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (cs: list clause)
  : Lemma (ensures rmap_cls f d (ren_tm_cls xi cs) == ren_tm_cls xi (rmap_cls f d cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> rmap_ren_tm f d (upn_ren 2 xi) b; rmap_ren_tm_cls f d xi cs
  | CFast _ _ _ b :: cs -> rmap_ren_tm f d (up_ren xi) b; rmap_ren_tm_cls f d xi cs

let rec rmap_ren_jp (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (e: exp)
  : Lemma (ensures rmap_exp f d (ren_jp xi e) == ren_jp xi (rmap_exp f d e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> rmap_ren_jp f d xi b
  | EApp e1 e2 -> rmap_ren_jp f d xi e1; rmap_ren_jp f d xi e2
  | ETyLam _ b -> rmap_ren_jp f d xi b
  | ETyApp b _ -> rmap_ren_jp f d xi b
  | ECLam _ b -> rmap_ren_jp f d xi b
  | ECApp b -> rmap_ren_jp f d xi b
  | ELet _ e1 e2 -> rmap_ren_jp f d xi e1; rmap_ren_jp f d xi e2
  | ELetRec bs b -> rmap_ren_jp_binds f d xi bs; rmap_ren_jp f d xi b
  | ECase es dt -> rmap_ren_jp_exps f d xi es; rmap_ren_jp_dt f d xi dt
  | ELetJoin _ _ e1 e2 -> rmap_ren_jp f d (up_ren xi) e1; rmap_ren_jp f d (up_ren xi) e2
  | EJump _ es -> rmap_ren_jp_exps f d xi es
  | EExtend _ e1 e2 -> rmap_ren_jp f d xi e1; rmap_ren_jp f d xi e2
  | ESelect _ b -> rmap_ren_jp f d xi b
  | ERestrict _ b -> rmap_ren_jp f d xi b
  | EUpdate _ e1 e2 -> rmap_ren_jp f d xi e1; rmap_ren_jp f d xi e2
  | EMerge e1 e2 -> rmap_ren_jp f d xi e1; rmap_ren_jp f d xi e2
  | EInject _ _ b -> rmap_ren_jp f d xi b
  | EWeaken _ _ b -> rmap_ren_jp f d xi b
  | EAbsurd _ b -> rmap_ren_jp f d xi b
  | EPerform _ _ _ b -> rmap_ren_jp f d xi b
  | EHandle b h ->
    rmap_ren_jp f d xi b; rmap_ren_jp f d xi h.h_ret; rmap_ren_jp_cls f d xi h.h_clauses
  | EOpenEff _ b -> rmap_ren_jp f d xi b
  | ERegion _ es b -> rmap_ren_jp_exps f d xi es; rmap_ren_jp f (d + 1) xi b
  | EWriteCell _ _ b -> rmap_ren_jp f d xi b
  | EMatch th dt -> rmap_ren_jp_exps f d xi th; rmap_ren_jp_dt f d xi dt
  | EOpenEffC _ b -> rmap_ren_jp f d xi b
  | EFill _ b -> rmap_ren_jp f d xi b
  | ERegionOpen _ th b -> rmap_ren_jp_cells f d xi th; rmap_ren_jp f d xi b

and rmap_ren_jp_exps (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (es: list exp)
  : Lemma (ensures rmap_exps f d (ren_jp_exps xi es) == ren_jp_exps xi (rmap_exps f d es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> rmap_ren_jp f d xi e; rmap_ren_jp_exps f d xi es

and rmap_ren_jp_binds (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures rmap_binds f d (ren_jp_binds xi bs) == ren_jp_binds xi (rmap_binds f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> rmap_ren_jp f d xi e; rmap_ren_jp_binds f d xi bs

and rmap_ren_jp_cells (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (th: list (key & exp))
  : Lemma (ensures rmap_cells f d (ren_jp_cells xi th) == ren_jp_cells xi (rmap_cells f d th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> rmap_ren_jp f d xi e; rmap_ren_jp_cells f d xi th

and rmap_ren_jp_dt (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures rmap_dt f d (ren_jp_dt xi dt) == ren_jp_dt xi (rmap_dt f d dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> rmap_ren_jp f d xi e
  | DBind _ dt -> rmap_ren_jp_dt f d xi dt
  | DSwitchCtor _ bs df -> rmap_ren_jp_brs f d xi bs; rmap_ren_jp_odt f d xi df
  | DSwitchLit _ bs df -> rmap_ren_jp_brs f d xi bs; rmap_ren_jp_dt f d xi df
  | DSwitchKey _ bs df -> rmap_ren_jp_kbrs f d xi bs; rmap_ren_jp_odt f d xi df
  | DGuard e dt1 dt2 -> rmap_ren_jp f d xi e; rmap_ren_jp_dt f d xi dt1; rmap_ren_jp_dt f d xi dt2

and rmap_ren_jp_odt (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (df: option dtree)
  : Lemma (ensures rmap_odt f d (ren_jp_odt xi df) == ren_jp_odt xi (rmap_odt f d df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> rmap_ren_jp_dt f d xi dt

and rmap_ren_jp_brs (#lb: eqtype) (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren)
    (bs: list (lb & dtree))
  : Lemma (ensures rmap_brs f d (ren_jp_brs xi bs) == ren_jp_brs xi (rmap_brs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_ren_jp_dt f d xi dt; rmap_ren_jp_brs f d xi bs

and rmap_ren_jp_kbrs (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren)
    (bs: list (key & dtree))
  : Lemma (ensures rmap_kbrs f d (ren_jp_brs xi bs) == ren_jp_brs xi (rmap_kbrs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_ren_jp_dt f d xi dt; rmap_ren_jp_kbrs f d xi bs

and rmap_ren_jp_cls (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (cs: list clause)
  : Lemma (ensures rmap_cls f d (ren_jp_cls xi cs) == ren_jp_cls xi (rmap_cls f d cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> rmap_ren_jp f d xi b; rmap_ren_jp_cls f d xi cs
  | CFast _ _ _ b :: cs -> rmap_ren_jp f d xi b; rmap_ren_jp_cls f d xi cs

let rec lc_ren_tm (n: nat) (xi: ren) (e: exp)
  : Lemma (ensures lc_exp_at n (ren_tm xi e) == lc_exp_at n e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> lc_ren_tm n (up_ren xi) b
  | EApp e1 e2 -> lc_ren_tm n xi e1; lc_ren_tm n xi e2
  | ETyLam _ b -> lc_ren_tm n xi b
  | ETyApp b _ -> lc_ren_tm n xi b
  | ECLam _ b -> lc_ren_tm n xi b
  | ECApp b -> lc_ren_tm n xi b
  | ELet _ e1 e2 -> lc_ren_tm n xi e1; lc_ren_tm n (up_ren xi) e2
  | ELetRec bs b ->
    lc_ren_tm_binds n (upn_ren (L.length bs) xi) bs; lc_ren_tm n (upn_ren (L.length bs) xi) b
  | ECase es dt -> lc_ren_tm_exps n xi es; lc_ren_tm_dt n xi dt
  | ELetJoin ts _ e1 e2 -> lc_ren_tm n (upn_ren (L.length ts) xi) e1; lc_ren_tm n xi e2
  | EJump _ es -> lc_ren_tm_exps n xi es
  | EExtend _ e1 e2 -> lc_ren_tm n xi e1; lc_ren_tm n xi e2
  | ESelect _ b -> lc_ren_tm n xi b
  | ERestrict _ b -> lc_ren_tm n xi b
  | EUpdate _ e1 e2 -> lc_ren_tm n xi e1; lc_ren_tm n xi e2
  | EMerge e1 e2 -> lc_ren_tm n xi e1; lc_ren_tm n xi e2
  | EInject _ _ b -> lc_ren_tm n xi b
  | EWeaken _ _ b -> lc_ren_tm n xi b
  | EAbsurd _ b -> lc_ren_tm n xi b
  | EPerform _ _ _ b -> lc_ren_tm n xi b
  | EHandle b h -> lc_ren_tm n xi b; lc_ren_tm n (up_ren xi) h.h_ret; lc_ren_tm_cls n xi h.h_clauses
  | EOpenEff _ b -> lc_ren_tm n xi b
  | ERegion _ es b -> lc_ren_tm_exps n xi es; lc_ren_tm (n + 1) xi b
  | EWriteCell _ _ b -> lc_ren_tm n xi b
  | EMatch th dt -> lc_ren_tm_exps n xi th; lc_ren_tm_dt n xi dt
  | EOpenEffC _ b -> lc_ren_tm n xi b
  | EFill _ b -> lc_ren_tm n xi b
  | ERegionOpen _ th b -> lc_ren_tm_cells n xi th; lc_ren_tm n xi b

and lc_ren_tm_exps (n: nat) (xi: ren) (es: list exp)
  : Lemma (ensures lc_exps_at n (ren_tm_exps xi es) == lc_exps_at n es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> lc_ren_tm n xi e; lc_ren_tm_exps n xi es

and lc_ren_tm_binds (n: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures lc_binds_at n (ren_tm_binds xi bs) == lc_binds_at n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> lc_ren_tm n xi e; lc_ren_tm_binds n xi bs

and lc_ren_tm_cells (n: nat) (xi: ren) (th: list (key & exp))
  : Lemma (ensures lc_cells_at n (ren_tm_cells xi th) == lc_cells_at n th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> lc_ren_tm n xi e; lc_ren_tm_cells n xi th

and lc_ren_tm_dt (n: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures lc_dt_at n (ren_tm_dt xi dt) == lc_dt_at n dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> lc_ren_tm n xi e
  | DBind _ dt -> lc_ren_tm_dt n (up_ren xi) dt
  | DSwitchCtor _ bs df -> lc_ren_tm_brs n xi bs; lc_ren_tm_odt n xi df
  | DSwitchLit _ bs df -> lc_ren_tm_brs n xi bs; lc_ren_tm_dt n xi df
  | DSwitchKey _ bs df -> lc_ren_tm_kbrs n xi bs; lc_ren_tm_odt n xi df
  | DGuard e dt1 dt2 -> lc_ren_tm n xi e; lc_ren_tm_dt n xi dt1; lc_ren_tm_dt n xi dt2

and lc_ren_tm_odt (n: nat) (xi: ren) (df: option dtree)
  : Lemma (ensures lc_odt_at n (ren_tm_odt xi df) == lc_odt_at n df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> lc_ren_tm_dt n xi dt

and lc_ren_tm_brs (#lb: eqtype) (n: nat) (xi: ren) (bs: list (lb & dtree))
  : Lemma (ensures lc_brs_at n (ren_tm_brs xi bs) == lc_brs_at n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_ren_tm_dt n xi dt; lc_ren_tm_brs n xi bs

and lc_ren_tm_kbrs (n: nat) (xi: ren) (bs: list (key & dtree))
  : Lemma (ensures lc_kbrs_at n (ren_tm_brs xi bs) == lc_kbrs_at n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_ren_tm_dt n xi dt; lc_ren_tm_kbrs n xi bs

and lc_ren_tm_cls (n: nat) (xi: ren) (cs: list clause)
  : Lemma (ensures lc_cls_at n (ren_tm_cls xi cs) == lc_cls_at n cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> lc_ren_tm n (upn_ren 2 xi) b; lc_ren_tm_cls n xi cs
  | CFast _ _ _ b :: cs -> lc_ren_tm n (up_ren xi) b; lc_ren_tm_cls n xi cs

let rec lc_ren_jp (n: nat) (xi: ren) (e: exp)
  : Lemma (ensures lc_exp_at n (ren_jp xi e) == lc_exp_at n e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> lc_ren_jp n xi b
  | EApp e1 e2 -> lc_ren_jp n xi e1; lc_ren_jp n xi e2
  | ETyLam _ b -> lc_ren_jp n xi b
  | ETyApp b _ -> lc_ren_jp n xi b
  | ECLam _ b -> lc_ren_jp n xi b
  | ECApp b -> lc_ren_jp n xi b
  | ELet _ e1 e2 -> lc_ren_jp n xi e1; lc_ren_jp n xi e2
  | ELetRec bs b -> lc_ren_jp_binds n xi bs; lc_ren_jp n xi b
  | ECase es dt -> lc_ren_jp_exps n xi es; lc_ren_jp_dt n xi dt
  | ELetJoin _ _ e1 e2 -> lc_ren_jp n (up_ren xi) e1; lc_ren_jp n (up_ren xi) e2
  | EJump _ es -> lc_ren_jp_exps n xi es
  | EExtend _ e1 e2 -> lc_ren_jp n xi e1; lc_ren_jp n xi e2
  | ESelect _ b -> lc_ren_jp n xi b
  | ERestrict _ b -> lc_ren_jp n xi b
  | EUpdate _ e1 e2 -> lc_ren_jp n xi e1; lc_ren_jp n xi e2
  | EMerge e1 e2 -> lc_ren_jp n xi e1; lc_ren_jp n xi e2
  | EInject _ _ b -> lc_ren_jp n xi b
  | EWeaken _ _ b -> lc_ren_jp n xi b
  | EAbsurd _ b -> lc_ren_jp n xi b
  | EPerform _ _ _ b -> lc_ren_jp n xi b
  | EHandle b h -> lc_ren_jp n xi b; lc_ren_jp n xi h.h_ret; lc_ren_jp_cls n xi h.h_clauses
  | EOpenEff _ b -> lc_ren_jp n xi b
  | ERegion _ es b -> lc_ren_jp_exps n xi es; lc_ren_jp (n + 1) xi b
  | EWriteCell _ _ b -> lc_ren_jp n xi b
  | EMatch th dt -> lc_ren_jp_exps n xi th; lc_ren_jp_dt n xi dt
  | EOpenEffC _ b -> lc_ren_jp n xi b
  | EFill _ b -> lc_ren_jp n xi b
  | ERegionOpen _ th b -> lc_ren_jp_cells n xi th; lc_ren_jp n xi b

and lc_ren_jp_exps (n: nat) (xi: ren) (es: list exp)
  : Lemma (ensures lc_exps_at n (ren_jp_exps xi es) == lc_exps_at n es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> lc_ren_jp n xi e; lc_ren_jp_exps n xi es

and lc_ren_jp_binds (n: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures lc_binds_at n (ren_jp_binds xi bs) == lc_binds_at n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> lc_ren_jp n xi e; lc_ren_jp_binds n xi bs

and lc_ren_jp_cells (n: nat) (xi: ren) (th: list (key & exp))
  : Lemma (ensures lc_cells_at n (ren_jp_cells xi th) == lc_cells_at n th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> lc_ren_jp n xi e; lc_ren_jp_cells n xi th

and lc_ren_jp_dt (n: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures lc_dt_at n (ren_jp_dt xi dt) == lc_dt_at n dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> lc_ren_jp n xi e
  | DBind _ dt -> lc_ren_jp_dt n xi dt
  | DSwitchCtor _ bs df -> lc_ren_jp_brs n xi bs; lc_ren_jp_odt n xi df
  | DSwitchLit _ bs df -> lc_ren_jp_brs n xi bs; lc_ren_jp_dt n xi df
  | DSwitchKey _ bs df -> lc_ren_jp_kbrs n xi bs; lc_ren_jp_odt n xi df
  | DGuard e dt1 dt2 -> lc_ren_jp n xi e; lc_ren_jp_dt n xi dt1; lc_ren_jp_dt n xi dt2

and lc_ren_jp_odt (n: nat) (xi: ren) (df: option dtree)
  : Lemma (ensures lc_odt_at n (ren_jp_odt xi df) == lc_odt_at n df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> lc_ren_jp_dt n xi dt

and lc_ren_jp_brs (#lb: eqtype) (n: nat) (xi: ren) (bs: list (lb & dtree))
  : Lemma (ensures lc_brs_at n (ren_jp_brs xi bs) == lc_brs_at n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_ren_jp_dt n xi dt; lc_ren_jp_brs n xi bs

and lc_ren_jp_kbrs (n: nat) (xi: ren) (bs: list (key & dtree))
  : Lemma (ensures lc_kbrs_at n (ren_jp_brs xi bs) == lc_kbrs_at n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_ren_jp_dt n xi dt; lc_ren_jp_kbrs n xi bs

and lc_ren_jp_cls (n: nat) (xi: ren) (cs: list clause)
  : Lemma (ensures lc_cls_at n (ren_jp_cls xi cs) == lc_cls_at n cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> lc_ren_jp n xi b; lc_ren_jp_cls n xi cs
  | CFast _ _ _ b :: cs -> lc_ren_jp n xi b; lc_ren_jp_cls n xi cs

let rmap_fix_upn_tsub (f: nat -> region_ref -> region_ref) (d m: nat) (sigma: tsub)
  : Lemma (requires forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i)
          (ensures forall (d': nat) (i: nat).
             d <= d' ==> rmap_ty (f d') (upn_tsub m sigma i) == upn_tsub m sigma i) =
  introduce forall (d': nat) (i: nat).
    d <= d' ==> rmap_ty (f d') (upn_tsub m sigma i) == upn_tsub m sigma i
  with introduce _ ==> _
  with if i < m then () else rmap_ren_ty (f d') (shift m) (sigma (i - m))

let rec rmap_sub_ty_exp (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub) (e: exp)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_exp f d (sub_ty_exp sigma e) == sub_ty_exp sigma (rmap_exp f d e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b ->
    rmap_sub_ty (f d) sigma sigma t; rmap_sub_ty (f d) sigma sigma r; rmap_sub_ty_exp f d sigma b
  | EApp e1 e2 -> rmap_sub_ty_exp f d sigma e1; rmap_sub_ty_exp f d sigma e2
  | ETyLam _ b -> rmap_fix_upn_tsub f d 1 sigma; rmap_sub_ty_exp f d (up_tsub sigma) b
  | ETyApp b t -> rmap_sub_ty_exp f d sigma b; rmap_sub_ty (f d) sigma sigma t
  | ECLam cn b -> rmap_sub_constr (f d) sigma sigma cn; rmap_sub_ty_exp f d sigma b
  | ECApp b -> rmap_sub_ty_exp f d sigma b
  | ELet t e1 e2 ->
    rmap_sub_ty (f d) sigma sigma t; rmap_sub_ty_exp f d sigma e1; rmap_sub_ty_exp f d sigma e2
  | ELetRec bs b -> rmap_sub_ty_binds f d sigma bs; rmap_sub_ty_exp f d sigma b
  | ECase es dt -> rmap_sub_ty_exps f d sigma es; rmap_sub_ty_dt f d sigma dt
  | ELetJoin ts t e1 e2 ->
    rmap_sub_tys (f d) sigma sigma ts; rmap_sub_ty (f d) sigma sigma t;
    rmap_sub_ty_exp f d sigma e1; rmap_sub_ty_exp f d sigma e2
  | EJump _ es -> rmap_sub_ty_exps f d sigma es
  | EExtend _ e1 e2 -> rmap_sub_ty_exp f d sigma e1; rmap_sub_ty_exp f d sigma e2
  | ESelect _ b -> rmap_sub_ty_exp f d sigma b
  | ERestrict _ b -> rmap_sub_ty_exp f d sigma b
  | EUpdate _ e1 e2 -> rmap_sub_ty_exp f d sigma e1; rmap_sub_ty_exp f d sigma e2
  | EMerge e1 e2 -> rmap_sub_ty_exp f d sigma e1; rmap_sub_ty_exp f d sigma e2
  | EInject _ t b -> rmap_sub_ty (f d) sigma sigma t; rmap_sub_ty_exp f d sigma b
  | EWeaken _ t b -> rmap_sub_ty (f d) sigma sigma t; rmap_sub_ty_exp f d sigma b
  | EAbsurd t b -> rmap_sub_ty (f d) sigma sigma t; rmap_sub_ty_exp f d sigma b
  | EPerform _ _ ts b -> rmap_sub_tys (f d) sigma sigma ts; rmap_sub_ty_exp f d sigma b
  | EHandle b h ->
    rmap_sub_ty_exp f d sigma b; rmap_sub_ent (f d) sigma sigma h.h_ent;
    rmap_sub_ty (f d) sigma sigma h.h_ret_ty; rmap_sub_ty_exp f d sigma h.h_ret;
    rmap_sub_ty_cls f d sigma h.h_clauses
  | EOpenEff t b -> rmap_sub_ty (f d) sigma sigma t; rmap_sub_ty_exp f d sigma b
  | ERegion l es b ->
    rmap_sub_layout (f d) sigma sigma l; rmap_sub_ty_exps f d sigma es;
    rmap_sub_ty_exp f (d + 1) sigma b
  | EWriteCell _ _ b -> rmap_sub_ty_exp f d sigma b
  | EMatch th dt -> rmap_sub_ty_exps f d sigma th; rmap_sub_ty_dt f d sigma dt
  | EOpenEffC t b -> rmap_sub_ty (f d) sigma sigma t; rmap_sub_ty_exp f d sigma b
  | EFill _ b -> rmap_sub_ty_exp f d sigma b
  | ERegionOpen _ th b -> rmap_sub_ty_cells f d sigma th; rmap_sub_ty_exp f d sigma b
  | EOpaque _ t -> rmap_sub_ty (f d) sigma sigma t

and rmap_sub_ty_exps (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub) (es: list exp)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_exps f d (sub_ty_exps sigma es) == sub_ty_exps sigma (rmap_exps f d es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> rmap_sub_ty_exp f d sigma e; rmap_sub_ty_exps f d sigma es

and rmap_sub_ty_binds (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub)
    (bs: list (typ & exp))
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_binds f d (sub_ty_binds sigma bs) == sub_ty_binds sigma (rmap_binds f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs ->
    rmap_sub_ty (f d) sigma sigma t; rmap_sub_ty_exp f d sigma e; rmap_sub_ty_binds f d sigma bs

and rmap_sub_ty_cells (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub)
    (th: list (key & exp))
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_cells f d (sub_ty_cells sigma th) == sub_ty_cells sigma (rmap_cells f d th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> rmap_sub_ty_exp f d sigma e; rmap_sub_ty_cells f d sigma th

and rmap_sub_ty_dt (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub) (dt: dtree)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_dt f d (sub_ty_dt sigma dt) == sub_ty_dt sigma (rmap_dt f d dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> rmap_sub_ty_exp f d sigma e
  | DBind _ dt -> rmap_sub_ty_dt f d sigma dt
  | DSwitchCtor _ bs df -> rmap_sub_ty_brs f d sigma bs; rmap_sub_ty_odt f d sigma df
  | DSwitchLit _ bs df -> rmap_sub_ty_brs f d sigma bs; rmap_sub_ty_dt f d sigma df
  | DSwitchKey _ bs df -> rmap_sub_ty_kbrs f d sigma bs; rmap_sub_ty_odt f d sigma df
  | DGuard e dt1 dt2 ->
    rmap_sub_ty_exp f d sigma e; rmap_sub_ty_dt f d sigma dt1; rmap_sub_ty_dt f d sigma dt2

and rmap_sub_ty_odt (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub) (df: option dtree)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_odt f d (sub_ty_odt sigma df) == sub_ty_odt sigma (rmap_odt f d df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> rmap_sub_ty_dt f d sigma dt

and rmap_sub_ty_brs (#lb: eqtype) (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub)
    (bs: list (lb & dtree))
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_brs f d (sub_ty_brs sigma bs) == sub_ty_brs sigma (rmap_brs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_sub_ty_dt f d sigma dt; rmap_sub_ty_brs f d sigma bs

and rmap_sub_ty_kbrs (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub)
    (bs: list (key & dtree))
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_kbrs f d (sub_ty_brs sigma bs) == sub_ty_brs sigma (rmap_kbrs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_sub_ty_dt f d sigma dt; rmap_sub_ty_kbrs f d sigma bs

and rmap_sub_ty_cls (f: nat -> region_ref -> region_ref) (d: nat) (sigma: tsub) (cs: list clause)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_ty (f d') (sigma i) == sigma i))
          (ensures rmap_cls f d (sub_ty_cls sigma cs) == sub_ty_cls sigma (rmap_cls f d cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb s kt b :: cs ->
    rmap_fix_upn_tsub f d nb sigma; rmap_sub_ty (f d) (upn_tsub nb sigma) (upn_tsub nb sigma) s;
    rmap_sub_ty (f d) (upn_tsub nb sigma) (upn_tsub nb sigma) kt;
    rmap_sub_ty_exp f d (upn_tsub nb sigma) b; rmap_sub_ty_cls f d sigma cs
  | CFast _ nb s b :: cs ->
    rmap_fix_upn_tsub f d nb sigma; rmap_sub_ty (f d) (upn_tsub nb sigma) (upn_tsub nb sigma) s;
    rmap_sub_ty_exp f d (upn_tsub nb sigma) b; rmap_sub_ty_cls f d sigma cs

let rmap_ren_ty_exp (f: nat -> region_ref -> region_ref) (d: nat) (xi: ren) (e: exp)
  : Lemma (rmap_exp f d (ren_ty_exp xi e) == ren_ty_exp xi (rmap_exp f d e)) =
  ren_ty_exp_as_sub xi e; ren_ty_exp_as_sub xi (rmap_exp f d e);
  rmap_sub_ty_exp f d (ren_tsub xi) e

let lc_tsub_mono (n: nat) (sigma: tsub)
  : Lemma (requires forall (i: nat). lc_ty_at n (sigma i))
          (ensures forall (i: nat). lc_ty_at (n + 1) (sigma i)) =
  introduce forall (i: nat). lc_ty_at (n + 1) (sigma i) with lc_mono_ty n (n + 1) (sigma i)

let rec lc_sub_ty_exp (n: nat) (sigma: tsub) (e: exp)
  : Lemma (requires lc_exp_at n e /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_exp_at n (sub_ty_exp sigma e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> lc_sub_ty n sigma t; lc_sub_ty n sigma r; lc_sub_ty_exp n sigma b
  | EApp e1 e2 -> lc_sub_ty_exp n sigma e1; lc_sub_ty_exp n sigma e2
  | ETyLam _ b -> lc_upn_tsub n 1 sigma; lc_sub_ty_exp n (up_tsub sigma) b
  | ETyApp b t -> lc_sub_ty_exp n sigma b; lc_sub_ty n sigma t
  | ECLam cn b -> lc_sub_constr n sigma cn; lc_sub_ty_exp n sigma b
  | ECApp b -> lc_sub_ty_exp n sigma b
  | ELet t e1 e2 -> lc_sub_ty n sigma t; lc_sub_ty_exp n sigma e1; lc_sub_ty_exp n sigma e2
  | ELetRec bs b -> lc_sub_ty_binds n sigma bs; lc_sub_ty_exp n sigma b
  | ECase es dt -> lc_sub_ty_exps n sigma es; lc_sub_ty_dt n sigma dt
  | ELetJoin ts t e1 e2 ->
    lc_sub_tys n sigma ts; lc_sub_ty n sigma t; lc_sub_ty_exp n sigma e1; lc_sub_ty_exp n sigma e2
  | EJump _ es -> lc_sub_ty_exps n sigma es
  | EExtend _ e1 e2 -> lc_sub_ty_exp n sigma e1; lc_sub_ty_exp n sigma e2
  | ESelect _ b -> lc_sub_ty_exp n sigma b
  | ERestrict _ b -> lc_sub_ty_exp n sigma b
  | EUpdate _ e1 e2 -> lc_sub_ty_exp n sigma e1; lc_sub_ty_exp n sigma e2
  | EMerge e1 e2 -> lc_sub_ty_exp n sigma e1; lc_sub_ty_exp n sigma e2
  | EInject _ t b -> lc_sub_ty n sigma t; lc_sub_ty_exp n sigma b
  | EWeaken _ t b -> lc_sub_ty n sigma t; lc_sub_ty_exp n sigma b
  | EAbsurd t b -> lc_sub_ty n sigma t; lc_sub_ty_exp n sigma b
  | EPerform _ _ ts b -> lc_sub_tys n sigma ts; lc_sub_ty_exp n sigma b
  | EHandle b h ->
    lc_sub_ty_exp n sigma b; lc_sub_ent n sigma h.h_ent; lc_sub_ty n sigma h.h_ret_ty;
    lc_sub_ty_exp n sigma h.h_ret; lc_sub_ty_cls n sigma h.h_clauses
  | EOpenEff t b -> lc_sub_ty n sigma t; lc_sub_ty_exp n sigma b
  | ERegion l es b ->
    lc_sub_layout n sigma l; lc_sub_ty_exps n sigma es; lc_tsub_mono n sigma;
    lc_sub_ty_exp (n + 1) sigma b
  | EWriteCell _ _ b -> lc_sub_ty_exp n sigma b
  | EMatch th dt -> lc_sub_ty_exps n sigma th; lc_sub_ty_dt n sigma dt
  | EOpenEffC t b -> lc_sub_ty n sigma t; lc_sub_ty_exp n sigma b
  | EFill _ b -> lc_sub_ty_exp n sigma b
  | ERegionOpen _ th b -> lc_sub_ty_cells n sigma th; lc_sub_ty_exp n sigma b
  | EOpaque _ t -> lc_sub_ty n sigma t

and lc_sub_ty_exps (n: nat) (sigma: tsub) (es: list exp)
  : Lemma (requires lc_exps_at n es /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_exps_at n (sub_ty_exps sigma es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> lc_sub_ty_exp n sigma e; lc_sub_ty_exps n sigma es

and lc_sub_ty_binds (n: nat) (sigma: tsub) (bs: list (typ & exp))
  : Lemma (requires lc_binds_at n bs /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_binds_at n (sub_ty_binds sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> lc_sub_ty n sigma t; lc_sub_ty_exp n sigma e; lc_sub_ty_binds n sigma bs

and lc_sub_ty_cells (n: nat) (sigma: tsub) (th: list (key & exp))
  : Lemma (requires lc_cells_at n th /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_cells_at n (sub_ty_cells sigma th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> lc_sub_ty_exp n sigma e; lc_sub_ty_cells n sigma th

and lc_sub_ty_dt (n: nat) (sigma: tsub) (dt: dtree)
  : Lemma (requires lc_dt_at n dt /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_dt_at n (sub_ty_dt sigma dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> lc_sub_ty_exp n sigma e
  | DBind _ dt -> lc_sub_ty_dt n sigma dt
  | DSwitchCtor _ bs df -> lc_sub_ty_brs n sigma bs; lc_sub_ty_odt n sigma df
  | DSwitchLit _ bs df -> lc_sub_ty_brs n sigma bs; lc_sub_ty_dt n sigma df
  | DSwitchKey _ bs df -> lc_sub_ty_kbrs n sigma bs; lc_sub_ty_odt n sigma df
  | DGuard e dt1 dt2 -> lc_sub_ty_exp n sigma e; lc_sub_ty_dt n sigma dt1; lc_sub_ty_dt n sigma dt2

and lc_sub_ty_odt (n: nat) (sigma: tsub) (df: option dtree)
  : Lemma (requires lc_odt_at n df /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_odt_at n (sub_ty_odt sigma df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> lc_sub_ty_dt n sigma dt

and lc_sub_ty_brs (#lb: eqtype) (n: nat) (sigma: tsub) (bs: list (lb & dtree))
  : Lemma (requires lc_brs_at n bs /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_brs_at n (sub_ty_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_sub_ty_dt n sigma dt; lc_sub_ty_brs n sigma bs

and lc_sub_ty_kbrs (n: nat) (sigma: tsub) (bs: list (key & dtree))
  : Lemma (requires lc_kbrs_at n bs /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_kbrs_at n (sub_ty_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_sub_ty_dt n sigma dt; lc_sub_ty_kbrs n sigma bs

and lc_sub_ty_cls (n: nat) (sigma: tsub) (cs: list clause)
  : Lemma (requires lc_cls_at n cs /\ (forall (i: nat). lc_ty_at n (sigma i)))
          (ensures lc_cls_at n (sub_ty_cls sigma cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb s kt b :: cs ->
    lc_upn_tsub n nb sigma; lc_sub_ty n (upn_tsub nb sigma) s; lc_sub_ty n (upn_tsub nb sigma) kt;
    lc_sub_ty_exp n (upn_tsub nb sigma) b; lc_sub_ty_cls n sigma cs
  | CFast _ nb s b :: cs ->
    lc_upn_tsub n nb sigma; lc_sub_ty n (upn_tsub nb sigma) s;
    lc_sub_ty_exp n (upn_tsub nb sigma) b; lc_sub_ty_cls n sigma cs

let lc_ren_ty_exp (n: nat) (xi: ren) (e: exp)
  : Lemma (requires lc_exp_at n e) (ensures lc_exp_at n (ren_ty_exp xi e)) =
  ren_ty_exp_as_sub xi e; lc_sub_ty_exp n (ren_tsub xi) e

let rmap_fix_upn_esub (f: nat -> region_ref -> region_ref) (d n: nat) (sigma: esub)
  : Lemma (requires forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i)
          (ensures forall (d': nat) (i: nat).
             d <= d' ==> rmap_exp f d' (upn_esub n sigma i) == upn_esub n sigma i) =
  introduce forall (d': nat) (i: nat).
    d <= d' ==> rmap_exp f d' (upn_esub n sigma i) == upn_esub n sigma i
  with introduce _ ==> _
  with if i < n then () else rmap_ren_tm f d' (shift n) (sigma (i - n))

let rmap_fix_tyup_esub (f: nat -> region_ref -> region_ref) (d m: nat) (sigma: esub)
  : Lemma (requires forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i)
          (ensures forall (d': nat) (i: nat).
             d <= d' ==> rmap_exp f d' (tyup_esub m sigma i) == tyup_esub m sigma i) =
  introduce forall (d': nat) (i: nat).
    d <= d' ==> rmap_exp f d' (tyup_esub m sigma i) == tyup_esub m sigma i
  with introduce _ ==> _
  with rmap_ren_ty_exp f d' (shift m) (sigma i)

let rmap_fix_jup_esub (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub)
  : Lemma (requires forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i)
          (ensures forall (d': nat) (i: nat).
             d <= d' ==> rmap_exp f d' (jup_esub sigma i) == jup_esub sigma i) =
  introduce forall (d': nat) (i: nat).
    d <= d' ==> rmap_exp f d' (jup_esub sigma i) == jup_esub sigma i
  with introduce _ ==> _
  with rmap_ren_jp f d' (shift 1) (sigma i)

let rec rmap_sub_tm (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub) (e: exp)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_exp f d (sub_tm sigma e) == sub_tm sigma (rmap_exp f d e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> rmap_fix_upn_esub f d 1 sigma; rmap_sub_tm f d (up_esub sigma) b
  | EApp e1 e2 -> rmap_sub_tm f d sigma e1; rmap_sub_tm f d sigma e2
  | ETyLam _ b -> rmap_fix_tyup_esub f d 1 sigma; rmap_sub_tm f d (tyup_esub 1 sigma) b
  | ETyApp b _ -> rmap_sub_tm f d sigma b
  | ECLam _ b -> rmap_sub_tm f d sigma b
  | ECApp b -> rmap_sub_tm f d sigma b
  | ELet _ e1 e2 ->
    rmap_sub_tm f d sigma e1; rmap_fix_upn_esub f d 1 sigma; rmap_sub_tm f d (up_esub sigma) e2
  | ELetRec bs b ->
    rmap_fix_upn_esub f d (L.length bs) sigma;
    rmap_sub_tm_binds f d (upn_esub (L.length bs) sigma) bs;
    rmap_sub_tm f d (upn_esub (L.length bs) sigma) b
  | ECase es dt -> rmap_sub_tm_exps f d sigma es; rmap_sub_tm_dt f d sigma dt
  | ELetJoin ts _ e1 e2 ->
    rmap_fix_jup_esub f d sigma; rmap_fix_upn_esub f d (L.length ts) (jup_esub sigma);
    rmap_sub_tm f d (upn_esub (L.length ts) (jup_esub sigma)) e1;
    rmap_sub_tm f d (jup_esub sigma) e2
  | EJump _ es -> rmap_sub_tm_exps f d sigma es
  | EExtend _ e1 e2 -> rmap_sub_tm f d sigma e1; rmap_sub_tm f d sigma e2
  | ESelect _ b -> rmap_sub_tm f d sigma b
  | ERestrict _ b -> rmap_sub_tm f d sigma b
  | EUpdate _ e1 e2 -> rmap_sub_tm f d sigma e1; rmap_sub_tm f d sigma e2
  | EMerge e1 e2 -> rmap_sub_tm f d sigma e1; rmap_sub_tm f d sigma e2
  | EInject _ _ b -> rmap_sub_tm f d sigma b
  | EWeaken _ _ b -> rmap_sub_tm f d sigma b
  | EAbsurd _ b -> rmap_sub_tm f d sigma b
  | EPerform _ _ _ b -> rmap_sub_tm f d sigma b
  | EHandle b h ->
    rmap_sub_tm f d sigma b; rmap_fix_upn_esub f d 1 sigma; rmap_sub_tm f d (up_esub sigma) h.h_ret;
    rmap_sub_tm_cls f d sigma h.h_clauses
  | EOpenEff _ b -> rmap_sub_tm f d sigma b
  | ERegion _ es b -> rmap_sub_tm_exps f d sigma es; rmap_sub_tm f (d + 1) sigma b
  | EWriteCell _ _ b -> rmap_sub_tm f d sigma b
  | EMatch th dt -> rmap_sub_tm_exps f d sigma th; rmap_sub_tm_dt f d sigma dt
  | EOpenEffC _ b -> rmap_sub_tm f d sigma b
  | EFill _ b -> rmap_sub_tm f d sigma b
  | ERegionOpen _ th b -> rmap_sub_tm_cells f d sigma th; rmap_sub_tm f d sigma b

and rmap_sub_tm_exps (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub) (es: list exp)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_exps f d (sub_tm_exps sigma es) == sub_tm_exps sigma (rmap_exps f d es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> rmap_sub_tm f d sigma e; rmap_sub_tm_exps f d sigma es

and rmap_sub_tm_binds (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub)
    (bs: list (typ & exp))
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_binds f d (sub_tm_binds sigma bs) == sub_tm_binds sigma (rmap_binds f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> rmap_sub_tm f d sigma e; rmap_sub_tm_binds f d sigma bs

and rmap_sub_tm_cells (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub)
    (th: list (key & exp))
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_cells f d (sub_tm_cells sigma th) == sub_tm_cells sigma (rmap_cells f d th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> rmap_sub_tm f d sigma e; rmap_sub_tm_cells f d sigma th

and rmap_sub_tm_dt (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub) (dt: dtree)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_dt f d (sub_tm_dt sigma dt) == sub_tm_dt sigma (rmap_dt f d dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> rmap_sub_tm f d sigma e
  | DBind _ dt -> rmap_fix_upn_esub f d 1 sigma; rmap_sub_tm_dt f d (up_esub sigma) dt
  | DSwitchCtor _ bs df -> rmap_sub_tm_brs f d sigma bs; rmap_sub_tm_odt f d sigma df
  | DSwitchLit _ bs df -> rmap_sub_tm_brs f d sigma bs; rmap_sub_tm_dt f d sigma df
  | DSwitchKey _ bs df -> rmap_sub_tm_kbrs f d sigma bs; rmap_sub_tm_odt f d sigma df
  | DGuard e dt1 dt2 ->
    rmap_sub_tm f d sigma e; rmap_sub_tm_dt f d sigma dt1; rmap_sub_tm_dt f d sigma dt2

and rmap_sub_tm_odt (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub) (df: option dtree)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_odt f d (sub_tm_odt sigma df) == sub_tm_odt sigma (rmap_odt f d df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> rmap_sub_tm_dt f d sigma dt

and rmap_sub_tm_brs (#lb: eqtype) (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub)
    (bs: list (lb & dtree))
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_brs f d (sub_tm_brs sigma bs) == sub_tm_brs sigma (rmap_brs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_sub_tm_dt f d sigma dt; rmap_sub_tm_brs f d sigma bs

and rmap_sub_tm_kbrs (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub)
    (bs: list (key & dtree))
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_kbrs f d (sub_tm_brs sigma bs) == sub_tm_brs sigma (rmap_kbrs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_sub_tm_dt f d sigma dt; rmap_sub_tm_kbrs f d sigma bs

and rmap_sub_tm_cls (f: nat -> region_ref -> region_ref) (d: nat) (sigma: esub) (cs: list clause)
  : Lemma (requires (forall (d': nat) (i: nat). d <= d' ==> rmap_exp f d' (sigma i) == sigma i))
          (ensures rmap_cls f d (sub_tm_cls sigma cs) == sub_tm_cls sigma (rmap_cls f d cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    rmap_fix_tyup_esub f d nb sigma; rmap_fix_upn_esub f d 2 (tyup_esub nb sigma);
    rmap_sub_tm f d (upn_esub 2 (tyup_esub nb sigma)) b; rmap_sub_tm_cls f d sigma cs
  | CFast _ nb _ b :: cs ->
    rmap_fix_tyup_esub f d nb sigma; rmap_fix_upn_esub f d 1 (tyup_esub nb sigma);
    rmap_sub_tm f d (up_esub (tyup_esub nb sigma)) b; rmap_sub_tm_cls f d sigma cs

let lc_upn_esub (n k: nat) (sigma: esub)
  : Lemma (requires forall (i: nat). lc_exp_at n (sigma i))
          (ensures forall (i: nat). lc_exp_at n (upn_esub k sigma i)) =
  introduce forall (i: nat). lc_exp_at n (upn_esub k sigma i)
  with if i < k then () else lc_ren_tm n (shift k) (sigma (i - k))

let lc_tyup_esub (n m: nat) (sigma: esub)
  : Lemma (requires forall (i: nat). lc_exp_at n (sigma i))
          (ensures forall (i: nat). lc_exp_at n (tyup_esub m sigma i)) =
  introduce forall (i: nat). lc_exp_at n (tyup_esub m sigma i)
  with lc_ren_ty_exp n (shift m) (sigma i)

let lc_jup_esub (n: nat) (sigma: esub)
  : Lemma (requires forall (i: nat). lc_exp_at n (sigma i))
          (ensures forall (i: nat). lc_exp_at n (jup_esub sigma i)) =
  introduce forall (i: nat). lc_exp_at n (jup_esub sigma i)
  with lc_ren_jp n (shift 1) (sigma i)

let lc_esub_mono (n: nat) (sigma: esub)
  : Lemma (requires forall (i: nat). lc_exp_at n (sigma i))
          (ensures forall (i: nat). lc_exp_at (n + 1) (sigma i)) =
  introduce forall (i: nat). lc_exp_at (n + 1) (sigma i) with lc_mono_exp n (n + 1) (sigma i)

let rec lc_sub_tm (n: nat) (sigma: esub) (e: exp)
  : Lemma (requires lc_exp_at n e /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_exp_at n (sub_tm sigma e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> lc_upn_esub n 1 sigma; lc_sub_tm n (up_esub sigma) b
  | EApp e1 e2 -> lc_sub_tm n sigma e1; lc_sub_tm n sigma e2
  | ETyLam _ b -> lc_tyup_esub n 1 sigma; lc_sub_tm n (tyup_esub 1 sigma) b
  | ETyApp b _ -> lc_sub_tm n sigma b
  | ECLam _ b -> lc_sub_tm n sigma b
  | ECApp b -> lc_sub_tm n sigma b
  | ELet _ e1 e2 -> lc_sub_tm n sigma e1; lc_upn_esub n 1 sigma; lc_sub_tm n (up_esub sigma) e2
  | ELetRec bs b ->
    lc_upn_esub n (L.length bs) sigma; lc_sub_tm_binds n (upn_esub (L.length bs) sigma) bs;
    lc_sub_tm n (upn_esub (L.length bs) sigma) b
  | ECase es dt -> lc_sub_tm_exps n sigma es; lc_sub_tm_dt n sigma dt
  | ELetJoin ts _ e1 e2 ->
    lc_jup_esub n sigma; lc_upn_esub n (L.length ts) (jup_esub sigma);
    lc_sub_tm n (upn_esub (L.length ts) (jup_esub sigma)) e1; lc_sub_tm n (jup_esub sigma) e2
  | EJump _ es -> lc_sub_tm_exps n sigma es
  | EExtend _ e1 e2 -> lc_sub_tm n sigma e1; lc_sub_tm n sigma e2
  | ESelect _ b -> lc_sub_tm n sigma b
  | ERestrict _ b -> lc_sub_tm n sigma b
  | EUpdate _ e1 e2 -> lc_sub_tm n sigma e1; lc_sub_tm n sigma e2
  | EMerge e1 e2 -> lc_sub_tm n sigma e1; lc_sub_tm n sigma e2
  | EInject _ _ b -> lc_sub_tm n sigma b
  | EWeaken _ _ b -> lc_sub_tm n sigma b
  | EAbsurd _ b -> lc_sub_tm n sigma b
  | EPerform _ _ _ b -> lc_sub_tm n sigma b
  | EHandle b h ->
    lc_sub_tm n sigma b; lc_upn_esub n 1 sigma; lc_sub_tm n (up_esub sigma) h.h_ret;
    lc_sub_tm_cls n sigma h.h_clauses
  | EOpenEff _ b -> lc_sub_tm n sigma b
  | ERegion _ es b -> lc_sub_tm_exps n sigma es; lc_esub_mono n sigma; lc_sub_tm (n + 1) sigma b
  | EWriteCell _ _ b -> lc_sub_tm n sigma b
  | EMatch th dt -> lc_sub_tm_exps n sigma th; lc_sub_tm_dt n sigma dt
  | EOpenEffC _ b -> lc_sub_tm n sigma b
  | EFill _ b -> lc_sub_tm n sigma b
  | ERegionOpen _ th b -> lc_sub_tm_cells n sigma th; lc_sub_tm n sigma b

and lc_sub_tm_exps (n: nat) (sigma: esub) (es: list exp)
  : Lemma (requires lc_exps_at n es /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_exps_at n (sub_tm_exps sigma es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> lc_sub_tm n sigma e; lc_sub_tm_exps n sigma es

and lc_sub_tm_binds (n: nat) (sigma: esub) (bs: list (typ & exp))
  : Lemma (requires lc_binds_at n bs /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_binds_at n (sub_tm_binds sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> lc_sub_tm n sigma e; lc_sub_tm_binds n sigma bs

and lc_sub_tm_cells (n: nat) (sigma: esub) (th: list (key & exp))
  : Lemma (requires lc_cells_at n th /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_cells_at n (sub_tm_cells sigma th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> lc_sub_tm n sigma e; lc_sub_tm_cells n sigma th

and lc_sub_tm_dt (n: nat) (sigma: esub) (dt: dtree)
  : Lemma (requires lc_dt_at n dt /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_dt_at n (sub_tm_dt sigma dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> lc_sub_tm n sigma e
  | DBind _ dt -> lc_upn_esub n 1 sigma; lc_sub_tm_dt n (up_esub sigma) dt
  | DSwitchCtor _ bs df -> lc_sub_tm_brs n sigma bs; lc_sub_tm_odt n sigma df
  | DSwitchLit _ bs df -> lc_sub_tm_brs n sigma bs; lc_sub_tm_dt n sigma df
  | DSwitchKey _ bs df -> lc_sub_tm_kbrs n sigma bs; lc_sub_tm_odt n sigma df
  | DGuard e dt1 dt2 -> lc_sub_tm n sigma e; lc_sub_tm_dt n sigma dt1; lc_sub_tm_dt n sigma dt2

and lc_sub_tm_odt (n: nat) (sigma: esub) (df: option dtree)
  : Lemma (requires lc_odt_at n df /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_odt_at n (sub_tm_odt sigma df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> lc_sub_tm_dt n sigma dt

and lc_sub_tm_brs (#lb: eqtype) (n: nat) (sigma: esub) (bs: list (lb & dtree))
  : Lemma (requires lc_brs_at n bs /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_brs_at n (sub_tm_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_sub_tm_dt n sigma dt; lc_sub_tm_brs n sigma bs

and lc_sub_tm_kbrs (n: nat) (sigma: esub) (bs: list (key & dtree))
  : Lemma (requires lc_kbrs_at n bs /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_kbrs_at n (sub_tm_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> lc_sub_tm_dt n sigma dt; lc_sub_tm_kbrs n sigma bs

and lc_sub_tm_cls (n: nat) (sigma: esub) (cs: list clause)
  : Lemma (requires lc_cls_at n cs /\ (forall (i: nat). lc_exp_at n (sigma i)))
          (ensures lc_cls_at n (sub_tm_cls sigma cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    lc_tyup_esub n nb sigma; lc_upn_esub n 2 (tyup_esub nb sigma);
    lc_sub_tm n (upn_esub 2 (tyup_esub nb sigma)) b; lc_sub_tm_cls n sigma cs
  | CFast _ nb _ b :: cs ->
    lc_tyup_esub n nb sigma; lc_upn_esub n 1 (tyup_esub nb sigma);
    lc_sub_tm n (up_esub (tyup_esub nb sigma)) b; lc_sub_tm_cls n sigma cs

let open_region_sub_ty (d: nat) (a: atom) (sigma: tsub) (t: typ)
  : Lemma (requires forall (i: nat). lc_ty (sigma i))
          (ensures open_region_ty d a (sub_ty sigma t) == sub_ty sigma (open_region_ty d a t)) =
  introduce forall (i: nat). sigma i == rmap_ty (open_rr a d) (sigma i)
  with begin lc_mono_ty 0 d (sigma i); open_lc_ty a d (sigma i) end;
  rmap_sub_ty (open_rr a d) sigma sigma t

let open_region_sub_ty_exp (d: nat) (a: atom) (sigma: tsub) (e: exp)
  : Lemma (requires forall (i: nat). lc_ty (sigma i))
          (ensures open_region_at d a (sub_ty_exp sigma e)
                   == sub_ty_exp sigma (open_region_at d a e)) =
  introduce forall (d': nat) (i: nat). d <= d' ==> rmap_ty (open_rr a d') (sigma i) == sigma i
  with introduce _ ==> _
  with begin lc_mono_ty 0 d' (sigma i); open_lc_ty a d' (sigma i) end;
  rmap_sub_ty_exp (open_rr a) d sigma e

let open_region_sub_tm (d: nat) (a: atom) (sigma: esub) (e: exp)
  : Lemma (requires forall (i: nat). lc_exp (sigma i))
          (ensures open_region_at d a (sub_tm sigma e) == sub_tm sigma (open_region_at d a e)) =
  introduce forall (d': nat) (i: nat). d <= d' ==> rmap_exp (open_rr a) d' (sigma i) == sigma i
  with introduce _ ==> _
  with begin lc_mono_exp 0 d' (sigma i); open_lc_exp a d' (sigma i) end;
  rmap_sub_tm (open_rr a) d sigma e

let open_region_ren_ty_exp (d: nat) (a: atom) (xi: ren) (e: exp)
  : Lemma (open_region_at d a (ren_ty_exp xi e) == ren_ty_exp xi (open_region_at d a e)) =
  rmap_ren_ty_exp (open_rr a) d xi e

let open_region_ren_tm (d: nat) (a: atom) (xi: ren) (e: exp)
  : Lemma (open_region_at d a (ren_tm xi e) == ren_tm xi (open_region_at d a e)) =
  rmap_ren_tm (open_rr a) d xi e

let open_region_ren_jp (d: nat) (a: atom) (xi: ren) (e: exp)
  : Lemma (open_region_at d a (ren_jp xi e) == ren_jp xi (open_region_at d a e)) =
  rmap_ren_jp (open_rr a) d xi e
