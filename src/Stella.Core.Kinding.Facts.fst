(* Proof structure.

   Local closure is one mutual induction following the definitions of
   `synth_kind`, `check`, `entry_ok`, `check_tys` and `constr_ok`, with
   their measures. A region element and a region key are kinded only as an
   atom in scope; entering a type binder and assuming a constraint keep the
   region domain (`rdom_push_tvar`, `rdom_add_assump`).

   The types of `Prim` are applications of a constructor that `prim_wf`
   records with no kind variable and a closed kind, so their kinding
   unfolds to that of their arguments. The remaining inversions are single
   unfoldings of `check`. *)
module Stella.Core.Kinding.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Prim
module L = FStar.List.Tot

(* Local closure and region names. *)

let rec synth_kind_lc (sg: sig) (g: ctx) (t: typ)
  : Lemma (requires Some? (synth_kind sg g t)) (ensures lc_ty t /\ in_rdom (frn_ty t) g)
          (decreases %[t; 0]) =
  match t with
  | TApp t1 t2 ->
    synth_kind_lc sg g t1;
    let Some (KArrow k1 _) = synth_kind sg g t1 in
    check_lc sg g t2 k1
  | TForall k t1 -> rdom_push_tvar g k; check_lc sg (push_tvar g k) t1 KType
  | TConstr c t1 ->
    rdom_add_assump g c;
    constr_ok_lc sg g c;
    check_lc sg (add_assump g c) t1 KType
  | _ -> ()

and check_lc (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg g t k) (ensures lc_ty t /\ in_rdom (frn_ty t) g)
          (decreases %[t; 1]) =
  match t with
  | TRowEmpty -> ()
  | TRowExt en r -> let KRow e = k in entry_ok_lc sg g en e; check_lc sg g r k
  | TRowUnion r1 r2 -> check_lc sg g r1 k; check_lc sg g r2 k
  | _ -> synth_kind_lc sg g t

and entry_ok_lc (sg: sig) (g: ctx) (en: entry) (e: elt_kind)
  : Lemma (requires entry_ok sg g en e) (ensures lc_ent_at 0 en /\ in_rdom (frn_ent en) g)
          (decreases en) =
  match en with
  | EntTy _ t -> check_lc sg g t KType
  | EntEff _ q ts -> check_tys_lc sg g ts (Some?.v (sg.effects q)).eff_params
  | EntRegion _ -> ()

and check_tys_lc (sg: sig) (g: ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g ts ks) (ensures lc_tys_at 0 ts /\ in_rdom (frn_tys ts) g)
          (decreases ts) =
  match ts, ks with
  | [], [] -> ()
  | t :: ts', k :: ks' -> check_lc sg g t k; check_tys_lc sg g ts' ks'

and constr_ok_lc (sg: sig) (g: ctx) (c: constr)
  : Lemma (requires constr_ok sg g c) (ensures lc_constr_at 0 c /\ in_rdom (frn_constr c) g)
          (decreases c) =
  match c with
  | CLacks _ r ->
    if check sg g r (KRow EType) then check_lc sg g r (KRow EType)
    else check_lc sg g r (KRow EEffect)
  | CDisj r1 r2 ->
    if check sg g r1 (KRow EType) && check sg g r2 (KRow EType) then begin
      check_lc sg g r1 (KRow EType);
      check_lc sg g r2 (KRow EType)
    end else begin
      check_lc sg g r1 (KRow EEffect);
      check_lc sg g r2 (KRow EEffect)
    end

let check_fresh sg g t k a = check_lc sg g t k

(* Type variables and kind variables in scope. *)

let rec nth_length (#a: Type) (l: list a) (i: nat)
  : Lemma (requires Some? (L.nth l i)) (ensures i < L.length l) (decreases l) =
  match l with
  | _ :: l' -> if i = 0 then () else nth_length l' (i - 1)

let rec synth_kind_tvs (sg: sig) (g: ctx) (t: typ)
  : Lemma (requires Some? (synth_kind sg g t)) (ensures tvs_below (L.length g.tvars) t)
          (decreases %[t; 0]) =
  match t with
  | TVar i -> nth_length g.tvars i
  | TApp t1 t2 ->
    synth_kind_tvs sg g t1;
    let Some (KArrow k1 _) = synth_kind sg g t1 in
    check_tvs sg g t2 k1
  | TForall k t1 -> check_tvs sg (push_tvar g k) t1 KType
  | TConstr c t1 -> constr_ok_tvs sg g c; check_tvs sg (add_assump g c) t1 KType
  | _ -> ()

and check_tvs (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg g t k) (ensures tvs_below (L.length g.tvars) t)
          (decreases %[t; 1]) =
  match t with
  | TRowEmpty -> ()
  | TRowExt en r -> let KRow e = k in entry_ok_tvs sg g en e; check_tvs sg g r k
  | TRowUnion r1 r2 -> check_tvs sg g r1 k; check_tvs sg g r2 k
  | _ -> synth_kind_tvs sg g t

and entry_ok_tvs (sg: sig) (g: ctx) (en: entry) (e: elt_kind)
  : Lemma (requires entry_ok sg g en e) (ensures tvs_below_ent (L.length g.tvars) en)
          (decreases en) =
  match en with
  | EntTy _ t -> check_tvs sg g t KType
  | EntEff _ q ts -> check_tys_tvs sg g ts (Some?.v (sg.effects q)).eff_params
  | EntRegion _ -> ()

and check_tys_tvs (sg: sig) (g: ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g ts ks) (ensures tvs_below_tys (L.length g.tvars) ts)
          (decreases ts) =
  match ts, ks with
  | [], [] -> ()
  | t :: ts', k :: ks' -> check_tvs sg g t k; check_tys_tvs sg g ts' ks'

and constr_ok_tvs (sg: sig) (g: ctx) (c: constr)
  : Lemma (requires constr_ok sg g c) (ensures tvs_below_constr (L.length g.tvars) c)
          (decreases c) =
  match c with
  | CLacks _ r ->
    if check sg g r (KRow EType) then check_tvs sg g r (KRow EType)
    else check_tvs sg g r (KRow EEffect)
  | CDisj r1 r2 ->
    if check sg g r1 (KRow EType) && check sg g r2 (KRow EType) then begin
      check_tvs sg g r1 (KRow EType);
      check_tvs sg g r2 (KRow EType)
    end else begin
      check_tvs sg g r1 (KRow EEffect);
      check_tvs sg g r2 (KRow EEffect)
    end

let check_tvs_below sg g t k = check_tvs sg g t k

let up_agree (n: nat) (sigma sigma': tsub)
  : Lemma (requires forall (i: nat). i < n ==> sigma i == sigma' i)
          (ensures forall (i: nat). i < n + 1 ==> up_tsub sigma i == up_tsub sigma' i) =
  introduce forall (i: nat). i < n + 1 ==> up_tsub sigma i == up_tsub sigma' i
  with introduce _ ==> _
  with (if i = 0 then () else assert (sigma (i - 1) == sigma' (i - 1)))

let rec sub_tvs (n: nat) (sigma sigma': tsub) (t: typ)
  : Lemma (requires tvs_below n t /\ (forall (i: nat). i < n ==> sigma i == sigma' i))
          (ensures sub_ty sigma t == sub_ty sigma' t) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 | TRowUnion t1 t2 -> sub_tvs n sigma sigma' t1; sub_tvs n sigma sigma' t2
  | TForall _ b -> up_agree n sigma sigma'; sub_tvs (n + 1) (up_tsub sigma) (up_tsub sigma') b
  | TConstr c b -> sub_tvs_constr n sigma sigma' c; sub_tvs n sigma sigma' b
  | TRowExt en r -> sub_tvs_ent n sigma sigma' en; sub_tvs n sigma sigma' r

and sub_tvs_ent (n: nat) (sigma sigma': tsub) (en: entry)
  : Lemma (requires tvs_below_ent n en /\ (forall (i: nat). i < n ==> sigma i == sigma' i))
          (ensures sub_ent sigma en == sub_ent sigma' en) (decreases en) =
  match en with
  | EntTy _ t -> sub_tvs n sigma sigma' t
  | EntEff _ _ ts -> sub_tvs_tys n sigma sigma' ts
  | EntRegion _ -> ()

and sub_tvs_constr (n: nat) (sigma sigma': tsub) (c: constr)
  : Lemma (requires tvs_below_constr n c /\ (forall (i: nat). i < n ==> sigma i == sigma' i))
          (ensures sub_constr sigma c == sub_constr sigma' c) (decreases c) =
  match c with
  | CLacks _ t -> sub_tvs n sigma sigma' t
  | CDisj t1 t2 -> sub_tvs n sigma sigma' t1; sub_tvs n sigma sigma' t2

and sub_tvs_tys (n: nat) (sigma sigma': tsub) (ts: list typ)
  : Lemma (requires tvs_below_tys n ts /\ (forall (i: nat). i < n ==> sigma i == sigma' i))
          (ensures sub_tys sigma ts == sub_tys sigma' ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> sub_tvs n sigma sigma' t; sub_tvs_tys n sigma sigma' ts'

let sub_tvs_ext n sigma sigma' t = sub_tvs n sigma sigma' t

let sub_tvs_below n sigma t = sub_tvs n sigma tvar t; sub_ty_tvar t

let rec kinst_tvs (ks: list kind) (n: nat) (t: typ)
  : Lemma (ensures tvs_below n (kinst_ty ks t) == tvs_below n t) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 | TRowUnion t1 t2 -> kinst_tvs ks n t1; kinst_tvs ks n t2
  | TForall _ b -> kinst_tvs ks (n + 1) b
  | TConstr c b -> kinst_tvs_constr ks n c; kinst_tvs ks n b
  | TRowExt en r -> kinst_tvs_ent ks n en; kinst_tvs ks n r

and kinst_tvs_ent (ks: list kind) (n: nat) (en: entry)
  : Lemma (ensures tvs_below_ent n (kinst_ent ks en) == tvs_below_ent n en) (decreases en) =
  match en with
  | EntTy _ t -> kinst_tvs ks n t
  | EntEff _ _ ts -> kinst_tvs_tys ks n ts
  | EntRegion _ -> ()

and kinst_tvs_constr (ks: list kind) (n: nat) (c: constr)
  : Lemma (ensures tvs_below_constr n (kinst_constr ks c) == tvs_below_constr n c) (decreases c) =
  match c with
  | CLacks _ t -> kinst_tvs ks n t
  | CDisj t1 t2 -> kinst_tvs ks n t1; kinst_tvs ks n t2

and kinst_tvs_tys (ks: list kind) (n: nat) (ts: list typ)
  : Lemma (ensures tvs_below_tys n (kinst_tys ks ts) == tvs_below_tys n ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> kinst_tvs ks n t; kinst_tvs_tys ks n ts'

let kinst_tvs_below ks n t = kinst_tvs ks n t

let rec synth_kind_kinst_fixed (sg: sig) (g: ctx) (t: typ) (ks: list kind)
  : Lemma (requires g.nk == 0 /\ Some? (synth_kind sg g t)) (ensures kinst_ty ks t == t)
          (decreases %[t; 0]) =
  match t with
  | TCon _ kl -> kinst_kinds_closed ks kl
  | TApp t1 t2 ->
    synth_kind_kinst_fixed sg g t1 ks;
    let Some (KArrow k1 _) = synth_kind sg g t1 in
    check_kinst_fixed' sg g t2 k1 ks
  | TForall k t1 -> kinst_kind_closed ks k; check_kinst_fixed' sg (push_tvar g k) t1 KType ks
  | TConstr c t1 ->
    constr_ok_kinst_fixed sg g c ks;
    check_kinst_fixed' sg (add_assump g c) t1 KType ks
  | _ -> ()

and check_kinst_fixed' (sg: sig) (g: ctx) (t: typ) (k: kind) (ks: list kind)
  : Lemma (requires g.nk == 0 /\ check sg g t k) (ensures kinst_ty ks t == t)
          (decreases %[t; 1]) =
  match t with
  | TRowEmpty -> ()
  | TRowExt en r ->
    let KRow e = k in
    entry_ok_kinst_fixed sg g en e ks;
    check_kinst_fixed' sg g r k ks
  | TRowUnion r1 r2 -> check_kinst_fixed' sg g r1 k ks; check_kinst_fixed' sg g r2 k ks
  | _ -> synth_kind_kinst_fixed sg g t ks

and entry_ok_kinst_fixed (sg: sig) (g: ctx) (en: entry) (e: elt_kind) (ks: list kind)
  : Lemma (requires g.nk == 0 /\ entry_ok sg g en e) (ensures kinst_ent ks en == en)
          (decreases en) =
  match en with
  | EntTy _ t -> check_kinst_fixed' sg g t KType ks
  | EntEff _ q ts -> check_tys_kinst_fixed sg g ts (Some?.v (sg.effects q)).eff_params ks
  | EntRegion _ -> ()

and check_tys_kinst_fixed (sg: sig) (g: ctx) (ts: list typ) (kl: list kind) (ks: list kind)
  : Lemma (requires g.nk == 0 /\ check_tys sg g ts kl) (ensures kinst_tys ks ts == ts)
          (decreases ts) =
  match ts, kl with
  | [], [] -> ()
  | t :: ts', k :: kl' -> check_kinst_fixed' sg g t k ks; check_tys_kinst_fixed sg g ts' kl' ks

and constr_ok_kinst_fixed (sg: sig) (g: ctx) (c: constr) (ks: list kind)
  : Lemma (requires g.nk == 0 /\ constr_ok sg g c) (ensures kinst_constr ks c == c)
          (decreases c) =
  match c with
  | CLacks _ r ->
    if check sg g r (KRow EType) then check_kinst_fixed' sg g r (KRow EType) ks
    else check_kinst_fixed' sg g r (KRow EEffect) ks
  | CDisj r1 r2 ->
    if check sg g r1 (KRow EType) && check sg g r2 (KRow EType) then begin
      check_kinst_fixed' sg g r1 (KRow EType) ks;
      check_kinst_fixed' sg g r2 (KRow EType) ks
    end else begin
      check_kinst_fixed' sg g r1 (KRow EEffect) ks;
      check_kinst_fixed' sg g r2 (KRow EEffect) ks
    end

let check_kinst_fixed sg g t k ks = check_kinst_fixed' sg g t k ks

(* The types of `Prim`. *)

let check_t_fun sg g t1 r t2 =
  let kf = KArrow KType (KArrow (KRow EEffect) (KArrow KType KType)) in
  let f = TCon prim_function [] in
  kinst_kind_nil kf;
  assert (synth_kind sg g f == Some kf);
  assert (synth_kind sg g (TApp f t1) ==
          (if check sg g t1 KType then Some (KArrow (KRow EEffect) (KArrow KType KType)) else None));
  assert (synth_kind sg g (TApp (TApp f t1) r) ==
          (if check sg g t1 KType && check sg g r (KRow EEffect) then Some (KArrow KType KType)
           else None))

let check_t_record sg g r =
  kinst_kind_nil (KArrow (KRow EType) KType);
  assert (synth_kind sg g (TCon prim_record []) == Some (KArrow (KRow EType) KType))

let check_t_variant sg g r =
  kinst_kind_nil (KArrow (KRow EType) KType);
  assert (synth_kind sg g (TCon prim_variant []) == Some (KArrow (KRow EType) KType))

let check_t_unit sg g = ()

let check_t_bool sg g = ()

let check_lit_type sg g c = ()

(* Rows and binders. *)

let key_ok_struct sg g k = ()

let check_ext sg g en r e = ()

let check_ext_ty sg g k t r = ()

let check_union sg g r1 r2 e = ()

let check_forall sg g k t = ()

let check_constr sg g c t = ()

let rec qkind_mono (n m: nat) (k: kind)
  : Lemma (requires n <= m /\ qkind n k) (ensures qkind m k /\ kind_wf m k) (decreases k) =
  match k with
  | KArrow k1 k2 -> qkind_mono n m k1; qkind_mono n m k2
  | _ -> ()

let rec qkinds_wf_mono n m ks =
  match ks with
  | [] -> ()
  | k :: ks' -> qkind_mono n m k; qkinds_wf_mono n m ks'

(* Term variables. *)

let same_kinding_ext g g' =
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps g') h
  with introduce _ ==> _
  with entails_hyp (hyps g') h;
  introduce forall (h: constr). L.mem h (hyps g') ==> entails (hyps g) h
  with introduce _ ==> _
  with entails_hyp (hyps g) h

let same_kinding_push_var g t = ()

let rec same_kinding_push_vars (g: ctx) (ts: list typ)
  : Lemma (same_kinding g (push_vars g ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> same_kinding_push_vars (push_var g t) ts'

let check_same_kinding sg g g' t k =
  same_kinding_ext g g';
  if check sg g t k then check_weaken sg g g' t k;
  if check sg g' t k then check_weaken sg g' g t k
