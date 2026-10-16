(* `kinst_exp_nil` is one mutual induction over the term classes; the
   interface exports its `exp` and `dtree` instances. *)
module Stella.Core.Subst.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Subst.Lemmas.Tm
module L = FStar.List.Tot

let rec kinst_kind_nil (k: kind) : Lemma (ensures kinst_kind [] k == k) (decreases k) =
  match k with
  | KArrow k1 k2 -> kinst_kind_nil k1; kinst_kind_nil k2
  | _ -> ()

let rec kinst_kinds_nil (kl: list kind) : Lemma (ensures kinst_kinds [] kl == kl) (decreases kl) =
  match kl with
  | [] -> ()
  | k :: kl -> kinst_kind_nil k; kinst_kinds_nil kl

let rec kinst_ty_nil (t: typ) : Lemma (ensures kinst_ty [] t == t) (decreases t) =
  match t with
  | TVar _ | TRowEmpty -> ()
  | TCon _ kl -> kinst_kinds_nil kl
  | TApp t1 t2 | TRowUnion t1 t2 -> kinst_ty_nil t1; kinst_ty_nil t2
  | TForall k t -> kinst_kind_nil k; kinst_ty_nil t
  | TConstr cn t -> kinst_constr_nil cn; kinst_ty_nil t
  | TRowExt en t -> kinst_ent_nil en; kinst_ty_nil t

and kinst_ent_nil (en: entry) : Lemma (ensures kinst_ent [] en == en) (decreases en) =
  match en with
  | EntTy _ t -> kinst_ty_nil t
  | EntEff _ _ ts -> kinst_tys_nil ts
  | EntRegion _ -> ()

and kinst_constr_nil (cn: constr) : Lemma (ensures kinst_constr [] cn == cn) (decreases cn) =
  match cn with
  | CLacks _ t -> kinst_ty_nil t
  | CDisj t1 t2 -> kinst_ty_nil t1; kinst_ty_nil t2

and kinst_tys_nil (ts: list typ) : Lemma (ensures kinst_tys [] ts == ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> kinst_ty_nil t; kinst_tys_nil ts

let rec kinst_layout_nil (l: list (key & typ))
  : Lemma (ensures kinst_layout [] l == l) (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> kinst_ty_nil t; kinst_layout_nil l

let rec kinst_exp_nil (e: exp) : Lemma (ensures kinst_exp [] e == e) (decreases e) =
  match e with
  | EVar _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | EGlobal _ kl -> kinst_kinds_nil kl
  | ECApp b | ESelect _ b | ERestrict _ b | EWriteCell _ _ b | EFill _ b -> kinst_exp_nil b
  | ETyApp b t | EInject _ t b | EWeaken _ t b | EAbsurd t b
  | EOpenEff t b | EOpenEffC t b -> kinst_ty_nil t; kinst_exp_nil b
  | ELam t r b -> kinst_ty_nil t; kinst_ty_nil r; kinst_exp_nil b
  | ETyLam k b -> kinst_kind_nil k; kinst_exp_nil b
  | ECLam cn b -> kinst_constr_nil cn; kinst_exp_nil b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    kinst_exp_nil e1; kinst_exp_nil e2
  | ELet t e1 e2 -> kinst_ty_nil t; kinst_exp_nil e1; kinst_exp_nil e2
  | ELetRec bs b -> kinst_binds_nil bs; kinst_exp_nil b
  | ECase es dt | EMatch es dt -> kinst_exps_nil es; kinst_dt_nil dt
  | ELetJoin ts t e1 e2 -> kinst_tys_nil ts; kinst_ty_nil t; kinst_exp_nil e1; kinst_exp_nil e2
  | EJump _ es -> kinst_exps_nil es
  | EPerform _ _ ts b -> kinst_tys_nil ts; kinst_exp_nil b
  | EHandle b h ->
    kinst_exp_nil b; kinst_ent_nil h.h_ent; kinst_ty_nil h.h_ret_ty;
    kinst_exp_nil h.h_ret; kinst_cls_nil h.h_clauses
  | ERegion l es b -> kinst_layout_nil l; kinst_exps_nil es; kinst_exp_nil b
  | ESpine _ sp -> kinst_spine_nil sp
  | ERegionOpen _ th b -> kinst_cells_nil th; kinst_exp_nil b
  | EOpaque _ t -> kinst_ty_nil t

and kinst_exps_nil (es: list exp) : Lemma (ensures kinst_exps [] es == es) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> kinst_exp_nil e; kinst_exps_nil es

and kinst_binds_nil (bs: list (typ & exp))
  : Lemma (ensures kinst_binds [] bs == bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> kinst_ty_nil t; kinst_exp_nil e; kinst_binds_nil bs

and kinst_cells_nil (th: list (key & exp))
  : Lemma (ensures kinst_cells [] th == th) (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> kinst_exp_nil e; kinst_cells_nil th

and kinst_spine_nil (sp: list spine_arg)
  : Lemma (ensures kinst_spine [] sp == sp) (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds kl :: sp -> kinst_kinds_nil kl; kinst_spine_nil sp
  | STy t :: sp -> kinst_ty_nil t; kinst_spine_nil sp
  | SConstr :: sp -> kinst_spine_nil sp
  | SVal v :: sp -> kinst_exp_nil v; kinst_spine_nil sp

and kinst_dt_nil (dt: dtree) : Lemma (ensures kinst_dt [] dt == dt) (decreases dt) =
  match dt with
  | DLeaf e -> kinst_exp_nil e
  | DBind _ dt -> kinst_dt_nil dt
  | DSwitchCtor _ bs df -> kinst_brs_nil bs; kinst_odt_nil df
  | DSwitchLit _ bs df -> kinst_brs_nil bs; kinst_dt_nil df
  | DSwitchKey _ bs df -> kinst_brs_nil bs; kinst_odt_nil df
  | DGuard e dt1 dt2 -> kinst_exp_nil e; kinst_dt_nil dt1; kinst_dt_nil dt2

and kinst_odt_nil (df: option dtree) : Lemma (ensures kinst_odt [] df == df) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> kinst_dt_nil dt

and kinst_brs_nil (#a: eqtype) (bs: list (a & dtree))
  : Lemma (ensures kinst_brs [] bs == bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> kinst_dt_nil dt; kinst_brs_nil bs

and kinst_cls_nil (cs: list clause) : Lemma (ensures kinst_cls [] cs == cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt b :: cs -> kinst_ty_nil s; kinst_ty_nil kt; kinst_exp_nil b; kinst_cls_nil cs
  | CFast _ _ s b :: cs -> kinst_ty_nil s; kinst_exp_nil b; kinst_cls_nil cs

let shift_ty_zero (c: nat) (t: typ) : Lemma (shift_ty c 0 t == t) =
  ren_id_ty (shift_from c 0) t

let shift_ty_exp_zero (c: nat) (e: exp) : Lemma (shift_ty_exp c 0 e == e) =
  ren_ty_exp_ext (shift_from c 0) id_ren e; ren_ty_exp_id e

let shift_tm_zero (c: nat) (e: exp) : Lemma (shift_tm c 0 e == e) =
  ren_tm_ext (shift_from c 0) id_ren e; ren_tm_id e

let shift_jp_zero (c: nat) (e: exp) : Lemma (shift_jp c 0 e == e) =
  ren_id_jp (shift_from c 0) e

let subst_shift_ty (c: nat) (ss: list typ) (t: typ)
  : Lemma (subst_ty c ss (shift_ty c (L.length ss) t) == t) =
  sub_ren_ty (upn_tsub c (list_tsub ss)) (shift_from c (L.length ss)) tvar t;
  sub_id_ty tvar t

let subst_shift_ty_exp (c: nat) (ss: list typ) (e: exp)
  : Lemma (subst_ty_exp c ss (shift_ty_exp c (L.length ss) e) == e) =
  sub_ren_ty_exp (upn_tsub c (list_tsub ss)) (shift_from c (L.length ss)) tvar e;
  sub_ty_exp_tvar e

let subst_shift_tm (c: nat) (vs: list exp) (e: exp)
  : Lemma (subst_tm c vs (shift_tm c (L.length vs) e) == e) =
  sub_ren_tm (upn_esub c (list_esub vs)) (shift_from c (L.length vs)) evar e;
  sub_tm_evar e

let subst1_shift_ty (s t: typ) : Lemma (subst1_ty s (shift_ty 0 1 t) == t) =
  sub_ren_ty (scons s tvar) (shift_from 0 1) tvar t; sub_id_ty tvar t

let subst1_shift_ty_exp (s: typ) (e: exp) : Lemma (subst1_ty_exp s (shift_ty_exp 0 1 e) == e) =
  sub_ren_ty_exp (scons s tvar) (shift_from 0 1) tvar e; sub_ty_exp_tvar e

let subst1_shift_tm (v e: exp) : Lemma (subst1_tm v (shift_tm 0 1 e) == e) =
  sub_ren_tm (scons v evar) (shift_from 0 1) evar e; sub_tm_evar e

let scons_list_tsub (s: typ)
  : Lemma (forall (i: nat). scons s tvar i == upn_tsub 0 (list_tsub [s]) i) =
  introduce forall (i: nat). scons s tvar i == upn_tsub 0 (list_tsub [s]) i
  with ren_ty_shift0 (list_tsub [s] i)

let subst1_ty_list (s t: typ) : Lemma (subst1_ty s t == subst_ty 0 [s] t) =
  scons_list_tsub s; sub_ty_ext (scons s tvar) (upn_tsub 0 (list_tsub [s])) t

let subst1_ty_exp_list (s: typ) (e: exp) : Lemma (subst1_ty_exp s e == subst_ty_exp 0 [s] e) =
  scons_list_tsub s; sub_ty_exp_ext (scons s tvar) (upn_tsub 0 (list_tsub [s])) e

let subst1_tm_list (v e: exp) : Lemma (subst1_tm v e == subst_tm 0 [v] e) =
  introduce forall (i: nat). scons v evar i == upn_esub 0 (list_esub [v]) i
  with ren_tm_shift0 (list_esub [v] i);
  sub_tm_ext (scons v evar) (upn_esub 0 (list_esub [v])) e
