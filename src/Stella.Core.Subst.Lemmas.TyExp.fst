(* Each family is one mutual induction over the term classes; the interface
   exports its `exp` and `dtree` instances. Type annotations go through the
   families of `Stella.Core.Subst.Lemmas.Typ`. *)
module Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
module L = FStar.List.Tot

let rec rinst_ty_exp (xi: ren) (sigma: tsub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_exp xi e == sub_ty_exp sigma e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> rinst_ty xi sigma t; rinst_ty xi sigma r; rinst_ty_exp xi sigma b
  | EApp e1 e2 -> rinst_ty_exp xi sigma e1; rinst_ty_exp xi sigma e2
  | ETyLam _ b -> upn_rinst_ty 1 xi sigma; rinst_ty_exp (up_ren xi) (up_tsub sigma) b
  | ETyApp b t -> rinst_ty_exp xi sigma b; rinst_ty xi sigma t
  | ECLam cn b -> rinst_constr xi sigma cn; rinst_ty_exp xi sigma b
  | ECApp b -> rinst_ty_exp xi sigma b
  | ELet t e1 e2 -> rinst_ty xi sigma t; rinst_ty_exp xi sigma e1; rinst_ty_exp xi sigma e2
  | ELetRec bs b -> rinst_ty_binds xi sigma bs; rinst_ty_exp xi sigma b
  | ECase es dt -> rinst_ty_exps xi sigma es; rinst_ty_dt xi sigma dt
  | ELetJoin ts t e1 e2 ->
    rinst_tys xi sigma ts; rinst_ty xi sigma t; rinst_ty_exp xi sigma e1; rinst_ty_exp xi sigma e2
  | EJump _ es -> rinst_ty_exps xi sigma es
  | EExtend _ e1 e2 -> rinst_ty_exp xi sigma e1; rinst_ty_exp xi sigma e2
  | ESelect _ b -> rinst_ty_exp xi sigma b
  | ERestrict _ b -> rinst_ty_exp xi sigma b
  | EUpdate _ e1 e2 -> rinst_ty_exp xi sigma e1; rinst_ty_exp xi sigma e2
  | EMerge e1 e2 -> rinst_ty_exp xi sigma e1; rinst_ty_exp xi sigma e2
  | EInject _ t b -> rinst_ty xi sigma t; rinst_ty_exp xi sigma b
  | EWeaken _ t b -> rinst_ty xi sigma t; rinst_ty_exp xi sigma b
  | EAbsurd t b -> rinst_ty xi sigma t; rinst_ty_exp xi sigma b
  | EPerform _ _ ts b -> rinst_tys xi sigma ts; rinst_ty_exp xi sigma b
  | EHandle b h ->
    rinst_ty_exp xi sigma b; rinst_ent xi sigma h.h_ent; rinst_ty xi sigma h.h_ret_ty;
    rinst_ty_exp xi sigma h.h_ret; rinst_ty_cls xi sigma h.h_clauses
  | EOpenEff t b -> rinst_ty xi sigma t; rinst_ty_exp xi sigma b
  | ERegion l es b -> rinst_layout xi sigma l; rinst_ty_exps xi sigma es; rinst_ty_exp xi sigma b
  | EWriteCell _ _ b -> rinst_ty_exp xi sigma b
  | EMatch th dt -> rinst_ty_exps xi sigma th; rinst_ty_dt xi sigma dt
  | EOpenEffC t b -> rinst_ty xi sigma t; rinst_ty_exp xi sigma b
  | EFill _ b -> rinst_ty_exp xi sigma b
  | ERegionOpen _ th b -> rinst_ty_cells xi sigma th; rinst_ty_exp xi sigma b
  | EOpaque _ t -> rinst_ty xi sigma t

and rinst_ty_exps (xi: ren) (sigma: tsub) (es: list exp)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_exps xi es == sub_ty_exps sigma es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> rinst_ty_exp xi sigma e; rinst_ty_exps xi sigma es

and rinst_ty_binds (xi: ren) (sigma: tsub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_binds xi bs == sub_ty_binds sigma bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> rinst_ty xi sigma t; rinst_ty_exp xi sigma e; rinst_ty_binds xi sigma bs

and rinst_ty_cells (xi: ren) (sigma: tsub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_cells xi th == sub_ty_cells sigma th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> rinst_ty_exp xi sigma e; rinst_ty_cells xi sigma th

and rinst_ty_dt (xi: ren) (sigma: tsub) (dt: dtree)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_dt xi dt == sub_ty_dt sigma dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> rinst_ty_exp xi sigma e
  | DBind _ dt -> rinst_ty_dt xi sigma dt
  | DSwitchCtor _ bs df -> rinst_ty_brs xi sigma bs; rinst_ty_odt xi sigma df
  | DSwitchLit _ bs df -> rinst_ty_brs xi sigma bs; rinst_ty_dt xi sigma df
  | DSwitchKey _ bs df -> rinst_ty_brs xi sigma bs; rinst_ty_odt xi sigma df
  | DGuard e dt1 dt2 -> rinst_ty_exp xi sigma e; rinst_ty_dt xi sigma dt1; rinst_ty_dt xi sigma dt2

and rinst_ty_odt (xi: ren) (sigma: tsub) (df: option dtree)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_odt xi df == sub_ty_odt sigma df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> rinst_ty_dt xi sigma dt

and rinst_ty_brs (#lb: eqtype) (xi: ren) (sigma: tsub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_brs xi bs == sub_ty_brs sigma bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rinst_ty_dt xi sigma dt; rinst_ty_brs xi sigma bs

and rinst_ty_cls (xi: ren) (sigma: tsub) (cs: list clause)
  : Lemma (requires forall (i: nat). sigma i == TVar (xi i))
          (ensures ren_ty_cls xi cs == sub_ty_cls sigma cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb s kt b :: cs ->
    upn_rinst_ty nb xi sigma; rinst_ty (upn_ren nb xi) (upn_tsub nb sigma) s;
    rinst_ty (upn_ren nb xi) (upn_tsub nb sigma) kt;
    rinst_ty_exp (upn_ren nb xi) (upn_tsub nb sigma) b; rinst_ty_cls xi sigma cs
  | CFast _ nb s b :: cs ->
    upn_rinst_ty nb xi sigma; rinst_ty (upn_ren nb xi) (upn_tsub nb sigma) s;
    rinst_ty_exp (upn_ren nb xi) (upn_tsub nb sigma) b; rinst_ty_cls xi sigma cs

let rec sub_sub_ty_exp (tau: tsub) (sigma: tsub) (theta: tsub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_exp tau (sub_ty_exp sigma e) == sub_ty_exp theta e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b ->
    sub_sub_ty tau sigma theta t; sub_sub_ty tau sigma theta r; sub_sub_ty_exp tau sigma theta b
  | EApp e1 e2 -> sub_sub_ty_exp tau sigma theta e1; sub_sub_ty_exp tau sigma theta e2
  | ETyLam _ b ->
    upn_sub_sub_ty 1 tau sigma theta;
    sub_sub_ty_exp (up_tsub tau) (up_tsub sigma) (up_tsub theta) b
  | ETyApp b t -> sub_sub_ty_exp tau sigma theta b; sub_sub_ty tau sigma theta t
  | ECLam cn b -> sub_sub_constr tau sigma theta cn; sub_sub_ty_exp tau sigma theta b
  | ECApp b -> sub_sub_ty_exp tau sigma theta b
  | ELet t e1 e2 ->
    sub_sub_ty tau sigma theta t; sub_sub_ty_exp tau sigma theta e1;
    sub_sub_ty_exp tau sigma theta e2
  | ELetRec bs b -> sub_sub_ty_binds tau sigma theta bs; sub_sub_ty_exp tau sigma theta b
  | ECase es dt -> sub_sub_ty_exps tau sigma theta es; sub_sub_ty_dt tau sigma theta dt
  | ELetJoin ts t e1 e2 ->
    sub_sub_tys tau sigma theta ts; sub_sub_ty tau sigma theta t; sub_sub_ty_exp tau sigma theta e1;
    sub_sub_ty_exp tau sigma theta e2
  | EJump _ es -> sub_sub_ty_exps tau sigma theta es
  | EExtend _ e1 e2 -> sub_sub_ty_exp tau sigma theta e1; sub_sub_ty_exp tau sigma theta e2
  | ESelect _ b -> sub_sub_ty_exp tau sigma theta b
  | ERestrict _ b -> sub_sub_ty_exp tau sigma theta b
  | EUpdate _ e1 e2 -> sub_sub_ty_exp tau sigma theta e1; sub_sub_ty_exp tau sigma theta e2
  | EMerge e1 e2 -> sub_sub_ty_exp tau sigma theta e1; sub_sub_ty_exp tau sigma theta e2
  | EInject _ t b -> sub_sub_ty tau sigma theta t; sub_sub_ty_exp tau sigma theta b
  | EWeaken _ t b -> sub_sub_ty tau sigma theta t; sub_sub_ty_exp tau sigma theta b
  | EAbsurd t b -> sub_sub_ty tau sigma theta t; sub_sub_ty_exp tau sigma theta b
  | EPerform _ _ ts b -> sub_sub_tys tau sigma theta ts; sub_sub_ty_exp tau sigma theta b
  | EHandle b h ->
    sub_sub_ty_exp tau sigma theta b; sub_sub_ent tau sigma theta h.h_ent;
    sub_sub_ty tau sigma theta h.h_ret_ty; sub_sub_ty_exp tau sigma theta h.h_ret;
    sub_sub_ty_cls tau sigma theta h.h_clauses
  | EOpenEff t b -> sub_sub_ty tau sigma theta t; sub_sub_ty_exp tau sigma theta b
  | ERegion l es b ->
    sub_sub_layout tau sigma theta l; sub_sub_ty_exps tau sigma theta es;
    sub_sub_ty_exp tau sigma theta b
  | EWriteCell _ _ b -> sub_sub_ty_exp tau sigma theta b
  | EMatch th dt -> sub_sub_ty_exps tau sigma theta th; sub_sub_ty_dt tau sigma theta dt
  | EOpenEffC t b -> sub_sub_ty tau sigma theta t; sub_sub_ty_exp tau sigma theta b
  | EFill _ b -> sub_sub_ty_exp tau sigma theta b
  | ERegionOpen _ th b -> sub_sub_ty_cells tau sigma theta th; sub_sub_ty_exp tau sigma theta b
  | EOpaque _ t -> sub_sub_ty tau sigma theta t

and sub_sub_ty_exps (tau: tsub) (sigma: tsub) (theta: tsub) (es: list exp)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_exps tau (sub_ty_exps sigma es) == sub_ty_exps theta es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> sub_sub_ty_exp tau sigma theta e; sub_sub_ty_exps tau sigma theta es

and sub_sub_ty_binds (tau: tsub) (sigma: tsub) (theta: tsub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_binds tau (sub_ty_binds sigma bs) == sub_ty_binds theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs ->
    sub_sub_ty tau sigma theta t; sub_sub_ty_exp tau sigma theta e;
    sub_sub_ty_binds tau sigma theta bs

and sub_sub_ty_cells (tau: tsub) (sigma: tsub) (theta: tsub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_cells tau (sub_ty_cells sigma th) == sub_ty_cells theta th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> sub_sub_ty_exp tau sigma theta e; sub_sub_ty_cells tau sigma theta th

and sub_sub_ty_dt (tau: tsub) (sigma: tsub) (theta: tsub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_dt tau (sub_ty_dt sigma dt) == sub_ty_dt theta dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> sub_sub_ty_exp tau sigma theta e
  | DBind _ dt -> sub_sub_ty_dt tau sigma theta dt
  | DSwitchCtor _ bs df -> sub_sub_ty_brs tau sigma theta bs; sub_sub_ty_odt tau sigma theta df
  | DSwitchLit _ bs df -> sub_sub_ty_brs tau sigma theta bs; sub_sub_ty_dt tau sigma theta df
  | DSwitchKey _ bs df -> sub_sub_ty_brs tau sigma theta bs; sub_sub_ty_odt tau sigma theta df
  | DGuard e dt1 dt2 ->
    sub_sub_ty_exp tau sigma theta e; sub_sub_ty_dt tau sigma theta dt1;
    sub_sub_ty_dt tau sigma theta dt2

and sub_sub_ty_odt (tau: tsub) (sigma: tsub) (theta: tsub) (df: option dtree)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_odt tau (sub_ty_odt sigma df) == sub_ty_odt theta df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> sub_sub_ty_dt tau sigma theta dt

and sub_sub_ty_brs (#lb: eqtype) (tau: tsub) (sigma: tsub) (theta: tsub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_brs tau (sub_ty_brs sigma bs) == sub_ty_brs theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> sub_sub_ty_dt tau sigma theta dt; sub_sub_ty_brs tau sigma theta bs

and sub_sub_ty_cls (tau: tsub) (sigma: tsub) (theta: tsub) (cs: list clause)
  : Lemma (requires forall (i: nat). theta i == sub_ty tau (sigma i))
          (ensures sub_ty_cls tau (sub_ty_cls sigma cs) == sub_ty_cls theta cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb s kt b :: cs ->
    upn_sub_sub_ty nb tau sigma theta;
    sub_sub_ty (upn_tsub nb tau) (upn_tsub nb sigma) (upn_tsub nb theta) s;
    sub_sub_ty (upn_tsub nb tau) (upn_tsub nb sigma) (upn_tsub nb theta) kt;
    sub_sub_ty_exp (upn_tsub nb tau) (upn_tsub nb sigma) (upn_tsub nb theta) b;
    sub_sub_ty_cls tau sigma theta cs
  | CFast _ nb s b :: cs ->
    upn_sub_sub_ty nb tau sigma theta;
    sub_sub_ty (upn_tsub nb tau) (upn_tsub nb sigma) (upn_tsub nb theta) s;
    sub_sub_ty_exp (upn_tsub nb tau) (upn_tsub nb sigma) (upn_tsub nb theta) b;
    sub_sub_ty_cls tau sigma theta cs

let rec sub_id_ty_exp (sigma: tsub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_exp sigma e == e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> sub_id_ty sigma t; sub_id_ty sigma r; sub_id_ty_exp sigma b
  | EApp e1 e2 -> sub_id_ty_exp sigma e1; sub_id_ty_exp sigma e2
  | ETyLam _ b -> upn_sub_id_ty 1 sigma; sub_id_ty_exp (up_tsub sigma) b
  | ETyApp b t -> sub_id_ty_exp sigma b; sub_id_ty sigma t
  | ECLam cn b -> sub_id_constr sigma cn; sub_id_ty_exp sigma b
  | ECApp b -> sub_id_ty_exp sigma b
  | ELet t e1 e2 -> sub_id_ty sigma t; sub_id_ty_exp sigma e1; sub_id_ty_exp sigma e2
  | ELetRec bs b -> sub_id_ty_binds sigma bs; sub_id_ty_exp sigma b
  | ECase es dt -> sub_id_ty_exps sigma es; sub_id_ty_dt sigma dt
  | ELetJoin ts t e1 e2 ->
    sub_id_tys sigma ts; sub_id_ty sigma t; sub_id_ty_exp sigma e1; sub_id_ty_exp sigma e2
  | EJump _ es -> sub_id_ty_exps sigma es
  | EExtend _ e1 e2 -> sub_id_ty_exp sigma e1; sub_id_ty_exp sigma e2
  | ESelect _ b -> sub_id_ty_exp sigma b
  | ERestrict _ b -> sub_id_ty_exp sigma b
  | EUpdate _ e1 e2 -> sub_id_ty_exp sigma e1; sub_id_ty_exp sigma e2
  | EMerge e1 e2 -> sub_id_ty_exp sigma e1; sub_id_ty_exp sigma e2
  | EInject _ t b -> sub_id_ty sigma t; sub_id_ty_exp sigma b
  | EWeaken _ t b -> sub_id_ty sigma t; sub_id_ty_exp sigma b
  | EAbsurd t b -> sub_id_ty sigma t; sub_id_ty_exp sigma b
  | EPerform _ _ ts b -> sub_id_tys sigma ts; sub_id_ty_exp sigma b
  | EHandle b h ->
    sub_id_ty_exp sigma b; sub_id_ent sigma h.h_ent; sub_id_ty sigma h.h_ret_ty;
    sub_id_ty_exp sigma h.h_ret; sub_id_ty_cls sigma h.h_clauses
  | EOpenEff t b -> sub_id_ty sigma t; sub_id_ty_exp sigma b
  | ERegion l es b -> sub_id_layout sigma l; sub_id_ty_exps sigma es; sub_id_ty_exp sigma b
  | EWriteCell _ _ b -> sub_id_ty_exp sigma b
  | EMatch th dt -> sub_id_ty_exps sigma th; sub_id_ty_dt sigma dt
  | EOpenEffC t b -> sub_id_ty sigma t; sub_id_ty_exp sigma b
  | EFill _ b -> sub_id_ty_exp sigma b
  | ERegionOpen _ th b -> sub_id_ty_cells sigma th; sub_id_ty_exp sigma b
  | EOpaque _ t -> sub_id_ty sigma t

and sub_id_ty_exps (sigma: tsub) (es: list exp)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_exps sigma es == es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> sub_id_ty_exp sigma e; sub_id_ty_exps sigma es

and sub_id_ty_binds (sigma: tsub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_binds sigma bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> sub_id_ty sigma t; sub_id_ty_exp sigma e; sub_id_ty_binds sigma bs

and sub_id_ty_cells (sigma: tsub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_cells sigma th == th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> sub_id_ty_exp sigma e; sub_id_ty_cells sigma th

and sub_id_ty_dt (sigma: tsub) (dt: dtree)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_dt sigma dt == dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> sub_id_ty_exp sigma e
  | DBind _ dt -> sub_id_ty_dt sigma dt
  | DSwitchCtor _ bs df -> sub_id_ty_brs sigma bs; sub_id_ty_odt sigma df
  | DSwitchLit _ bs df -> sub_id_ty_brs sigma bs; sub_id_ty_dt sigma df
  | DSwitchKey _ bs df -> sub_id_ty_brs sigma bs; sub_id_ty_odt sigma df
  | DGuard e dt1 dt2 -> sub_id_ty_exp sigma e; sub_id_ty_dt sigma dt1; sub_id_ty_dt sigma dt2

and sub_id_ty_odt (sigma: tsub) (df: option dtree)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_odt sigma df == df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> sub_id_ty_dt sigma dt

and sub_id_ty_brs (#lb: eqtype) (sigma: tsub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_brs sigma bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> sub_id_ty_dt sigma dt; sub_id_ty_brs sigma bs

and sub_id_ty_cls (sigma: tsub) (cs: list clause)
  : Lemma (requires forall (i: nat). sigma i == TVar i)
          (ensures sub_ty_cls sigma cs == cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb s kt b :: cs ->
    upn_sub_id_ty nb sigma; sub_id_ty (upn_tsub nb sigma) s; sub_id_ty (upn_tsub nb sigma) kt;
    sub_id_ty_exp (upn_tsub nb sigma) b; sub_id_ty_cls sigma cs
  | CFast _ nb s b :: cs ->
    upn_sub_id_ty nb sigma; sub_id_ty (upn_tsub nb sigma) s; sub_id_ty_exp (upn_tsub nb sigma) b;
    sub_id_ty_cls sigma cs

let ren_ty_exp_as_sub (xi: ren) (e: exp)
  : Lemma (ren_ty_exp xi e == sub_ty_exp (ren_tsub xi) e) =
  rinst_ty_exp xi (ren_tsub xi) e

let sub_ty_exp_ext (sigma sigma': tsub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == sigma' i)
          (ensures sub_ty_exp sigma e == sub_ty_exp sigma' e) =
  sub_sub_ty_exp sigma' tvar sigma e; sub_id_ty_exp tvar e

let ren_ty_exp_ext (xi xi': ren) (e: exp)
  : Lemma (requires forall (i: nat). xi i == xi' i)
          (ensures ren_ty_exp xi e == ren_ty_exp xi' e) =
  ren_ty_exp_as_sub xi e; ren_ty_exp_as_sub xi' e;
  sub_ty_exp_ext (ren_tsub xi) (ren_tsub xi') e

let sub_ty_exp_tvar (e: exp) : Lemma (sub_ty_exp tvar e == e) = sub_id_ty_exp tvar e

let ren_ty_exp_id (e: exp) : Lemma (ren_ty_exp id_ren e == e) =
  ren_ty_exp_as_sub id_ren e; sub_id_ty_exp (ren_tsub id_ren) e

let ren_ty_exp_shift0 (e: exp) : Lemma (ren_ty_exp (shift 0) e == e) =
  ren_ty_exp_as_sub (shift 0) e; sub_id_ty_exp (ren_tsub (shift 0)) e

let ren_ren_ty_exp (xi zeta theta: ren) (e: exp)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_ty_exp xi (ren_ty_exp zeta e) == ren_ty_exp theta e) =
  ren_ty_exp_as_sub zeta e;
  ren_ty_exp_as_sub xi (ren_ty_exp zeta e);
  ren_ty_exp_as_sub theta e;
  sub_sub_ty_exp (ren_tsub xi) (ren_tsub zeta) (ren_tsub theta) e

let sub_ren_ty_exp (sigma: tsub) (xi: ren) (theta: tsub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_ty_exp sigma (ren_ty_exp xi e) == sub_ty_exp theta e) =
  ren_ty_exp_as_sub xi e;
  sub_sub_ty_exp sigma (ren_tsub xi) theta e

let ren_sub_ty_exp (xi: ren) (sigma theta: tsub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == ren_ty xi (sigma i))
          (ensures ren_ty_exp xi (sub_ty_exp sigma e) == sub_ty_exp theta e) =
  ren_ty_exp_as_sub xi (sub_ty_exp sigma e);
  introduce forall (i: nat). theta i == sub_ty (ren_tsub xi) (sigma i)
  with rinst_ty xi (ren_tsub xi) (sigma i);
  sub_sub_ty_exp (ren_tsub xi) sigma theta e

let sub_ty_exp_shift (m: nat) (sigma: tsub) (e: exp)
  : Lemma (ren_ty_exp (shift m) (sub_ty_exp sigma e)
           == sub_ty_exp (upn_tsub m sigma) (ren_ty_exp (shift m) e)) =
  ren_sub_ty_exp (shift m) sigma (tsub_shift m sigma) e;
  sub_ren_ty_exp (upn_tsub m sigma) (shift m) (tsub_shift m sigma) e

let ren_ty_exp_shift (m: nat) (xi: ren) (e: exp)
  : Lemma (ren_ty_exp (shift m) (ren_ty_exp xi e)
           == ren_ty_exp (upn_ren m xi) (ren_ty_exp (shift m) e)) =
  ren_ren_ty_exp (shift m) xi (ren_shift m xi) e;
  ren_ren_ty_exp (upn_ren m xi) (shift m) (ren_shift m xi) e
