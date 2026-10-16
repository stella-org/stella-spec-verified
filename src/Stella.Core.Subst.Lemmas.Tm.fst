(* Each family is one mutual induction over the term classes; the interface
   exports its `exp` and `dtree` instances. Before a family come its lifting
   lemmas: `upn_*`, `tyup_*` and `jup_*` re-establish the hypothesis under
   term, type and join binders. *)
module Stella.Core.Subst.Lemmas.Tm
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
module L = FStar.List.Tot

(* `σ >> ren_tm ↑n` *)
let esub_shift (n: nat) (sigma: esub) (k: nat) : exp = ren_tm (shift n) (sigma k)

let rec ren_ren_jp (xi: ren) (zeta: ren) (theta: ren) (e: exp)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp xi (ren_jp zeta e) == ren_jp theta e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> ren_ren_jp xi zeta theta b
  | EApp e1 e2 -> ren_ren_jp xi zeta theta e1; ren_ren_jp xi zeta theta e2
  | ETyLam _ b -> ren_ren_jp xi zeta theta b
  | ETyApp b _ -> ren_ren_jp xi zeta theta b
  | ECLam _ b -> ren_ren_jp xi zeta theta b
  | ECApp b -> ren_ren_jp xi zeta theta b
  | ELet _ e1 e2 -> ren_ren_jp xi zeta theta e1; ren_ren_jp xi zeta theta e2
  | ELetRec bs b -> ren_ren_jp_binds xi zeta theta bs; ren_ren_jp xi zeta theta b
  | ECase es dt -> ren_ren_jp_exps xi zeta theta es; ren_ren_jp_dt xi zeta theta dt
  | ELetJoin _ _ e1 e2 ->
    upn_ren_comp 1 xi zeta theta; ren_ren_jp (up_ren xi) (up_ren zeta) (up_ren theta) e1;
    ren_ren_jp (up_ren xi) (up_ren zeta) (up_ren theta) e2
  | EJump _ es -> ren_ren_jp_exps xi zeta theta es
  | EExtend _ e1 e2 -> ren_ren_jp xi zeta theta e1; ren_ren_jp xi zeta theta e2
  | ESelect _ b -> ren_ren_jp xi zeta theta b
  | ERestrict _ b -> ren_ren_jp xi zeta theta b
  | EUpdate _ e1 e2 -> ren_ren_jp xi zeta theta e1; ren_ren_jp xi zeta theta e2
  | EMerge e1 e2 -> ren_ren_jp xi zeta theta e1; ren_ren_jp xi zeta theta e2
  | EInject _ _ b -> ren_ren_jp xi zeta theta b
  | EWeaken _ _ b -> ren_ren_jp xi zeta theta b
  | EAbsurd _ b -> ren_ren_jp xi zeta theta b
  | EPerform _ _ _ b -> ren_ren_jp xi zeta theta b
  | EHandle b h ->
    ren_ren_jp xi zeta theta b; ren_ren_jp xi zeta theta h.h_ret;
    ren_ren_jp_cls xi zeta theta h.h_clauses
  | EOpenEff _ b -> ren_ren_jp xi zeta theta b
  | ERegion _ es b -> ren_ren_jp_exps xi zeta theta es; ren_ren_jp xi zeta theta b
  | EWriteCell _ _ b -> ren_ren_jp xi zeta theta b
  | ESpine _ sp -> ren_ren_jp_spine xi zeta theta sp
  | EMatch th dt -> ren_ren_jp_exps xi zeta theta th; ren_ren_jp_dt xi zeta theta dt
  | EOpenEffC _ b -> ren_ren_jp xi zeta theta b
  | EFill _ b -> ren_ren_jp xi zeta theta b
  | ERegionOpen _ th b -> ren_ren_jp_cells xi zeta theta th; ren_ren_jp xi zeta theta b

and ren_ren_jp_exps (xi: ren) (zeta: ren) (theta: ren) (es: list exp)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp_exps xi (ren_jp_exps zeta es) == ren_jp_exps theta es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ren_ren_jp xi zeta theta e; ren_ren_jp_exps xi zeta theta es

and ren_ren_jp_binds (xi: ren) (zeta: ren) (theta: ren) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp_binds xi (ren_jp_binds zeta bs) == ren_jp_binds theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> ren_ren_jp xi zeta theta e; ren_ren_jp_binds xi zeta theta bs

and ren_ren_jp_cells (xi: ren) (zeta: ren) (theta: ren) (th: list (key & exp))
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp_cells xi (ren_jp_cells zeta th) == ren_jp_cells theta th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> ren_ren_jp xi zeta theta e; ren_ren_jp_cells xi zeta theta th

and ren_ren_jp_spine (xi: ren) (zeta: ren) (theta: ren) (sp: list spine_arg)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp_spine xi (ren_jp_spine zeta sp) == ren_jp_spine theta sp)
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> ren_ren_jp_spine xi zeta theta sp
  | STy _ :: sp -> ren_ren_jp_spine xi zeta theta sp
  | SConstr :: sp -> ren_ren_jp_spine xi zeta theta sp
  | SVal v :: sp -> ren_ren_jp xi zeta theta v; ren_ren_jp_spine xi zeta theta sp

and ren_ren_jp_dt (xi: ren) (zeta: ren) (theta: ren) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp_dt xi (ren_jp_dt zeta dt) == ren_jp_dt theta dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> ren_ren_jp xi zeta theta e
  | DBind _ dt -> ren_ren_jp_dt xi zeta theta dt
  | DSwitchCtor _ bs df -> ren_ren_jp_brs xi zeta theta bs; ren_ren_jp_odt xi zeta theta df
  | DSwitchLit _ bs df -> ren_ren_jp_brs xi zeta theta bs; ren_ren_jp_dt xi zeta theta df
  | DSwitchKey _ bs df -> ren_ren_jp_brs xi zeta theta bs; ren_ren_jp_odt xi zeta theta df
  | DGuard e dt1 dt2 ->
    ren_ren_jp xi zeta theta e; ren_ren_jp_dt xi zeta theta dt1; ren_ren_jp_dt xi zeta theta dt2

and ren_ren_jp_odt (xi: ren) (zeta: ren) (theta: ren) (df: option dtree)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp_odt xi (ren_jp_odt zeta df) == ren_jp_odt theta df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ren_ren_jp_dt xi zeta theta dt

and ren_ren_jp_brs (#lb: eqtype) (xi: ren) (zeta: ren) (theta: ren) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp_brs xi (ren_jp_brs zeta bs) == ren_jp_brs theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> ren_ren_jp_dt xi zeta theta dt; ren_ren_jp_brs xi zeta theta bs

and ren_ren_jp_cls (xi: ren) (zeta: ren) (theta: ren) (cs: list clause)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_jp_cls xi (ren_jp_cls zeta cs) == ren_jp_cls theta cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> ren_ren_jp xi zeta theta b; ren_ren_jp_cls xi zeta theta cs
  | CFast _ _ _ b :: cs -> ren_ren_jp xi zeta theta b; ren_ren_jp_cls xi zeta theta cs

let rec ren_id_jp (xi: ren) (e: exp)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp xi e == e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> ren_id_jp xi b
  | EApp e1 e2 -> ren_id_jp xi e1; ren_id_jp xi e2
  | ETyLam _ b -> ren_id_jp xi b
  | ETyApp b _ -> ren_id_jp xi b
  | ECLam _ b -> ren_id_jp xi b
  | ECApp b -> ren_id_jp xi b
  | ELet _ e1 e2 -> ren_id_jp xi e1; ren_id_jp xi e2
  | ELetRec bs b -> ren_id_jp_binds xi bs; ren_id_jp xi b
  | ECase es dt -> ren_id_jp_exps xi es; ren_id_jp_dt xi dt
  | ELetJoin _ _ e1 e2 -> upn_ren_id 1 xi; ren_id_jp (up_ren xi) e1; ren_id_jp (up_ren xi) e2
  | EJump _ es -> ren_id_jp_exps xi es
  | EExtend _ e1 e2 -> ren_id_jp xi e1; ren_id_jp xi e2
  | ESelect _ b -> ren_id_jp xi b
  | ERestrict _ b -> ren_id_jp xi b
  | EUpdate _ e1 e2 -> ren_id_jp xi e1; ren_id_jp xi e2
  | EMerge e1 e2 -> ren_id_jp xi e1; ren_id_jp xi e2
  | EInject _ _ b -> ren_id_jp xi b
  | EWeaken _ _ b -> ren_id_jp xi b
  | EAbsurd _ b -> ren_id_jp xi b
  | EPerform _ _ _ b -> ren_id_jp xi b
  | EHandle b h -> ren_id_jp xi b; ren_id_jp xi h.h_ret; ren_id_jp_cls xi h.h_clauses
  | EOpenEff _ b -> ren_id_jp xi b
  | ERegion _ es b -> ren_id_jp_exps xi es; ren_id_jp xi b
  | EWriteCell _ _ b -> ren_id_jp xi b
  | ESpine _ sp -> ren_id_jp_spine xi sp
  | EMatch th dt -> ren_id_jp_exps xi th; ren_id_jp_dt xi dt
  | EOpenEffC _ b -> ren_id_jp xi b
  | EFill _ b -> ren_id_jp xi b
  | ERegionOpen _ th b -> ren_id_jp_cells xi th; ren_id_jp xi b

and ren_id_jp_exps (xi: ren) (es: list exp)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp_exps xi es == es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ren_id_jp xi e; ren_id_jp_exps xi es

and ren_id_jp_binds (xi: ren) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp_binds xi bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> ren_id_jp xi e; ren_id_jp_binds xi bs

and ren_id_jp_cells (xi: ren) (th: list (key & exp))
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp_cells xi th == th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> ren_id_jp xi e; ren_id_jp_cells xi th

and ren_id_jp_spine (xi: ren) (sp: list spine_arg)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp_spine xi sp == sp)
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> ren_id_jp_spine xi sp
  | STy _ :: sp -> ren_id_jp_spine xi sp
  | SConstr :: sp -> ren_id_jp_spine xi sp
  | SVal v :: sp -> ren_id_jp xi v; ren_id_jp_spine xi sp

and ren_id_jp_dt (xi: ren) (dt: dtree)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp_dt xi dt == dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> ren_id_jp xi e
  | DBind _ dt -> ren_id_jp_dt xi dt
  | DSwitchCtor _ bs df -> ren_id_jp_brs xi bs; ren_id_jp_odt xi df
  | DSwitchLit _ bs df -> ren_id_jp_brs xi bs; ren_id_jp_dt xi df
  | DSwitchKey _ bs df -> ren_id_jp_brs xi bs; ren_id_jp_odt xi df
  | DGuard e dt1 dt2 -> ren_id_jp xi e; ren_id_jp_dt xi dt1; ren_id_jp_dt xi dt2

and ren_id_jp_odt (xi: ren) (df: option dtree)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp_odt xi df == df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ren_id_jp_dt xi dt

and ren_id_jp_brs (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp_brs xi bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> ren_id_jp_dt xi dt; ren_id_jp_brs xi bs

and ren_id_jp_cls (xi: ren) (cs: list clause)
  : Lemma (requires forall (i: nat). xi i == i)
          (ensures ren_jp_cls xi cs == cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> ren_id_jp xi b; ren_id_jp_cls xi cs
  | CFast _ _ _ b :: cs -> ren_id_jp xi b; ren_id_jp_cls xi cs

let ren_jp_ext (xi xi': ren) (e: exp)
  : Lemma (requires forall (i: nat). xi i == xi' i) (ensures ren_jp xi e == ren_jp xi' e) =
  ren_ren_jp xi' id_ren xi e; ren_id_jp id_ren e

let ren_jp_id (e: exp) : Lemma (ren_jp id_ren e == e) = ren_id_jp id_ren e

let rec sub_ty_ren_tm (sigma: tsub) (xi: ren) (e: exp)
  : Lemma (ensures sub_ty_exp sigma (ren_tm xi e) == ren_tm xi (sub_ty_exp sigma e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> sub_ty_ren_tm sigma (up_ren xi) b
  | EApp e1 e2 -> sub_ty_ren_tm sigma xi e1; sub_ty_ren_tm sigma xi e2
  | ETyLam _ b -> sub_ty_ren_tm (up_tsub sigma) xi b
  | ETyApp b _ -> sub_ty_ren_tm sigma xi b
  | ECLam _ b -> sub_ty_ren_tm sigma xi b
  | ECApp b -> sub_ty_ren_tm sigma xi b
  | ELet _ e1 e2 -> sub_ty_ren_tm sigma xi e1; sub_ty_ren_tm sigma (up_ren xi) e2
  | ELetRec bs b ->
    sub_ty_ren_tm_binds sigma (upn_ren (L.length bs) xi) bs;
    sub_ty_ren_tm sigma (upn_ren (L.length bs) xi) b
  | ECase es dt -> sub_ty_ren_tm_exps sigma xi es; sub_ty_ren_tm_dt sigma xi dt
  | ELetJoin ts _ e1 e2 ->
    sub_ty_ren_tm sigma (upn_ren (L.length ts) xi) e1; sub_ty_ren_tm sigma xi e2
  | EJump _ es -> sub_ty_ren_tm_exps sigma xi es
  | EExtend _ e1 e2 -> sub_ty_ren_tm sigma xi e1; sub_ty_ren_tm sigma xi e2
  | ESelect _ b -> sub_ty_ren_tm sigma xi b
  | ERestrict _ b -> sub_ty_ren_tm sigma xi b
  | EUpdate _ e1 e2 -> sub_ty_ren_tm sigma xi e1; sub_ty_ren_tm sigma xi e2
  | EMerge e1 e2 -> sub_ty_ren_tm sigma xi e1; sub_ty_ren_tm sigma xi e2
  | EInject _ _ b -> sub_ty_ren_tm sigma xi b
  | EWeaken _ _ b -> sub_ty_ren_tm sigma xi b
  | EAbsurd _ b -> sub_ty_ren_tm sigma xi b
  | EPerform _ _ _ b -> sub_ty_ren_tm sigma xi b
  | EHandle b h ->
    sub_ty_ren_tm sigma xi b; sub_ty_ren_tm sigma (up_ren xi) h.h_ret;
    sub_ty_ren_tm_cls sigma xi h.h_clauses
  | EOpenEff _ b -> sub_ty_ren_tm sigma xi b
  | ERegion _ es b -> sub_ty_ren_tm_exps sigma xi es; sub_ty_ren_tm sigma xi b
  | EWriteCell _ _ b -> sub_ty_ren_tm sigma xi b
  | ESpine _ sp -> sub_ty_ren_tm_spine sigma xi sp
  | EMatch th dt -> sub_ty_ren_tm_exps sigma xi th; sub_ty_ren_tm_dt sigma xi dt
  | EOpenEffC _ b -> sub_ty_ren_tm sigma xi b
  | EFill _ b -> sub_ty_ren_tm sigma xi b
  | ERegionOpen _ th b -> sub_ty_ren_tm_cells sigma xi th; sub_ty_ren_tm sigma xi b

and sub_ty_ren_tm_exps (sigma: tsub) (xi: ren) (es: list exp)
  : Lemma (ensures sub_ty_exps sigma (ren_tm_exps xi es) == ren_tm_exps xi (sub_ty_exps sigma es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> sub_ty_ren_tm sigma xi e; sub_ty_ren_tm_exps sigma xi es

and sub_ty_ren_tm_binds (sigma: tsub) (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures sub_ty_binds sigma (ren_tm_binds xi bs)
                     == ren_tm_binds xi (sub_ty_binds sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> sub_ty_ren_tm sigma xi e; sub_ty_ren_tm_binds sigma xi bs

and sub_ty_ren_tm_cells (sigma: tsub) (xi: ren) (th: list (key & exp))
  : Lemma (ensures sub_ty_cells sigma (ren_tm_cells xi th)
                     == ren_tm_cells xi (sub_ty_cells sigma th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> sub_ty_ren_tm sigma xi e; sub_ty_ren_tm_cells sigma xi th

and sub_ty_ren_tm_spine (sigma: tsub) (xi: ren) (sp: list spine_arg)
  : Lemma (ensures sub_ty_spine sigma (ren_tm_spine xi sp)
                     == ren_tm_spine xi (sub_ty_spine sigma sp))
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> sub_ty_ren_tm_spine sigma xi sp
  | STy _ :: sp -> sub_ty_ren_tm_spine sigma xi sp
  | SConstr :: sp -> sub_ty_ren_tm_spine sigma xi sp
  | SVal v :: sp -> sub_ty_ren_tm sigma xi v; sub_ty_ren_tm_spine sigma xi sp

and sub_ty_ren_tm_dt (sigma: tsub) (xi: ren) (dt: dtree)
  : Lemma (ensures sub_ty_dt sigma (ren_tm_dt xi dt) == ren_tm_dt xi (sub_ty_dt sigma dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> sub_ty_ren_tm sigma xi e
  | DBind _ dt -> sub_ty_ren_tm_dt sigma (up_ren xi) dt
  | DSwitchCtor _ bs df -> sub_ty_ren_tm_brs sigma xi bs; sub_ty_ren_tm_odt sigma xi df
  | DSwitchLit _ bs df -> sub_ty_ren_tm_brs sigma xi bs; sub_ty_ren_tm_dt sigma xi df
  | DSwitchKey _ bs df -> sub_ty_ren_tm_brs sigma xi bs; sub_ty_ren_tm_odt sigma xi df
  | DGuard e dt1 dt2 ->
    sub_ty_ren_tm sigma xi e; sub_ty_ren_tm_dt sigma xi dt1; sub_ty_ren_tm_dt sigma xi dt2

and sub_ty_ren_tm_odt (sigma: tsub) (xi: ren) (df: option dtree)
  : Lemma (ensures sub_ty_odt sigma (ren_tm_odt xi df) == ren_tm_odt xi (sub_ty_odt sigma df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> sub_ty_ren_tm_dt sigma xi dt

and sub_ty_ren_tm_brs (#lb: eqtype) (sigma: tsub) (xi: ren) (bs: list (lb & dtree))
  : Lemma (ensures sub_ty_brs sigma (ren_tm_brs xi bs) == ren_tm_brs xi (sub_ty_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> sub_ty_ren_tm_dt sigma xi dt; sub_ty_ren_tm_brs sigma xi bs

and sub_ty_ren_tm_cls (sigma: tsub) (xi: ren) (cs: list clause)
  : Lemma (ensures sub_ty_cls sigma (ren_tm_cls xi cs) == ren_tm_cls xi (sub_ty_cls sigma cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    sub_ty_ren_tm (upn_tsub nb sigma) (upn_ren 2 xi) b; sub_ty_ren_tm_cls sigma xi cs
  | CFast _ nb _ b :: cs ->
    sub_ty_ren_tm (upn_tsub nb sigma) (up_ren xi) b; sub_ty_ren_tm_cls sigma xi cs

let rec ren_jp_ren_tm (zeta: ren) (xi: ren) (e: exp)
  : Lemma (ensures ren_jp zeta (ren_tm xi e) == ren_tm xi (ren_jp zeta e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> ren_jp_ren_tm zeta (up_ren xi) b
  | EApp e1 e2 -> ren_jp_ren_tm zeta xi e1; ren_jp_ren_tm zeta xi e2
  | ETyLam _ b -> ren_jp_ren_tm zeta xi b
  | ETyApp b _ -> ren_jp_ren_tm zeta xi b
  | ECLam _ b -> ren_jp_ren_tm zeta xi b
  | ECApp b -> ren_jp_ren_tm zeta xi b
  | ELet _ e1 e2 -> ren_jp_ren_tm zeta xi e1; ren_jp_ren_tm zeta (up_ren xi) e2
  | ELetRec bs b ->
    ren_jp_ren_tm_binds zeta (upn_ren (L.length bs) xi) bs;
    ren_jp_ren_tm zeta (upn_ren (L.length bs) xi) b
  | ECase es dt -> ren_jp_ren_tm_exps zeta xi es; ren_jp_ren_tm_dt zeta xi dt
  | ELetJoin ts _ e1 e2 ->
    ren_jp_ren_tm (up_ren zeta) (upn_ren (L.length ts) xi) e1; ren_jp_ren_tm (up_ren zeta) xi e2
  | EJump _ es -> ren_jp_ren_tm_exps zeta xi es
  | EExtend _ e1 e2 -> ren_jp_ren_tm zeta xi e1; ren_jp_ren_tm zeta xi e2
  | ESelect _ b -> ren_jp_ren_tm zeta xi b
  | ERestrict _ b -> ren_jp_ren_tm zeta xi b
  | EUpdate _ e1 e2 -> ren_jp_ren_tm zeta xi e1; ren_jp_ren_tm zeta xi e2
  | EMerge e1 e2 -> ren_jp_ren_tm zeta xi e1; ren_jp_ren_tm zeta xi e2
  | EInject _ _ b -> ren_jp_ren_tm zeta xi b
  | EWeaken _ _ b -> ren_jp_ren_tm zeta xi b
  | EAbsurd _ b -> ren_jp_ren_tm zeta xi b
  | EPerform _ _ _ b -> ren_jp_ren_tm zeta xi b
  | EHandle b h ->
    ren_jp_ren_tm zeta xi b; ren_jp_ren_tm zeta (up_ren xi) h.h_ret;
    ren_jp_ren_tm_cls zeta xi h.h_clauses
  | EOpenEff _ b -> ren_jp_ren_tm zeta xi b
  | ERegion _ es b -> ren_jp_ren_tm_exps zeta xi es; ren_jp_ren_tm zeta xi b
  | EWriteCell _ _ b -> ren_jp_ren_tm zeta xi b
  | ESpine _ sp -> ren_jp_ren_tm_spine zeta xi sp
  | EMatch th dt -> ren_jp_ren_tm_exps zeta xi th; ren_jp_ren_tm_dt zeta xi dt
  | EOpenEffC _ b -> ren_jp_ren_tm zeta xi b
  | EFill _ b -> ren_jp_ren_tm zeta xi b
  | ERegionOpen _ th b -> ren_jp_ren_tm_cells zeta xi th; ren_jp_ren_tm zeta xi b

and ren_jp_ren_tm_exps (zeta: ren) (xi: ren) (es: list exp)
  : Lemma (ensures ren_jp_exps zeta (ren_tm_exps xi es) == ren_tm_exps xi (ren_jp_exps zeta es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ren_jp_ren_tm zeta xi e; ren_jp_ren_tm_exps zeta xi es

and ren_jp_ren_tm_binds (zeta: ren) (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures ren_jp_binds zeta (ren_tm_binds xi bs) == ren_tm_binds xi (ren_jp_binds zeta bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> ren_jp_ren_tm zeta xi e; ren_jp_ren_tm_binds zeta xi bs

and ren_jp_ren_tm_cells (zeta: ren) (xi: ren) (th: list (key & exp))
  : Lemma (ensures ren_jp_cells zeta (ren_tm_cells xi th) == ren_tm_cells xi (ren_jp_cells zeta th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> ren_jp_ren_tm zeta xi e; ren_jp_ren_tm_cells zeta xi th

and ren_jp_ren_tm_spine (zeta: ren) (xi: ren) (sp: list spine_arg)
  : Lemma (ensures ren_jp_spine zeta (ren_tm_spine xi sp) == ren_tm_spine xi (ren_jp_spine zeta sp))
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> ren_jp_ren_tm_spine zeta xi sp
  | STy _ :: sp -> ren_jp_ren_tm_spine zeta xi sp
  | SConstr :: sp -> ren_jp_ren_tm_spine zeta xi sp
  | SVal v :: sp -> ren_jp_ren_tm zeta xi v; ren_jp_ren_tm_spine zeta xi sp

and ren_jp_ren_tm_dt (zeta: ren) (xi: ren) (dt: dtree)
  : Lemma (ensures ren_jp_dt zeta (ren_tm_dt xi dt) == ren_tm_dt xi (ren_jp_dt zeta dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> ren_jp_ren_tm zeta xi e
  | DBind _ dt -> ren_jp_ren_tm_dt zeta (up_ren xi) dt
  | DSwitchCtor _ bs df -> ren_jp_ren_tm_brs zeta xi bs; ren_jp_ren_tm_odt zeta xi df
  | DSwitchLit _ bs df -> ren_jp_ren_tm_brs zeta xi bs; ren_jp_ren_tm_dt zeta xi df
  | DSwitchKey _ bs df -> ren_jp_ren_tm_brs zeta xi bs; ren_jp_ren_tm_odt zeta xi df
  | DGuard e dt1 dt2 ->
    ren_jp_ren_tm zeta xi e; ren_jp_ren_tm_dt zeta xi dt1; ren_jp_ren_tm_dt zeta xi dt2

and ren_jp_ren_tm_odt (zeta: ren) (xi: ren) (df: option dtree)
  : Lemma (ensures ren_jp_odt zeta (ren_tm_odt xi df) == ren_tm_odt xi (ren_jp_odt zeta df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ren_jp_ren_tm_dt zeta xi dt

and ren_jp_ren_tm_brs (#lb: eqtype) (zeta: ren) (xi: ren) (bs: list (lb & dtree))
  : Lemma (ensures ren_jp_brs zeta (ren_tm_brs xi bs) == ren_tm_brs xi (ren_jp_brs zeta bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> ren_jp_ren_tm_dt zeta xi dt; ren_jp_ren_tm_brs zeta xi bs

and ren_jp_ren_tm_cls (zeta: ren) (xi: ren) (cs: list clause)
  : Lemma (ensures ren_jp_cls zeta (ren_tm_cls xi cs) == ren_tm_cls xi (ren_jp_cls zeta cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> ren_jp_ren_tm zeta (upn_ren 2 xi) b; ren_jp_ren_tm_cls zeta xi cs
  | CFast _ _ _ b :: cs -> ren_jp_ren_tm zeta (up_ren xi) b; ren_jp_ren_tm_cls zeta xi cs

let rec sub_ty_ren_jp (sigma: tsub) (zeta: ren) (e: exp)
  : Lemma (ensures sub_ty_exp sigma (ren_jp zeta e) == ren_jp zeta (sub_ty_exp sigma e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> sub_ty_ren_jp sigma zeta b
  | EApp e1 e2 -> sub_ty_ren_jp sigma zeta e1; sub_ty_ren_jp sigma zeta e2
  | ETyLam _ b -> sub_ty_ren_jp (up_tsub sigma) zeta b
  | ETyApp b _ -> sub_ty_ren_jp sigma zeta b
  | ECLam _ b -> sub_ty_ren_jp sigma zeta b
  | ECApp b -> sub_ty_ren_jp sigma zeta b
  | ELet _ e1 e2 -> sub_ty_ren_jp sigma zeta e1; sub_ty_ren_jp sigma zeta e2
  | ELetRec bs b -> sub_ty_ren_jp_binds sigma zeta bs; sub_ty_ren_jp sigma zeta b
  | ECase es dt -> sub_ty_ren_jp_exps sigma zeta es; sub_ty_ren_jp_dt sigma zeta dt
  | ELetJoin _ _ e1 e2 -> sub_ty_ren_jp sigma (up_ren zeta) e1; sub_ty_ren_jp sigma (up_ren zeta) e2
  | EJump _ es -> sub_ty_ren_jp_exps sigma zeta es
  | EExtend _ e1 e2 -> sub_ty_ren_jp sigma zeta e1; sub_ty_ren_jp sigma zeta e2
  | ESelect _ b -> sub_ty_ren_jp sigma zeta b
  | ERestrict _ b -> sub_ty_ren_jp sigma zeta b
  | EUpdate _ e1 e2 -> sub_ty_ren_jp sigma zeta e1; sub_ty_ren_jp sigma zeta e2
  | EMerge e1 e2 -> sub_ty_ren_jp sigma zeta e1; sub_ty_ren_jp sigma zeta e2
  | EInject _ _ b -> sub_ty_ren_jp sigma zeta b
  | EWeaken _ _ b -> sub_ty_ren_jp sigma zeta b
  | EAbsurd _ b -> sub_ty_ren_jp sigma zeta b
  | EPerform _ _ _ b -> sub_ty_ren_jp sigma zeta b
  | EHandle b h ->
    sub_ty_ren_jp sigma zeta b; sub_ty_ren_jp sigma zeta h.h_ret;
    sub_ty_ren_jp_cls sigma zeta h.h_clauses
  | EOpenEff _ b -> sub_ty_ren_jp sigma zeta b
  | ERegion _ es b -> sub_ty_ren_jp_exps sigma zeta es; sub_ty_ren_jp sigma zeta b
  | EWriteCell _ _ b -> sub_ty_ren_jp sigma zeta b
  | ESpine _ sp -> sub_ty_ren_jp_spine sigma zeta sp
  | EMatch th dt -> sub_ty_ren_jp_exps sigma zeta th; sub_ty_ren_jp_dt sigma zeta dt
  | EOpenEffC _ b -> sub_ty_ren_jp sigma zeta b
  | EFill _ b -> sub_ty_ren_jp sigma zeta b
  | ERegionOpen _ th b -> sub_ty_ren_jp_cells sigma zeta th; sub_ty_ren_jp sigma zeta b

and sub_ty_ren_jp_exps (sigma: tsub) (zeta: ren) (es: list exp)
  : Lemma (ensures sub_ty_exps sigma (ren_jp_exps zeta es)
                     == ren_jp_exps zeta (sub_ty_exps sigma es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> sub_ty_ren_jp sigma zeta e; sub_ty_ren_jp_exps sigma zeta es

and sub_ty_ren_jp_binds (sigma: tsub) (zeta: ren) (bs: list (typ & exp))
  : Lemma (ensures sub_ty_binds sigma (ren_jp_binds zeta bs)
                     == ren_jp_binds zeta (sub_ty_binds sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> sub_ty_ren_jp sigma zeta e; sub_ty_ren_jp_binds sigma zeta bs

and sub_ty_ren_jp_cells (sigma: tsub) (zeta: ren) (th: list (key & exp))
  : Lemma (ensures sub_ty_cells sigma (ren_jp_cells zeta th)
                     == ren_jp_cells zeta (sub_ty_cells sigma th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> sub_ty_ren_jp sigma zeta e; sub_ty_ren_jp_cells sigma zeta th

and sub_ty_ren_jp_spine (sigma: tsub) (zeta: ren) (sp: list spine_arg)
  : Lemma (ensures sub_ty_spine sigma (ren_jp_spine zeta sp)
                     == ren_jp_spine zeta (sub_ty_spine sigma sp))
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> sub_ty_ren_jp_spine sigma zeta sp
  | STy _ :: sp -> sub_ty_ren_jp_spine sigma zeta sp
  | SConstr :: sp -> sub_ty_ren_jp_spine sigma zeta sp
  | SVal v :: sp -> sub_ty_ren_jp sigma zeta v; sub_ty_ren_jp_spine sigma zeta sp

and sub_ty_ren_jp_dt (sigma: tsub) (zeta: ren) (dt: dtree)
  : Lemma (ensures sub_ty_dt sigma (ren_jp_dt zeta dt) == ren_jp_dt zeta (sub_ty_dt sigma dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> sub_ty_ren_jp sigma zeta e
  | DBind _ dt -> sub_ty_ren_jp_dt sigma zeta dt
  | DSwitchCtor _ bs df -> sub_ty_ren_jp_brs sigma zeta bs; sub_ty_ren_jp_odt sigma zeta df
  | DSwitchLit _ bs df -> sub_ty_ren_jp_brs sigma zeta bs; sub_ty_ren_jp_dt sigma zeta df
  | DSwitchKey _ bs df -> sub_ty_ren_jp_brs sigma zeta bs; sub_ty_ren_jp_odt sigma zeta df
  | DGuard e dt1 dt2 ->
    sub_ty_ren_jp sigma zeta e; sub_ty_ren_jp_dt sigma zeta dt1; sub_ty_ren_jp_dt sigma zeta dt2

and sub_ty_ren_jp_odt (sigma: tsub) (zeta: ren) (df: option dtree)
  : Lemma (ensures sub_ty_odt sigma (ren_jp_odt zeta df) == ren_jp_odt zeta (sub_ty_odt sigma df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> sub_ty_ren_jp_dt sigma zeta dt

and sub_ty_ren_jp_brs (#lb: eqtype) (sigma: tsub) (zeta: ren) (bs: list (lb & dtree))
  : Lemma (ensures sub_ty_brs sigma (ren_jp_brs zeta bs) == ren_jp_brs zeta (sub_ty_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> sub_ty_ren_jp_dt sigma zeta dt; sub_ty_ren_jp_brs sigma zeta bs

and sub_ty_ren_jp_cls (sigma: tsub) (zeta: ren) (cs: list clause)
  : Lemma (ensures sub_ty_cls sigma (ren_jp_cls zeta cs) == ren_jp_cls zeta (sub_ty_cls sigma cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    sub_ty_ren_jp (upn_tsub nb sigma) zeta b; sub_ty_ren_jp_cls sigma zeta cs
  | CFast _ nb _ b :: cs ->
    sub_ty_ren_jp (upn_tsub nb sigma) zeta b; sub_ty_ren_jp_cls sigma zeta cs

let ren_ty_ren_tm (xi zeta: ren) (e: exp)
  : Lemma (ren_ty_exp xi (ren_tm zeta e) == ren_tm zeta (ren_ty_exp xi e)) =
  ren_ty_exp_as_sub xi (ren_tm zeta e); ren_ty_exp_as_sub xi e;
  sub_ty_ren_tm (ren_tsub xi) zeta e

let ren_ty_ren_jp (xi zeta: ren) (e: exp)
  : Lemma (ren_ty_exp xi (ren_jp zeta e) == ren_jp zeta (ren_ty_exp xi e)) =
  ren_ty_exp_as_sub xi (ren_jp zeta e); ren_ty_exp_as_sub xi e;
  sub_ty_ren_jp (ren_tsub xi) zeta e

let upn_rinst_tm (n: nat) (xi: ren) (sigma: esub)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures forall (i: nat). upn_esub n sigma i == EVar (upn_ren n xi i)) = ()

let tyup_rinst_tm (m: nat) (xi: ren) (sigma: esub)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures forall (i: nat). tyup_esub m sigma i == EVar (xi i)) = ()

let jup_rinst_tm (xi: ren) (sigma: esub)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures forall (i: nat). jup_esub sigma i == EVar (xi i)) = ()

let rec rinst_tm (xi: ren) (sigma: esub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm xi e == sub_tm sigma e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> upn_rinst_tm 1 xi sigma; rinst_tm (up_ren xi) (up_esub sigma) b
  | EApp e1 e2 -> rinst_tm xi sigma e1; rinst_tm xi sigma e2
  | ETyLam _ b -> tyup_rinst_tm 1 xi sigma; rinst_tm xi (tyup_esub 1 sigma) b
  | ETyApp b _ -> rinst_tm xi sigma b
  | ECLam _ b -> rinst_tm xi sigma b
  | ECApp b -> rinst_tm xi sigma b
  | ELet _ e1 e2 ->
    rinst_tm xi sigma e1; upn_rinst_tm 1 xi sigma; rinst_tm (up_ren xi) (up_esub sigma) e2
  | ELetRec bs b ->
    upn_rinst_tm (L.length bs) xi sigma;
    rinst_tm_binds (upn_ren (L.length bs) xi) (upn_esub (L.length bs) sigma) bs;
    rinst_tm (upn_ren (L.length bs) xi) (upn_esub (L.length bs) sigma) b
  | ECase es dt -> rinst_tm_exps xi sigma es; rinst_tm_dt xi sigma dt
  | ELetJoin ts _ e1 e2 ->
    jup_rinst_tm xi sigma; upn_rinst_tm (L.length ts) xi (jup_esub sigma);
    rinst_tm (upn_ren (L.length ts) xi) (upn_esub (L.length ts) (jup_esub sigma)) e1;
    rinst_tm xi (jup_esub sigma) e2
  | EJump _ es -> rinst_tm_exps xi sigma es
  | EExtend _ e1 e2 -> rinst_tm xi sigma e1; rinst_tm xi sigma e2
  | ESelect _ b -> rinst_tm xi sigma b
  | ERestrict _ b -> rinst_tm xi sigma b
  | EUpdate _ e1 e2 -> rinst_tm xi sigma e1; rinst_tm xi sigma e2
  | EMerge e1 e2 -> rinst_tm xi sigma e1; rinst_tm xi sigma e2
  | EInject _ _ b -> rinst_tm xi sigma b
  | EWeaken _ _ b -> rinst_tm xi sigma b
  | EAbsurd _ b -> rinst_tm xi sigma b
  | EPerform _ _ _ b -> rinst_tm xi sigma b
  | EHandle b h ->
    rinst_tm xi sigma b; upn_rinst_tm 1 xi sigma; rinst_tm (up_ren xi) (up_esub sigma) h.h_ret;
    rinst_tm_cls xi sigma h.h_clauses
  | EOpenEff _ b -> rinst_tm xi sigma b
  | ERegion _ es b -> rinst_tm_exps xi sigma es; rinst_tm xi sigma b
  | EWriteCell _ _ b -> rinst_tm xi sigma b
  | ESpine _ sp -> rinst_tm_spine xi sigma sp
  | EMatch th dt -> rinst_tm_exps xi sigma th; rinst_tm_dt xi sigma dt
  | EOpenEffC _ b -> rinst_tm xi sigma b
  | EFill _ b -> rinst_tm xi sigma b
  | ERegionOpen _ th b -> rinst_tm_cells xi sigma th; rinst_tm xi sigma b

and rinst_tm_exps (xi: ren) (sigma: esub) (es: list exp)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm_exps xi es == sub_tm_exps sigma es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> rinst_tm xi sigma e; rinst_tm_exps xi sigma es

and rinst_tm_binds (xi: ren) (sigma: esub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm_binds xi bs == sub_tm_binds sigma bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> rinst_tm xi sigma e; rinst_tm_binds xi sigma bs

and rinst_tm_cells (xi: ren) (sigma: esub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm_cells xi th == sub_tm_cells sigma th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> rinst_tm xi sigma e; rinst_tm_cells xi sigma th

and rinst_tm_spine (xi: ren) (sigma: esub) (sp: list spine_arg)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm_spine xi sp == sub_tm_spine sigma sp)
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> rinst_tm_spine xi sigma sp
  | STy _ :: sp -> rinst_tm_spine xi sigma sp
  | SConstr :: sp -> rinst_tm_spine xi sigma sp
  | SVal v :: sp -> rinst_tm xi sigma v; rinst_tm_spine xi sigma sp

and rinst_tm_dt (xi: ren) (sigma: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm_dt xi dt == sub_tm_dt sigma dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> rinst_tm xi sigma e
  | DBind _ dt -> upn_rinst_tm 1 xi sigma; rinst_tm_dt (up_ren xi) (up_esub sigma) dt
  | DSwitchCtor _ bs df -> rinst_tm_brs xi sigma bs; rinst_tm_odt xi sigma df
  | DSwitchLit _ bs df -> rinst_tm_brs xi sigma bs; rinst_tm_dt xi sigma df
  | DSwitchKey _ bs df -> rinst_tm_brs xi sigma bs; rinst_tm_odt xi sigma df
  | DGuard e dt1 dt2 -> rinst_tm xi sigma e; rinst_tm_dt xi sigma dt1; rinst_tm_dt xi sigma dt2

and rinst_tm_odt (xi: ren) (sigma: esub) (df: option dtree)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm_odt xi df == sub_tm_odt sigma df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> rinst_tm_dt xi sigma dt

and rinst_tm_brs (#lb: eqtype) (xi: ren) (sigma: esub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm_brs xi bs == sub_tm_brs sigma bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rinst_tm_dt xi sigma dt; rinst_tm_brs xi sigma bs

and rinst_tm_cls (xi: ren) (sigma: esub) (cs: list clause)
  : Lemma (requires forall (i: nat). sigma i == EVar (xi i))
          (ensures ren_tm_cls xi cs == sub_tm_cls sigma cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    tyup_rinst_tm nb xi sigma; upn_rinst_tm 2 xi (tyup_esub nb sigma);
    rinst_tm (upn_ren 2 xi) (upn_esub 2 (tyup_esub nb sigma)) b; rinst_tm_cls xi sigma cs
  | CFast _ nb _ b :: cs ->
    tyup_rinst_tm nb xi sigma; upn_rinst_tm 1 xi (tyup_esub nb sigma);
    rinst_tm (up_ren xi) (up_esub (tyup_esub nb sigma)) b; rinst_tm_cls xi sigma cs

let ren_tm_as_sub (xi: ren) (e: exp) : Lemma (ren_tm xi e == sub_tm (ren_esub xi) e) =
  rinst_tm xi (ren_esub xi) e

let upn_sub_ren_tm (n: nat) (sigma: esub) (xi: ren) (theta: esub)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures forall (i: nat). upn_esub n theta i == upn_esub n sigma (upn_ren n xi i)) = ()

let tyup_sub_ren_tm (m: nat) (sigma: esub) (xi: ren) (theta: esub)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures forall (i: nat). tyup_esub m theta i == tyup_esub m sigma (xi i)) = ()

let jup_sub_ren_tm (sigma: esub) (xi: ren) (theta: esub)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures forall (i: nat). jup_esub theta i == jup_esub sigma (xi i)) = ()

let rec sub_ren_tm (sigma: esub) (xi: ren) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm sigma (ren_tm xi e) == sub_tm theta e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b ->
    upn_sub_ren_tm 1 sigma xi theta; sub_ren_tm (up_esub sigma) (up_ren xi) (up_esub theta) b
  | EApp e1 e2 -> sub_ren_tm sigma xi theta e1; sub_ren_tm sigma xi theta e2
  | ETyLam _ b ->
    tyup_sub_ren_tm 1 sigma xi theta; sub_ren_tm (tyup_esub 1 sigma) xi (tyup_esub 1 theta) b
  | ETyApp b _ -> sub_ren_tm sigma xi theta b
  | ECLam _ b -> sub_ren_tm sigma xi theta b
  | ECApp b -> sub_ren_tm sigma xi theta b
  | ELet _ e1 e2 ->
    sub_ren_tm sigma xi theta e1; upn_sub_ren_tm 1 sigma xi theta;
    sub_ren_tm (up_esub sigma) (up_ren xi) (up_esub theta) e2
  | ELetRec bs b ->
    upn_sub_ren_tm (L.length bs) sigma xi theta;
    sub_ren_tm_binds (upn_esub (L.length bs) sigma) (upn_ren (L.length bs) xi)
      (upn_esub (L.length bs) theta) bs;
    sub_ren_tm (upn_esub (L.length bs) sigma) (upn_ren (L.length bs) xi)
      (upn_esub (L.length bs) theta) b
  | ECase es dt -> sub_ren_tm_exps sigma xi theta es; sub_ren_tm_dt sigma xi theta dt
  | ELetJoin ts _ e1 e2 ->
    jup_sub_ren_tm sigma xi theta;
    upn_sub_ren_tm (L.length ts) (jup_esub sigma) xi (jup_esub theta);
    sub_ren_tm (upn_esub (L.length ts) (jup_esub sigma)) (upn_ren (L.length ts) xi)
      (upn_esub (L.length ts) (jup_esub theta)) e1;
    sub_ren_tm (jup_esub sigma) xi (jup_esub theta) e2
  | EJump _ es -> sub_ren_tm_exps sigma xi theta es
  | EExtend _ e1 e2 -> sub_ren_tm sigma xi theta e1; sub_ren_tm sigma xi theta e2
  | ESelect _ b -> sub_ren_tm sigma xi theta b
  | ERestrict _ b -> sub_ren_tm sigma xi theta b
  | EUpdate _ e1 e2 -> sub_ren_tm sigma xi theta e1; sub_ren_tm sigma xi theta e2
  | EMerge e1 e2 -> sub_ren_tm sigma xi theta e1; sub_ren_tm sigma xi theta e2
  | EInject _ _ b -> sub_ren_tm sigma xi theta b
  | EWeaken _ _ b -> sub_ren_tm sigma xi theta b
  | EAbsurd _ b -> sub_ren_tm sigma xi theta b
  | EPerform _ _ _ b -> sub_ren_tm sigma xi theta b
  | EHandle b h ->
    sub_ren_tm sigma xi theta b; upn_sub_ren_tm 1 sigma xi theta;
    sub_ren_tm (up_esub sigma) (up_ren xi) (up_esub theta) h.h_ret;
    sub_ren_tm_cls sigma xi theta h.h_clauses
  | EOpenEff _ b -> sub_ren_tm sigma xi theta b
  | ERegion _ es b -> sub_ren_tm_exps sigma xi theta es; sub_ren_tm sigma xi theta b
  | EWriteCell _ _ b -> sub_ren_tm sigma xi theta b
  | ESpine _ sp -> sub_ren_tm_spine sigma xi theta sp
  | EMatch th dt -> sub_ren_tm_exps sigma xi theta th; sub_ren_tm_dt sigma xi theta dt
  | EOpenEffC _ b -> sub_ren_tm sigma xi theta b
  | EFill _ b -> sub_ren_tm sigma xi theta b
  | ERegionOpen _ th b -> sub_ren_tm_cells sigma xi theta th; sub_ren_tm sigma xi theta b

and sub_ren_tm_exps (sigma: esub) (xi: ren) (theta: esub) (es: list exp)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm_exps sigma (ren_tm_exps xi es) == sub_tm_exps theta es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> sub_ren_tm sigma xi theta e; sub_ren_tm_exps sigma xi theta es

and sub_ren_tm_binds (sigma: esub) (xi: ren) (theta: esub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm_binds sigma (ren_tm_binds xi bs) == sub_tm_binds theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> sub_ren_tm sigma xi theta e; sub_ren_tm_binds sigma xi theta bs

and sub_ren_tm_cells (sigma: esub) (xi: ren) (theta: esub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm_cells sigma (ren_tm_cells xi th) == sub_tm_cells theta th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> sub_ren_tm sigma xi theta e; sub_ren_tm_cells sigma xi theta th

and sub_ren_tm_spine (sigma: esub) (xi: ren) (theta: esub) (sp: list spine_arg)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm_spine sigma (ren_tm_spine xi sp) == sub_tm_spine theta sp)
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> sub_ren_tm_spine sigma xi theta sp
  | STy _ :: sp -> sub_ren_tm_spine sigma xi theta sp
  | SConstr :: sp -> sub_ren_tm_spine sigma xi theta sp
  | SVal v :: sp -> sub_ren_tm sigma xi theta v; sub_ren_tm_spine sigma xi theta sp

and sub_ren_tm_dt (sigma: esub) (xi: ren) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm_dt sigma (ren_tm_dt xi dt) == sub_tm_dt theta dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> sub_ren_tm sigma xi theta e
  | DBind _ dt ->
    upn_sub_ren_tm 1 sigma xi theta; sub_ren_tm_dt (up_esub sigma) (up_ren xi) (up_esub theta) dt
  | DSwitchCtor _ bs df -> sub_ren_tm_brs sigma xi theta bs; sub_ren_tm_odt sigma xi theta df
  | DSwitchLit _ bs df -> sub_ren_tm_brs sigma xi theta bs; sub_ren_tm_dt sigma xi theta df
  | DSwitchKey _ bs df -> sub_ren_tm_brs sigma xi theta bs; sub_ren_tm_odt sigma xi theta df
  | DGuard e dt1 dt2 ->
    sub_ren_tm sigma xi theta e; sub_ren_tm_dt sigma xi theta dt1; sub_ren_tm_dt sigma xi theta dt2

and sub_ren_tm_odt (sigma: esub) (xi: ren) (theta: esub) (df: option dtree)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm_odt sigma (ren_tm_odt xi df) == sub_tm_odt theta df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> sub_ren_tm_dt sigma xi theta dt

and sub_ren_tm_brs (#lb: eqtype) (sigma: esub) (xi: ren) (theta: esub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm_brs sigma (ren_tm_brs xi bs) == sub_tm_brs theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> sub_ren_tm_dt sigma xi theta dt; sub_ren_tm_brs sigma xi theta bs

and sub_ren_tm_cls (sigma: esub) (xi: ren) (theta: esub) (cs: list clause)
  : Lemma (requires forall (i: nat). theta i == sigma (xi i))
          (ensures sub_tm_cls sigma (ren_tm_cls xi cs) == sub_tm_cls theta cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    tyup_sub_ren_tm nb sigma xi theta;
    upn_sub_ren_tm 2 (tyup_esub nb sigma) xi (tyup_esub nb theta);
    sub_ren_tm (upn_esub 2 (tyup_esub nb sigma)) (upn_ren 2 xi) (upn_esub 2 (tyup_esub nb theta)) b;
    sub_ren_tm_cls sigma xi theta cs
  | CFast _ nb _ b :: cs ->
    tyup_sub_ren_tm nb sigma xi theta;
    upn_sub_ren_tm 1 (tyup_esub nb sigma) xi (tyup_esub nb theta);
    sub_ren_tm (up_esub (tyup_esub nb sigma)) (up_ren xi) (up_esub (tyup_esub nb theta)) b;
    sub_ren_tm_cls sigma xi theta cs

let ren_ren_tm (xi zeta theta: ren) (e: exp)
  : Lemma (requires forall (i: nat). theta i == xi (zeta i))
          (ensures ren_tm xi (ren_tm zeta e) == ren_tm theta e) =
  ren_tm_as_sub xi (ren_tm zeta e);
  sub_ren_tm (ren_esub xi) zeta (ren_esub theta) e;
  ren_tm_as_sub theta e

let upn_ren_sub_tm (n: nat) (xi: ren) (sigma theta: esub)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures forall (i: nat).
             upn_esub n theta i == ren_tm (upn_ren n xi) (upn_esub n sigma i)) =
  introduce forall (i: nat). upn_esub n theta i == ren_tm (upn_ren n xi) (upn_esub n sigma i)
  with if i < n then () else begin
    ren_ren_tm (shift n) xi (ren_shift n xi) (sigma (i - n));
    ren_ren_tm (upn_ren n xi) (shift n) (ren_shift n xi) (sigma (i - n))
  end

let tyup_ren_sub_tm (m: nat) (xi: ren) (sigma theta: esub)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures forall (i: nat). tyup_esub m theta i == ren_tm xi (tyup_esub m sigma i)) =
  introduce forall (i: nat). tyup_esub m theta i == ren_tm xi (tyup_esub m sigma i)
  with ren_ty_ren_tm (shift m) xi (sigma i)

let jup_ren_sub_tm (xi: ren) (sigma theta: esub)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures forall (i: nat). jup_esub theta i == ren_tm xi (jup_esub sigma i)) =
  introduce forall (i: nat). jup_esub theta i == ren_tm xi (jup_esub sigma i)
  with ren_jp_ren_tm (shift 1) xi (sigma i)

let rec ren_sub_tm (xi: ren) (sigma: esub) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm xi (sub_tm sigma e) == sub_tm theta e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b ->
    upn_ren_sub_tm 1 xi sigma theta; ren_sub_tm (up_ren xi) (up_esub sigma) (up_esub theta) b
  | EApp e1 e2 -> ren_sub_tm xi sigma theta e1; ren_sub_tm xi sigma theta e2
  | ETyLam _ b ->
    tyup_ren_sub_tm 1 xi sigma theta; ren_sub_tm xi (tyup_esub 1 sigma) (tyup_esub 1 theta) b
  | ETyApp b _ -> ren_sub_tm xi sigma theta b
  | ECLam _ b -> ren_sub_tm xi sigma theta b
  | ECApp b -> ren_sub_tm xi sigma theta b
  | ELet _ e1 e2 ->
    ren_sub_tm xi sigma theta e1; upn_ren_sub_tm 1 xi sigma theta;
    ren_sub_tm (up_ren xi) (up_esub sigma) (up_esub theta) e2
  | ELetRec bs b ->
    upn_ren_sub_tm (L.length bs) xi sigma theta;
    ren_sub_tm_binds (upn_ren (L.length bs) xi) (upn_esub (L.length bs) sigma)
      (upn_esub (L.length bs) theta) bs;
    ren_sub_tm (upn_ren (L.length bs) xi) (upn_esub (L.length bs) sigma)
      (upn_esub (L.length bs) theta) b
  | ECase es dt -> ren_sub_tm_exps xi sigma theta es; ren_sub_tm_dt xi sigma theta dt
  | ELetJoin ts _ e1 e2 ->
    jup_ren_sub_tm xi sigma theta;
    upn_ren_sub_tm (L.length ts) xi (jup_esub sigma) (jup_esub theta);
    ren_sub_tm (upn_ren (L.length ts) xi) (upn_esub (L.length ts) (jup_esub sigma))
      (upn_esub (L.length ts) (jup_esub theta)) e1;
    ren_sub_tm xi (jup_esub sigma) (jup_esub theta) e2
  | EJump _ es -> ren_sub_tm_exps xi sigma theta es
  | EExtend _ e1 e2 -> ren_sub_tm xi sigma theta e1; ren_sub_tm xi sigma theta e2
  | ESelect _ b -> ren_sub_tm xi sigma theta b
  | ERestrict _ b -> ren_sub_tm xi sigma theta b
  | EUpdate _ e1 e2 -> ren_sub_tm xi sigma theta e1; ren_sub_tm xi sigma theta e2
  | EMerge e1 e2 -> ren_sub_tm xi sigma theta e1; ren_sub_tm xi sigma theta e2
  | EInject _ _ b -> ren_sub_tm xi sigma theta b
  | EWeaken _ _ b -> ren_sub_tm xi sigma theta b
  | EAbsurd _ b -> ren_sub_tm xi sigma theta b
  | EPerform _ _ _ b -> ren_sub_tm xi sigma theta b
  | EHandle b h ->
    ren_sub_tm xi sigma theta b; upn_ren_sub_tm 1 xi sigma theta;
    ren_sub_tm (up_ren xi) (up_esub sigma) (up_esub theta) h.h_ret;
    ren_sub_tm_cls xi sigma theta h.h_clauses
  | EOpenEff _ b -> ren_sub_tm xi sigma theta b
  | ERegion _ es b -> ren_sub_tm_exps xi sigma theta es; ren_sub_tm xi sigma theta b
  | EWriteCell _ _ b -> ren_sub_tm xi sigma theta b
  | ESpine _ sp -> ren_sub_tm_spine xi sigma theta sp
  | EMatch th dt -> ren_sub_tm_exps xi sigma theta th; ren_sub_tm_dt xi sigma theta dt
  | EOpenEffC _ b -> ren_sub_tm xi sigma theta b
  | EFill _ b -> ren_sub_tm xi sigma theta b
  | ERegionOpen _ th b -> ren_sub_tm_cells xi sigma theta th; ren_sub_tm xi sigma theta b

and ren_sub_tm_exps (xi: ren) (sigma: esub) (theta: esub) (es: list exp)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm_exps xi (sub_tm_exps sigma es) == sub_tm_exps theta es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ren_sub_tm xi sigma theta e; ren_sub_tm_exps xi sigma theta es

and ren_sub_tm_binds (xi: ren) (sigma: esub) (theta: esub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm_binds xi (sub_tm_binds sigma bs) == sub_tm_binds theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> ren_sub_tm xi sigma theta e; ren_sub_tm_binds xi sigma theta bs

and ren_sub_tm_cells (xi: ren) (sigma: esub) (theta: esub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm_cells xi (sub_tm_cells sigma th) == sub_tm_cells theta th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> ren_sub_tm xi sigma theta e; ren_sub_tm_cells xi sigma theta th

and ren_sub_tm_spine (xi: ren) (sigma: esub) (theta: esub) (sp: list spine_arg)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm_spine xi (sub_tm_spine sigma sp) == sub_tm_spine theta sp)
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> ren_sub_tm_spine xi sigma theta sp
  | STy _ :: sp -> ren_sub_tm_spine xi sigma theta sp
  | SConstr :: sp -> ren_sub_tm_spine xi sigma theta sp
  | SVal v :: sp -> ren_sub_tm xi sigma theta v; ren_sub_tm_spine xi sigma theta sp

and ren_sub_tm_dt (xi: ren) (sigma: esub) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm_dt xi (sub_tm_dt sigma dt) == sub_tm_dt theta dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> ren_sub_tm xi sigma theta e
  | DBind _ dt ->
    upn_ren_sub_tm 1 xi sigma theta; ren_sub_tm_dt (up_ren xi) (up_esub sigma) (up_esub theta) dt
  | DSwitchCtor _ bs df -> ren_sub_tm_brs xi sigma theta bs; ren_sub_tm_odt xi sigma theta df
  | DSwitchLit _ bs df -> ren_sub_tm_brs xi sigma theta bs; ren_sub_tm_dt xi sigma theta df
  | DSwitchKey _ bs df -> ren_sub_tm_brs xi sigma theta bs; ren_sub_tm_odt xi sigma theta df
  | DGuard e dt1 dt2 ->
    ren_sub_tm xi sigma theta e; ren_sub_tm_dt xi sigma theta dt1; ren_sub_tm_dt xi sigma theta dt2

and ren_sub_tm_odt (xi: ren) (sigma: esub) (theta: esub) (df: option dtree)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm_odt xi (sub_tm_odt sigma df) == sub_tm_odt theta df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ren_sub_tm_dt xi sigma theta dt

and ren_sub_tm_brs (#lb: eqtype) (xi: ren) (sigma: esub) (theta: esub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm_brs xi (sub_tm_brs sigma bs) == sub_tm_brs theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> ren_sub_tm_dt xi sigma theta dt; ren_sub_tm_brs xi sigma theta bs

and ren_sub_tm_cls (xi: ren) (sigma: esub) (theta: esub) (cs: list clause)
  : Lemma (requires forall (i: nat). theta i == ren_tm xi (sigma i))
          (ensures ren_tm_cls xi (sub_tm_cls sigma cs) == sub_tm_cls theta cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    tyup_ren_sub_tm nb xi sigma theta;
    upn_ren_sub_tm 2 xi (tyup_esub nb sigma) (tyup_esub nb theta);
    ren_sub_tm (upn_ren 2 xi) (upn_esub 2 (tyup_esub nb sigma)) (upn_esub 2 (tyup_esub nb theta)) b;
    ren_sub_tm_cls xi sigma theta cs
  | CFast _ nb _ b :: cs ->
    tyup_ren_sub_tm nb xi sigma theta;
    upn_ren_sub_tm 1 xi (tyup_esub nb sigma) (tyup_esub nb theta);
    ren_sub_tm (up_ren xi) (up_esub (tyup_esub nb sigma)) (up_esub (tyup_esub nb theta)) b;
    ren_sub_tm_cls xi sigma theta cs

let upn_ren_jp_sub_tm (n: nat) (zeta: ren) (tau theta: esub)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures forall (i: nat). upn_esub n theta i == ren_jp zeta (upn_esub n tau i)) =
  introduce forall (i: nat). upn_esub n theta i == ren_jp zeta (upn_esub n tau i)
  with if i < n then () else ren_jp_ren_tm zeta (shift n) (tau (i - n))

let tyup_ren_jp_sub_tm (m: nat) (zeta: ren) (tau theta: esub)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures forall (i: nat). tyup_esub m theta i == ren_jp zeta (tyup_esub m tau i)) =
  introduce forall (i: nat). tyup_esub m theta i == ren_jp zeta (tyup_esub m tau i)
  with ren_ty_ren_jp (shift m) zeta (tau i)

let jup_ren_jp_sub_tm (zeta: ren) (tau theta: esub)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures forall (i: nat). jup_esub theta i == ren_jp (up_ren zeta) (jup_esub tau i)) =
  introduce forall (i: nat). jup_esub theta i == ren_jp (up_ren zeta) (jup_esub tau i)
  with begin
    ren_ren_jp (shift 1) zeta (ren_shift 1 zeta) (tau i);
    ren_ren_jp (up_ren zeta) (shift 1) (ren_shift 1 zeta) (tau i)
  end

let rec ren_jp_sub_tm (zeta: ren) (tau: esub) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp zeta (sub_tm tau e) == sub_tm theta (ren_jp zeta e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b ->
    upn_ren_jp_sub_tm 1 zeta tau theta; ren_jp_sub_tm zeta (up_esub tau) (up_esub theta) b
  | EApp e1 e2 -> ren_jp_sub_tm zeta tau theta e1; ren_jp_sub_tm zeta tau theta e2
  | ETyLam _ b ->
    tyup_ren_jp_sub_tm 1 zeta tau theta; ren_jp_sub_tm zeta (tyup_esub 1 tau) (tyup_esub 1 theta) b
  | ETyApp b _ -> ren_jp_sub_tm zeta tau theta b
  | ECLam _ b -> ren_jp_sub_tm zeta tau theta b
  | ECApp b -> ren_jp_sub_tm zeta tau theta b
  | ELet _ e1 e2 ->
    ren_jp_sub_tm zeta tau theta e1; upn_ren_jp_sub_tm 1 zeta tau theta;
    ren_jp_sub_tm zeta (up_esub tau) (up_esub theta) e2
  | ELetRec bs b ->
    upn_ren_jp_sub_tm (L.length bs) zeta tau theta;
    ren_jp_sub_tm_binds zeta (upn_esub (L.length bs) tau) (upn_esub (L.length bs) theta) bs;
    ren_jp_sub_tm zeta (upn_esub (L.length bs) tau) (upn_esub (L.length bs) theta) b
  | ECase es dt -> ren_jp_sub_tm_exps zeta tau theta es; ren_jp_sub_tm_dt zeta tau theta dt
  | ELetJoin ts _ e1 e2 ->
    jup_ren_jp_sub_tm zeta tau theta;
    upn_ren_jp_sub_tm (L.length ts) (up_ren zeta) (jup_esub tau) (jup_esub theta);
    ren_jp_sub_tm (up_ren zeta) (upn_esub (L.length ts) (jup_esub tau))
      (upn_esub (L.length ts) (jup_esub theta)) e1;
    ren_jp_sub_tm (up_ren zeta) (jup_esub tau) (jup_esub theta) e2
  | EJump _ es -> ren_jp_sub_tm_exps zeta tau theta es
  | EExtend _ e1 e2 -> ren_jp_sub_tm zeta tau theta e1; ren_jp_sub_tm zeta tau theta e2
  | ESelect _ b -> ren_jp_sub_tm zeta tau theta b
  | ERestrict _ b -> ren_jp_sub_tm zeta tau theta b
  | EUpdate _ e1 e2 -> ren_jp_sub_tm zeta tau theta e1; ren_jp_sub_tm zeta tau theta e2
  | EMerge e1 e2 -> ren_jp_sub_tm zeta tau theta e1; ren_jp_sub_tm zeta tau theta e2
  | EInject _ _ b -> ren_jp_sub_tm zeta tau theta b
  | EWeaken _ _ b -> ren_jp_sub_tm zeta tau theta b
  | EAbsurd _ b -> ren_jp_sub_tm zeta tau theta b
  | EPerform _ _ _ b -> ren_jp_sub_tm zeta tau theta b
  | EHandle b h ->
    ren_jp_sub_tm zeta tau theta b; upn_ren_jp_sub_tm 1 zeta tau theta;
    ren_jp_sub_tm zeta (up_esub tau) (up_esub theta) h.h_ret;
    ren_jp_sub_tm_cls zeta tau theta h.h_clauses
  | EOpenEff _ b -> ren_jp_sub_tm zeta tau theta b
  | ERegion _ es b -> ren_jp_sub_tm_exps zeta tau theta es; ren_jp_sub_tm zeta tau theta b
  | EWriteCell _ _ b -> ren_jp_sub_tm zeta tau theta b
  | ESpine _ sp -> ren_jp_sub_tm_spine zeta tau theta sp
  | EMatch th dt -> ren_jp_sub_tm_exps zeta tau theta th; ren_jp_sub_tm_dt zeta tau theta dt
  | EOpenEffC _ b -> ren_jp_sub_tm zeta tau theta b
  | EFill _ b -> ren_jp_sub_tm zeta tau theta b
  | ERegionOpen _ th b -> ren_jp_sub_tm_cells zeta tau theta th; ren_jp_sub_tm zeta tau theta b

and ren_jp_sub_tm_exps (zeta: ren) (tau: esub) (theta: esub) (es: list exp)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp_exps zeta (sub_tm_exps tau es) == sub_tm_exps theta (ren_jp_exps zeta es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ren_jp_sub_tm zeta tau theta e; ren_jp_sub_tm_exps zeta tau theta es

and ren_jp_sub_tm_binds (zeta: ren) (tau: esub) (theta: esub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp_binds zeta (sub_tm_binds tau bs)
                     == sub_tm_binds theta (ren_jp_binds zeta bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> ren_jp_sub_tm zeta tau theta e; ren_jp_sub_tm_binds zeta tau theta bs

and ren_jp_sub_tm_cells (zeta: ren) (tau: esub) (theta: esub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp_cells zeta (sub_tm_cells tau th)
                     == sub_tm_cells theta (ren_jp_cells zeta th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> ren_jp_sub_tm zeta tau theta e; ren_jp_sub_tm_cells zeta tau theta th

and ren_jp_sub_tm_spine (zeta: ren) (tau: esub) (theta: esub) (sp: list spine_arg)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp_spine zeta (sub_tm_spine tau sp)
                     == sub_tm_spine theta (ren_jp_spine zeta sp))
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> ren_jp_sub_tm_spine zeta tau theta sp
  | STy _ :: sp -> ren_jp_sub_tm_spine zeta tau theta sp
  | SConstr :: sp -> ren_jp_sub_tm_spine zeta tau theta sp
  | SVal v :: sp -> ren_jp_sub_tm zeta tau theta v; ren_jp_sub_tm_spine zeta tau theta sp

and ren_jp_sub_tm_dt (zeta: ren) (tau: esub) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp_dt zeta (sub_tm_dt tau dt) == sub_tm_dt theta (ren_jp_dt zeta dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> ren_jp_sub_tm zeta tau theta e
  | DBind _ dt ->
    upn_ren_jp_sub_tm 1 zeta tau theta; ren_jp_sub_tm_dt zeta (up_esub tau) (up_esub theta) dt
  | DSwitchCtor _ bs df -> ren_jp_sub_tm_brs zeta tau theta bs; ren_jp_sub_tm_odt zeta tau theta df
  | DSwitchLit _ bs df -> ren_jp_sub_tm_brs zeta tau theta bs; ren_jp_sub_tm_dt zeta tau theta df
  | DSwitchKey _ bs df -> ren_jp_sub_tm_brs zeta tau theta bs; ren_jp_sub_tm_odt zeta tau theta df
  | DGuard e dt1 dt2 ->
    ren_jp_sub_tm zeta tau theta e; ren_jp_sub_tm_dt zeta tau theta dt1;
    ren_jp_sub_tm_dt zeta tau theta dt2

and ren_jp_sub_tm_odt (zeta: ren) (tau: esub) (theta: esub) (df: option dtree)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp_odt zeta (sub_tm_odt tau df) == sub_tm_odt theta (ren_jp_odt zeta df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ren_jp_sub_tm_dt zeta tau theta dt

and ren_jp_sub_tm_brs (#lb: eqtype) (zeta: ren) (tau: esub) (theta: esub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp_brs zeta (sub_tm_brs tau bs) == sub_tm_brs theta (ren_jp_brs zeta bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> ren_jp_sub_tm_dt zeta tau theta dt; ren_jp_sub_tm_brs zeta tau theta bs

and ren_jp_sub_tm_cls (zeta: ren) (tau: esub) (theta: esub) (cs: list clause)
  : Lemma (requires forall (i: nat). theta i == ren_jp zeta (tau i))
          (ensures ren_jp_cls zeta (sub_tm_cls tau cs) == sub_tm_cls theta (ren_jp_cls zeta cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    tyup_ren_jp_sub_tm nb zeta tau theta;
    upn_ren_jp_sub_tm 2 zeta (tyup_esub nb tau) (tyup_esub nb theta);
    ren_jp_sub_tm zeta (upn_esub 2 (tyup_esub nb tau)) (upn_esub 2 (tyup_esub nb theta)) b;
    ren_jp_sub_tm_cls zeta tau theta cs
  | CFast _ nb _ b :: cs ->
    tyup_ren_jp_sub_tm nb zeta tau theta;
    upn_ren_jp_sub_tm 1 zeta (tyup_esub nb tau) (tyup_esub nb theta);
    ren_jp_sub_tm zeta (up_esub (tyup_esub nb tau)) (up_esub (tyup_esub nb theta)) b;
    ren_jp_sub_tm_cls zeta tau theta cs

let upn_sub_ty_sub_tm (n: nat) (sigma: tsub) (tau theta: esub)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures forall (i: nat). upn_esub n theta i == sub_ty_exp sigma (upn_esub n tau i)) =
  introduce forall (i: nat). upn_esub n theta i == sub_ty_exp sigma (upn_esub n tau i)
  with if i < n then () else sub_ty_ren_tm sigma (shift n) (tau (i - n))

let tyup_sub_ty_sub_tm (m: nat) (sigma: tsub) (tau theta: esub)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures forall (i: nat).
             tyup_esub m theta i == sub_ty_exp (upn_tsub m sigma) (tyup_esub m tau i)) =
  introduce forall (i: nat).
    tyup_esub m theta i == sub_ty_exp (upn_tsub m sigma) (tyup_esub m tau i)
  with sub_ty_exp_shift m sigma (tau i)

let jup_sub_ty_sub_tm (sigma: tsub) (tau theta: esub)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures forall (i: nat). jup_esub theta i == sub_ty_exp sigma (jup_esub tau i)) =
  introduce forall (i: nat). jup_esub theta i == sub_ty_exp sigma (jup_esub tau i)
  with sub_ty_ren_jp sigma (shift 1) (tau i)

let rec sub_ty_sub_tm (sigma: tsub) (tau: esub) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_exp sigma (sub_tm tau e) == sub_tm theta (sub_ty_exp sigma e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b ->
    upn_sub_ty_sub_tm 1 sigma tau theta; sub_ty_sub_tm sigma (up_esub tau) (up_esub theta) b
  | EApp e1 e2 -> sub_ty_sub_tm sigma tau theta e1; sub_ty_sub_tm sigma tau theta e2
  | ETyLam _ b ->
    tyup_sub_ty_sub_tm 1 sigma tau theta;
    sub_ty_sub_tm (up_tsub sigma) (tyup_esub 1 tau) (tyup_esub 1 theta) b
  | ETyApp b _ -> sub_ty_sub_tm sigma tau theta b
  | ECLam _ b -> sub_ty_sub_tm sigma tau theta b
  | ECApp b -> sub_ty_sub_tm sigma tau theta b
  | ELet _ e1 e2 ->
    sub_ty_sub_tm sigma tau theta e1; upn_sub_ty_sub_tm 1 sigma tau theta;
    sub_ty_sub_tm sigma (up_esub tau) (up_esub theta) e2
  | ELetRec bs b ->
    upn_sub_ty_sub_tm (L.length bs) sigma tau theta;
    sub_ty_sub_tm_binds sigma (upn_esub (L.length bs) tau) (upn_esub (L.length bs) theta) bs;
    sub_ty_sub_tm sigma (upn_esub (L.length bs) tau) (upn_esub (L.length bs) theta) b
  | ECase es dt -> sub_ty_sub_tm_exps sigma tau theta es; sub_ty_sub_tm_dt sigma tau theta dt
  | ELetJoin ts _ e1 e2 ->
    jup_sub_ty_sub_tm sigma tau theta;
    upn_sub_ty_sub_tm (L.length ts) sigma (jup_esub tau) (jup_esub theta);
    sub_ty_sub_tm sigma (upn_esub (L.length ts) (jup_esub tau))
      (upn_esub (L.length ts) (jup_esub theta)) e1;
    sub_ty_sub_tm sigma (jup_esub tau) (jup_esub theta) e2
  | EJump _ es -> sub_ty_sub_tm_exps sigma tau theta es
  | EExtend _ e1 e2 -> sub_ty_sub_tm sigma tau theta e1; sub_ty_sub_tm sigma tau theta e2
  | ESelect _ b -> sub_ty_sub_tm sigma tau theta b
  | ERestrict _ b -> sub_ty_sub_tm sigma tau theta b
  | EUpdate _ e1 e2 -> sub_ty_sub_tm sigma tau theta e1; sub_ty_sub_tm sigma tau theta e2
  | EMerge e1 e2 -> sub_ty_sub_tm sigma tau theta e1; sub_ty_sub_tm sigma tau theta e2
  | EInject _ _ b -> sub_ty_sub_tm sigma tau theta b
  | EWeaken _ _ b -> sub_ty_sub_tm sigma tau theta b
  | EAbsurd _ b -> sub_ty_sub_tm sigma tau theta b
  | EPerform _ _ _ b -> sub_ty_sub_tm sigma tau theta b
  | EHandle b h ->
    sub_ty_sub_tm sigma tau theta b; upn_sub_ty_sub_tm 1 sigma tau theta;
    sub_ty_sub_tm sigma (up_esub tau) (up_esub theta) h.h_ret;
    sub_ty_sub_tm_cls sigma tau theta h.h_clauses
  | EOpenEff _ b -> sub_ty_sub_tm sigma tau theta b
  | ERegion _ es b -> sub_ty_sub_tm_exps sigma tau theta es; sub_ty_sub_tm sigma tau theta b
  | EWriteCell _ _ b -> sub_ty_sub_tm sigma tau theta b
  | ESpine _ sp -> sub_ty_sub_tm_spine sigma tau theta sp
  | EMatch th dt -> sub_ty_sub_tm_exps sigma tau theta th; sub_ty_sub_tm_dt sigma tau theta dt
  | EOpenEffC _ b -> sub_ty_sub_tm sigma tau theta b
  | EFill _ b -> sub_ty_sub_tm sigma tau theta b
  | ERegionOpen _ th b -> sub_ty_sub_tm_cells sigma tau theta th; sub_ty_sub_tm sigma tau theta b

and sub_ty_sub_tm_exps (sigma: tsub) (tau: esub) (theta: esub) (es: list exp)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_exps sigma (sub_tm_exps tau es)
                     == sub_tm_exps theta (sub_ty_exps sigma es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> sub_ty_sub_tm sigma tau theta e; sub_ty_sub_tm_exps sigma tau theta es

and sub_ty_sub_tm_binds (sigma: tsub) (tau: esub) (theta: esub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_binds sigma (sub_tm_binds tau bs)
                     == sub_tm_binds theta (sub_ty_binds sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> sub_ty_sub_tm sigma tau theta e; sub_ty_sub_tm_binds sigma tau theta bs

and sub_ty_sub_tm_cells (sigma: tsub) (tau: esub) (theta: esub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_cells sigma (sub_tm_cells tau th)
                     == sub_tm_cells theta (sub_ty_cells sigma th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> sub_ty_sub_tm sigma tau theta e; sub_ty_sub_tm_cells sigma tau theta th

and sub_ty_sub_tm_spine (sigma: tsub) (tau: esub) (theta: esub) (sp: list spine_arg)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_spine sigma (sub_tm_spine tau sp)
                     == sub_tm_spine theta (sub_ty_spine sigma sp))
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> sub_ty_sub_tm_spine sigma tau theta sp
  | STy _ :: sp -> sub_ty_sub_tm_spine sigma tau theta sp
  | SConstr :: sp -> sub_ty_sub_tm_spine sigma tau theta sp
  | SVal v :: sp -> sub_ty_sub_tm sigma tau theta v; sub_ty_sub_tm_spine sigma tau theta sp

and sub_ty_sub_tm_dt (sigma: tsub) (tau: esub) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_dt sigma (sub_tm_dt tau dt) == sub_tm_dt theta (sub_ty_dt sigma dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> sub_ty_sub_tm sigma tau theta e
  | DBind _ dt ->
    upn_sub_ty_sub_tm 1 sigma tau theta; sub_ty_sub_tm_dt sigma (up_esub tau) (up_esub theta) dt
  | DSwitchCtor _ bs df ->
    sub_ty_sub_tm_brs sigma tau theta bs; sub_ty_sub_tm_odt sigma tau theta df
  | DSwitchLit _ bs df -> sub_ty_sub_tm_brs sigma tau theta bs; sub_ty_sub_tm_dt sigma tau theta df
  | DSwitchKey _ bs df -> sub_ty_sub_tm_brs sigma tau theta bs; sub_ty_sub_tm_odt sigma tau theta df
  | DGuard e dt1 dt2 ->
    sub_ty_sub_tm sigma tau theta e; sub_ty_sub_tm_dt sigma tau theta dt1;
    sub_ty_sub_tm_dt sigma tau theta dt2

and sub_ty_sub_tm_odt (sigma: tsub) (tau: esub) (theta: esub) (df: option dtree)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_odt sigma (sub_tm_odt tau df) == sub_tm_odt theta (sub_ty_odt sigma df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> sub_ty_sub_tm_dt sigma tau theta dt

and sub_ty_sub_tm_brs (#lb: eqtype) (sigma: tsub) (tau: esub) (theta: esub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_brs sigma (sub_tm_brs tau bs) == sub_tm_brs theta (sub_ty_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> sub_ty_sub_tm_dt sigma tau theta dt; sub_ty_sub_tm_brs sigma tau theta bs

and sub_ty_sub_tm_cls (sigma: tsub) (tau: esub) (theta: esub) (cs: list clause)
  : Lemma (requires forall (i: nat). theta i == sub_ty_exp sigma (tau i))
          (ensures sub_ty_cls sigma (sub_tm_cls tau cs) == sub_tm_cls theta (sub_ty_cls sigma cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    tyup_sub_ty_sub_tm nb sigma tau theta;
    upn_sub_ty_sub_tm 2 (upn_tsub nb sigma) (tyup_esub nb tau) (tyup_esub nb theta);
    sub_ty_sub_tm (upn_tsub nb sigma) (upn_esub 2 (tyup_esub nb tau))
      (upn_esub 2 (tyup_esub nb theta)) b; sub_ty_sub_tm_cls sigma tau theta cs
  | CFast _ nb _ b :: cs ->
    tyup_sub_ty_sub_tm nb sigma tau theta;
    upn_sub_ty_sub_tm 1 (upn_tsub nb sigma) (tyup_esub nb tau) (tyup_esub nb theta);
    sub_ty_sub_tm (upn_tsub nb sigma) (up_esub (tyup_esub nb tau)) (up_esub (tyup_esub nb theta)) b;
    sub_ty_sub_tm_cls sigma tau theta cs

let ren_ty_sub_tm (xi: ren) (tau theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == ren_ty_exp xi (tau i))
          (ensures ren_ty_exp xi (sub_tm tau e) == sub_tm theta (ren_ty_exp xi e)) =
  ren_ty_exp_as_sub xi (sub_tm tau e); ren_ty_exp_as_sub xi e;
  introduce forall (i: nat). theta i == sub_ty_exp (ren_tsub xi) (tau i)
  with ren_ty_exp_as_sub xi (tau i);
  sub_ty_sub_tm (ren_tsub xi) tau theta e

let upn_sub_sub_tm (n: nat) (tau sigma theta: esub)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures forall (i: nat).
             upn_esub n theta i == sub_tm (upn_esub n tau) (upn_esub n sigma i)) =
  introduce forall (i: nat). upn_esub n theta i == sub_tm (upn_esub n tau) (upn_esub n sigma i)
  with if i < n then () else begin
    ren_sub_tm (shift n) tau (esub_shift n tau) (sigma (i - n));
    sub_ren_tm (upn_esub n tau) (shift n) (esub_shift n tau) (sigma (i - n))
  end

let tyup_sub_sub_tm (m: nat) (tau sigma theta: esub)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures forall (i: nat).
             tyup_esub m theta i == sub_tm (tyup_esub m tau) (tyup_esub m sigma i)) =
  introduce forall (i: nat). tyup_esub m theta i == sub_tm (tyup_esub m tau) (tyup_esub m sigma i)
  with ren_ty_sub_tm (shift m) tau (tyup_esub m tau) (sigma i)

let jup_sub_sub_tm (tau sigma theta: esub)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures forall (i: nat). jup_esub theta i == sub_tm (jup_esub tau) (jup_esub sigma i)) =
  introduce forall (i: nat). jup_esub theta i == sub_tm (jup_esub tau) (jup_esub sigma i)
  with ren_jp_sub_tm (shift 1) tau (jup_esub tau) (sigma i)

let rec sub_sub_tm (tau: esub) (sigma: esub) (theta: esub) (e: exp)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm tau (sub_tm sigma e) == sub_tm theta e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b ->
    upn_sub_sub_tm 1 tau sigma theta; sub_sub_tm (up_esub tau) (up_esub sigma) (up_esub theta) b
  | EApp e1 e2 -> sub_sub_tm tau sigma theta e1; sub_sub_tm tau sigma theta e2
  | ETyLam _ b ->
    tyup_sub_sub_tm 1 tau sigma theta;
    sub_sub_tm (tyup_esub 1 tau) (tyup_esub 1 sigma) (tyup_esub 1 theta) b
  | ETyApp b _ -> sub_sub_tm tau sigma theta b
  | ECLam _ b -> sub_sub_tm tau sigma theta b
  | ECApp b -> sub_sub_tm tau sigma theta b
  | ELet _ e1 e2 ->
    sub_sub_tm tau sigma theta e1; upn_sub_sub_tm 1 tau sigma theta;
    sub_sub_tm (up_esub tau) (up_esub sigma) (up_esub theta) e2
  | ELetRec bs b ->
    upn_sub_sub_tm (L.length bs) tau sigma theta;
    sub_sub_tm_binds (upn_esub (L.length bs) tau) (upn_esub (L.length bs) sigma)
      (upn_esub (L.length bs) theta) bs;
    sub_sub_tm (upn_esub (L.length bs) tau) (upn_esub (L.length bs) sigma)
      (upn_esub (L.length bs) theta) b
  | ECase es dt -> sub_sub_tm_exps tau sigma theta es; sub_sub_tm_dt tau sigma theta dt
  | ELetJoin ts _ e1 e2 ->
    jup_sub_sub_tm tau sigma theta;
    upn_sub_sub_tm (L.length ts) (jup_esub tau) (jup_esub sigma) (jup_esub theta);
    sub_sub_tm (upn_esub (L.length ts) (jup_esub tau)) (upn_esub (L.length ts) (jup_esub sigma))
      (upn_esub (L.length ts) (jup_esub theta)) e1;
    sub_sub_tm (jup_esub tau) (jup_esub sigma) (jup_esub theta) e2
  | EJump _ es -> sub_sub_tm_exps tau sigma theta es
  | EExtend _ e1 e2 -> sub_sub_tm tau sigma theta e1; sub_sub_tm tau sigma theta e2
  | ESelect _ b -> sub_sub_tm tau sigma theta b
  | ERestrict _ b -> sub_sub_tm tau sigma theta b
  | EUpdate _ e1 e2 -> sub_sub_tm tau sigma theta e1; sub_sub_tm tau sigma theta e2
  | EMerge e1 e2 -> sub_sub_tm tau sigma theta e1; sub_sub_tm tau sigma theta e2
  | EInject _ _ b -> sub_sub_tm tau sigma theta b
  | EWeaken _ _ b -> sub_sub_tm tau sigma theta b
  | EAbsurd _ b -> sub_sub_tm tau sigma theta b
  | EPerform _ _ _ b -> sub_sub_tm tau sigma theta b
  | EHandle b h ->
    sub_sub_tm tau sigma theta b; upn_sub_sub_tm 1 tau sigma theta;
    sub_sub_tm (up_esub tau) (up_esub sigma) (up_esub theta) h.h_ret;
    sub_sub_tm_cls tau sigma theta h.h_clauses
  | EOpenEff _ b -> sub_sub_tm tau sigma theta b
  | ERegion _ es b -> sub_sub_tm_exps tau sigma theta es; sub_sub_tm tau sigma theta b
  | EWriteCell _ _ b -> sub_sub_tm tau sigma theta b
  | ESpine _ sp -> sub_sub_tm_spine tau sigma theta sp
  | EMatch th dt -> sub_sub_tm_exps tau sigma theta th; sub_sub_tm_dt tau sigma theta dt
  | EOpenEffC _ b -> sub_sub_tm tau sigma theta b
  | EFill _ b -> sub_sub_tm tau sigma theta b
  | ERegionOpen _ th b -> sub_sub_tm_cells tau sigma theta th; sub_sub_tm tau sigma theta b

and sub_sub_tm_exps (tau: esub) (sigma: esub) (theta: esub) (es: list exp)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm_exps tau (sub_tm_exps sigma es) == sub_tm_exps theta es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> sub_sub_tm tau sigma theta e; sub_sub_tm_exps tau sigma theta es

and sub_sub_tm_binds (tau: esub) (sigma: esub) (theta: esub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm_binds tau (sub_tm_binds sigma bs) == sub_tm_binds theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> sub_sub_tm tau sigma theta e; sub_sub_tm_binds tau sigma theta bs

and sub_sub_tm_cells (tau: esub) (sigma: esub) (theta: esub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm_cells tau (sub_tm_cells sigma th) == sub_tm_cells theta th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> sub_sub_tm tau sigma theta e; sub_sub_tm_cells tau sigma theta th

and sub_sub_tm_spine (tau: esub) (sigma: esub) (theta: esub) (sp: list spine_arg)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm_spine tau (sub_tm_spine sigma sp) == sub_tm_spine theta sp)
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> sub_sub_tm_spine tau sigma theta sp
  | STy _ :: sp -> sub_sub_tm_spine tau sigma theta sp
  | SConstr :: sp -> sub_sub_tm_spine tau sigma theta sp
  | SVal v :: sp -> sub_sub_tm tau sigma theta v; sub_sub_tm_spine tau sigma theta sp

and sub_sub_tm_dt (tau: esub) (sigma: esub) (theta: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm_dt tau (sub_tm_dt sigma dt) == sub_tm_dt theta dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> sub_sub_tm tau sigma theta e
  | DBind _ dt ->
    upn_sub_sub_tm 1 tau sigma theta;
    sub_sub_tm_dt (up_esub tau) (up_esub sigma) (up_esub theta) dt
  | DSwitchCtor _ bs df -> sub_sub_tm_brs tau sigma theta bs; sub_sub_tm_odt tau sigma theta df
  | DSwitchLit _ bs df -> sub_sub_tm_brs tau sigma theta bs; sub_sub_tm_dt tau sigma theta df
  | DSwitchKey _ bs df -> sub_sub_tm_brs tau sigma theta bs; sub_sub_tm_odt tau sigma theta df
  | DGuard e dt1 dt2 ->
    sub_sub_tm tau sigma theta e; sub_sub_tm_dt tau sigma theta dt1;
    sub_sub_tm_dt tau sigma theta dt2

and sub_sub_tm_odt (tau: esub) (sigma: esub) (theta: esub) (df: option dtree)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm_odt tau (sub_tm_odt sigma df) == sub_tm_odt theta df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> sub_sub_tm_dt tau sigma theta dt

and sub_sub_tm_brs (#lb: eqtype) (tau: esub) (sigma: esub) (theta: esub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm_brs tau (sub_tm_brs sigma bs) == sub_tm_brs theta bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> sub_sub_tm_dt tau sigma theta dt; sub_sub_tm_brs tau sigma theta bs

and sub_sub_tm_cls (tau: esub) (sigma: esub) (theta: esub) (cs: list clause)
  : Lemma (requires forall (i: nat). theta i == sub_tm tau (sigma i))
          (ensures sub_tm_cls tau (sub_tm_cls sigma cs) == sub_tm_cls theta cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    tyup_sub_sub_tm nb tau sigma theta;
    upn_sub_sub_tm 2 (tyup_esub nb tau) (tyup_esub nb sigma) (tyup_esub nb theta);
    sub_sub_tm (upn_esub 2 (tyup_esub nb tau)) (upn_esub 2 (tyup_esub nb sigma))
      (upn_esub 2 (tyup_esub nb theta)) b; sub_sub_tm_cls tau sigma theta cs
  | CFast _ nb _ b :: cs ->
    tyup_sub_sub_tm nb tau sigma theta;
    upn_sub_sub_tm 1 (tyup_esub nb tau) (tyup_esub nb sigma) (tyup_esub nb theta);
    sub_sub_tm (up_esub (tyup_esub nb tau)) (up_esub (tyup_esub nb sigma))
      (up_esub (tyup_esub nb theta)) b; sub_sub_tm_cls tau sigma theta cs

let upn_sub_id_tm (n: nat) (sigma: esub)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures forall (i: nat). upn_esub n sigma i == EVar i) = ()

let tyup_sub_id_tm (m: nat) (sigma: esub)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures forall (i: nat). tyup_esub m sigma i == EVar i) = ()

let jup_sub_id_tm (sigma: esub)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures forall (i: nat). jup_esub sigma i == EVar i) = ()

let rec sub_id_tm (sigma: esub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm sigma e == e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> upn_sub_id_tm 1 sigma; sub_id_tm (up_esub sigma) b
  | EApp e1 e2 -> sub_id_tm sigma e1; sub_id_tm sigma e2
  | ETyLam _ b -> tyup_sub_id_tm 1 sigma; sub_id_tm (tyup_esub 1 sigma) b
  | ETyApp b _ -> sub_id_tm sigma b
  | ECLam _ b -> sub_id_tm sigma b
  | ECApp b -> sub_id_tm sigma b
  | ELet _ e1 e2 -> sub_id_tm sigma e1; upn_sub_id_tm 1 sigma; sub_id_tm (up_esub sigma) e2
  | ELetRec bs b ->
    upn_sub_id_tm (L.length bs) sigma; sub_id_tm_binds (upn_esub (L.length bs) sigma) bs;
    sub_id_tm (upn_esub (L.length bs) sigma) b
  | ECase es dt -> sub_id_tm_exps sigma es; sub_id_tm_dt sigma dt
  | ELetJoin ts _ e1 e2 ->
    jup_sub_id_tm sigma; upn_sub_id_tm (L.length ts) (jup_esub sigma);
    sub_id_tm (upn_esub (L.length ts) (jup_esub sigma)) e1; sub_id_tm (jup_esub sigma) e2
  | EJump _ es -> sub_id_tm_exps sigma es
  | EExtend _ e1 e2 -> sub_id_tm sigma e1; sub_id_tm sigma e2
  | ESelect _ b -> sub_id_tm sigma b
  | ERestrict _ b -> sub_id_tm sigma b
  | EUpdate _ e1 e2 -> sub_id_tm sigma e1; sub_id_tm sigma e2
  | EMerge e1 e2 -> sub_id_tm sigma e1; sub_id_tm sigma e2
  | EInject _ _ b -> sub_id_tm sigma b
  | EWeaken _ _ b -> sub_id_tm sigma b
  | EAbsurd _ b -> sub_id_tm sigma b
  | EPerform _ _ _ b -> sub_id_tm sigma b
  | EHandle b h ->
    sub_id_tm sigma b; upn_sub_id_tm 1 sigma; sub_id_tm (up_esub sigma) h.h_ret;
    sub_id_tm_cls sigma h.h_clauses
  | EOpenEff _ b -> sub_id_tm sigma b
  | ERegion _ es b -> sub_id_tm_exps sigma es; sub_id_tm sigma b
  | EWriteCell _ _ b -> sub_id_tm sigma b
  | ESpine _ sp -> sub_id_tm_spine sigma sp
  | EMatch th dt -> sub_id_tm_exps sigma th; sub_id_tm_dt sigma dt
  | EOpenEffC _ b -> sub_id_tm sigma b
  | EFill _ b -> sub_id_tm sigma b
  | ERegionOpen _ th b -> sub_id_tm_cells sigma th; sub_id_tm sigma b

and sub_id_tm_exps (sigma: esub) (es: list exp)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm_exps sigma es == es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> sub_id_tm sigma e; sub_id_tm_exps sigma es

and sub_id_tm_binds (sigma: esub) (bs: list (typ & exp))
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm_binds sigma bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> sub_id_tm sigma e; sub_id_tm_binds sigma bs

and sub_id_tm_cells (sigma: esub) (th: list (key & exp))
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm_cells sigma th == th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> sub_id_tm sigma e; sub_id_tm_cells sigma th

and sub_id_tm_spine (sigma: esub) (sp: list spine_arg)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm_spine sigma sp == sp)
          (decreases sp) =
  match sp with
  | [] -> ()
  | SKinds _ :: sp -> sub_id_tm_spine sigma sp
  | STy _ :: sp -> sub_id_tm_spine sigma sp
  | SConstr :: sp -> sub_id_tm_spine sigma sp
  | SVal v :: sp -> sub_id_tm sigma v; sub_id_tm_spine sigma sp

and sub_id_tm_dt (sigma: esub) (dt: dtree)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm_dt sigma dt == dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> sub_id_tm sigma e
  | DBind _ dt -> upn_sub_id_tm 1 sigma; sub_id_tm_dt (up_esub sigma) dt
  | DSwitchCtor _ bs df -> sub_id_tm_brs sigma bs; sub_id_tm_odt sigma df
  | DSwitchLit _ bs df -> sub_id_tm_brs sigma bs; sub_id_tm_dt sigma df
  | DSwitchKey _ bs df -> sub_id_tm_brs sigma bs; sub_id_tm_odt sigma df
  | DGuard e dt1 dt2 -> sub_id_tm sigma e; sub_id_tm_dt sigma dt1; sub_id_tm_dt sigma dt2

and sub_id_tm_odt (sigma: esub) (df: option dtree)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm_odt sigma df == df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> sub_id_tm_dt sigma dt

and sub_id_tm_brs (#lb: eqtype) (sigma: esub) (bs: list (lb & dtree))
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm_brs sigma bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> sub_id_tm_dt sigma dt; sub_id_tm_brs sigma bs

and sub_id_tm_cls (sigma: esub) (cs: list clause)
  : Lemma (requires forall (i: nat). sigma i == EVar i)
          (ensures sub_tm_cls sigma cs == cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    tyup_sub_id_tm nb sigma; upn_sub_id_tm 2 (tyup_esub nb sigma);
    sub_id_tm (upn_esub 2 (tyup_esub nb sigma)) b; sub_id_tm_cls sigma cs
  | CFast _ nb _ b :: cs ->
    tyup_sub_id_tm nb sigma; upn_sub_id_tm 1 (tyup_esub nb sigma);
    sub_id_tm (up_esub (tyup_esub nb sigma)) b; sub_id_tm_cls sigma cs

let sub_tm_ext (sigma sigma': esub) (e: exp)
  : Lemma (requires forall (i: nat). sigma i == sigma' i)
          (ensures sub_tm sigma e == sub_tm sigma' e) =
  sub_sub_tm sigma' evar sigma e; sub_id_tm evar e

let ren_tm_ext (xi xi': ren) (e: exp)
  : Lemma (requires forall (i: nat). xi i == xi' i)
          (ensures ren_tm xi e == ren_tm xi' e) =
  ren_ren_tm xi' id_ren xi e; ren_tm_as_sub id_ren e; sub_id_tm (ren_esub id_ren) e

let sub_tm_evar (e: exp) : Lemma (sub_tm evar e == e) = sub_id_tm evar e

let ren_tm_id (e: exp) : Lemma (ren_tm id_ren e == e) =
  ren_tm_as_sub id_ren e; sub_id_tm (ren_esub id_ren) e

let ren_tm_shift0 (e: exp) : Lemma (ren_tm (shift 0) e == e) =
  ren_tm_as_sub (shift 0) e; sub_id_tm (ren_esub (shift 0)) e

let ren_jp_shift0 (e: exp) : Lemma (ren_jp (shift 0) e == e) = ren_id_jp (shift 0) e
