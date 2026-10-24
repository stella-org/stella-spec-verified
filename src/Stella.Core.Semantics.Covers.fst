(* Coverage under the operations of a step.

   The operations that keep `globals` are one mutual induction each over
   the term classes (`g_*`), all of one shape: every node's names
   are its own, if it is a global, followed by those of its subterms, and
   the operation keeps the node's constructor and its global, if any. The
   parameter of the operation is quantified in the statement, so that the
   induction at a binder, where the parameter is lifted, is the same call
   as anywhere else; the quantifier is triggered on the operation applied
   to the subterm.

   Term substitution is an induction on `exp_all (covered sg gi)` directly,
   with `esub_covers` carried under binders by the lifting lemmas
   (`esub_covers_upn`, `_tyup`, `_jup`), whose substitutes are renamings of
   covered terms. *)
module Stella.Core.Semantics.Covers
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.Sig
open Stella.Core.Typing.Aux
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let covers_globals_eq sg gi e e' =
  covers_globals sg gi e;
  covers_globals sg gi e'

(* * Lists and branches *)

let rec covers_exps sg gi es =
  match es with
  | [] -> ()
  | _ :: es' -> covers_exps sg gi es'

let rec covers_branch #lb sg gi l bs dt =
  match bs with
  | (l', _) :: bs' -> if l' = l then () else covers_branch sg gi l bs' dt

(* * Operations that keep the global names *)

(* ** `kinst_exp` *)

let rec g_kinst (e: exp)
  : Lemma (ensures forall (ks: list kind). {:pattern (kinst_exp ks e)}
                     globals (kinst_exp ks e) == globals e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> g_kinst b
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> g_kinst e1; g_kinst e2
  | ELetRec bs b -> g_kinst_binds bs; g_kinst b
  | ECase es dt | EMatch es dt -> g_kinst_exps es; g_kinst_dt dt
  | EJump _ es -> g_kinst_exps es
  | EHandle b h -> g_kinst b; g_kinst h.h_ret; g_kinst_cls h.h_clauses
  | ERegion _ es b -> g_kinst_exps es; g_kinst b
  | ERegionOpen _ th b -> g_kinst_cells th; g_kinst b

and g_kinst_exps (es: list exp)
  : Lemma (ensures forall (ks: list kind). {:pattern (kinst_exps ks es)}
                     globals_exps (kinst_exps ks es) == globals_exps es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es' -> g_kinst e; g_kinst_exps es'

and g_kinst_binds (bs: list (typ & exp))
  : Lemma (ensures forall (ks: list kind). {:pattern (kinst_binds ks bs)}
                     globals_binds (kinst_binds ks bs) == globals_binds bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs' -> g_kinst e; g_kinst_binds bs'

and g_kinst_cells (th: list (key & exp))
  : Lemma (ensures forall (ks: list kind). {:pattern (kinst_cells ks th)}
                     globals_cells (kinst_cells ks th) == globals_cells th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th' -> g_kinst e; g_kinst_cells th'

and g_kinst_dt (dt: dtree)
  : Lemma (ensures forall (ks: list kind). {:pattern (kinst_dt ks dt)}
                     globals_dt (kinst_dt ks dt) == globals_dt dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> g_kinst e
  | DBind _ dt' -> g_kinst_dt dt'
  | DSwitchCtor _ bs df -> g_kinst_brs bs; g_kinst_odt df
  | DSwitchLit _ bs df -> g_kinst_brs bs; g_kinst_dt df
  | DSwitchKey _ bs df -> g_kinst_brs bs; g_kinst_odt df
  | DGuard e dt1 dt2 -> g_kinst e; g_kinst_dt dt1; g_kinst_dt dt2

and g_kinst_odt (df: option dtree)
  : Lemma (ensures forall (ks: list kind). {:pattern (kinst_odt ks df)}
                     globals_odt (kinst_odt ks df) == globals_odt df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> g_kinst_dt dt

and g_kinst_brs (#lb: eqtype) (bs: list (lb & dtree))
  : Lemma (ensures forall (ks: list kind). {:pattern (kinst_brs #lb ks bs)}
                     globals_brs (kinst_brs #lb ks bs) == globals_brs bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs' -> g_kinst_dt dt; g_kinst_brs bs'

and g_kinst_cls (cs: list clause)
  : Lemma (ensures forall (ks: list kind). {:pattern (kinst_cls ks cs)}
                     globals_cls (kinst_cls ks cs) == globals_cls cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs' -> g_kinst b; g_kinst_cls cs'
  | CFast _ _ _ b :: cs' -> g_kinst b; g_kinst_cls cs'

(* ** `sub_ty_exp` *)

let rec g_sub_ty (e: exp)
  : Lemma (ensures forall (sigma: tsub). {:pattern (sub_ty_exp sigma e)}
                     globals (sub_ty_exp sigma e) == globals e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> g_sub_ty b
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> g_sub_ty e1; g_sub_ty e2
  | ELetRec bs b -> g_sub_ty_binds bs; g_sub_ty b
  | ECase es dt | EMatch es dt -> g_sub_ty_exps es; g_sub_ty_dt dt
  | EJump _ es -> g_sub_ty_exps es
  | EHandle b h -> g_sub_ty b; g_sub_ty h.h_ret; g_sub_ty_cls h.h_clauses
  | ERegion _ es b -> g_sub_ty_exps es; g_sub_ty b
  | ERegionOpen _ th b -> g_sub_ty_cells th; g_sub_ty b

and g_sub_ty_exps (es: list exp)
  : Lemma (ensures forall (sigma: tsub). {:pattern (sub_ty_exps sigma es)}
                     globals_exps (sub_ty_exps sigma es) == globals_exps es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es' -> g_sub_ty e; g_sub_ty_exps es'

and g_sub_ty_binds (bs: list (typ & exp))
  : Lemma (ensures forall (sigma: tsub). {:pattern (sub_ty_binds sigma bs)}
                     globals_binds (sub_ty_binds sigma bs) == globals_binds bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs' -> g_sub_ty e; g_sub_ty_binds bs'

and g_sub_ty_cells (th: list (key & exp))
  : Lemma (ensures forall (sigma: tsub). {:pattern (sub_ty_cells sigma th)}
                     globals_cells (sub_ty_cells sigma th) == globals_cells th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th' -> g_sub_ty e; g_sub_ty_cells th'

and g_sub_ty_dt (dt: dtree)
  : Lemma (ensures forall (sigma: tsub). {:pattern (sub_ty_dt sigma dt)}
                     globals_dt (sub_ty_dt sigma dt) == globals_dt dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> g_sub_ty e
  | DBind _ dt' -> g_sub_ty_dt dt'
  | DSwitchCtor _ bs df -> g_sub_ty_brs bs; g_sub_ty_odt df
  | DSwitchLit _ bs df -> g_sub_ty_brs bs; g_sub_ty_dt df
  | DSwitchKey _ bs df -> g_sub_ty_brs bs; g_sub_ty_odt df
  | DGuard e dt1 dt2 -> g_sub_ty e; g_sub_ty_dt dt1; g_sub_ty_dt dt2

and g_sub_ty_odt (df: option dtree)
  : Lemma (ensures forall (sigma: tsub). {:pattern (sub_ty_odt sigma df)}
                     globals_odt (sub_ty_odt sigma df) == globals_odt df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> g_sub_ty_dt dt

and g_sub_ty_brs (#lb: eqtype) (bs: list (lb & dtree))
  : Lemma (ensures forall (sigma: tsub). {:pattern (sub_ty_brs #lb sigma bs)}
                     globals_brs (sub_ty_brs #lb sigma bs) == globals_brs bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs' -> g_sub_ty_dt dt; g_sub_ty_brs bs'

and g_sub_ty_cls (cs: list clause)
  : Lemma (ensures forall (sigma: tsub). {:pattern (sub_ty_cls sigma cs)}
                     globals_cls (sub_ty_cls sigma cs) == globals_cls cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs' -> g_sub_ty b; g_sub_ty_cls cs'
  | CFast _ _ _ b :: cs' -> g_sub_ty b; g_sub_ty_cls cs'

(* ** `ren_ty_exp` *)

let rec g_ren_ty (e: exp)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_ty_exp xi e)}
                     globals (ren_ty_exp xi e) == globals e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> g_ren_ty b
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> g_ren_ty e1; g_ren_ty e2
  | ELetRec bs b -> g_ren_ty_binds bs; g_ren_ty b
  | ECase es dt | EMatch es dt -> g_ren_ty_exps es; g_ren_ty_dt dt
  | EJump _ es -> g_ren_ty_exps es
  | EHandle b h -> g_ren_ty b; g_ren_ty h.h_ret; g_ren_ty_cls h.h_clauses
  | ERegion _ es b -> g_ren_ty_exps es; g_ren_ty b
  | ERegionOpen _ th b -> g_ren_ty_cells th; g_ren_ty b

and g_ren_ty_exps (es: list exp)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_ty_exps xi es)}
                     globals_exps (ren_ty_exps xi es) == globals_exps es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es' -> g_ren_ty e; g_ren_ty_exps es'

and g_ren_ty_binds (bs: list (typ & exp))
  : Lemma (ensures forall (xi: ren). {:pattern (ren_ty_binds xi bs)}
                     globals_binds (ren_ty_binds xi bs) == globals_binds bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs' -> g_ren_ty e; g_ren_ty_binds bs'

and g_ren_ty_cells (th: list (key & exp))
  : Lemma (ensures forall (xi: ren). {:pattern (ren_ty_cells xi th)}
                     globals_cells (ren_ty_cells xi th) == globals_cells th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th' -> g_ren_ty e; g_ren_ty_cells th'

and g_ren_ty_dt (dt: dtree)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_ty_dt xi dt)}
                     globals_dt (ren_ty_dt xi dt) == globals_dt dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> g_ren_ty e
  | DBind _ dt' -> g_ren_ty_dt dt'
  | DSwitchCtor _ bs df -> g_ren_ty_brs bs; g_ren_ty_odt df
  | DSwitchLit _ bs df -> g_ren_ty_brs bs; g_ren_ty_dt df
  | DSwitchKey _ bs df -> g_ren_ty_brs bs; g_ren_ty_odt df
  | DGuard e dt1 dt2 -> g_ren_ty e; g_ren_ty_dt dt1; g_ren_ty_dt dt2

and g_ren_ty_odt (df: option dtree)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_ty_odt xi df)}
                     globals_odt (ren_ty_odt xi df) == globals_odt df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> g_ren_ty_dt dt

and g_ren_ty_brs (#lb: eqtype) (bs: list (lb & dtree))
  : Lemma (ensures forall (xi: ren). {:pattern (ren_ty_brs #lb xi bs)}
                     globals_brs (ren_ty_brs #lb xi bs) == globals_brs bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs' -> g_ren_ty_dt dt; g_ren_ty_brs bs'

and g_ren_ty_cls (cs: list clause)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_ty_cls xi cs)}
                     globals_cls (ren_ty_cls xi cs) == globals_cls cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs' -> g_ren_ty b; g_ren_ty_cls cs'
  | CFast _ _ _ b :: cs' -> g_ren_ty b; g_ren_ty_cls cs'

(* ** `ren_tm` *)

let rec g_ren_tm (e: exp)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_tm xi e)}
                     globals (ren_tm xi e) == globals e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> g_ren_tm b
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> g_ren_tm e1; g_ren_tm e2
  | ELetRec bs b -> g_ren_tm_binds bs; g_ren_tm b
  | ECase es dt | EMatch es dt -> g_ren_tm_exps es; g_ren_tm_dt dt
  | EJump _ es -> g_ren_tm_exps es
  | EHandle b h -> g_ren_tm b; g_ren_tm h.h_ret; g_ren_tm_cls h.h_clauses
  | ERegion _ es b -> g_ren_tm_exps es; g_ren_tm b
  | ERegionOpen _ th b -> g_ren_tm_cells th; g_ren_tm b

and g_ren_tm_exps (es: list exp)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_tm_exps xi es)}
                     globals_exps (ren_tm_exps xi es) == globals_exps es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es' -> g_ren_tm e; g_ren_tm_exps es'

and g_ren_tm_binds (bs: list (typ & exp))
  : Lemma (ensures forall (xi: ren). {:pattern (ren_tm_binds xi bs)}
                     globals_binds (ren_tm_binds xi bs) == globals_binds bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs' -> g_ren_tm e; g_ren_tm_binds bs'

and g_ren_tm_cells (th: list (key & exp))
  : Lemma (ensures forall (xi: ren). {:pattern (ren_tm_cells xi th)}
                     globals_cells (ren_tm_cells xi th) == globals_cells th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th' -> g_ren_tm e; g_ren_tm_cells th'

and g_ren_tm_dt (dt: dtree)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_tm_dt xi dt)}
                     globals_dt (ren_tm_dt xi dt) == globals_dt dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> g_ren_tm e
  | DBind _ dt' -> g_ren_tm_dt dt'
  | DSwitchCtor _ bs df -> g_ren_tm_brs bs; g_ren_tm_odt df
  | DSwitchLit _ bs df -> g_ren_tm_brs bs; g_ren_tm_dt df
  | DSwitchKey _ bs df -> g_ren_tm_brs bs; g_ren_tm_odt df
  | DGuard e dt1 dt2 -> g_ren_tm e; g_ren_tm_dt dt1; g_ren_tm_dt dt2

and g_ren_tm_odt (df: option dtree)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_tm_odt xi df)}
                     globals_odt (ren_tm_odt xi df) == globals_odt df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> g_ren_tm_dt dt

and g_ren_tm_brs (#lb: eqtype) (bs: list (lb & dtree))
  : Lemma (ensures forall (xi: ren). {:pattern (ren_tm_brs #lb xi bs)}
                     globals_brs (ren_tm_brs #lb xi bs) == globals_brs bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs' -> g_ren_tm_dt dt; g_ren_tm_brs bs'

and g_ren_tm_cls (cs: list clause)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_tm_cls xi cs)}
                     globals_cls (ren_tm_cls xi cs) == globals_cls cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs' -> g_ren_tm b; g_ren_tm_cls cs'
  | CFast _ _ _ b :: cs' -> g_ren_tm b; g_ren_tm_cls cs'

(* ** `ren_jp` *)

let rec g_ren_jp (e: exp)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_jp xi e)}
                     globals (ren_jp xi e) == globals e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> g_ren_jp b
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> g_ren_jp e1; g_ren_jp e2
  | ELetRec bs b -> g_ren_jp_binds bs; g_ren_jp b
  | ECase es dt | EMatch es dt -> g_ren_jp_exps es; g_ren_jp_dt dt
  | EJump _ es -> g_ren_jp_exps es
  | EHandle b h -> g_ren_jp b; g_ren_jp h.h_ret; g_ren_jp_cls h.h_clauses
  | ERegion _ es b -> g_ren_jp_exps es; g_ren_jp b
  | ERegionOpen _ th b -> g_ren_jp_cells th; g_ren_jp b

and g_ren_jp_exps (es: list exp)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_jp_exps xi es)}
                     globals_exps (ren_jp_exps xi es) == globals_exps es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es' -> g_ren_jp e; g_ren_jp_exps es'

and g_ren_jp_binds (bs: list (typ & exp))
  : Lemma (ensures forall (xi: ren). {:pattern (ren_jp_binds xi bs)}
                     globals_binds (ren_jp_binds xi bs) == globals_binds bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs' -> g_ren_jp e; g_ren_jp_binds bs'

and g_ren_jp_cells (th: list (key & exp))
  : Lemma (ensures forall (xi: ren). {:pattern (ren_jp_cells xi th)}
                     globals_cells (ren_jp_cells xi th) == globals_cells th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th' -> g_ren_jp e; g_ren_jp_cells th'

and g_ren_jp_dt (dt: dtree)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_jp_dt xi dt)}
                     globals_dt (ren_jp_dt xi dt) == globals_dt dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> g_ren_jp e
  | DBind _ dt' -> g_ren_jp_dt dt'
  | DSwitchCtor _ bs df -> g_ren_jp_brs bs; g_ren_jp_odt df
  | DSwitchLit _ bs df -> g_ren_jp_brs bs; g_ren_jp_dt df
  | DSwitchKey _ bs df -> g_ren_jp_brs bs; g_ren_jp_odt df
  | DGuard e dt1 dt2 -> g_ren_jp e; g_ren_jp_dt dt1; g_ren_jp_dt dt2

and g_ren_jp_odt (df: option dtree)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_jp_odt xi df)}
                     globals_odt (ren_jp_odt xi df) == globals_odt df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> g_ren_jp_dt dt

and g_ren_jp_brs (#lb: eqtype) (bs: list (lb & dtree))
  : Lemma (ensures forall (xi: ren). {:pattern (ren_jp_brs #lb xi bs)}
                     globals_brs (ren_jp_brs #lb xi bs) == globals_brs bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs' -> g_ren_jp_dt dt; g_ren_jp_brs bs'

and g_ren_jp_cls (cs: list clause)
  : Lemma (ensures forall (xi: ren). {:pattern (ren_jp_cls xi cs)}
                     globals_cls (ren_jp_cls xi cs) == globals_cls cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs' -> g_ren_jp b; g_ren_jp_cls cs'
  | CFast _ _ _ b :: cs' -> g_ren_jp b; g_ren_jp_cls cs'

(* ** Region maps *)

let rec g_rmap (f: nat -> region_ref -> region_ref) (e: exp)
  : Lemma (ensures forall (d: nat). {:pattern (rmap_exp f d e)}
                     globals (rmap_exp f d e) == globals e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> g_rmap f b
  | EApp e1 e2 | ELet _ e1 e2 | ELetJoin _ _ e1 e2
  | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 -> g_rmap f e1; g_rmap f e2
  | ELetRec bs b -> g_rmap_binds f bs; g_rmap f b
  | ECase es dt | EMatch es dt -> g_rmap_exps f es; g_rmap_dt f dt
  | EJump _ es -> g_rmap_exps f es
  | EHandle b h -> g_rmap f b; g_rmap f h.h_ret; g_rmap_cls f h.h_clauses
  | ERegion _ es b -> g_rmap_exps f es; g_rmap f b
  | ERegionOpen _ th b -> g_rmap_cells f th; g_rmap f b

and g_rmap_exps (f: nat -> region_ref -> region_ref) (es: list exp)
  : Lemma (ensures forall (d: nat). {:pattern (rmap_exps f d es)}
                     globals_exps (rmap_exps f d es) == globals_exps es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es' -> g_rmap f e; g_rmap_exps f es'

and g_rmap_binds (f: nat -> region_ref -> region_ref) (bs: list (typ & exp))
  : Lemma (ensures forall (d: nat). {:pattern (rmap_binds f d bs)}
                     globals_binds (rmap_binds f d bs) == globals_binds bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs' -> g_rmap f e; g_rmap_binds f bs'

and g_rmap_cells (f: nat -> region_ref -> region_ref) (th: list (key & exp))
  : Lemma (ensures forall (d: nat). {:pattern (rmap_cells f d th)}
                     globals_cells (rmap_cells f d th) == globals_cells th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th' -> g_rmap f e; g_rmap_cells f th'

and g_rmap_dt (f: nat -> region_ref -> region_ref) (dt: dtree)
  : Lemma (ensures forall (d: nat). {:pattern (rmap_dt f d dt)}
                     globals_dt (rmap_dt f d dt) == globals_dt dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> g_rmap f e
  | DBind _ dt' -> g_rmap_dt f dt'
  | DSwitchCtor _ bs df -> g_rmap_brs f bs; g_rmap_odt f df
  | DSwitchLit _ bs df -> g_rmap_brs f bs; g_rmap_dt f df
  | DSwitchKey _ bs df -> g_rmap_kbrs f bs; g_rmap_odt f df
  | DGuard e dt1 dt2 -> g_rmap f e; g_rmap_dt f dt1; g_rmap_dt f dt2

and g_rmap_odt (f: nat -> region_ref -> region_ref) (df: option dtree)
  : Lemma (ensures forall (d: nat). {:pattern (rmap_odt f d df)}
                     globals_odt (rmap_odt f d df) == globals_odt df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> g_rmap_dt f dt

and g_rmap_brs (#lb: eqtype) (f: nat -> region_ref -> region_ref) (bs: list (lb & dtree))
  : Lemma (ensures forall (d: nat). {:pattern (rmap_brs #lb f d bs)}
                     globals_brs (rmap_brs #lb f d bs) == globals_brs bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs' -> g_rmap_dt f dt; g_rmap_brs f bs'

and g_rmap_kbrs (f: nat -> region_ref -> region_ref) (bs: list (key & dtree))
  : Lemma (ensures forall (d: nat). {:pattern (rmap_kbrs f d bs)}
                     globals_brs (rmap_kbrs f d bs) == globals_brs bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs' -> g_rmap_dt f dt; g_rmap_kbrs f bs'

and g_rmap_cls (f: nat -> region_ref -> region_ref) (cs: list clause)
  : Lemma (ensures forall (d: nat). {:pattern (rmap_cls f d cs)}
                     globals_cls (rmap_cls f d cs) == globals_cls cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs' -> g_rmap f b; g_rmap_cls f cs'
  | CFast _ _ _ b :: cs' -> g_rmap f b; g_rmap_cls f cs'

let covers_kinst ks e = g_kinst e
let covers_sub_ty_exp sigma e = g_sub_ty e
let covers_ren_ty_exp xi e = g_ren_ty e
let covers_ren_tm xi e = g_ren_tm e
let covers_ren_jp xi e = g_ren_jp e
let covers_open_region a e = g_rmap (open_rr a) e

(* * Term substitution *)

let covers_var (sg: sig) (gi: genv) (i: nat) : Lemma (covers sg gi (EVar i)) = ()

let esub_covers_upn (sg: sig) (gi: genv) (n: nat) (sigma: esub)
  : Lemma (requires esub_covers sg gi sigma) (ensures esub_covers sg gi (upn_esub n sigma)) =
  introduce forall (i: nat). covers sg gi (upn_esub n sigma i)
  with (if i < n then covers_var sg gi i
        else begin
          covers_ren_tm (shift n) (sigma (i - n));
          covers_globals_eq sg gi (ren_tm (shift n) (sigma (i - n))) (sigma (i - n))
        end)

let esub_covers_tyup (sg: sig) (gi: genv) (m: nat) (sigma: esub)
  : Lemma (requires esub_covers sg gi sigma) (ensures esub_covers sg gi (tyup_esub m sigma)) =
  introduce forall (i: nat). covers sg gi (tyup_esub m sigma i)
  with begin
    covers_ren_ty_exp (shift m) (sigma i);
    covers_globals_eq sg gi (ren_ty_exp (shift m) (sigma i)) (sigma i)
  end

let esub_covers_jup (sg: sig) (gi: genv) (sigma: esub)
  : Lemma (requires esub_covers sg gi sigma) (ensures esub_covers sg gi (jup_esub sigma)) =
  introduce forall (i: nat). covers sg gi (jup_esub sigma i)
  with begin
    covers_ren_jp (shift 1) (sigma i);
    covers_globals_eq sg gi (ren_jp (shift 1) (sigma i)) (sigma i)
  end

let rec cs_e (sg: sig) (gi: genv) (sigma: esub) (e: exp)
  : Lemma (requires esub_covers sg gi sigma /\ covers sg gi e)
          (ensures covers sg gi (sub_tm sigma e))
          (decreases e) =
  match e with
  | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ | EVar _ -> ()
  | ELam _ _ b -> esub_covers_upn sg gi 1 sigma; cs_e sg gi (up_esub sigma) b
  | ETyLam _ b -> esub_covers_tyup sg gi 1 sigma; cs_e sg gi (tyup_esub 1 sigma) b
  | ETyApp b _ | ECLam _ b | ECApp b
  | ESelect _ b | ERestrict _ b | EInject _ _ b | EWeaken _ _ b
  | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> cs_e sg gi sigma b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    cs_e sg gi sigma e1; cs_e sg gi sigma e2
  | ELet _ e1 e2 ->
    cs_e sg gi sigma e1; esub_covers_upn sg gi 1 sigma; cs_e sg gi (up_esub sigma) e2
  | ELetRec bs b ->
    let n = L.length bs in
    esub_covers_upn sg gi n sigma;
    cs_binds sg gi (upn_esub n sigma) bs; cs_e sg gi (upn_esub n sigma) b
  | ECase es dt | EMatch es dt -> cs_exps sg gi sigma es; cs_dt sg gi sigma dt
  | ELetJoin ts _ e1 e2 ->
    esub_covers_jup sg gi sigma;
    esub_covers_upn sg gi (L.length ts) (jup_esub sigma);
    cs_e sg gi (upn_esub (L.length ts) (jup_esub sigma)) e1;
    cs_e sg gi (jup_esub sigma) e2
  | EJump _ es -> cs_exps sg gi sigma es
  | EHandle b h ->
    cs_e sg gi sigma b;
    esub_covers_upn sg gi 1 sigma; cs_e sg gi (up_esub sigma) h.h_ret;
    cs_cls sg gi sigma h.h_clauses
  | ERegion _ es b -> cs_exps sg gi sigma es; cs_e sg gi sigma b
  | ERegionOpen _ th b -> cs_cells sg gi sigma th; cs_e sg gi sigma b

and cs_exps (sg: sig) (gi: genv) (sigma: esub) (es: list exp)
  : Lemma (requires esub_covers sg gi sigma /\ exp_all_exps (covered sg gi) es)
          (ensures exp_all_exps (covered sg gi) (sub_tm_exps sigma es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es' -> cs_e sg gi sigma e; cs_exps sg gi sigma es'

and cs_binds (sg: sig) (gi: genv) (sigma: esub) (bs: list (typ & exp))
  : Lemma (requires esub_covers sg gi sigma /\ exp_all_binds (covered sg gi) bs)
          (ensures exp_all_binds (covered sg gi) (sub_tm_binds sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs' -> cs_e sg gi sigma e; cs_binds sg gi sigma bs'

and cs_cells (sg: sig) (gi: genv) (sigma: esub) (th: list (key & exp))
  : Lemma (requires esub_covers sg gi sigma /\ exp_all_cells (covered sg gi) th)
          (ensures exp_all_cells (covered sg gi) (sub_tm_cells sigma th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th' -> cs_e sg gi sigma e; cs_cells sg gi sigma th'

and cs_dt (sg: sig) (gi: genv) (sigma: esub) (dt: dtree)
  : Lemma (requires esub_covers sg gi sigma /\ exp_all_dt (covered sg gi) dt)
          (ensures exp_all_dt (covered sg gi) (sub_tm_dt sigma dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> cs_e sg gi sigma e
  | DBind _ dt' -> esub_covers_upn sg gi 1 sigma; cs_dt sg gi (up_esub sigma) dt'
  | DSwitchCtor _ bs df -> cs_brs sg gi sigma bs; cs_odt sg gi sigma df
  | DSwitchLit _ bs df -> cs_brs sg gi sigma bs; cs_dt sg gi sigma df
  | DSwitchKey _ bs df -> cs_brs sg gi sigma bs; cs_odt sg gi sigma df
  | DGuard e dt1 dt2 -> cs_e sg gi sigma e; cs_dt sg gi sigma dt1; cs_dt sg gi sigma dt2

and cs_odt (sg: sig) (gi: genv) (sigma: esub) (df: option dtree)
  : Lemma (requires esub_covers sg gi sigma /\ exp_all_odt (covered sg gi) df)
          (ensures exp_all_odt (covered sg gi) (sub_tm_odt sigma df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> cs_dt sg gi sigma dt

and cs_brs (#lb: eqtype) (sg: sig) (gi: genv) (sigma: esub) (bs: list (lb & dtree))
  : Lemma (requires esub_covers sg gi sigma /\ exp_all_brs (covered sg gi) bs)
          (ensures exp_all_brs (covered sg gi) (sub_tm_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs' -> cs_dt sg gi sigma dt; cs_brs sg gi sigma bs'

and cs_cls (sg: sig) (gi: genv) (sigma: esub) (cs: list clause)
  : Lemma (requires esub_covers sg gi sigma /\ exp_all_cls (covered sg gi) cs)
          (ensures exp_all_cls (covered sg gi) (sub_tm_cls sigma cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs' ->
    esub_covers_tyup sg gi nb sigma;
    esub_covers_upn sg gi 2 (tyup_esub nb sigma);
    cs_e sg gi (upn_esub 2 (tyup_esub nb sigma)) b;
    cs_cls sg gi sigma cs'
  | CFast _ nb _ b :: cs' ->
    esub_covers_tyup sg gi nb sigma;
    esub_covers_upn sg gi 1 (tyup_esub nb sigma);
    cs_e sg gi (up_esub (tyup_esub nb sigma)) b;
    cs_cls sg gi sigma cs'

let covers_sub_tm sg gi sigma e = cs_e sg gi sigma e

let covers_sub_tm_dt sg gi sigma dt = cs_dt sg gi sigma dt

let esub_covers_scons (sg: sig) (gi: genv) (v: exp)
  : Lemma (requires covers sg gi v) (ensures esub_covers sg gi (scons v evar)) =
  introduce forall (i: nat). covers sg gi (scons v evar i)
  with (if i = 0 then () else covers_var sg gi (i - 1))

let covers_subst1_tm sg gi v e =
  esub_covers_scons sg gi v;
  cs_e sg gi (scons v evar) e

let covers_subst1_dt sg gi v dt =
  esub_covers_scons sg gi v;
  cs_dt sg gi (scons v evar) dt

let rec for_all_index (#a: Type) (p: a -> bool) (l: list a) (i: nat)
  : Lemma (requires L.for_all p l /\ i < L.length l) (ensures p (L.index l i)) (decreases l) =
  match l with
  | _ :: l' -> if i = 0 then () else for_all_index p l' (i - 1)

let covers_list_esub sg gi vs e =
  introduce forall (i: nat). covers sg gi (list_esub vs i)
  with (if i < L.length vs then for_all_index (covers sg gi) vs i
        else covers_var sg gi (i - L.length vs));
  cs_e sg gi (list_esub vs) e

let covers_rev sg gi vs =
  L.for_all_mem (covers sg gi) vs;
  L.for_all_mem (covers sg gi) (L.rev vs);
  introduce forall (x: exp). L.memP x (L.rev vs) ==> covers sg gi x
  with LP.rev_memP vs x

(* * Values read out of values *)

let rec value_args_append (a b: list spine_arg)
  : Lemma (value_args (L.append a b) == L.append (value_args a) (value_args b)) (decreases a) =
  match a with
  | [] -> ()
  | SVal _ :: a' | STy _ :: a' | SConstr :: a' -> value_args_append a' b

let rec covers_value_args sg gi e q ks args =
  match e with
  | EGlobal _ _ -> ()
  | EApp f v ->
    let Some (_, _, args0) = decompose_global_app f in
    covers_value_args sg gi f q ks args0;
    value_args_append args0 [SVal v];
    LP.for_all_append (covers sg gi) (value_args args0) [v]
  | ETyApp f t ->
    let Some (_, _, args0) = decompose_global_app f in
    covers_value_args sg gi f q ks args0;
    value_args_append args0 [STy t];
    LP.append_l_nil (value_args args0)
  | ECApp f ->
    let Some (_, _, args0) = decompose_global_app f in
    covers_value_args sg gi f q ks args0;
    value_args_append args0 [SConstr];
    LP.append_l_nil (value_args args0)

let rec for_all_nth (#a: Type) (p: a -> bool) (l: list a) (i: nat) (x: a)
  : Lemma (requires L.for_all p l /\ L.nth l i == Some x) (ensures p x) (decreases l) =
  match l with
  | _ :: l' -> if i = 0 then () else for_all_nth p l' (i - 1) x

let rec covers_record_field (sg: sig) (gi: genv) (k: key) (w v: exp)
  : Lemma (requires covers sg gi w /\ record_field k w == Some v) (ensures covers sg gi v)
          (decreases w) =
  match w with
  | EExtend k' _ w2 -> if k' = k then () else covers_record_field sg gi k w2 v

let rec covers_variant_payload (sg: sig) (gi: genv) (k: key) (w v: exp)
  : Lemma (requires covers sg gi w /\ variant_payload k w == Some v) (ensures covers sg gi v)
          (decreases w) =
  match w with
  | EInject _ _ _ -> ()
  | EWeaken _ _ w1 -> covers_variant_payload sg gi k w1 v

let rec covers_proj sg gi th o v =
  match o with
  | OScrut i -> for_all_nth (covers sg gi) th i v
  | OCtor o' q j ->
    let Some w = proj sg th o' in
    covers_proj sg gi th o' w;
    let Some (q', ks, args) = decompose_global_app w in
    covers_value_args sg gi w q' ks args;
    for_all_nth (covers sg gi) (value_args args) j v
  | ORecord o' k ->
    let Some w = proj sg th o' in
    covers_proj sg gi th o' w;
    covers_record_field sg gi k w v
  | OVariant o' k ->
    let Some w = proj sg th o' in
    covers_proj sg gi th o' w;
    covers_variant_payload sg gi k w v

(* * Evaluation contexts *)

let rec exps_mid_replace (p: exp -> bool) (vs: list exp) (e e': exp) (es: list exp)
  : Lemma (requires exp_all_exps p (L.append vs (e :: es)) /\ exp_all p e')
          (ensures exp_all_exps p (L.append vs (e' :: es)))
          (decreases vs) =
  match vs with
  | [] -> ()
  | _ :: vs' -> exps_mid_replace p vs' e e' es

let covers_plug1_replace sg gi f e e' =
  match f with
  | FCase vs es _ | FJump _ vs es | FRegion _ vs es _ ->
    exps_mid_replace (covered sg gi) vs e e' es
  | _ -> ()

let rec covers_plug sg gi fs e =
  match fs with
  | [] -> ()
  | f :: fs' ->
    covers_plug sg gi fs' (plug1 f e);
    Stella.Core.Semantics.Step.covers_plug1 sg gi f e

let rec covers_plug_replace sg gi fs e e' =
  match fs with
  | [] -> ()
  | f :: fs' ->
    covers_plug sg gi fs' (plug1 f e);
    covers_plug1_replace sg gi f e e';
    covers_plug_replace sg gi fs' (plug1 f e) (plug1 f e')
