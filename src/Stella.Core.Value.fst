(* Each family is one mutual induction over the term classes; the interface
   exports its `exp` and `dtree` instances. The helpers before a family
   re-establish its hypothesis under binders. *)
module Stella.Core.Value
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Spine
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
module L = FStar.List.Tot

let rec jp_scoped_mono (n: nat) (m: nat) (e: exp)
  : Lemma (requires n <= m /\ jp_scoped n e)
          (ensures jp_scoped m e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> jp_scoped_mono 0 0 b
  | EApp e1 e2 -> jp_scoped_mono n m e1; jp_scoped_mono n m e2
  | ETyLam _ b -> jp_scoped_mono 0 0 b
  | ETyApp b _ -> jp_scoped_mono n m b
  | ECLam _ b -> jp_scoped_mono 0 0 b
  | ECApp b -> jp_scoped_mono n m b
  | ELet _ e1 e2 -> jp_scoped_mono n m e1; jp_scoped_mono n m e2
  | ELetRec bs b -> jp_scoped_mono_binds 0 0 bs; jp_scoped_mono n m b
  | ECase es dt -> jp_scoped_mono_exps n m es; jp_scoped_mono_dt n m dt
  | ELetJoin _ _ e1 e2 -> jp_scoped_mono (n + 1) (m + 1) e1; jp_scoped_mono (n + 1) (m + 1) e2
  | EJump _ es -> jp_scoped_mono_exps n m es
  | EExtend _ e1 e2 -> jp_scoped_mono n m e1; jp_scoped_mono n m e2
  | ESelect _ b -> jp_scoped_mono n m b
  | ERestrict _ b -> jp_scoped_mono n m b
  | EUpdate _ e1 e2 -> jp_scoped_mono n m e1; jp_scoped_mono n m e2
  | EMerge e1 e2 -> jp_scoped_mono n m e1; jp_scoped_mono n m e2
  | EInject _ _ b -> jp_scoped_mono n m b
  | EWeaken _ _ b -> jp_scoped_mono n m b
  | EAbsurd _ b -> jp_scoped_mono n m b
  | EPerform _ _ _ b -> jp_scoped_mono n m b
  | EHandle b h ->
    jp_scoped_mono 0 0 b; jp_scoped_mono 0 0 h.h_ret; jp_scoped_mono_cls 0 0 h.h_clauses
  | EOpenEff _ b -> jp_scoped_mono n m b
  | ERegion _ es b -> jp_scoped_mono_exps n m es; jp_scoped_mono 0 0 b
  | EWriteCell _ _ b -> jp_scoped_mono n m b
  | EMatch th dt -> jp_scoped_mono_exps n m th; jp_scoped_mono_dt n m dt
  | EOpenEffC _ b -> jp_scoped_mono n m b
  | EFill _ b -> jp_scoped_mono 0 0 b
  | ERegionOpen _ th b -> jp_scoped_mono_cells 0 0 th; jp_scoped_mono 0 0 b

and jp_scoped_mono_exps (n: nat) (m: nat) (es: list exp)
  : Lemma (requires n <= m /\ jp_scoped_exps n es)
          (ensures jp_scoped_exps m es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> jp_scoped_mono n m e; jp_scoped_mono_exps n m es

and jp_scoped_mono_binds (n: nat) (m: nat) (bs: list (typ & exp))
  : Lemma (requires n <= m /\ jp_scoped_binds n bs)
          (ensures jp_scoped_binds m bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> jp_scoped_mono n m e; jp_scoped_mono_binds n m bs

and jp_scoped_mono_cells (n: nat) (m: nat) (th: list (key & exp))
  : Lemma (requires n <= m /\ jp_scoped_cells n th)
          (ensures jp_scoped_cells m th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> jp_scoped_mono n m e; jp_scoped_mono_cells n m th

and jp_scoped_mono_dt (n: nat) (m: nat) (dt: dtree)
  : Lemma (requires n <= m /\ jp_scoped_dt n dt)
          (ensures jp_scoped_dt m dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> jp_scoped_mono n m e
  | DBind _ dt -> jp_scoped_mono_dt n m dt
  | DSwitchCtor _ bs df -> jp_scoped_mono_brs n m bs; jp_scoped_mono_odt n m df
  | DSwitchLit _ bs df -> jp_scoped_mono_brs n m bs; jp_scoped_mono_dt n m df
  | DSwitchKey _ bs df -> jp_scoped_mono_brs n m bs; jp_scoped_mono_odt n m df
  | DGuard e dt1 dt2 -> jp_scoped_mono n m e; jp_scoped_mono_dt n m dt1; jp_scoped_mono_dt n m dt2

and jp_scoped_mono_odt (n: nat) (m: nat) (df: option dtree)
  : Lemma (requires n <= m /\ jp_scoped_odt n df)
          (ensures jp_scoped_odt m df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> jp_scoped_mono_dt n m dt

and jp_scoped_mono_brs (#lb: eqtype) (n: nat) (m: nat) (bs: list (lb & dtree))
  : Lemma (requires n <= m /\ jp_scoped_brs n bs)
          (ensures jp_scoped_brs m bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> jp_scoped_mono_dt n m dt; jp_scoped_mono_brs n m bs

and jp_scoped_mono_cls (n: nat) (m: nat) (cs: list clause)
  : Lemma (requires n <= m /\ jp_scoped_cls n cs)
          (ensures jp_scoped_cls m cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> jp_scoped_mono n m b; jp_scoped_mono_cls n m cs
  | CFast _ _ _ b :: cs -> jp_scoped_mono n m b; jp_scoped_mono_cls n m cs

let up_ren_fix_below (n: nat) (xi: ren)
  : Lemma (requires forall (j: nat). j < n ==> xi j == j)
          (ensures forall (j: nat). j < n + 1 ==> up_ren xi j == j) = ()

let rec ren_jp_scoped (n: nat) (xi: ren) (e: exp)
  : Lemma (requires jp_scoped n e /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp xi e == e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> ren_jp_scoped 0 xi b
  | EApp e1 e2 -> ren_jp_scoped n xi e1; ren_jp_scoped n xi e2
  | ETyLam _ b -> ren_jp_scoped 0 xi b
  | ETyApp b _ -> ren_jp_scoped n xi b
  | ECLam _ b -> ren_jp_scoped 0 xi b
  | ECApp b -> ren_jp_scoped n xi b
  | ELet _ e1 e2 -> ren_jp_scoped n xi e1; ren_jp_scoped n xi e2
  | ELetRec bs b -> ren_jp_scoped_binds 0 xi bs; ren_jp_scoped n xi b
  | ECase es dt -> ren_jp_scoped_exps n xi es; ren_jp_scoped_dt n xi dt
  | ELetJoin _ _ e1 e2 ->
    up_ren_fix_below n xi; ren_jp_scoped (n + 1) (up_ren xi) e1;
    ren_jp_scoped (n + 1) (up_ren xi) e2
  | EJump _ es -> ren_jp_scoped_exps n xi es
  | EExtend _ e1 e2 -> ren_jp_scoped n xi e1; ren_jp_scoped n xi e2
  | ESelect _ b -> ren_jp_scoped n xi b
  | ERestrict _ b -> ren_jp_scoped n xi b
  | EUpdate _ e1 e2 -> ren_jp_scoped n xi e1; ren_jp_scoped n xi e2
  | EMerge e1 e2 -> ren_jp_scoped n xi e1; ren_jp_scoped n xi e2
  | EInject _ _ b -> ren_jp_scoped n xi b
  | EWeaken _ _ b -> ren_jp_scoped n xi b
  | EAbsurd _ b -> ren_jp_scoped n xi b
  | EPerform _ _ _ b -> ren_jp_scoped n xi b
  | EHandle b h ->
    ren_jp_scoped 0 xi b; ren_jp_scoped 0 xi h.h_ret; ren_jp_scoped_cls 0 xi h.h_clauses
  | EOpenEff _ b -> ren_jp_scoped n xi b
  | ERegion _ es b -> ren_jp_scoped_exps n xi es; ren_jp_scoped 0 xi b
  | EWriteCell _ _ b -> ren_jp_scoped n xi b
  | EMatch th dt -> ren_jp_scoped_exps n xi th; ren_jp_scoped_dt n xi dt
  | EOpenEffC _ b -> ren_jp_scoped n xi b
  | EFill _ b -> ren_jp_scoped 0 xi b
  | ERegionOpen _ th b -> ren_jp_scoped_cells 0 xi th; ren_jp_scoped 0 xi b

and ren_jp_scoped_exps (n: nat) (xi: ren) (es: list exp)
  : Lemma (requires jp_scoped_exps n es /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp_exps xi es == es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ren_jp_scoped n xi e; ren_jp_scoped_exps n xi es

and ren_jp_scoped_binds (n: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (requires jp_scoped_binds n bs /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp_binds xi bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> ren_jp_scoped n xi e; ren_jp_scoped_binds n xi bs

and ren_jp_scoped_cells (n: nat) (xi: ren) (th: list (key & exp))
  : Lemma (requires jp_scoped_cells n th /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp_cells xi th == th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> ren_jp_scoped n xi e; ren_jp_scoped_cells n xi th

and ren_jp_scoped_dt (n: nat) (xi: ren) (dt: dtree)
  : Lemma (requires jp_scoped_dt n dt /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp_dt xi dt == dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> ren_jp_scoped n xi e
  | DBind _ dt -> ren_jp_scoped_dt n xi dt
  | DSwitchCtor _ bs df -> ren_jp_scoped_brs n xi bs; ren_jp_scoped_odt n xi df
  | DSwitchLit _ bs df -> ren_jp_scoped_brs n xi bs; ren_jp_scoped_dt n xi df
  | DSwitchKey _ bs df -> ren_jp_scoped_brs n xi bs; ren_jp_scoped_odt n xi df
  | DGuard e dt1 dt2 -> ren_jp_scoped n xi e; ren_jp_scoped_dt n xi dt1; ren_jp_scoped_dt n xi dt2

and ren_jp_scoped_odt (n: nat) (xi: ren) (df: option dtree)
  : Lemma (requires jp_scoped_odt n df /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp_odt xi df == df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ren_jp_scoped_dt n xi dt

and ren_jp_scoped_brs (#lb: eqtype) (n: nat) (xi: ren) (bs: list (lb & dtree))
  : Lemma (requires jp_scoped_brs n bs /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp_brs xi bs == bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> ren_jp_scoped_dt n xi dt; ren_jp_scoped_brs n xi bs

and ren_jp_scoped_cls (n: nat) (xi: ren) (cs: list clause)
  : Lemma (requires jp_scoped_cls n cs /\ (forall (j: nat). j < n ==> xi j == j))
          (ensures ren_jp_cls xi cs == cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> ren_jp_scoped n xi b; ren_jp_scoped_cls n xi cs
  | CFast _ _ _ b :: cs -> ren_jp_scoped n xi b; ren_jp_scoped_cls n xi cs

let rec jp_scoped_ren_tm (n: nat) (xi: ren) (e: exp)
  : Lemma (ensures jp_scoped n (ren_tm xi e) == jp_scoped n e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> jp_scoped_ren_tm 0 (up_ren xi) b
  | EApp e1 e2 -> jp_scoped_ren_tm n xi e1; jp_scoped_ren_tm n xi e2
  | ETyLam _ b -> jp_scoped_ren_tm 0 xi b
  | ETyApp b _ -> jp_scoped_ren_tm n xi b
  | ECLam _ b -> jp_scoped_ren_tm 0 xi b
  | ECApp b -> jp_scoped_ren_tm n xi b
  | ELet _ e1 e2 -> jp_scoped_ren_tm n xi e1; jp_scoped_ren_tm n (up_ren xi) e2
  | ELetRec bs b ->
    jp_scoped_ren_tm_binds 0 (upn_ren (L.length bs) xi) bs;
    jp_scoped_ren_tm n (upn_ren (L.length bs) xi) b
  | ECase es dt -> jp_scoped_ren_tm_exps n xi es; jp_scoped_ren_tm_dt n xi dt
  | ELetJoin ts _ e1 e2 ->
    jp_scoped_ren_tm (n + 1) (upn_ren (L.length ts) xi) e1; jp_scoped_ren_tm (n + 1) xi e2
  | EJump _ es -> jp_scoped_ren_tm_exps n xi es
  | EExtend _ e1 e2 -> jp_scoped_ren_tm n xi e1; jp_scoped_ren_tm n xi e2
  | ESelect _ b -> jp_scoped_ren_tm n xi b
  | ERestrict _ b -> jp_scoped_ren_tm n xi b
  | EUpdate _ e1 e2 -> jp_scoped_ren_tm n xi e1; jp_scoped_ren_tm n xi e2
  | EMerge e1 e2 -> jp_scoped_ren_tm n xi e1; jp_scoped_ren_tm n xi e2
  | EInject _ _ b -> jp_scoped_ren_tm n xi b
  | EWeaken _ _ b -> jp_scoped_ren_tm n xi b
  | EAbsurd _ b -> jp_scoped_ren_tm n xi b
  | EPerform _ _ _ b -> jp_scoped_ren_tm n xi b
  | EHandle b h ->
    jp_scoped_ren_tm 0 xi b; jp_scoped_ren_tm 0 (up_ren xi) h.h_ret;
    jp_scoped_ren_tm_cls 0 xi h.h_clauses
  | EOpenEff _ b -> jp_scoped_ren_tm n xi b
  | ERegion _ es b -> jp_scoped_ren_tm_exps n xi es; jp_scoped_ren_tm 0 xi b
  | EWriteCell _ _ b -> jp_scoped_ren_tm n xi b
  | EMatch th dt -> jp_scoped_ren_tm_exps n xi th; jp_scoped_ren_tm_dt n xi dt
  | EOpenEffC _ b -> jp_scoped_ren_tm n xi b
  | EFill _ b -> jp_scoped_ren_tm 0 xi b
  | ERegionOpen _ th b -> jp_scoped_ren_tm_cells 0 xi th; jp_scoped_ren_tm 0 xi b

and jp_scoped_ren_tm_exps (n: nat) (xi: ren) (es: list exp)
  : Lemma (ensures jp_scoped_exps n (ren_tm_exps xi es) == jp_scoped_exps n es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> jp_scoped_ren_tm n xi e; jp_scoped_ren_tm_exps n xi es

and jp_scoped_ren_tm_binds (n: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures jp_scoped_binds n (ren_tm_binds xi bs) == jp_scoped_binds n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> jp_scoped_ren_tm n xi e; jp_scoped_ren_tm_binds n xi bs

and jp_scoped_ren_tm_cells (n: nat) (xi: ren) (th: list (key & exp))
  : Lemma (ensures jp_scoped_cells n (ren_tm_cells xi th) == jp_scoped_cells n th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> jp_scoped_ren_tm n xi e; jp_scoped_ren_tm_cells n xi th

and jp_scoped_ren_tm_dt (n: nat) (xi: ren) (dt: dtree)
  : Lemma (ensures jp_scoped_dt n (ren_tm_dt xi dt) == jp_scoped_dt n dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> jp_scoped_ren_tm n xi e
  | DBind _ dt -> jp_scoped_ren_tm_dt n (up_ren xi) dt
  | DSwitchCtor _ bs df -> jp_scoped_ren_tm_brs n xi bs; jp_scoped_ren_tm_odt n xi df
  | DSwitchLit _ bs df -> jp_scoped_ren_tm_brs n xi bs; jp_scoped_ren_tm_dt n xi df
  | DSwitchKey _ bs df -> jp_scoped_ren_tm_brs n xi bs; jp_scoped_ren_tm_odt n xi df
  | DGuard e dt1 dt2 ->
    jp_scoped_ren_tm n xi e; jp_scoped_ren_tm_dt n xi dt1; jp_scoped_ren_tm_dt n xi dt2

and jp_scoped_ren_tm_odt (n: nat) (xi: ren) (df: option dtree)
  : Lemma (ensures jp_scoped_odt n (ren_tm_odt xi df) == jp_scoped_odt n df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> jp_scoped_ren_tm_dt n xi dt

and jp_scoped_ren_tm_brs (#lb: eqtype) (n: nat) (xi: ren) (bs: list (lb & dtree))
  : Lemma (ensures jp_scoped_brs n (ren_tm_brs xi bs) == jp_scoped_brs n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> jp_scoped_ren_tm_dt n xi dt; jp_scoped_ren_tm_brs n xi bs

and jp_scoped_ren_tm_cls (n: nat) (xi: ren) (cs: list clause)
  : Lemma (ensures jp_scoped_cls n (ren_tm_cls xi cs) == jp_scoped_cls n cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> jp_scoped_ren_tm n (upn_ren 2 xi) b; jp_scoped_ren_tm_cls n xi cs
  | CFast _ _ _ b :: cs -> jp_scoped_ren_tm n (up_ren xi) b; jp_scoped_ren_tm_cls n xi cs

let rec jp_scoped_sub_ty (n: nat) (sigma: tsub) (e: exp)
  : Lemma (ensures jp_scoped n (sub_ty_exp sigma e) == jp_scoped n e)
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> jp_scoped_sub_ty 0 sigma b
  | EApp e1 e2 -> jp_scoped_sub_ty n sigma e1; jp_scoped_sub_ty n sigma e2
  | ETyLam _ b -> jp_scoped_sub_ty 0 (up_tsub sigma) b
  | ETyApp b _ -> jp_scoped_sub_ty n sigma b
  | ECLam _ b -> jp_scoped_sub_ty 0 sigma b
  | ECApp b -> jp_scoped_sub_ty n sigma b
  | ELet _ e1 e2 -> jp_scoped_sub_ty n sigma e1; jp_scoped_sub_ty n sigma e2
  | ELetRec bs b -> jp_scoped_sub_ty_binds 0 sigma bs; jp_scoped_sub_ty n sigma b
  | ECase es dt -> jp_scoped_sub_ty_exps n sigma es; jp_scoped_sub_ty_dt n sigma dt
  | ELetJoin _ _ e1 e2 -> jp_scoped_sub_ty (n + 1) sigma e1; jp_scoped_sub_ty (n + 1) sigma e2
  | EJump _ es -> jp_scoped_sub_ty_exps n sigma es
  | EExtend _ e1 e2 -> jp_scoped_sub_ty n sigma e1; jp_scoped_sub_ty n sigma e2
  | ESelect _ b -> jp_scoped_sub_ty n sigma b
  | ERestrict _ b -> jp_scoped_sub_ty n sigma b
  | EUpdate _ e1 e2 -> jp_scoped_sub_ty n sigma e1; jp_scoped_sub_ty n sigma e2
  | EMerge e1 e2 -> jp_scoped_sub_ty n sigma e1; jp_scoped_sub_ty n sigma e2
  | EInject _ _ b -> jp_scoped_sub_ty n sigma b
  | EWeaken _ _ b -> jp_scoped_sub_ty n sigma b
  | EAbsurd _ b -> jp_scoped_sub_ty n sigma b
  | EPerform _ _ _ b -> jp_scoped_sub_ty n sigma b
  | EHandle b h ->
    jp_scoped_sub_ty 0 sigma b; jp_scoped_sub_ty 0 sigma h.h_ret;
    jp_scoped_sub_ty_cls 0 sigma h.h_clauses
  | EOpenEff _ b -> jp_scoped_sub_ty n sigma b
  | ERegion _ es b -> jp_scoped_sub_ty_exps n sigma es; jp_scoped_sub_ty 0 sigma b
  | EWriteCell _ _ b -> jp_scoped_sub_ty n sigma b
  | EMatch th dt -> jp_scoped_sub_ty_exps n sigma th; jp_scoped_sub_ty_dt n sigma dt
  | EOpenEffC _ b -> jp_scoped_sub_ty n sigma b
  | EFill _ b -> jp_scoped_sub_ty 0 sigma b
  | ERegionOpen _ th b -> jp_scoped_sub_ty_cells 0 sigma th; jp_scoped_sub_ty 0 sigma b

and jp_scoped_sub_ty_exps (n: nat) (sigma: tsub) (es: list exp)
  : Lemma (ensures jp_scoped_exps n (sub_ty_exps sigma es) == jp_scoped_exps n es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> jp_scoped_sub_ty n sigma e; jp_scoped_sub_ty_exps n sigma es

and jp_scoped_sub_ty_binds (n: nat) (sigma: tsub) (bs: list (typ & exp))
  : Lemma (ensures jp_scoped_binds n (sub_ty_binds sigma bs) == jp_scoped_binds n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> jp_scoped_sub_ty n sigma e; jp_scoped_sub_ty_binds n sigma bs

and jp_scoped_sub_ty_cells (n: nat) (sigma: tsub) (th: list (key & exp))
  : Lemma (ensures jp_scoped_cells n (sub_ty_cells sigma th) == jp_scoped_cells n th)
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> jp_scoped_sub_ty n sigma e; jp_scoped_sub_ty_cells n sigma th

and jp_scoped_sub_ty_dt (n: nat) (sigma: tsub) (dt: dtree)
  : Lemma (ensures jp_scoped_dt n (sub_ty_dt sigma dt) == jp_scoped_dt n dt)
          (decreases dt) =
  match dt with
  | DLeaf e -> jp_scoped_sub_ty n sigma e
  | DBind _ dt -> jp_scoped_sub_ty_dt n sigma dt
  | DSwitchCtor _ bs df -> jp_scoped_sub_ty_brs n sigma bs; jp_scoped_sub_ty_odt n sigma df
  | DSwitchLit _ bs df -> jp_scoped_sub_ty_brs n sigma bs; jp_scoped_sub_ty_dt n sigma df
  | DSwitchKey _ bs df -> jp_scoped_sub_ty_brs n sigma bs; jp_scoped_sub_ty_odt n sigma df
  | DGuard e dt1 dt2 ->
    jp_scoped_sub_ty n sigma e; jp_scoped_sub_ty_dt n sigma dt1; jp_scoped_sub_ty_dt n sigma dt2

and jp_scoped_sub_ty_odt (n: nat) (sigma: tsub) (df: option dtree)
  : Lemma (ensures jp_scoped_odt n (sub_ty_odt sigma df) == jp_scoped_odt n df)
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> jp_scoped_sub_ty_dt n sigma dt

and jp_scoped_sub_ty_brs (#lb: eqtype) (n: nat) (sigma: tsub) (bs: list (lb & dtree))
  : Lemma (ensures jp_scoped_brs n (sub_ty_brs sigma bs) == jp_scoped_brs n bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> jp_scoped_sub_ty_dt n sigma dt; jp_scoped_sub_ty_brs n sigma bs

and jp_scoped_sub_ty_cls (n: nat) (sigma: tsub) (cs: list clause)
  : Lemma (ensures jp_scoped_cls n (sub_ty_cls sigma cs) == jp_scoped_cls n cs)
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    jp_scoped_sub_ty n (upn_tsub nb sigma) b; jp_scoped_sub_ty_cls n sigma cs
  | CFast _ nb _ b :: cs ->
    jp_scoped_sub_ty n (upn_tsub nb sigma) b; jp_scoped_sub_ty_cls n sigma cs

let jp_scoped_ren_ty_exp (n: nat) (xi: ren) (e: exp)
  : Lemma (jp_scoped n (ren_ty_exp xi e) == jp_scoped n e) =
  ren_ty_exp_as_sub xi e; jp_scoped_sub_ty n (ren_tsub xi) e

let up_ren_bound (n m: nat) (xi: ren)
  : Lemma (requires forall (j: nat). j < n ==> xi j < m)
          (ensures forall (j: nat). j < n + 1 ==> up_ren xi j < m + 1) = ()

let rec jp_scoped_ren_jp (n: nat) (m: nat) (xi: ren) (e: exp)
  : Lemma (requires jp_scoped n e /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped m (ren_jp xi e))
          (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> jp_scoped_ren_jp 0 0 xi b
  | EApp e1 e2 -> jp_scoped_ren_jp n m xi e1; jp_scoped_ren_jp n m xi e2
  | ETyLam _ b -> jp_scoped_ren_jp 0 0 xi b
  | ETyApp b _ -> jp_scoped_ren_jp n m xi b
  | ECLam _ b -> jp_scoped_ren_jp 0 0 xi b
  | ECApp b -> jp_scoped_ren_jp n m xi b
  | ELet _ e1 e2 -> jp_scoped_ren_jp n m xi e1; jp_scoped_ren_jp n m xi e2
  | ELetRec bs b -> jp_scoped_ren_jp_binds 0 0 xi bs; jp_scoped_ren_jp n m xi b
  | ECase es dt -> jp_scoped_ren_jp_exps n m xi es; jp_scoped_ren_jp_dt n m xi dt
  | ELetJoin _ _ e1 e2 ->
    up_ren_bound n m xi; jp_scoped_ren_jp (n + 1) (m + 1) (up_ren xi) e1;
    jp_scoped_ren_jp (n + 1) (m + 1) (up_ren xi) e2
  | EJump _ es -> jp_scoped_ren_jp_exps n m xi es
  | EExtend _ e1 e2 -> jp_scoped_ren_jp n m xi e1; jp_scoped_ren_jp n m xi e2
  | ESelect _ b -> jp_scoped_ren_jp n m xi b
  | ERestrict _ b -> jp_scoped_ren_jp n m xi b
  | EUpdate _ e1 e2 -> jp_scoped_ren_jp n m xi e1; jp_scoped_ren_jp n m xi e2
  | EMerge e1 e2 -> jp_scoped_ren_jp n m xi e1; jp_scoped_ren_jp n m xi e2
  | EInject _ _ b -> jp_scoped_ren_jp n m xi b
  | EWeaken _ _ b -> jp_scoped_ren_jp n m xi b
  | EAbsurd _ b -> jp_scoped_ren_jp n m xi b
  | EPerform _ _ _ b -> jp_scoped_ren_jp n m xi b
  | EHandle b h ->
    jp_scoped_ren_jp 0 0 xi b; jp_scoped_ren_jp 0 0 xi h.h_ret;
    jp_scoped_ren_jp_cls 0 0 xi h.h_clauses
  | EOpenEff _ b -> jp_scoped_ren_jp n m xi b
  | ERegion _ es b -> jp_scoped_ren_jp_exps n m xi es; jp_scoped_ren_jp 0 0 xi b
  | EWriteCell _ _ b -> jp_scoped_ren_jp n m xi b
  | EMatch th dt -> jp_scoped_ren_jp_exps n m xi th; jp_scoped_ren_jp_dt n m xi dt
  | EOpenEffC _ b -> jp_scoped_ren_jp n m xi b
  | EFill _ b -> jp_scoped_ren_jp 0 0 xi b
  | ERegionOpen _ th b -> jp_scoped_ren_jp_cells 0 0 xi th; jp_scoped_ren_jp 0 0 xi b

and jp_scoped_ren_jp_exps (n: nat) (m: nat) (xi: ren) (es: list exp)
  : Lemma (requires jp_scoped_exps n es /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped_exps m (ren_jp_exps xi es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> jp_scoped_ren_jp n m xi e; jp_scoped_ren_jp_exps n m xi es

and jp_scoped_ren_jp_binds (n: nat) (m: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (requires jp_scoped_binds n bs /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped_binds m (ren_jp_binds xi bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> jp_scoped_ren_jp n m xi e; jp_scoped_ren_jp_binds n m xi bs

and jp_scoped_ren_jp_cells (n: nat) (m: nat) (xi: ren) (th: list (key & exp))
  : Lemma (requires jp_scoped_cells n th /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped_cells m (ren_jp_cells xi th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> jp_scoped_ren_jp n m xi e; jp_scoped_ren_jp_cells n m xi th

and jp_scoped_ren_jp_dt (n: nat) (m: nat) (xi: ren) (dt: dtree)
  : Lemma (requires jp_scoped_dt n dt /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped_dt m (ren_jp_dt xi dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> jp_scoped_ren_jp n m xi e
  | DBind _ dt -> jp_scoped_ren_jp_dt n m xi dt
  | DSwitchCtor _ bs df -> jp_scoped_ren_jp_brs n m xi bs; jp_scoped_ren_jp_odt n m xi df
  | DSwitchLit _ bs df -> jp_scoped_ren_jp_brs n m xi bs; jp_scoped_ren_jp_dt n m xi df
  | DSwitchKey _ bs df -> jp_scoped_ren_jp_brs n m xi bs; jp_scoped_ren_jp_odt n m xi df
  | DGuard e dt1 dt2 ->
    jp_scoped_ren_jp n m xi e; jp_scoped_ren_jp_dt n m xi dt1; jp_scoped_ren_jp_dt n m xi dt2

and jp_scoped_ren_jp_odt (n: nat) (m: nat) (xi: ren) (df: option dtree)
  : Lemma (requires jp_scoped_odt n df /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped_odt m (ren_jp_odt xi df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> jp_scoped_ren_jp_dt n m xi dt

and jp_scoped_ren_jp_brs (#lb: eqtype) (n: nat) (m: nat) (xi: ren) (bs: list (lb & dtree))
  : Lemma (requires jp_scoped_brs n bs /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped_brs m (ren_jp_brs xi bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> jp_scoped_ren_jp_dt n m xi dt; jp_scoped_ren_jp_brs n m xi bs

and jp_scoped_ren_jp_cls (n: nat) (m: nat) (xi: ren) (cs: list clause)
  : Lemma (requires jp_scoped_cls n cs /\
                    (forall (j: nat). j < n ==> xi j < m))
          (ensures jp_scoped_cls m (ren_jp_cls xi cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> jp_scoped_ren_jp n m xi b; jp_scoped_ren_jp_cls n m xi cs
  | CFast _ _ _ b :: cs -> jp_scoped_ren_jp n m xi b; jp_scoped_ren_jp_cls n m xi cs

let jp_upn_esub (k: nat) (sigma: esub)
  : Lemma (requires forall (i: nat). jp_scoped 0 (sigma i))
          (ensures forall (i: nat). jp_scoped 0 (upn_esub k sigma i)) =
  introduce forall (i: nat). jp_scoped 0 (upn_esub k sigma i)
  with if i < k then () else jp_scoped_ren_tm 0 (shift k) (sigma (i - k))

let jp_tyup_esub (m: nat) (sigma: esub)
  : Lemma (requires forall (i: nat). jp_scoped 0 (sigma i))
          (ensures forall (i: nat). jp_scoped 0 (tyup_esub m sigma i)) =
  introduce forall (i: nat). jp_scoped 0 (tyup_esub m sigma i)
  with jp_scoped_ren_ty_exp 0 (shift m) (sigma i)

let jp_jup_esub (sigma: esub)
  : Lemma (requires forall (i: nat). jp_scoped 0 (sigma i))
          (ensures forall (i: nat). jp_scoped 0 (jup_esub sigma i)) =
  introduce forall (i: nat). jp_scoped 0 (jup_esub sigma i)
  with jp_scoped_ren_jp 0 0 (shift 1) (sigma i)

let rec jp_scoped_sub_tm (n: nat) (sigma: esub) (e: exp)
  : Lemma (requires jp_scoped n e /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped n (sub_tm sigma e))
          (decreases e) =
  match e with
  | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | EVar i -> jp_scoped_mono 0 n (sigma i)
  | ELam _ _ b -> jp_upn_esub 1 sigma; jp_scoped_sub_tm 0 (up_esub sigma) b
  | EApp e1 e2 -> jp_scoped_sub_tm n sigma e1; jp_scoped_sub_tm n sigma e2
  | ETyLam _ b -> jp_tyup_esub 1 sigma; jp_scoped_sub_tm 0 (tyup_esub 1 sigma) b
  | ETyApp b _ -> jp_scoped_sub_tm n sigma b
  | ECLam _ b -> jp_scoped_sub_tm 0 sigma b
  | ECApp b -> jp_scoped_sub_tm n sigma b
  | ELet _ e1 e2 ->
    jp_scoped_sub_tm n sigma e1; jp_upn_esub 1 sigma; jp_scoped_sub_tm n (up_esub sigma) e2
  | ELetRec bs b ->
    jp_upn_esub (L.length bs) sigma; jp_scoped_sub_tm_binds 0 (upn_esub (L.length bs) sigma) bs;
    jp_scoped_sub_tm n (upn_esub (L.length bs) sigma) b
  | ECase es dt -> jp_scoped_sub_tm_exps n sigma es; jp_scoped_sub_tm_dt n sigma dt
  | ELetJoin ts _ e1 e2 ->
    jp_jup_esub sigma; jp_upn_esub (L.length ts) (jup_esub sigma);
    jp_scoped_sub_tm (n + 1) (upn_esub (L.length ts) (jup_esub sigma)) e1;
    jp_scoped_sub_tm (n + 1) (jup_esub sigma) e2
  | EJump _ es -> jp_scoped_sub_tm_exps n sigma es
  | EExtend _ e1 e2 -> jp_scoped_sub_tm n sigma e1; jp_scoped_sub_tm n sigma e2
  | ESelect _ b -> jp_scoped_sub_tm n sigma b
  | ERestrict _ b -> jp_scoped_sub_tm n sigma b
  | EUpdate _ e1 e2 -> jp_scoped_sub_tm n sigma e1; jp_scoped_sub_tm n sigma e2
  | EMerge e1 e2 -> jp_scoped_sub_tm n sigma e1; jp_scoped_sub_tm n sigma e2
  | EInject _ _ b -> jp_scoped_sub_tm n sigma b
  | EWeaken _ _ b -> jp_scoped_sub_tm n sigma b
  | EAbsurd _ b -> jp_scoped_sub_tm n sigma b
  | EPerform _ _ _ b -> jp_scoped_sub_tm n sigma b
  | EHandle b h ->
    jp_scoped_sub_tm 0 sigma b; jp_upn_esub 1 sigma; jp_scoped_sub_tm 0 (up_esub sigma) h.h_ret;
    jp_scoped_sub_tm_cls 0 sigma h.h_clauses
  | EOpenEff _ b -> jp_scoped_sub_tm n sigma b
  | ERegion _ es b -> jp_scoped_sub_tm_exps n sigma es; jp_scoped_sub_tm 0 sigma b
  | EWriteCell _ _ b -> jp_scoped_sub_tm n sigma b
  | EMatch th dt -> jp_scoped_sub_tm_exps n sigma th; jp_scoped_sub_tm_dt n sigma dt
  | EOpenEffC _ b -> jp_scoped_sub_tm n sigma b
  | EFill _ b -> jp_scoped_sub_tm 0 sigma b
  | ERegionOpen _ th b -> jp_scoped_sub_tm_cells 0 sigma th; jp_scoped_sub_tm 0 sigma b

and jp_scoped_sub_tm_exps (n: nat) (sigma: esub) (es: list exp)
  : Lemma (requires jp_scoped_exps n es /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped_exps n (sub_tm_exps sigma es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> jp_scoped_sub_tm n sigma e; jp_scoped_sub_tm_exps n sigma es

and jp_scoped_sub_tm_binds (n: nat) (sigma: esub) (bs: list (typ & exp))
  : Lemma (requires jp_scoped_binds n bs /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped_binds n (sub_tm_binds sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> jp_scoped_sub_tm n sigma e; jp_scoped_sub_tm_binds n sigma bs

and jp_scoped_sub_tm_cells (n: nat) (sigma: esub) (th: list (key & exp))
  : Lemma (requires jp_scoped_cells n th /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped_cells n (sub_tm_cells sigma th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> jp_scoped_sub_tm n sigma e; jp_scoped_sub_tm_cells n sigma th

and jp_scoped_sub_tm_dt (n: nat) (sigma: esub) (dt: dtree)
  : Lemma (requires jp_scoped_dt n dt /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped_dt n (sub_tm_dt sigma dt))
          (decreases dt) =
  match dt with
  | DLeaf e -> jp_scoped_sub_tm n sigma e
  | DBind _ dt -> jp_upn_esub 1 sigma; jp_scoped_sub_tm_dt n (up_esub sigma) dt
  | DSwitchCtor _ bs df -> jp_scoped_sub_tm_brs n sigma bs; jp_scoped_sub_tm_odt n sigma df
  | DSwitchLit _ bs df -> jp_scoped_sub_tm_brs n sigma bs; jp_scoped_sub_tm_dt n sigma df
  | DSwitchKey _ bs df -> jp_scoped_sub_tm_brs n sigma bs; jp_scoped_sub_tm_odt n sigma df
  | DGuard e dt1 dt2 ->
    jp_scoped_sub_tm n sigma e; jp_scoped_sub_tm_dt n sigma dt1; jp_scoped_sub_tm_dt n sigma dt2

and jp_scoped_sub_tm_odt (n: nat) (sigma: esub) (df: option dtree)
  : Lemma (requires jp_scoped_odt n df /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped_odt n (sub_tm_odt sigma df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> jp_scoped_sub_tm_dt n sigma dt

and jp_scoped_sub_tm_brs (#lb: eqtype) (n: nat) (sigma: esub) (bs: list (lb & dtree))
  : Lemma (requires jp_scoped_brs n bs /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped_brs n (sub_tm_brs sigma bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> jp_scoped_sub_tm_dt n sigma dt; jp_scoped_sub_tm_brs n sigma bs

and jp_scoped_sub_tm_cls (n: nat) (sigma: esub) (cs: list clause)
  : Lemma (requires jp_scoped_cls n cs /\
                    (forall (i: nat). jp_scoped 0 (sigma i)))
          (ensures jp_scoped_cls n (sub_tm_cls sigma cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs ->
    jp_tyup_esub nb sigma; jp_upn_esub 2 (tyup_esub nb sigma);
    jp_scoped_sub_tm n (upn_esub 2 (tyup_esub nb sigma)) b; jp_scoped_sub_tm_cls n sigma cs
  | CFast _ nb _ b :: cs ->
    jp_tyup_esub nb sigma; jp_upn_esub 1 (tyup_esub nb sigma);
    jp_scoped_sub_tm n (up_esub (tyup_esub nb sigma)) b; jp_scoped_sub_tm_cls n sigma cs

let rec args_values_snoc (sg: sig) (args: list spine_arg) (a: spine_arg)
  : Lemma (ensures args_values sg (L.append args [a]) ==
                   (args_values sg args && args_values sg [a]))
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: args -> args_values_snoc sg args a

let rec chain_values_view (sg: sig) (e: exp)
  : Lemma (ensures chain_values sg e ==
                   (match decompose_global_app e with
                    | Some (_, _, args) -> args_values sg args
                    | None -> false))
          (decreases e) =
  match e with
  | EApp f v ->
    chain_values_view sg f;
    (match decompose_global_app f with
     | Some (_, _, args) -> args_values_snoc sg args (SVal v)
     | None -> ())
  | ETyApp f t ->
    chain_values_view sg f;
    (match decompose_global_app f with
     | Some (_, _, args) -> args_values_snoc sg args (STy t)
     | None -> ())
  | ECApp f ->
    chain_values_view sg f;
    (match decompose_global_app f with
     | Some (_, _, args) -> args_values_snoc sg args SConstr
     | None -> ())
  | _ -> ()

let foreign_redex_not_value (sg: sig) (e: exp)
  : Lemma (requires foreign_redex sg e) (ensures not (is_value sg e)) =
  ()

let rec value_jp_scoped (sg: sig) (n: nat) (v: exp)
  : Lemma (requires is_value sg v /\ jp_scoped n v) (ensures jp_scoped 0 v)
          (decreases %[v; 1]) =
  match v with
  | ETyLam _ _ | ECLam _ _ | ELit _ | ELam _ _ _ | ERecEmpty | EOpaque _ _ -> ()
  | EInject _ _ v | EWeaken _ _ v | EOpenEff _ v -> value_jp_scoped sg n v
  | EExtend _ v1 v2 -> value_jp_scoped sg n v1; value_jp_scoped sg n v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> chain_values_jp_scoped sg n v
  | _ -> ()

(* The value arguments of a chain are values, and the rest of it holds no
   term, so the chain is scoped as its value arguments are. *)
and chain_values_jp_scoped (sg: sig) (n: nat) (e: exp)
  : Lemma (requires chain_values sg e /\ jp_scoped n e) (ensures jp_scoped 0 e)
          (decreases %[e; 0]) =
  match e with
  | EGlobal _ _ -> ()
  | EApp f v -> chain_values_jp_scoped sg n f; value_jp_scoped sg n v
  | ETyApp f _ | ECApp f -> chain_values_jp_scoped sg n f

let value_jp_scoped_any (sg: sig) (n m: nat) (v: exp)
  : Lemma (requires is_value sg v /\ jp_scoped n v) (ensures jp_scoped m v) =
  value_jp_scoped sg n v; jp_scoped_mono 0 m v

let value_ren_jp (sg: sig) (n: nat) (xi: ren) (v: exp)
  : Lemma (requires is_value sg v /\ jp_scoped n v) (ensures ren_jp xi v == v) =
  value_jp_scoped sg n v; ren_jp_scoped 0 xi v

let letjoin_value (sg: sig) (n: nat) (v: exp)
  : Lemma (requires is_value sg v /\ jp_scoped (n + 1) v) (ensures ren_jp jp_down v == v) =
  value_ren_jp sg (n + 1) jp_down v

let jp_scoped_subst1_value (sg: sig) (n k: nat) (v e: exp)
  : Lemma (requires jp_scoped n e /\ is_value sg v /\ jp_scoped k v)
          (ensures jp_scoped n (subst1_tm v e)) =
  value_jp_scoped sg k v;
  introduce forall (i: nat). jp_scoped 0 (scons v evar i) with ();
  jp_scoped_sub_tm n (scons v evar) e

(* The example of spec 06 §Saturation is a position in the declared type,
   `foreign id : forall a. a -> a` used at `Int -> Int`, in a signature
   holding only `Prim.Function`, `Prim.Int` and `M.id`. *)
let ex_function : qname = { qmod = ["Prim"]; qid = "Function" }
let ex_int_q : qname = { qmod = ["Prim"]; qid = "Int" }
let ex_id : qname = { qmod = ["M"]; qid = "id" }
let ex_int : typ = TCon ex_int_q []
let ex_int_to_int : typ = fun_ty ex_function ex_int TRowEmpty ex_int

let ex_sig : sig = {
  tycons = (fun q ->
    if q = ex_function then
      Some { tc_nk = 0;
             tc_kind = KArrow KType (KArrow (KRow EEffect) (KArrow KType KType));
             tc_class = TcIntrinsic ClsFunction }
    else if q = ex_int_q then
      Some { tc_nk = 0; tc_kind = KType; tc_class = TcIntrinsic ClsLiteral }
    else None);
  effects = (fun _ -> None);
  ctors = (fun _ -> None);
  foreigns = (fun q ->
    if q = ex_id then
      Some { fr_nk = 0;
             fr_ty = TForall KType (fun_ty ex_function (TVar 0) TRowEmpty (TVar 0));
             fr_observ_none = true }
    else None);
  values = (fun _ -> None);
}

(* `M.id` expects a type, `M.id [Int -> Int]` one value, and
   `M.id [Int -> Int] f` is saturated although `θ(a)` is a function type,
   so `(M.id [Int -> Int] f) 0` has no cursor. *)
let _ = assert_norm (is_value ex_sig (recompose ex_id [] []))
let _ = assert_norm (is_value ex_sig (recompose ex_id [] [STy ex_int_to_int]))
let _ = assert_norm (foreign_redex ex_sig (recompose ex_id [] [STy ex_int_to_int; SVal (ELam ex_int TRowEmpty (EVar 0))]))
let _ = assert_norm (None? (spine_cursor ex_sig ex_id []
                             [STy ex_int_to_int; SVal (ELam ex_int TRowEmpty (EVar 0));
                              SVal (ELit (LInt 0l))]))
