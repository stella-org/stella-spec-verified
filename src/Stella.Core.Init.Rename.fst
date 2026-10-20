(* Proof structure.

   The simulation is that of `Stella.Core.Init.Sim`: `ssim c e e'` keeps the
   shape of `e` and its term variables below the cutoff `c`, replaces its
   types and kinds arbitrarily, and puts an inert term, a variable at or
   beyond `c` among them, where a variable at or beyond `c` stood.

   A type substitution changes types alone, so it relates a term to its
   image at any cutoff (`ssim_sub_ty`); a type renaming is the type
   substitution of its renaming (`ren_ty_binds_as_sub`). A term renaming
   that fixes the variables below `c` and sends every other variable to one
   at or beyond `c` (`fixes c ξ`) relates a term to its image at `c`
   (`ssim_ren_tm`); its lifts under the term binders do so at the grown
   cutoff (`fixes_up`).

   A `letrec` binds its members as its innermost term variables, and the
   renaming under it is lifted past them, `upn_ren n ξ` for `n` members:
   it fixes the members and sends every variable bound outside the group
   above them, for any `ξ`. Each theorem of the interface is then an
   instance of `init_safe_ssim` at the cutoff `n`. *)
module Stella.Core.Init.Rename
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Sig
open Stella.Core.Init
open Stella.Core.Init.Sim
module L = FStar.List.Tot

(* A type substitution relates a term to its image at any cutoff. *)

let rec ssim_sub_ty (c: nat) (sigma: tsub) (e: exp)
  : Lemma (ensures ssim c e (sub_ty_exp sigma e)) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> ssim_sub_ty (c + 1) sigma b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    ssim_sub_ty c sigma e1; ssim_sub_ty c sigma e2
  | ETyLam _ b -> ssim_sub_ty c (up_tsub sigma) b
  | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> ssim_sub_ty c sigma b
  | ELet _ e1 e2 -> ssim_sub_ty c sigma e1; ssim_sub_ty (c + 1) sigma e2
  | ELetRec bs b ->
    ssim_binds_sub_ty (c + L.length bs) sigma bs; ssim_sub_ty (c + L.length bs) sigma b
  | ECase es dt | EMatch es dt -> ssim_exps_sub_ty c sigma es; ssim_dt_sub_ty c sigma dt
  | ELetJoin ts _ e1 e2 -> ssim_sub_ty (c + L.length ts) sigma e1; ssim_sub_ty c sigma e2
  | EJump _ es -> ssim_exps_sub_ty c sigma es
  | EHandle b h ->
    ssim_sub_ty c sigma b; ssim_sub_ty (c + 1) sigma h.h_ret; ssim_cls_sub_ty c sigma h.h_clauses
  | ERegion _ es b -> ssim_exps_sub_ty c sigma es; ssim_sub_ty c sigma b
  | ERegionOpen _ th b -> ssim_cells_sub_ty c sigma th; ssim_sub_ty c sigma b

and ssim_exps_sub_ty (c: nat) (sigma: tsub) (es: list exp)
  : Lemma (ensures ssim_exps c es (sub_ty_exps sigma es)) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ssim_sub_ty c sigma e; ssim_exps_sub_ty c sigma es

and ssim_binds_sub_ty (c: nat) (sigma: tsub) (bs: list (typ & exp))
  : Lemma (ensures ssim_binds c bs (sub_ty_binds sigma bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> ssim_sub_ty c sigma e; ssim_binds_sub_ty c sigma bs

and ssim_cells_sub_ty (c: nat) (sigma: tsub) (th: list (key & exp))
  : Lemma (ensures ssim_cells c th (sub_ty_cells sigma th)) (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> ssim_sub_ty c sigma e; ssim_cells_sub_ty c sigma th

and ssim_dt_sub_ty (c: nat) (sigma: tsub) (dt: dtree)
  : Lemma (ensures ssim_dt c dt (sub_ty_dt sigma dt)) (decreases dt) =
  match dt with
  | DLeaf e -> ssim_sub_ty c sigma e
  | DBind _ dt -> ssim_dt_sub_ty (c + 1) sigma dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df ->
    ssim_brs_sub_ty c sigma bs; ssim_odt_sub_ty c sigma df
  | DSwitchLit _ bs df -> ssim_brs_sub_ty c sigma bs; ssim_dt_sub_ty c sigma df
  | DGuard e dt1 dt2 ->
    ssim_sub_ty c sigma e; ssim_dt_sub_ty c sigma dt1; ssim_dt_sub_ty c sigma dt2

and ssim_odt_sub_ty (c: nat) (sigma: tsub) (df: option dtree)
  : Lemma (ensures ssim_odt c df (sub_ty_odt sigma df)) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ssim_dt_sub_ty c sigma dt

and ssim_brs_sub_ty (#lb: eqtype) (c: nat) (sigma: tsub) (bs: list (lb & dtree))
  : Lemma (ensures ssim_brs c bs (sub_ty_brs sigma bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> ssim_dt_sub_ty c sigma dt; ssim_brs_sub_ty c sigma bs

and ssim_cls_sub_ty (c: nat) (sigma: tsub) (cs: list clause)
  : Lemma (ensures ssim_cls c cs (sub_ty_cls sigma cs)) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb _ _ b :: cs -> ssim_sub_ty (c + 2) (upn_tsub nb sigma) b; ssim_cls_sub_ty c sigma cs
  | CFast _ nb _ b :: cs -> ssim_sub_ty (c + 1) (upn_tsub nb sigma) b; ssim_cls_sub_ty c sigma cs

let rec ren_ty_binds_as_sub (zeta: ren) (bs: list (typ & exp))
  : Lemma (ensures ren_ty_binds zeta bs == sub_ty_binds (ren_tsub zeta) bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs ->
    ren_ty_as_sub zeta t; ren_ty_exp_as_sub zeta e; ren_ty_binds_as_sub zeta bs

(* A term renaming that fixes the variables below `c` and keeps the others
   at or beyond `c` relates a term to its image at `c`. *)

let fixes (c: nat) (xi: ren) : prop =
  (forall (i: nat). i < c ==> xi i == i) /\ (forall (i: nat). i >= c ==> xi i >= c)

let fixes_up (n c: nat) (xi: ren)
  : Lemma (requires fixes c xi) (ensures fixes (c + n) (upn_ren n xi)) =
  introduce forall (i: nat). i < c + n ==> upn_ren n xi i == i
  with introduce _ ==> _ with (if i < n then () else assert (xi (i - n) == i - n));
  introduce forall (i: nat). i >= c + n ==> upn_ren n xi i >= c + n
  with introduce _ ==> _ with assert (xi (i - n) >= c)

let rec ssim_ren_tm (c: nat) (xi: ren) (e: exp)
  : Lemma (requires fixes c xi) (ensures ssim c e (ren_tm xi e)) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> fixes_up 1 c xi; ssim_ren_tm (c + 1) (up_ren xi) b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    ssim_ren_tm c xi e1; ssim_ren_tm c xi e2
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> ssim_ren_tm c xi b
  | ELet _ e1 e2 -> ssim_ren_tm c xi e1; fixes_up 1 c xi; ssim_ren_tm (c + 1) (up_ren xi) e2
  | ELetRec bs b ->
    let n = L.length bs in
    fixes_up n c xi;
    ssim_binds_ren_tm (c + n) (upn_ren n xi) bs; ssim_ren_tm (c + n) (upn_ren n xi) b
  | ECase es dt | EMatch es dt -> ssim_exps_ren_tm c xi es; ssim_dt_ren_tm c xi dt
  | ELetJoin ts _ e1 e2 ->
    let n = L.length ts in
    fixes_up n c xi;
    ssim_ren_tm (c + n) (upn_ren n xi) e1; ssim_ren_tm c xi e2
  | EJump _ es -> ssim_exps_ren_tm c xi es
  | EHandle b h ->
    ssim_ren_tm c xi b; fixes_up 1 c xi; ssim_ren_tm (c + 1) (up_ren xi) h.h_ret;
    ssim_cls_ren_tm c xi h.h_clauses
  | ERegion _ es b -> ssim_exps_ren_tm c xi es; ssim_ren_tm c xi b
  | ERegionOpen _ th b -> ssim_cells_ren_tm c xi th; ssim_ren_tm c xi b

and ssim_exps_ren_tm (c: nat) (xi: ren) (es: list exp)
  : Lemma (requires fixes c xi) (ensures ssim_exps c es (ren_tm_exps xi es)) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ssim_ren_tm c xi e; ssim_exps_ren_tm c xi es

and ssim_binds_ren_tm (c: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (requires fixes c xi) (ensures ssim_binds c bs (ren_tm_binds xi bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> ssim_ren_tm c xi e; ssim_binds_ren_tm c xi bs

and ssim_cells_ren_tm (c: nat) (xi: ren) (th: list (key & exp))
  : Lemma (requires fixes c xi) (ensures ssim_cells c th (ren_tm_cells xi th)) (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> ssim_ren_tm c xi e; ssim_cells_ren_tm c xi th

and ssim_dt_ren_tm (c: nat) (xi: ren) (dt: dtree)
  : Lemma (requires fixes c xi) (ensures ssim_dt c dt (ren_tm_dt xi dt)) (decreases dt) =
  match dt with
  | DLeaf e -> ssim_ren_tm c xi e
  | DBind _ dt -> fixes_up 1 c xi; ssim_dt_ren_tm (c + 1) (up_ren xi) dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df -> ssim_brs_ren_tm c xi bs; ssim_odt_ren_tm c xi df
  | DSwitchLit _ bs df -> ssim_brs_ren_tm c xi bs; ssim_dt_ren_tm c xi df
  | DGuard e dt1 dt2 -> ssim_ren_tm c xi e; ssim_dt_ren_tm c xi dt1; ssim_dt_ren_tm c xi dt2

and ssim_odt_ren_tm (c: nat) (xi: ren) (df: option dtree)
  : Lemma (requires fixes c xi) (ensures ssim_odt c df (ren_tm_odt xi df)) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ssim_dt_ren_tm c xi dt

and ssim_brs_ren_tm (#lb: eqtype) (c: nat) (xi: ren) (bs: list (lb & dtree))
  : Lemma (requires fixes c xi) (ensures ssim_brs c bs (ren_tm_brs xi bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> ssim_dt_ren_tm c xi dt; ssim_brs_ren_tm c xi bs

and ssim_cls_ren_tm (c: nat) (xi: ren) (cs: list clause)
  : Lemma (requires fixes c xi) (ensures ssim_cls c cs (ren_tm_cls xi cs)) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs ->
    fixes_up 2 c xi; ssim_ren_tm (c + 2) (upn_ren 2 xi) b; ssim_cls_ren_tm c xi cs
  | CFast _ _ _ b :: cs ->
    fixes_up 1 c xi; ssim_ren_tm (c + 1) (up_ren xi) b; ssim_cls_ren_tm c xi cs

let init_safe_sub_ty sg sigma bs =
  ssim_binds_sub_ty (L.length bs) sigma bs;
  init_safe_ssim sg bs (sub_ty_binds sigma bs)

let init_safe_ren_ty sg xi bs =
  ren_ty_binds_as_sub xi bs;
  init_safe_sub_ty sg (ren_tsub xi) bs

let init_safe_ren_tm sg xi bs =
  let n = L.length bs in
  fixes_up n 0 xi;
  ssim_binds_ren_tm n (upn_ren n xi) bs;
  init_safe_ssim sg bs (ren_tm_binds (upn_ren n xi) bs)
