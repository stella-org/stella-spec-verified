(* Proof structure.

   The simulation is that of `Stella.Core.Init.Sim`: `ssim c e e'` keeps the
   shape of `e` and its term variables below the cutoff `c`, and replaces
   its types and kinds arbitrarily. A kind instantiation changes kinds and
   types alone and keeps every term variable, so it relates a term to its
   image at any cutoff (`ssim_kinst`), which gives `init_safe_kinst` as an
   instance of `init_safe_ssim`. *)
module Stella.Core.Typing.Kinst.Init
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Init
open Stella.Core.Init.Sim
module L = FStar.List.Tot

let rec kinst_binds_length (ks: list kind) (bs: list (typ & exp))
  : Lemma (ensures L.length (kinst_binds ks bs) == L.length bs) (decreases bs) =
  match bs with
  | [] -> ()
  | _ :: bs -> kinst_binds_length ks bs

let rec kinst_tys_length (ks: list kind) (ts: list typ)
  : Lemma (ensures L.length (kinst_tys ks ts) == L.length ts) (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts -> kinst_tys_length ks ts

let rec ssim_kinst (c: nat) (ks: list kind) (e: exp)
  : Lemma (ensures ssim c e (kinst_exp ks e)) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> ssim_kinst (c + 1) ks b
  | EApp e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 | EMerge e1 e2 ->
    ssim_kinst c ks e1; ssim_kinst c ks e2
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EInject _ _ b
  | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b | EWriteCell _ _ b
  | EOpenEffC _ b | EFill _ b -> ssim_kinst c ks b
  | ELet _ e1 e2 -> ssim_kinst c ks e1; ssim_kinst (c + 1) ks e2
  | ELetRec bs b ->
    kinst_binds_length ks bs;
    ssim_binds_kinst (c + L.length bs) ks bs; ssim_kinst (c + L.length bs) ks b
  | ECase es dt | EMatch es dt -> ssim_exps_kinst c ks es; ssim_dt_kinst c ks dt
  | ELetJoin ts _ e1 e2 ->
    kinst_tys_length ks ts;
    ssim_kinst (c + L.length ts) ks e1; ssim_kinst c ks e2
  | EJump _ es -> ssim_exps_kinst c ks es
  | EHandle b h ->
    ssim_kinst c ks b; ssim_kinst (c + 1) ks h.h_ret; ssim_cls_kinst c ks h.h_clauses
  | ERegion _ es b -> ssim_exps_kinst c ks es; ssim_kinst c ks b
  | ERegionOpen _ th b -> ssim_cells_kinst c ks th; ssim_kinst c ks b

and ssim_exps_kinst (c: nat) (ks: list kind) (es: list exp)
  : Lemma (ensures ssim_exps c es (kinst_exps ks es)) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ssim_kinst c ks e; ssim_exps_kinst c ks es

and ssim_binds_kinst (c: nat) (ks: list kind) (bs: list (typ & exp))
  : Lemma (ensures ssim_binds c bs (kinst_binds ks bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> ssim_kinst c ks e; ssim_binds_kinst c ks bs

and ssim_cells_kinst (c: nat) (ks: list kind) (th: list (key & exp))
  : Lemma (ensures ssim_cells c th (kinst_cells ks th)) (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> ssim_kinst c ks e; ssim_cells_kinst c ks th

and ssim_dt_kinst (c: nat) (ks: list kind) (dt: dtree)
  : Lemma (ensures ssim_dt c dt (kinst_dt ks dt)) (decreases dt) =
  match dt with
  | DLeaf e -> ssim_kinst c ks e
  | DBind _ dt -> ssim_dt_kinst (c + 1) ks dt
  | DSwitchCtor _ bs df | DSwitchKey _ bs df -> ssim_brs_kinst c ks bs; ssim_odt_kinst c ks df
  | DSwitchLit _ bs df -> ssim_brs_kinst c ks bs; ssim_dt_kinst c ks df
  | DGuard e dt1 dt2 -> ssim_kinst c ks e; ssim_dt_kinst c ks dt1; ssim_dt_kinst c ks dt2

and ssim_odt_kinst (c: nat) (ks: list kind) (df: option dtree)
  : Lemma (ensures ssim_odt c df (kinst_odt ks df)) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> ssim_dt_kinst c ks dt

and ssim_brs_kinst (#lb: eqtype) (c: nat) (ks: list kind) (bs: list (lb & dtree))
  : Lemma (ensures ssim_brs c bs (kinst_brs ks bs)) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> ssim_dt_kinst c ks dt; ssim_brs_kinst c ks bs

and ssim_cls_kinst (c: nat) (ks: list kind) (cs: list clause)
  : Lemma (ensures ssim_cls c cs (kinst_cls ks cs)) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> ssim_kinst (c + 2) ks b; ssim_cls_kinst c ks cs
  | CFast _ _ _ b :: cs -> ssim_kinst (c + 1) ks b; ssim_cls_kinst c ks cs

let init_safe_kinst sg ks bs =
  ssim_binds_kinst (L.length bs) ks bs;
  init_safe_ssim sg bs (kinst_binds ks bs)
