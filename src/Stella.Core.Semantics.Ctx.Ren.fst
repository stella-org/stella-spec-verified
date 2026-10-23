(* Each lemma is a case analysis on the frame, or an induction on the
   context. The lists of `case`, `jump` and `region` are split at the hole,
   and `ren_tm_exps` distributes over the split (`ren_tm_exps_append`).
   Values are kept by `is_value_ren_tm`, the values of an open region's
   cells one cell at a time. *)
module Stella.Core.Semantics.Ctx.Ren
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Semantics.Ctx
open Stella.Core.Typing.Rename.Facts
module L = FStar.List.Tot
module V = Stella.Core.Value

let ren_tm_handle xi e h = ()

let rec ren_frames_length (xi: ren) (fs: list frame)
  : Lemma (ensures L.length (ren_frames xi fs) == L.length fs) (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs -> ren_frames_length xi fs

let rec ren_frames_append (xi: ren) (fs1 fs2: list frame)
  : Lemma (ensures ren_frames xi (L.append fs1 fs2) ==
                   L.append (ren_frames xi fs1) (ren_frames xi fs2))
          (decreases fs1) =
  match fs1 with
  | [] -> ()
  | _ :: fs1 -> ren_frames_append xi fs1 fs2

(* * Plugging *)

let rec ren_tm_exps_append (xi: ren) (vs es: list exp)
  : Lemma (ensures ren_tm_exps xi (L.append vs es) ==
                   L.append (ren_tm_exps xi vs) (ren_tm_exps xi es))
          (decreases vs) =
  match vs with
  | [] -> ()
  | _ :: vs -> ren_tm_exps_append xi vs es

let ren_tm_plug1 xi f e =
  match f with
  | FCase vs es _ | FJump _ vs es | FRegion _ vs es _ -> ren_tm_exps_append xi vs (e :: es)
  | FAppArg _ | FAppFun _ | FTyApp _ | FCApp | FOpenEff _ | FOpenEffC _ -> ()
  | FExtendL _ _ | FExtendR _ _ | FUpdateL _ _ | FUpdateR _ _ | FMergeL _ | FMergeR _ -> ()
  | FSelect _ | FRestrict _ | FInject _ _ | FWeaken _ _ | FAbsurd _ -> ()
  | FLet _ _ -> ()
  | FGuard _ _ _ -> ()
  | FLetJoin _ _ _ -> ()
  | FPerform _ _ _ -> ()
  | FHandle _ -> ()
  | FRegionOpen _ _ -> ()
  | FWriteCell _ _ | FFill _ -> ()

let rec ren_tm_plug (xi: ren) (fs: list frame) (e: exp)
  : Lemma (ensures ren_tm xi (plug fs e) == plug (ren_frames xi fs) (ren_tm xi e))
          (decreases fs) =
  match fs with
  | [] -> ()
  | f :: fs -> ren_tm_plug1 xi f e; ren_tm_plug xi fs (plug1 f e)

(* * Sub-grammars *)

let rec cells_values_ren (sg: sig) (xi: ren) (th: list (key & exp))
  : Lemma (ensures cells_values sg (ren_tm_cells xi th) == cells_values sg th) (decreases th) =
  match th with
  | [] -> ()
  | (_, v) :: th -> is_value_ren_tm sg xi v; cells_values_ren sg xi th

let frame_ok_ren sg xi f =
  match f with
  | FAppFun v | FExtendR _ v | FUpdateR _ v | FMergeR v -> is_value_ren_tm sg xi v
  | FCase vs _ _ | FJump _ vs _ | FRegion _ vs _ _ -> values_ren_tm sg xi vs
  | FGuard th _ _ -> values_ren_tm sg xi th
  | FRegionOpen _ th -> cells_values_ren sg xi th
  | _ -> ()

let rec frames_ok_ren (sg: sig) (xi: ren) (fs: list frame)
  : Lemma (ensures frames_ok sg (ren_frames xi fs) == frames_ok sg fs) (decreases fs) =
  match fs with
  | [] -> ()
  | f :: fs -> frame_ok_ren sg xi f; frames_ok_ren sg xi fs

let handler_key_ren xi h = ()

let rec ev_k_ren (k: key) (xi: ren) (fs: list frame)
  : Lemma (ensures ev_k k (ren_frames xi fs) == ev_k k fs) (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs -> ev_k_ren k xi fs

let rec ev_l_ren (a: atom) (xi: ren) (fs: list frame)
  : Lemma (ensures ev_l a (ren_frames xi fs) == ev_l a fs) (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs -> ev_l_ren a xi fs

let rec tl_frames_ren (xi: ren) (fs: list frame)
  : Lemma (ensures tl_frames (ren_frames xi fs) == tl_frames fs) (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs -> tl_frames_ren xi fs
