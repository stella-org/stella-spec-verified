(**
 * Term renamings of handlers, frames and evaluation contexts (spec 06
 * §Evaluation contexts, §Operations and handlers; design §1.1).
 *
 * The rules for operations rebuild `handle Ev_k[y] with h` under one new
 * term binder, the parameter `y` of the continuation `λ` or the binder of
 * the `let` of a `fast` clause. The context and the handler move under
 * that binder, so their free term variables are shifted by one
 * (`ren_frames (shift 1)`, `ren_handler (shift 1)`).
 *
 * Each frame is renamed as `ren_tm` renames the term it builds: every
 * part the frame stores is renamed under the term binders that stand over
 * it in that term.
 *
 *   - `let x : τ = Ev in e`: the body `e` under `up_ren ξ`;
 *   - `letjoin j (x̄ : τ̄) : τ = e1 in Ev`: the definition `e1` under
 *     `upn_ren |τ̄| ξ`, the hole (the continuation) at `ξ`;
 *   - `handle Ev with h`: the return clause under one binder, a `full`
 *     clause's body under two (`x` and `k`), a `fast` clause's body under
 *     one (`x`). Type binders of a clause do not move term indices;
 *   - every other stored term at `ξ`, including the values `v̄` of `case`,
 *     `jump` and `region`, the values `θ` of `match` and of an open
 *     region, the trees of `case` and `guard`, and the body of `region`.
 *
 * Types bind no term variable, so every type and key a frame stores is
 * kept. No frame stands under a term binder of the plugged term, so all
 * the frames of a context are renamed by the same `ξ`, and renaming
 * commutes with plugging (`ren_tm_plug`). A renaming keeps values
 * (`Stella.Core.Typing.Rename.Facts.is_value_ren_tm`), the handler's
 * element, and the kind of each frame, so it keeps `frames_ok`, `ev_k`,
 * `ev_l` and `tl_frames`.
 *)
module Stella.Core.Semantics.Ctx.Ren
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Semantics.Ctx
module L = FStar.List.Tot

(** * Handlers *)

(** `h` renamed as `ren_tm` renames the handler of `handle e with h`: the
    return clause under its binder, the operation clauses by
    `ren_tm_cls`, the element and the return annotation kept. *)
let ren_handler (xi: ren) (h: handler) : handler =
  { h_ent = h.h_ent;
    h_ret_ty = h.h_ret_ty;
    h_ret = ren_tm (up_ren xi) h.h_ret;
    h_clauses = ren_tm_cls xi h.h_clauses }

val ren_tm_handle (xi: ren) (e: exp) (h: handler)
  : Lemma (ren_tm xi (EHandle e h) == EHandle (ren_tm xi e) (ren_handler xi h))

(** * Frames *)

(** `f` renamed as `ren_tm ξ` renames `f[e]` around the hole. *)
let ren_frame (xi: ren) (f: frame) : frame =
  match f with
  | FAppArg fn -> FAppArg (ren_tm xi fn)
  | FAppFun v -> FAppFun (ren_tm xi v)
  | FTyApp t -> FTyApp t
  | FCApp -> FCApp
  | FOpenEff r -> FOpenEff r
  | FOpenEffC r -> FOpenEffC r
  | FExtendL k e2 -> FExtendL k (ren_tm xi e2)
  | FExtendR k v1 -> FExtendR k (ren_tm xi v1)
  | FUpdateL k e2 -> FUpdateL k (ren_tm xi e2)
  | FUpdateR k v1 -> FUpdateR k (ren_tm xi v1)
  | FMergeL e2 -> FMergeL (ren_tm xi e2)
  | FMergeR v1 -> FMergeR (ren_tm xi v1)
  | FSelect k -> FSelect k
  | FRestrict k -> FRestrict k
  | FInject k r -> FInject k r
  | FWeaken k t -> FWeaken k t
  | FAbsurd t -> FAbsurd t
  | FLet t e2 -> FLet t (ren_tm (up_ren xi) e2)
  | FCase vs es dt -> FCase (ren_tm_exps xi vs) (ren_tm_exps xi es) (ren_tm_dt xi dt)
  | FGuard th dt1 dt2 -> FGuard (ren_tm_exps xi th) (ren_tm_dt xi dt1) (ren_tm_dt xi dt2)
  | FLetJoin ts t e1 -> FLetJoin ts t (ren_tm (upn_ren (L.length ts) xi) e1)
  | FJump j vs es -> FJump j (ren_tm_exps xi vs) (ren_tm_exps xi es)
  | FPerform k op ts -> FPerform k op ts
  | FHandle h -> FHandle (ren_handler xi h)
  | FRegion lay vs es body ->
    FRegion lay (ren_tm_exps xi vs) (ren_tm_exps xi es) (ren_tm xi body)
  | FRegionOpen a th -> FRegionOpen a (ren_tm_cells xi th)
  | FWriteCell rr k -> FWriteCell rr k
  | FFill nu -> FFill nu

(** Every frame of a context renamed by the same `ξ`, innermost first. *)
let rec ren_frames (xi: ren) (fs: list frame) : Tot (list frame) (decreases fs) =
  match fs with
  | [] -> []
  | f :: fs -> ren_frame xi f :: ren_frames xi fs

val ren_frames_length (xi: ren) (fs: list frame)
  : Lemma (L.length (ren_frames xi fs) == L.length fs)

val ren_frames_append (xi: ren) (fs1 fs2: list frame)
  : Lemma (ren_frames xi (L.append fs1 fs2) == L.append (ren_frames xi fs1) (ren_frames xi fs2))

(** * Plugging *)

(** Renaming `f[e]` renames the frame and the hole. *)
val ren_tm_plug1 (xi: ren) (f: frame) (e: exp)
  : Lemma (ren_tm xi (plug1 f e) == plug1 (ren_frame xi f) (ren_tm xi e))

(** Renaming `Ev[e]` renames the context and the hole. *)
val ren_tm_plug (xi: ren) (fs: list frame) (e: exp)
  : Lemma (ren_tm xi (plug fs e) == plug (ren_frames xi fs) (ren_tm xi e))

(** * Sub-grammars *)

val frame_ok_ren (sg: sig) (xi: ren) (f: frame)
  : Lemma (frame_ok sg (ren_frame xi f) == frame_ok sg f)

val frames_ok_ren (sg: sig) (xi: ren) (fs: list frame)
  : Lemma (frames_ok sg (ren_frames xi fs) == frames_ok sg fs)

(** The renamed handler has the same element, so the same key. *)
val handler_key_ren (xi: ren) (h: handler)
  : Lemma ((ren_handler xi h).h_ent == h.h_ent /\ handler_key (ren_handler xi h) == handler_key h)

val ev_k_ren (k: key) (xi: ren) (fs: list frame)
  : Lemma (ev_k k (ren_frames xi fs) == ev_k k fs)

val ev_l_ren (a: atom) (xi: ren) (fs: list frame)
  : Lemma (ev_l a (ren_frames xi fs) == ev_l a fs)

val tl_frames_ren (xi: ren) (fs: list frame)
  : Lemma (tl_frames (ren_frames xi fs) == tl_frames fs)
