(* Plugging into a context extended outside, by induction on the inner
   context. *)
module Stella.Core.Semantics.Ctx
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Rows
open Stella.Core.Spine
module L = FStar.List.Tot
module V = Stella.Core.Value

let rec plug_append (fs1 fs2: list frame) (e: exp)
  : Lemma (ensures plug (L.append fs1 fs2) e == plug fs2 (plug fs1 e)) (decreases fs1) =
  match fs1 with
  | [] -> ()
  | f :: fs1' -> plug_append fs1' fs2 (plug1 f e)

let plug_snoc fs f e = plug_append fs [f] e

(* The hole of a value. A prefix of a chain whose cursor goes one step
   further is unsaturated (`spine_cursor_snoc`): a saturated remainder is
   no `forall`, no constraint arrow and no function type, so no argument
   steps it. *)

let prefix_unsaturated (sg: sig) (q: qname) (ks: list kind) (args: list spine_arg) (a: spine_arg)
  : Lemma (requires Some? (spine_cursor sg q ks (L.append args [a])))
          (ensures spine_unsaturated sg q ks args) =
  spine_cursor_snoc sg q ks args a

let chain_prefix_value (sg: sig) (x: exp) (a: spine_arg)
  : Lemma (requires V.is_value sg (apply_arg x a)) (ensures V.is_value sg x) =
  match decompose_global_app x with
  | Some (q, ks, args) ->
    assert (decompose_global_app (apply_arg x a) == Some (q, ks, L.append args [a]));
    (match global_scheme sg q with
     | Some (GForeign, _, _) -> prefix_unsaturated sg q ks args a
     | _ -> ())
  | None -> ()

let plug1_not_value sg f e =
  match f with
  | FAppFun v -> if V.is_value sg (EApp e v) then chain_prefix_value sg e (SVal v)
  | FTyApp t -> if V.is_value sg (ETyApp e t) then chain_prefix_value sg e (STy t)
  | FCApp -> if V.is_value sg (ECApp e) then chain_prefix_value sg e SConstr
  | _ -> ()

(* * Sub-grammars *)

let rec tl_frames_snoc (fs: list frame) (f: frame)
  : Lemma (requires tl_frames fs /\ FLetJoin? f)
          (ensures tl_frames (L.append fs [f]) /\ L.length (L.append fs [f]) == L.length fs + 1)
          (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs' -> tl_frames_snoc fs' f
