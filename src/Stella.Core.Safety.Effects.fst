(* Proof structure.

   `steps_preservation` and `steps_typed` recurse on the sequence, one
   step at a time by `preservation` and `preservation_typed`. Effect
   safety types the last term of the sequence (`steps_preservation`) and
   applies `unhandled_perform_untypable` to it; `closed_ctx rs` is well
   formed by `rctx_ok_wf_ctx`. *)
module Stella.Core.Safety.Effects
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
open Stella.Core.Safety.Preservation
open Stella.Core.Safety.Progress.Eff

let rec steps_pres (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (#t: typ)
  (h: typing sg ln (closed_ctx rs) [] e t TRowEmpty)
  (s: steps sg gi ra st e ra' st' e')
  : Ghost (typing sg ln (closed_ctx rs) [] e' t TRowEmpty)
          (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi)
          (ensures fun _ -> True)
          (decreases s) =
  match s with
  | Steps_Refl -> h
  | Steps_Step s1 rest -> steps_pres (preservation h s1) rest

let steps_preservation #sg #gi #ln #rs #ra #st #e #ra' #st' #e' #t h s = steps_pres h s

let rec steps_typed_aux (#sg: sig) (#gi: genv) (ln: lctx) (rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (t: typ) (s: steps sg gi ra st e ra' st' e')
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    typed sg ln (closed_ctx rs) e t)
          (ensures typed sg ln (closed_ctx rs) e' t)
          (decreases s) =
  match s with
  | Steps_Refl -> ()
  | Steps_Step s1 rest ->
    preservation_typed ln rs t s1;
    steps_typed_aux ln rs t rest

let steps_typed #sg #gi ln rs #ra #st #e #ra' #st' #e' t s = steps_typed_aux ln rs t s

let effect_safety #sg #gi #ln #rs #ra #st #e #ra' #st' #e' #t h s =
  let h' = steps_preservation h s in
  rctx_ok_wf_ctx sg rs;
  unhandled_perform_untypable h'

let effect_safety_typed #sg #gi ln rs #ra #st #e #ra' #st' #e' t s =
  steps_typed ln rs t s;
  rctx_ok_wf_ctx sg rs;
  eliminate exists (h: typing sg ln (closed_ctx rs) [] e' t TRowEmpty). True
  with unhandled_perform_untypable h
