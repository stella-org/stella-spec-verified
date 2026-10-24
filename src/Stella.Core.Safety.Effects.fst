(* Proof structure.

   `steps_preservation` and `steps_typed` recurse on the sequence, one
   step at a time by `preservation` and `preservation_typed`, the next
   step starting from the `Γ_R2` the previous one gives; the extensions
   compose (`layouts_ext_trans`). Effect safety types the last term of the
   sequence (`steps_preservation`) and applies
   `unhandled_perform_untypable` to it; the closed context of the last
   `Γ_R2` is well formed by `rctx_ok_wf_ctx`. *)
module Stella.Core.Safety.Effects
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Rename.Tm
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
  : Ghost (preserved sg gi ln rs ra' [] e' t TRowEmpty)
          (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    rdom_in rs ra)
          (ensures fun _ -> True)
          (decreases s) =
  match s with
  | Steps_Refl ->
    layouts_ext_refl (closed_ctx rs);
    { rs' = rs; ok = (); der = h }
  | Steps_Step s1 rest ->
    let p1 = preservation h s1 in
    let p2 = steps_pres p1.der rest in
    layouts_ext_trans (closed_ctx rs) (closed_ctx p1.rs') (closed_ctx p2.rs');
    { rs' = p2.rs'; ok = (); der = p2.der }

let steps_preservation #sg #gi #ln #rs #ra #st #e #ra' #st' #e' #t h s = steps_pres h s

let rec steps_typed_aux (#sg: sig) (#gi: genv) (ln: lctx) (rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (t: typ) (s: steps sg gi ra st e ra' st' e')
  : Lemma (requires sig_ok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    rdom_in rs ra /\ typed sg ln (closed_ctx rs) e t)
          (ensures exists (rs': list (atom & layout)).
                     rctx_after sg gi ln rs ra' rs' /\ typed sg ln (closed_ctx rs') e' t)
          (decreases s) =
  match s with
  | Steps_Refl ->
    layouts_ext_refl (closed_ctx rs);
    FStar.Classical.exists_intro
      (fun (rs': list (atom & layout)) ->
         rctx_after sg gi ln rs ra' rs' /\ typed sg ln (closed_ctx rs') e' t) rs
  | Steps_Step #_ #_ #_ #_ #_ #ra1 #_ #e1 s1 rest ->
    preservation_typed ln rs t s1;
    eliminate exists (rs1: list (atom & layout)).
      rctx_after sg gi ln rs ra1 rs1 /\ typed sg ln (closed_ctx rs1) e1 t
    with begin
      steps_typed_aux ln rs1 t rest;
      eliminate exists (rs2: list (atom & layout)).
        rctx_after sg gi ln rs1 ra' rs2 /\ typed sg ln (closed_ctx rs2) e' t
      with begin
        layouts_ext_trans (closed_ctx rs) (closed_ctx rs1) (closed_ctx rs2);
        FStar.Classical.exists_intro
          (fun (rs': list (atom & layout)) ->
             rctx_after sg gi ln rs ra' rs' /\ typed sg ln (closed_ctx rs') e' t) rs2
      end
    end

let steps_typed #sg #gi ln rs #ra #st #e #ra' #st' #e' t s = steps_typed_aux ln rs t s

let effect_safety #sg #gi #ln #rs #ra #st #e #ra' #st' #e' #t h s =
  let p = steps_preservation h s in
  rctx_ok_wf_ctx sg p.rs';
  unhandled_perform_untypable p.der

let effect_safety_typed #sg #gi ln rs #ra #st #e #ra' #st' #e' t s =
  steps_typed ln rs t s;
  eliminate exists (rs': list (atom & layout)).
    rctx_after sg gi ln rs ra' rs' /\ typed sg ln (closed_ctx rs') e' t
  with begin
    rctx_ok_wf_ctx sg rs';
    eliminate exists (h: typing sg ln (closed_ctx rs') [] e' t TRowEmpty). True
    with unhandled_perform_untypable h
  end
