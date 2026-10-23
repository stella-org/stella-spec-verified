(* Proof structure.

   By induction on the step, as for typing. A step under a frame is a step
   of the hole: the hole is covered (`covers_plug1`), the induction covers
   its reduct, and the frame is filled back (`covers_plug1_replace`). The
   foreign rule reads the derivation of its redex, so the hole's
   derivation is taken from `plug1_typing`; a value has no step, so the
   hole is no value, which `plug1_typing` asks.

   A head rule is handled by one helper per family of rules (`cov_*`), on
   the syntax alone except for the two rules that read `G`. The foreign
   rule types its redex at the cursor instance (`foreign_redex_typed`),
   which is what condition (3) asks to give the adapter's outcome
   (`genv_ok_foreign`); the outcome is the step's, the adapter being a
   function.

   `sig_ok` is hidden behind `sok`, and the two lemmas that ask for it
   are called through the wrappers that reveal it (`*_h`), all from
   `Stella.Core.Safety.Hidden`, so its quantifiers do not enter the
   queries of the helpers. *)
module Stella.Core.Safety.Covers
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Spine
open Stella.Core.Erase
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Plug
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
open Stella.Core.Semantics.Covers
open Stella.Core.Safety.Hidden
module L = FStar.List.Tot
module V = Stella.Core.Value

(* * Substitution *)

let cov_beta (sg: sig) (gi: genv) (v body: exp)
  : Lemma (requires covers sg gi v /\ covers sg gi body)
          (ensures covers sg gi (subst1_tm v body)) =
  covers_subst1_tm sg gi v body

let cov_tybeta (sg: sig) (gi: genv) (s: typ) (v: exp)
  : Lemma (requires covers sg gi v) (ensures covers sg gi (subst1_ty_exp s v)) =
  covers_sub_ty_exp (scons s tvar) v;
  covers_globals_eq sg gi (subst1_ty_exp s v) v

(* * Globals *)

let cov_unfold (sg: sig) (gi: genv) (ln: lctx) (rs: list (atom & layout)) (q: qname)
  (ks: list kind) (v: exp)
  : Lemma (requires genv_ok sg ln rs gi /\ gi.gvals q == Some v)
          (ensures covers sg gi (kinst_exp ks v)) =
  genv_ok_covered sg ln rs gi q v;
  covers_kinst ks v;
  covers_globals_eq sg gi (kinst_exp ks v) v

let cov_foreign (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#e: exp) (#t #r: typ) (q: qname) (ks: list kind) (args: list spine_arg)
  (fe: foreign_entry) (v: exp)
  (h: typing sg ln (closed_ctx rs) d e t r)
  : Lemma (requires sok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    covers sg gi e /\
                    V.foreign_redex sg e /\ decompose_global_app e == Some (q, ks, args) /\
                    gi.gforeign q == Some fe /\ fe.fe_pre (L.map erase (value_args args)) /\
                    fe.fe_adapt (chain_instance e) (value_args args) == Some (FOVal v))
          (ensures covers sg gi v) =
  rctx_ok_wf_ctx sg rs;
  match chain_cursor sg e with
  | Some (s, th) ->
    foreign_redex_typed_h h s th;
    genv_ok_foreign sg ln rs gi e;
    assert (outcome_ok sg gi ln rs q (value_args args) (sub_ty th s) (FOVal v));
    covers_value_args sg gi e q ks args;
    covers_relative_covers sg gi (value_args args) v
  | None -> ()

(* * Pattern matching *)

let cov_bind (sg: sig) (gi: genv) (th: list exp) (o: occ) (dt: dtree) (v: exp)
  : Lemma (requires covers sg gi (EMatch th (DBind o dt)) /\ proj sg th o == Some v)
          (ensures covers sg gi (EMatch th (sub_tm_dt (scons v evar) dt))) =
  covers_exps sg gi th;
  covers_proj sg gi th o v;
  covers_subst1_dt sg gi v dt

let cov_switch (#lb: eqtype) (sg: sig) (gi: genv) (th: list exp) (l: option lb)
  (bs: list (lb & dtree)) (dt: dtree)
  : Lemma (requires exp_all_exps (covered sg gi) th /\
                    exp_all_brs (covered sg gi) bs /\ branch l bs == Some dt)
          (ensures covers sg gi (EMatch th dt)) =
  let Some l0 = l in
  covers_branch sg gi l0 bs dt

(* * Join points *)

let cov_join (sg: sig) (gi: genv) (ts: list typ) (t1: typ) (e1: exp) (fs: list frame) (n: nat)
  (vs: list exp)
  : Lemma (requires covers sg gi (ELetJoin ts t1 e1 (plug fs (EJump n vs))))
          (ensures covers sg gi
                     (ELetJoin ts t1 e1
                        (plug fs (sub_tm (list_esub (L.rev vs)) (ren_jp (shift n) e1))))) =
  let x = sub_tm (list_esub (L.rev vs)) (ren_jp (shift n) e1) in
  covers_plug sg gi fs (EJump n vs);
  covers_exps sg gi vs;
  covers_rev sg gi vs;
  covers_ren_jp (shift n) e1;
  covers_globals_eq sg gi (ren_jp (shift n) e1) e1;
  covers_list_esub sg gi (L.rev vs) (ren_jp (shift n) e1);
  covers_plug_replace sg gi fs (EJump n vs) x

(* * The head rules *)

(* The rules that do not read `G`: coverage from the syntax alone. *)
let cov_syntactic (#sg: sig) (#gi: genv) (#e #e': exp) (ph: pure_head sg gi e (CTerm e'))
  : Lemma (requires covers sg gi e /\ not (PH_Unfold? ph) /\ not (PH_Foreign? ph))
          (ensures covers sg gi e') =
  match ph with
  | PH_Beta #_ #_ #_ #_ #body #v _ -> cov_beta sg gi v body
  | PH_TyBeta #_ #_ #_ #v #s _ -> cov_tybeta sg gi s v
  | PH_CBeta _ -> ()
  | PH_OpenEffApp _ -> ()
  | PH_OpenEffC _ -> ()
  | PH_Let #_ #_ #_ #v #body _ -> cov_beta sg gi v body
  | PH_SelectHit _ -> ()
  | PH_SelectMiss _ _ -> ()
  | PH_RestrictHit _ -> ()
  | PH_RestrictMiss _ _ -> ()
  | PH_UpdateHit _ -> ()
  | PH_UpdateMiss _ _ -> ()
  | PH_MergeEmpty _ -> ()
  | PH_MergeExtend _ -> ()
  | PH_Case _ -> ()
  | PH_Leaf -> ()
  | PH_Bind #_ #_ #th #o #dt #v _ -> cov_bind sg gi th o dt v
  | PH_GuardTrue -> ()
  | PH_GuardFalse -> ()
  | PH_SwitchCtor #_ #_ #th #_ #bs #_ #v #dt _ -> cov_switch sg gi th (ctor_head sg v) bs dt
  | PH_SwitchCtorDef _ -> ()
  | PH_SwitchLit #_ #_ #th #_ #bs #_ #v #dt _ -> cov_switch sg gi th (lit_of v) bs dt
  | PH_SwitchLitDef _ -> ()
  | PH_SwitchKey #_ #_ #th #_ #bs #_ #v #dt _ -> cov_switch sg gi th (carrier_key v) bs dt
  | PH_SwitchKeyDef _ -> ()
  | PH_Join #_ #_ #ts #t1 #e1 #fs #n #vs _ _ -> cov_join sg gi ts t1 e1 fs n vs
  | PH_JoinValue _ -> ()

let cov_head (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#e #e': exp) (#t #r: typ)
  (h: typing sg ln (closed_ctx rs) d e t r) (ph: pure_head sg gi e (CTerm e'))
  : Lemma (requires sok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    covers sg gi e)
          (ensures covers sg gi e') =
  match ph with
  | PH_Unfold #_ #_ #q #ks #_ #v _ _ -> cov_unfold sg gi ln rs q ks v
  | PH_Foreign #_ #_ #_ #q #ks #args #fe #_ _ _ _ _ ->
    cov_foreign #sg #gi #ln #rs #d #e #t #r q ks args fe e' h
  | _ -> cov_syntactic ph

(* * Steps *)

let rec cov_step (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (#d: jctx) (#t #r: typ)
  (h: typing sg ln (closed_ctx rs) d e t r)
  (s: step sg gi ra st e ra' st' (CTerm e'))
  : Lemma (requires sok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    covers sg gi e)
          (ensures covers sg gi e')
          (decreases s) =
  match s with
  | S_Pure ph -> cov_head #sg #gi #ln #rs #d #e #e' #t #r h ph
  | S_Ctx #_ #_ #_ #_ #e1 #_ #_ #e1' f _ s1 ->
    rctx_ok_wf_ctx sg rs;
    if V.is_value sg e1 then value_no_step s1
    else begin
      let pi = plug1_typing_h #sg #ln #(closed_ctx rs) #d #f #e1 #t #r (retm h (plug1 f e1)) in
      covers_plug1 sg gi f e1;
      cov_step pi.hole s1;
      covers_plug1_replace sg gi f e1 e1'
    end

(* * The theorem *)

let preservation_covers #sg #gi #ln #rs #ra #st #e #ra' #st' #e' #d #t #r h s =
  sok_intro sg;
  cov_step h s
