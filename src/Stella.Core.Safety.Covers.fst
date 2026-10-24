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

   The rules of operations and handlers (`cov_eff`) read no derivation:
   the clause `clause_of` selects is one of the handler's (`cov_clause`),
   instantiating its type binders keeps its names (`cov_inst`), and the
   reinstalled handler is the redex's `handle` renamed, which keeps its
   names, with a variable in the hole (`cov_resume`).

   The rules of regions and cells (`cov_region`) read no derivation
   either: the cells are covered one by one (`cells_*_all`), and the hole
   of the `Ev_ℓ` is replaced by a covered term (`covers_plug_replace`).

   `sig_ok` is hidden behind `sok`, and the two lemmas that ask for it
   are called through the wrappers that reveal it (`*_h`), all from
   `Stella.Core.Safety.Hidden`, so its quantifiers do not enter the
   queries of the helpers. *)
module Stella.Core.Safety.Covers
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
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
open Stella.Core.Semantics.Ctx.Ren
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

(* * Operations and handlers *)

let rec cov_clause (sg: sig) (gi: genv) (op: opname) (cs: list clause) (c: clause)
  : Lemma (requires exp_all_cls (covered sg gi) cs /\ clause_of op cs == Some c)
          (ensures (match c with
                    | CFull _ _ _ _ b -> covers sg gi b
                    | CFast _ _ _ b -> covers sg gi b))
          (decreases cs) =
  match cs with
  | c' :: cs' -> if clause_op c' = op then () else cov_clause sg gi op cs' c

(* The body of a clause with its type binders instantiated. *)
let cov_inst (sg: sig) (gi: genv) (ss: list typ) (body: exp)
  : Lemma (requires covers sg gi body) (ensures covers sg gi (sub_ty_exp (binders_tsub ss) body)) =
  covers_sub_ty_exp (binders_tsub ss) body;
  covers_globals_eq sg gi (sub_ty_exp (binders_tsub ss) body) body

(* `handle Ev_k[y] with h` is covered when `handle Ev_k[e] with h` is. *)
let cov_resume (sg: sig) (gi: genv) (fs: list frame) (e: exp) (hd: handler)
  : Lemma (requires covers sg gi (EHandle (plug fs e) hd)) (ensures covers sg gi (resume fs hd)) =
  let fs1 = ren_frames (shift 1) fs in
  let hd1 = ren_handler (shift 1) hd in
  let e1 = ren_tm (shift 1) e in
  covers_ren_tm (shift 1) (EHandle (plug fs e) hd);
  covers_globals_eq sg gi (ren_tm (shift 1) (EHandle (plug fs e) hd)) (EHandle (plug fs e) hd);
  ren_tm_handle (shift 1) (plug fs e) hd;
  ren_tm_plug (shift 1) fs e;
  assert (covers sg gi (plug1 (FHandle hd1) (plug fs1 e1)));
  covers_plug_replace sg gi fs1 e1 (EVar 0);
  covers_plug1_replace sg gi (FHandle hd1) (plug fs1 e1) (plug fs1 (EVar 0))

let for_all_pair (p: exp -> bool) (a b: exp)
  : Lemma (requires p a /\ p b) (ensures L.for_all p [a; b]) =
  assert_norm (L.for_all p [a; b] == (p a && p b))

let cov_eff (#sg: sig) (#gi: genv) (#e #e': exp) (eh: eff_head sg gi e (CTerm e'))
  : Lemma (requires covers sg gi e) (ensures covers sg gi e') =
  match eh with
  | EH_Return #_ #_ #v #hd _ -> covers_subst1_tm sg gi v hd.h_ret
  | EH_Full #_ #_ #fs #k #op #ss #v #hd #_ #_ #_ #_ #_ #nb #s #kt #body #tp #rho _ _ _ _ _ ->
    let p = EPerform k op ss v in
    covers_plug sg gi fs p;
    cov_clause sg gi op hd.h_clauses (CFull op nb s kt body);
    cov_inst sg gi ss body;
    cov_resume sg gi fs p hd;
    let kv = continuation tp rho fs hd in
    assert (covers sg gi kv);
    for_all_pair (covers sg gi) kv v;
    covers_list_esub sg gi [kv; v] (sub_ty_exp (binders_tsub ss) body)
  | EH_Fast #_ #_ #fs #k #op #ss #v #hd #_ #_ #ts #_ #os #nb #s #body _ _ _ _ ->
    let p = EPerform k op ss v in
    covers_plug sg gi fs p;
    cov_clause sg gi op hd.h_clauses (CFast op nb s body);
    cov_inst sg gi ss body;
    cov_resume sg gi fs p hd;
    covers_subst1_tm sg gi v (sub_ty_exp (binders_tsub ss) body)

(* * Regions and cells *)

let rec cells_init_all (p: exp -> bool) (ks: list key) (vs: list exp)
  : Lemma (requires exp_all_exps p vs) (ensures exp_all_cells p (init_cells ks vs)) (decreases ks) =
  match ks, vs with
  | _ :: ks', _ :: vs' -> cells_init_all p ks' vs'
  | _ -> ()

let rec cells_assoc_all (p: exp -> bool) (th: list (key & exp)) (k: key) (v: exp)
  : Lemma (requires exp_all_cells p th /\ L.assoc k th == Some v) (ensures exp_all p v)
          (decreases th) =
  match th with
  | (k', _) :: th' -> if k' = k then () else cells_assoc_all p th' k v

let rec cells_update_all (p: exp -> bool) (th: list (key & exp)) (k: key) (v: exp)
  : Lemma (requires exp_all_cells p th /\ exp_all p v) (ensures exp_all_cells p (cells_update th k v))
          (decreases th) =
  match th with
  | [] -> ()
  | (k', _) :: th' -> if k' = k then () else cells_update_all p th' k v

(* `Prim.Unit` is a constructor, which needs no entry. *)
let unit_covered (sg: sig) (gi: genv) : Lemma (requires sok sg) (ensures covers sg gi unit_exp) =
  sok_elim sg

let cov_region (#sg: sig) (#gi: genv) (#ra: list atom) (#e: exp) (#ra': list atom) (#e': exp)
  (rh: region_head sg gi ra e ra' (CTerm e'))
  : Lemma (requires sok sg /\ covers sg gi e) (ensures covers sg gi e') =
  match rh with
  | RH_Open #_ #_ #_ #lay #vs #body #a _ _ ->
    cells_init_all (covered sg gi) (L.map fst lay) vs;
    covers_open_region a body;
    covers_globals_eq sg gi (open_region a body) body
  | RH_Exit _ -> ()
  | RH_Read #_ #_ #_ #a #th #fs #k #v _ _ ->
    cells_assoc_all (covered sg gi) th k v;
    covers_plug_replace sg gi fs (EReadCell (RFree a) k) v
  | RH_Write #_ #_ #_ #a #th #fs #k #v _ _ ->
    covers_plug sg gi fs (EWriteCell (RFree a) k v);
    cells_update_all (covered sg gi) th k v;
    unit_covered sg gi;
    covers_plug_replace sg gi fs (EWriteCell (RFree a) k v) unit_exp

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
  | S_Eff eh -> cov_eff eh
  | S_Region rh -> cov_region rh
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
