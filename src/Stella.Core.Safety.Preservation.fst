(* Proof structure.

   By induction on the step. A step under a frame is split at the hole
   (`plug1_typing`), the induction types the hole's reduct at the hole's
   own `Δ` and row, and the frame is filled back, the cursor of a chain
   being kept by the step (`step_plug1_cursor_kept`). A value has no step,
   so the hole is no value, which `plug1_typing` asks. The hole of a term
   of the stage-5 fragment is one (`stage5_frag_plug1`), and no effect
   rule applies to such a term (`stage5_no_eff`).

   A head rule is handled by one helper per rule (`pres_*`). Each strips
   the conversions at the bottom of the redex's derivation (`strip_conv`),
   inverts the one rule left, types the reduct, and converts it back to
   the type and row of the redex. The redex is no chain and no value, so
   its shape excludes `T_Chain` and `T_VariantValue`. The two rules that
   read `G` are the exceptions: the reference to a top-level value is
   inverted by `inv_global`, and the saturated foreign chain by
   `foreign_redex_typed`, whose `typed` the conformance condition (3)
   reads. Both reducts come from a `typed` of `genv_ok`, through
   `indefinite_description_ghost`.

   Pattern matching: the scrutinee's occurrence is sound (`occ_sound`), a
   constructor branch takes its constructor from `ctor_head` and its
   fields from `ctor_value_fields_typing`, a key branch its key from
   `carrier_key` and its payload from `variant_payload_typing`, and a
   literal branch needs no value at all. The `switchKey` default retypes
   `θ(o)` at the residual (`key_default_typing`).

   Join: the jump's join point is the head of the `letjoin`'s `Δ`
   (`nth_append` at `n = |Tl|`), so its signature is the `letjoin`'s
   itself; the definition is weakened past `Tl` (`typing_weaken_jps`),
   instantiated (`typing_subst_values`) and put back (`tl_fill`).

   Records: a hit cancels the extension at the common key
   (`ext_ty_cancel_entails`), both rests lacking it by kinding; a miss
   splits the rest of the operand at the key, which the rest holds since
   the keys differ (`check_split_ty_other`), and the row of the result is
   the row of the redex up to `ext_comm` (`ext_ty_cancel_swap`). `merge`
   reads the disjointness of the rest through `entails_constr_eq` and
   `entails_disj_ext`.

   `sig_ok` is hidden behind `sok` (`Stella.Core.Safety.Hidden`), and
   every lemma that asks for it is called through a wrapper that reveals
   it (`*_h`, those shared with the other safety proofs in
   `Safety.Hidden`), so its quantifiers do not enter the queries of the
   helpers. *)
module Stella.Core.Safety.Preservation
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Rows.Split
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Entail.Split
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Sharp
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Erase
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Wf
open Stella.Core.Typing.Inversion
open Stella.Core.Typing.Closed
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Kinst
open Stella.Core.Typing.Join
open Stella.Core.Typing.Cut
open Stella.Core.Typing.Subst.Ty
open Stella.Core.Typing.Subst.Tm.Inst
open Stella.Core.Typing.Occ
open Stella.Core.Typing.Ctor
open Stella.Core.Typing.Plug
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
open Stella.Core.Safety.Hidden
module L = FStar.List.Tot
module V = Stella.Core.Value
module KF = Stella.Core.Kinding.Facts
module RG = Stella.Core.Typing.Regularity
module TV = Stella.Core.Typing.Values
module VF = Stella.Core.Typing.ValueForm
module RF = Stella.Core.Typing.Rename.Facts
module ID = FStar.IndefiniteDescription

(* * Wrappers of the lemmas that ask `sig_ok`, used here alone *)

let reg (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r)
  : Lemma (requires sok sg /\ wf_ctx sg g)
          (ensures check sg g t KType /\ check sg g r (KRow EEffect)) =
  sok_elim sg;
  RG.typing_regular h

let reg_record (sg: sig) (g: ctx) (r: typ)
  : Lemma (requires sok sg) (ensures check sg g (t_record r) KType <==> check sg g r (KRow EType)) =
  sok_elim sg;
  KF.check_t_record sg g r

let reg_fun (sg: sig) (g: ctx) (t1 r t2: typ)
  : Lemma (requires sok sg /\ check sg g (t_fun t1 r t2) KType)
          (ensures check sg g t1 KType /\ check sg g r (KRow EEffect) /\ check sg g t2 KType) =
  sok_elim sg;
  KF.check_t_fun sg g t1 r t2

let match_typing_regular_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#th: list exp) (#om: octx) (h: match_typing sg ln g d r th om)
  : Lemma (requires sok sg /\ wf_ctx sg g) (ensures octx_ok sg g om /\ check sg g r (KRow EEffect)) =
  sok_elim sg;
  RG.match_typing_regular h

let vt (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d v t r) (d': jctx) (r': typ)
  : Pure (typing sg ln g d' v t r')
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v /\ check sg g r' (KRow EEffect))
         (ensures fun _ -> True) =
  sok_elim sg;
  TV.value_typing h d' r'

let inv_extend_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: key) (#v1 #v2: exp)
  (#t #r: typ) (h: typing sg ln g d (EExtend k v1 v2) t r) (rr: typ)
  : Pure (extend_inv sg ln g r k v1 v2 rr)
         (requires sok sg /\ wf_ctx sg g /\ ty_eq t (t_record rr))
         (ensures fun _ -> True) =
  sok_elim sg;
  inv_extend h rr

let inv_openeff_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r': typ) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d (EOpenEff r' e) t r) (q: qname) (a rho c: typ)
  : Pure (openeff_inv sg ln g r r' e a rho c)
         (requires sok sg /\ wf_ctx sg g /\ ty_eq t (fun_ty q a rho c))
         (ensures fun _ -> q == prim_function) =
  sok_elim sg;
  inv_openeff h q a rho c

let typing_beta_h (#sg: sig) (#ln: lctx) (#g: ctx) (#t1: typ) (#body: exp) (#t2 #r': typ)
  (hb: typing sg ln (push_var g t1) [] body t2 r')
  (#d0: jctx) (#v: exp) (#r0: typ) (hv: typing sg ln g d0 v t1 r0) (d: jctx)
  : Pure (typing sg ln g d (subst1_tm v body) t2 r')
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True) =
  sok_elim sg;
  typing_beta hb hv d

let typing_subst1_h (#sg: sig) (#ln: lctx) (#g: ctx) (#k: kind) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln (push_tvar g k) d e t r) (s: typ)
  : Pure (typing sg ln g (sub_jctx (scons s tvar) d) (subst1_ty_exp s e) (subst1_ty s t)
            (subst1_ty s r))
         (requires sok sg /\ wf_ctx sg g /\ check sg g s k)
         (ensures fun _ -> True) =
  sok_elim sg;
  typing_subst1 h s

let typing_let_value_h (#sg: sig) (#ln: lctx) (#g: ctx) (#t1: typ) (#d: jctx)
  (#e2: exp) (#t #r: typ) (h2: typing sg ln (push_var g t1) d e2 t r)
  (#v: exp) (hv: typing sg ln g [] v t1 r)
  : Pure (typing sg ln g d (subst1_tm v e2) t r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True) =
  sok_elim sg;
  typing_let_value h2 hv

let typing_subst_values_h (#sg: sig) (#ln: lctx) (#g: ctx) (#ts: list typ) (#d: jctx)
  (#e: exp) (#t #r: typ) (h: typing sg ln (push_vars g ts) d e t r)
  (#d0: jctx) (#r0: typ) (#vs: list exp) (hvs: exps_typing sg ln g d0 r0 vs ts)
  : Pure (typing sg ln g d (sub_tm (list_esub (L.rev vs)) e) t r)
         (requires sok sg /\ wf_ctx sg g /\ L.for_all (V.is_value sg) vs)
         (ensures fun _ -> True) =
  sok_elim sg;
  typing_subst_values h hvs

let dt_typing_bind_value_h (#sg: sig) (#ln: lctx) (#g: ctx) (#t_o: typ) (#d: jctx)
  (#om: octx) (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln (push_var g t_o) d om dt t r)
  (#d0: jctx) (#v: exp) (#r0: typ) (hv: typing sg ln g d0 v t_o r0)
  : Pure (dt_typing sg ln g d om (sub_tm_dt (scons v evar) dt) t r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v /\ octx_ok sg g om)
         (ensures fun _ -> True) =
  sok_elim sg;
  dt_typing_bind_value h hv

let ctor_value_fields_typing_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp)
  (#t_o #r: typ) (h: typing sg ln g d v t_o r) (c: qname) (ks: list kind)
  (args: list spine_arg) (tq: qname) (ks': list kind) (ss': list typ) (cs: list qname)
  (fs': list typ)
  : Pure (exps_typing sg ln g [] r (value_args args) fs')
         (requires sok sg /\ decompose_global_app v == Some (c, ks, args) /\ is_ctor sg c /\
                   ty_eq t_o (tapps (TCon tq ks') ss') /\
                   check sg g (tapps (TCon tq ks') ss') KType /\
                   has_class sg tq (TcData cs) /\ L.mem c cs /\
                   ctor_fields sg c ks' ss' == Some fs')
         (ensures fun _ -> True) =
  sok_elim sg;
  ctor_value_fields_typing h c ks args tq ks' ss' cs fs'

let variant_payload_typing_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t_o #r: typ)
  (h: typing sg ln g d v t_o r) (vr: typ) (kts: list (key & typ)) (vr': typ) (k: key) (w: exp)
  (pt: typ)
  : Pure (typing sg ln g [] w pt r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   ty_eq t_o (t_variant vr) /\ check sg g vr (KRow EType) /\
                   key_split vr kts vr' /\ L.mem (k, pt) kts /\ check sg g pt KType /\
                   variant_view v == Some (k, w))
         (ensures fun _ -> True) =
  sok_elim sg;
  variant_payload_typing h vr kts vr' k w pt

let key_default_typing_h (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp) (#t_o #r: typ)
  (#d': jctx) (#om: octx) (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree))
  (#t #r': typ)
  (h: typing sg ln g d v t_o r) (hb: key_brs_typing sg ln g d' om o kts bs t r')
  (vr vr': typ)
  : Pure (typing sg ln g [] v (t_variant vr') r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v /\ ty_eq t_o (t_variant vr) /\
                   check sg g vr (KRow EType) /\ key_split vr kts vr' /\
                   check sg g vr' (KRow EType) /\ branch (carrier_key v) bs == None)
         (ensures fun _ -> True) =
  sok_elim sg;
  key_default_typing h hb vr vr'

let typing_global_unfold_h (#sg: sig) (#ln: lctx) (#nk: nat) (#rs: list (atom & layout))
  (#v: exp) (#t: typ)
  (h: typing sg ln (decl_rctx nk rs) [] v t TRowEmpty) (ks: list kind) (g: ctx) (d: jctx)
  (r: typ)
  : Pure (typing sg ln g d (kinst_exp ks v) (kinst_ty ks t) r)
         (requires sok sg /\ wf_ctx sg g /\ L.length ks == nk /\ qkinds_wf g.nk ks /\
                   V.is_value sg v /\ wf_ctx sg (closed_ctx rs) /\
                   layouts_ext (closed_ctx rs) g /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  sok_elim sg;
  typing_global_unfold h ks g d r

(* * Small facts *)

(* `T_Conv`. *)
let conv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t1 #r1: typ)
  (h: typing sg ln g d e t1 r1) (t2 r2: typ)
  : Pure (typing sg ln g d e t2 r2)
         (requires ty_eq t1 t2 /\ ty_eq r1 r2 /\ check sg g t2 KType /\
                   check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  T_Conv h () ()

(* * β and the other rules of abstraction *)

let pres_beta (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#t1 #r1: typ) (#body #v: exp)
  (#t #r: typ) (h: typing sg ln g d (EApp (ELam t1 r1 body) v) t r)
  : Pure (typing sg ln g d (subst1_tm v body) t r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_App #_ #_ #_ #_ #e1 #e2 #ta #tb #rr h1 h2 ->
    let h1 = retm h1 (ELam t1 r1 body) in
    let li = inv_lam h1 prim_function ta rr tb in
    reg h2;
    let h2 = conv (retm h2 v) t1 rr in
    let hb = typing_beta_h li.lam_body h2 d in
    conv hb t r
  | _ -> false_elim ()

let pres_tybeta (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: kind) (#v: exp) (#s: typ)
  (#t #r: typ) (h: typing sg ln g d (ETyApp (ETyLam k v) s) t r)
  : Pure (typing sg ln g d (subst1_ty_exp s v) t r)
         (requires sok sg /\ wf_ctx sg g)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_TyApp #_ #_ #_ #_ #e1 #s1 #k0 #t0 #rr h1 _ ->
    let h1 = retm h1 (ETyLam k v) in
    let ti = inv_tylam h1 k0 t0 in
    let hs = typing_subst1_h ti.tylam_body s in
    RF.value_form_sub_ty sg (scons s tvar) v;
    VF.value_form_is_value sg (subst1_ty_exp s v);
    ty_eq_sub (scons s tvar) ti.tylam_res t0;
    let hs : typing sg ln g [] (subst1_ty_exp s v) (subst1_ty s ti.tylam_res) TRowEmpty = hs in
    let hv = vt hs d r in
    conv hv t r
  | _ -> false_elim ()

let pres_cbeta (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#c: constr) (#v: exp)
  (#t #r: typ) (h: typing sg ln g d (ECApp (ECLam c v)) t r)
  : Pure (typing sg ln g d v t r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_CApp #_ #_ #_ #_ #e1 #c0 #t0 #rr h1 _ ->
    let h1 = retm h1 (ECLam c v) in
    let ci = inv_clam h1 c0 t0 in
    entails_constr_eq (hyps g) c c0;
    let hc = typing_cut ci.clam_body in
    let hv = vt hc d r in
    conv hv t r
  | _ -> false_elim ()

let pres_openeff_app (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r': typ) (#v #w: exp)
  (#t #r: typ) (h: typing sg ln g d (EApp (EOpenEff r' v) w) t r)
  : Pure (typing sg ln g d (EOpenEffC r' (EApp v w)) t r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v /\ V.is_value sg w)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_App #_ #_ #_ #_ #e1 #e2 #ta #tb #rr h1 h2 ->
    let h1 = retm h1 (EOpenEff r' v) in
    let oi = inv_openeff_h h1 prim_function ta rr tb in
    reg oi.oe_h;
    reg_fun sg g oi.oe_arg oi.oe_row oi.oe_res;
    let hv = vt oi.oe_h [] oi.oe_row in
    let hw = conv (vt (retm h2 w) [] oi.oe_row) oi.oe_arg oi.oe_row in
    let happ : typing sg ln g [] (EApp v w) oi.oe_res oi.oe_row = T_App hv hw in
    let hc : typing sg ln g d (EOpenEffC r' (EApp v w)) oi.oe_res (TRowUnion oi.oe_row r') =
      T_OpenEffC happ () in
    conv hc t r
  | _ -> false_elim ()

let pres_openeffc (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r': typ) (#v: exp)
  (#t #r: typ) (h: typing sg ln g d (EOpenEffC r' v) t r)
  : Pure (typing sg ln g d v t r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_OpenEffC h1 _ ->
    let hv = vt (retm h1 v) d r in
    conv hv t r
  | _ -> false_elim ()

let pres_let (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#t1: typ) (#v #body: exp)
  (#t #r: typ) (h: typing sg ln g d (ELet t1 v body) t r)
  : Pure (typing sg ln g d (subst1_tm v body) t r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Let _ h1 h2 ->
    let hb = typing_let_value_h h2 h1 in
    conv hb t r
  | _ -> false_elim ()

(* * Records *)

(* The split of `check_split_ty_other`, read at the record types of the
   operand and of its rest. *)
let miss_split (sg: sig) (g: ctx) (k k': key) (t0 t1 r0 r1: typ)
  : Lemma (requires sok sg /\ not (inconsistent (hyps g)) /\ k <> k' /\
                    ty_eq (TRowExt (EntTy k t0) r0) (TRowExt (EntTy k' t1) r1) /\
                    check sg g (t_record r1) KType /\
                    check sg g (t_record (TRowExt (EntTy k t0) r0)) KType /\
                    entails (hyps g) (CLacks k' r1))
          (ensures (let rd = row_drop k r1 in
                    ty_eq (t_record r1) (t_record (TRowExt (EntTy k t0) rd)) /\
                    ty_eq r1 (TRowExt (EntTy k t0) rd) /\
                    check sg g (t_record (TRowExt (EntTy k t0) rd)) KType /\
                    check sg g rd (KRow EType) /\
                    entails (hyps g) (CLacks k rd) /\ entails (hyps g) (CLacks k' rd) /\
                    entails (hyps g) (CLacks k r0) /\ check sg g t0 KType)) =
  let rd = row_drop k r1 in
  reg_record sg g r1;
  reg_record sg g (TRowExt (EntTy k t0) r0);
  check_split_ty_other sg g k k' t0 t1 r0 r1;
  reg_record sg g (TRowExt (EntTy k t0) rd);
  ty_eq_record r1 (TRowExt (EntTy k t0) rd)

let pres_select_hit (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: key) (#v1 #v2: exp)
  (#t #r: typ) (h: typing sg ln g d (ESelect k (EExtend k v1 v2)) t r)
  : Pure (typing sg ln g d v1 t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   V.is_value sg v1 /\ V.is_value sg v2)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Select #_ #_ #_ #_ #_ #e1 #t0 #r0 #rr h1 _ ->
    let rx = TRowExt (EntTy k t0) r0 in
    let h1 : typing sg ln g [] (EExtend k v1 v2) (t_record rx) rr = retm h1 (EExtend k v1 v2) in
    let ei = inv_extend_h h1 rx in
    reg h1;
    reg_record sg g rx;
    KF.check_ext_ty sg g k t0 r0;
    ext_ty_cancel_entails (hyps g) k t0 ei.ext_ty r0 ei.ext_rest;
    let hv = vt ei.ext_head d r in
    conv hv t r
  | _ -> false_elim ()

let pres_select_miss (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k #k': key) (#v1 #v2: exp)
  (#t #r: typ) (h: typing sg ln g d (ESelect k (EExtend k' v1 v2)) t r)
  : Pure (typing sg ln g d (ESelect k v2) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\ k <> k')
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Select #_ #_ #_ #_ #_ #e1 #t0 #r0 #rr h1 sqk ->
    let rx = TRowExt (EntTy k t0) r0 in
    let h1 : typing sg ln g [] (EExtend k' v1 v2) (t_record rx) rr = retm h1 (EExtend k' v1 v2) in
    let ei = inv_extend_h h1 rx in
    reg h1;
    reg ei.ext_tail;
    miss_split sg g k k' t0 ei.ext_ty r0 ei.ext_rest;
    let rd = row_drop k ei.ext_rest in
    let h2 = conv ei.ext_tail (t_record (TRowExt (EntTy k t0) rd)) rr in
    let hs : typing sg ln g d (ESelect k v2) t0 rr = T_Select h2 sqk in
    conv hs t r
  | _ -> false_elim ()

let pres_restrict_hit (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: key) (#v1 #v2: exp)
  (#t #r: typ) (h: typing sg ln g d (ERestrict k (EExtend k v1 v2)) t r)
  : Pure (typing sg ln g d v2 t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   V.is_value sg v1 /\ V.is_value sg v2)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Restrict #_ #_ #_ #_ #_ #e1 #t0 #r0 #rr h1 _ ->
    let rx = TRowExt (EntTy k t0) r0 in
    let h1 : typing sg ln g [] (EExtend k v1 v2) (t_record rx) rr = retm h1 (EExtend k v1 v2) in
    let ei = inv_extend_h h1 rx in
    reg h1;
    reg_record sg g rx;
    KF.check_ext_ty sg g k t0 r0;
    ext_ty_cancel_entails (hyps g) k t0 ei.ext_ty r0 ei.ext_rest;
    ty_eq_record ei.ext_rest r0;
    let hv = vt ei.ext_tail d r in
    conv hv t r
  | _ -> false_elim ()

let pres_restrict_miss (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k #k': key)
  (#v1 #v2: exp) (#t #r: typ) (h: typing sg ln g d (ERestrict k (EExtend k' v1 v2)) t r)
  : Pure (typing sg ln g d (EExtend k' v1 (ERestrict k v2)) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\ k <> k')
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Restrict #_ #_ #_ #_ #_ #e1 #t0 #r0 #rr h1 sqk ->
    let rx = TRowExt (EntTy k t0) r0 in
    let h1 : typing sg ln g [] (EExtend k' v1 v2) (t_record rx) rr = retm h1 (EExtend k' v1 v2) in
    let ei = inv_extend_h h1 rx in
    reg h1;
    reg ei.ext_tail;
    miss_split sg g k k' t0 ei.ext_ty r0 ei.ext_rest;
    let rd = row_drop k ei.ext_rest in
    let h2 = conv ei.ext_tail (t_record (TRowExt (EntTy k t0) rd)) rr in
    let hres : typing sg ln g [] (ERestrict k v2) (t_record rd) rr = T_Restrict h2 sqk in
    let hext : typing sg ln g d (EExtend k' v1 (ERestrict k v2))
                 (t_record (TRowExt (EntTy k' ei.ext_ty) rd)) rr =
      T_Extend ei.ext_head hres () in
    ext_ty_cancel_swap (hyps g) k k' t0 ei.ext_ty r0 ei.ext_rest rd;
    ty_eq_record (TRowExt (EntTy k' ei.ext_ty) rd) r0;
    conv hext t r
  | _ -> false_elim ()

let pres_update_hit (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: key) (#v1 #v2 #v3: exp)
  (#t #r: typ) (h: typing sg ln g d (EUpdate k (EExtend k v1 v2) v3) t r)
  : Pure (typing sg ln g d (EExtend k v3 v2) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)))
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Update #_ #_ #_ #_ #_ #e1 #e2 #t0 #t' #r0 #rr h1 h3 _ ->
    let rx = TRowExt (EntTy k t0) r0 in
    let h1 : typing sg ln g [] (EExtend k v1 v2) (t_record rx) rr = retm h1 (EExtend k v1 v2) in
    let ei = inv_extend_h h1 rx in
    reg h1;
    reg_record sg g rx;
    KF.check_ext_ty sg g k t0 r0;
    ext_ty_cancel_entails (hyps g) k t0 ei.ext_ty r0 ei.ext_rest;
    let h3 : typing sg ln g [] v3 t' rr = retm h3 v3 in
    let hext : typing sg ln g d (EExtend k v3 v2) (t_record (TRowExt (EntTy k t') ei.ext_rest)) rr =
      T_Extend h3 ei.ext_tail () in
    ty_eq_ext_cong (EntTy k t') (EntTy k t') ei.ext_rest r0;
    ty_eq_record (TRowExt (EntTy k t') ei.ext_rest) (TRowExt (EntTy k t') r0);
    conv hext t r
  | _ -> false_elim ()

let pres_update_miss (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k #k': key)
  (#v1 #v2 #v3: exp) (#t #r: typ) (h: typing sg ln g d (EUpdate k (EExtend k' v1 v2) v3) t r)
  : Pure (typing sg ln g d (EExtend k' v1 (EUpdate k v2 v3)) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\ k <> k')
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Update #_ #_ #_ #_ #_ #e1 #e2 #t0 #t' #r0 #rr h1 h3 sqk ->
    let rx = TRowExt (EntTy k t0) r0 in
    let h1 : typing sg ln g [] (EExtend k' v1 v2) (t_record rx) rr = retm h1 (EExtend k' v1 v2) in
    let ei = inv_extend_h h1 rx in
    reg h1;
    reg ei.ext_tail;
    miss_split sg g k k' t0 ei.ext_ty r0 ei.ext_rest;
    let rd = row_drop k ei.ext_rest in
    let h2 = conv ei.ext_tail (t_record (TRowExt (EntTy k t0) rd)) rr in
    let h3 : typing sg ln g [] v3 t' rr = retm h3 v3 in
    let hupd : typing sg ln g [] (EUpdate k v2 v3) (t_record (TRowExt (EntTy k t') rd)) rr =
      T_Update h2 h3 sqk in
    entails_lacks_ext (hyps g) k' (EntTy k t') rd;
    let hext : typing sg ln g d (EExtend k' v1 (EUpdate k v2 v3))
                 (t_record (TRowExt (EntTy k' ei.ext_ty) (TRowExt (EntTy k t') rd))) rr =
      T_Extend ei.ext_head hupd () in
    ext_ty_cancel_swap (hyps g) k k' t0 ei.ext_ty r0 ei.ext_rest rd;
    ty_eq_ext_cong (EntTy k t') (EntTy k t') r0 (TRowExt (EntTy k' ei.ext_ty) rd);
    ext_comm (EntTy k t') (EntTy k' ei.ext_ty) rd;
    ty_eq_record (TRowExt (EntTy k' ei.ext_ty) (TRowExt (EntTy k t') rd))
                 (TRowExt (EntTy k t') r0);
    conv hext t r
  | _ -> false_elim ()

let pres_merge_empty (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp)
  (#t #r: typ) (h: typing sg ln g d (EMerge ERecEmpty v) t r)
  : Pure (typing sg ln g d v t r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Merge #_ #_ #_ #_ #e1 #e2 #r1 #r2 #rr h1 h2 _ ->
    inv_rec_empty (retm h1 ERecEmpty) r1;
    ty_eq_union_cong r1 TRowEmpty r2 r2;
    union_empty_l r2;
    ty_eq_record r2 (TRowUnion r1 r2);
    let hv = vt (retm h2 v) d r in
    conv hv t r
  | _ -> false_elim ()

let pres_merge_extend (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#k: key) (#v1 #v2 #v3: exp)
  (#t #r: typ) (h: typing sg ln g d (EMerge (EExtend k v1 v2) v3) t r)
  : Pure (typing sg ln g d (EExtend k v1 (EMerge v2 v3)) t r)
         (requires sok sg /\ wf_ctx sg g)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Merge #_ #_ #_ #_ #e1 #e2 #r1 #r3 #rr h1 h3 _ ->
    let h1 : typing sg ln g [] (EExtend k v1 v2) (t_record r1) rr = retm h1 (EExtend k v1 v2) in
    let ei = inv_extend_h h1 r1 in
    let rx = TRowExt (EntTy k ei.ext_ty) ei.ext_rest in
    entails_constr_eq (hyps g) (CDisj r1 r3) (CDisj rx r3);
    entails_disj_ext (hyps g) (EntTy k ei.ext_ty) ei.ext_rest r3;
    let h3 : typing sg ln g [] v3 (t_record r3) rr = retm h3 v3 in
    let hm : typing sg ln g [] (EMerge v2 v3) (t_record (TRowUnion ei.ext_rest r3)) rr =
      T_Merge ei.ext_tail h3 () in
    entails_lacks_union (hyps g) k ei.ext_rest r3;
    let hext : typing sg ln g d (EExtend k v1 (EMerge v2 v3))
                 (t_record (TRowExt (EntTy k ei.ext_ty) (TRowUnion ei.ext_rest r3))) rr =
      T_Extend ei.ext_head hm () in
    union_ext_l (EntTy k ei.ext_ty) ei.ext_rest r3;
    ty_eq_union_cong r1 rx r3 r3;
    ty_eq_record (TRowExt (EntTy k ei.ext_ty) (TRowUnion ei.ext_rest r3)) (TRowUnion r1 r3);
    conv hext t r
  | _ -> false_elim ()

(* * Globals *)

let pres_unfold (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#q: qname) (#ks: list kind) (#t #r: typ) (vi: value_info) (v: exp)
  (h: typing sg ln (closed_ctx rs) d (EGlobal q ks) t r)
  : Ghost (typing sg ln (closed_ctx rs) d (kinst_exp ks v) t r)
          (requires sok sg /\ wf_ctx sg (closed_ctx rs) /\ genv_ok sg ln rs gi /\
                    value_scheme sg q == Some vi /\ gi.gvals q == Some v)
          (ensures fun _ -> True) =
  let g = closed_ctx rs in
  reg h;
  inv_global h vi;
  genv_ok_gval sg ln rs gi q vi v;
  let hv = ID.indefinite_description_ghost
             (typing sg ln (decl_rctx vi.vl_nk rs) [] v vi.vl_ty TRowEmpty) (fun _ -> True) in
  layouts_ext_refl g;
  let hu = typing_global_unfold_h hv ks g d r in
  conv hu t r

let pres_foreign (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#e: exp) (#t #r: typ) (q: qname) (ks: list kind) (args: list spine_arg)
  (fe: foreign_entry) (v: exp)
  (h: typing sg ln (closed_ctx rs) d e t r)
  : Ghost (typing sg ln (closed_ctx rs) d v t r)
          (requires sok sg /\ wf_ctx sg (closed_ctx rs) /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\
                    genv_ok sg ln rs gi /\
                    V.foreign_redex sg e /\ decompose_global_app e == Some (q, ks, args) /\
                    gi.gforeign q == Some fe /\ fe.fe_pre (L.map erase (value_args args)) /\
                    fe.fe_adapt (chain_instance e) (value_args args) == Some (FOVal v))
          (ensures fun _ -> True) =
  reg h;
  match chain_cursor sg e with
  | Some (s, th) ->
    foreign_redex_typed_h h s th;
    genv_ok_foreign sg ln rs gi e;
    assert (outcome_ok sg gi ln rs q (value_args args) (sub_ty th s) (FOVal v));
    let hv = ID.indefinite_description_ghost
               (typing sg ln (closed_ctx rs) [] v (sub_ty th s) TRowEmpty) (fun _ -> True) in
    let hv = vt hv d r in
    conv hv t r
  | None -> false_elim ()

(* * Pattern matching *)

let pres_case (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#vs: list exp) (#dt: dtree)
  (#t #r: typ) (h: typing sg ln g d (ECase vs dt) t r)
  : Pure (typing sg ln g d (EMatch vs dt) t r)
         (requires sok sg /\ wf_ctx sg g /\ L.for_all (V.is_value sg) vs)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Case #_ #_ #_ #_ #es #dt1 #ts hes hdt ->
    let hm = match_typing_scrut hes in
    let hc = T_Match (scrut_occs 0 ts) hes () hm hdt in
    conv hc t r
  | _ -> false_elim ()

let pres_leaf (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#th: list exp) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d (EMatch th (DLeaf e)) t r)
  : Pure (typing sg ln g d e t r) (requires sok sg /\ wf_ctx sg g) (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match om hes _ hm hdt ->
    (match hdt with
     | TD_Leaf h1 -> conv h1 t r
     | _ -> false_elim ())
  | _ -> false_elim ()

let pres_bind (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#th: list exp) (#o: occ)
  (#dt: dtree) (#v: exp) (#t #r: typ) (h: typing sg ln g d (EMatch th (DBind o dt)) t r)
  : Pure (typing sg ln g d (EMatch th (sub_tm_dt (scons v evar) dt)) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   proj sg th o == Some v)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match om hes sqv hm hdt ->
    (match hdt with
     | TD_Bind ho hdt1 ->
       let (| v', hv |) = occ_sound_h hm ho in
       match_typing_regular_h hm;
       let hdt2 = dt_typing_bind_value_h hdt1 hv in
       let hc = T_Match om hes sqv hm hdt2 in
       conv hc t r
     | _ -> false_elim ())
  | _ -> false_elim ()

let pres_guard (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#th: list exp) (#b: bool)
  (#dt1 #dt2: dtree) (#t #r: typ)
  (h: typing sg ln g d (EMatch th (DGuard (bool_lit b) dt1 dt2)) t r)
  : Pure (typing sg ln g d (EMatch th (if b then dt1 else dt2)) t r)
         (requires sok sg /\ wf_ctx sg g)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match om hes sqv hm hdt ->
    (match hdt with
     | TD_Guard _ hdt1 hdt2 ->
       if b then conv (T_Match om hes sqv hm hdt1) t r
       else conv (T_Match om hes sqv hm hdt2) t r
     | _ -> false_elim ())
  | _ -> false_elim ()

(* The branch of a `switchCtor` at the constructor of `θ(o)`. *)
let switch_ctor_core (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#ts: list typ) (#om: octx) (#o: occ) (#t_o: typ) (#ks: list kind) (#ss: list typ)
  (#cs: list qname) (#bs: list (qname & dtree)) (#t: typ)
  (hes: exps_typing sg ln g [] r th ts) (hm: match_typing sg ln g [] r th om)
  (ho: occ_typing sg g om o t_o) (tq: qname)
  (hb: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (v: exp) (dt: dtree)
  : Pure (typing sg ln g d (EMatch th dt) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   L.for_all (V.is_value sg) th /\
                   ty_eq t_o (tapps (TCon tq ks) ss) /\ check sg g (tapps (TCon tq ks) ss) KType /\
                   has_class sg tq (TcData cs) /\
                   proj sg th o == Some v /\ branch (ctor_head sg v) bs == Some dt)
         (ensures fun _ -> True) =
  let (| v', hv |) = occ_sound_h hm ho in
  match decompose_global_app v with
  | Some (c, ks', args) ->
    let (| fs, hdt |) = ctor_brs_select hb c dt in
    let hf = ctor_value_fields_typing_h hv c ks' args tq ks ss cs fs in
    let mf : match_typing sg ln g [] r th (field_occs o c 0 fs) =
      match_typing_fields #sg #ln #g #[] #r #th o v c ks' args hf in
    let ma = match_typing_append mf hm in
    T_Match (L.append (field_occs o c 0 fs) om) hes () ma hdt
  | None -> false_elim ()

let pres_switch_ctor (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#th: list exp) (#o: occ)
  (#bs: list (qname & dtree)) (#df: option dtree) (#v: exp) (#dt: dtree) (#t #r: typ)
  (h: typing sg ln g d (EMatch th (DSwitchCtor o bs df)) t r)
  : Pure (typing sg ln g d (EMatch th dt) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   proj sg th o == Some v /\ branch (ctor_head sg v) bs == Some dt)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match om hes sqv hm hdt ->
    (match hdt with
     | TD_SwitchCtor tq ks ss cs ho sq1 sq2 sq3 hb ->
       conv (switch_ctor_core hes hm ho tq hb v dt) t r
     | TD_SwitchCtorDef tq ks ss cs ho sq1 sq2 sq3 hb _ ->
       conv (switch_ctor_core hes hm ho tq hb v dt) t r
     | _ -> false_elim ())
  | _ -> false_elim ()

let pres_switch_ctor_def (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#th: list exp) (#o: occ)
  (#bs: list (qname & dtree)) (#dt0: dtree) (#t #r: typ)
  (h: typing sg ln g d (EMatch th (DSwitchCtor o bs (Some dt0))) t r)
  : Pure (typing sg ln g d (EMatch th dt0) t r) (requires sok sg /\ wf_ctx sg g)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match om hes sqv hm hdt ->
    (match hdt with
     | TD_SwitchCtorDef _ _ _ _ _ _ _ _ _ hdf -> conv (T_Match om hes sqv hm hdf) t r
     | _ -> false_elim ())
  | _ -> false_elim ()

let pres_switch_lit (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#th: list exp) (#o: occ)
  (#bs: list (lit & dtree)) (#dt0: dtree) (#v: exp) (#dt: dtree) (#t #r: typ)
  (h: typing sg ln g d (EMatch th (DSwitchLit o bs dt0)) t r)
  : Pure (typing sg ln g d (EMatch th dt) t r)
         (requires sok sg /\ wf_ctx sg g /\ branch (lit_of v) bs == Some dt)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match om hes sqv hm hdt ->
    (match hdt with
     | TD_SwitchLit _ _ _ _ hb _ ->
       (match lit_of v with
        | Some c -> conv (T_Match om hes sqv hm (lit_brs_select hb c dt)) t r
        | None -> false_elim ())
     | _ -> false_elim ())
  | _ -> false_elim ()

let pres_switch_lit_def (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#th: list exp) (#o: occ)
  (#bs: list (lit & dtree)) (#dt0: dtree) (#t #r: typ)
  (h: typing sg ln g d (EMatch th (DSwitchLit o bs dt0)) t r)
  : Pure (typing sg ln g d (EMatch th dt0) t r) (requires sok sg /\ wf_ctx sg g)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match om hes sqv hm hdt ->
    (match hdt with
     | TD_SwitchLit _ _ _ _ _ hdf -> conv (T_Match om hes sqv hm hdf) t r
     | _ -> false_elim ())
  | _ -> false_elim ()

(* The branch of a `switchKey` at the key of `θ(o)`. *)
let switch_key_core (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#ts: list typ) (#om: octx) (#o: occ) (#t_o: typ) (#kts: list (key & typ))
  (#bs: list (key & dtree)) (#t: typ)
  (hes: exps_typing sg ln g [] r th ts) (hm: match_typing sg ln g [] r th om)
  (ho: occ_typing sg g om o t_o) (vr vr': typ)
  (hb: key_brs_typing sg ln g d om o kts bs t r) (v: exp) (dt: dtree)
  : Pure (typing sg ln g d (EMatch th dt) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   L.for_all (V.is_value sg) th /\
                   ty_eq t_o (t_variant vr) /\ check sg g vr (KRow EType) /\
                   key_split vr kts vr' /\
                   proj sg th o == Some v /\ branch (carrier_key v) bs == Some dt)
         (ensures fun _ -> True) =
  let (| v', hv |) = occ_sound_h hm ho in
  match variant_view v with
  | Some (k, w) ->
    let (| pt, hdt |) = key_brs_select hb k dt in
    let hw = variant_payload_typing_h hv vr kts vr' k w pt in
    let ma = match_typing_variant hm o v k hw in
    T_Match ((OVariant o k, pt) :: om) hes () ma hdt
  | None -> false_elim ()

let pres_switch_key (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#th: list exp) (#o: occ)
  (#bs: list (key & dtree)) (#df: option dtree) (#v: exp) (#dt: dtree) (#t #r: typ)
  (h: typing sg ln g d (EMatch th (DSwitchKey o bs df)) t r)
  : Pure (typing sg ln g d (EMatch th dt) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   proj sg th o == Some v /\ branch (carrier_key v) bs == Some dt)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match om hes sqv hm hdt ->
    (match hdt with
     | TD_SwitchKey vr kts ho sq1 sq2 sq3 hb ->
       conv (switch_key_core hes hm ho vr TRowEmpty hb v dt) t r
     | TD_SwitchKeyDef vr vr' kts ho sq1 sq2 sq3 hb _ ->
       conv (switch_key_core hes hm ho vr vr' hb v dt) t r
     | _ -> false_elim ())
  | _ -> false_elim ()

let pres_switch_key_def (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#th: list exp) (#o: occ)
  (#bs: list (key & dtree)) (#dt0: dtree) (#v: exp) (#t #r: typ)
  (h: typing sg ln g d (EMatch th (DSwitchKey o bs (Some dt0))) t r)
  : Pure (typing sg ln g d (EMatch th dt0) t r)
         (requires sok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\
                   proj sg th o == Some v /\ branch (carrier_key v) bs == None)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Match #_ #_ #_ #_ #_ #_ #_ #_ #rr om hes sqv hm hdt ->
    (match hdt with
     | TD_SwitchKeyDef vr vr' kts ho _ _ _ hb hdf ->
       let (| v', hv |) = occ_sound_h hm ho in
       let hv' = key_default_typing_h hv hb vr vr' in
       let ma : match_typing sg ln g [] rr th ((o, t_variant vr') :: om) = TM_Cons () hv' hm in
       conv (T_Match ((o, t_variant vr') :: om) hes sqv ma hdf) t r
     | _ -> false_elim ())
  | _ -> false_elim ()

(* * Join points *)

let pres_join (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#ts: list typ) (#t1: typ)
  (#e1: exp) (#fs: list frame) (#n: nat) (#vs: list exp) (#t #r: typ)
  (h: typing sg ln g d (ELetJoin ts t1 e1 (plug fs (EJump n vs))) t r)
  : Pure (typing sg ln g d
            (ELetJoin ts t1 e1 (plug fs (sub_tm (list_esub (L.rev vs)) (ren_jp (shift n) e1))))
            t r)
         (requires sok sg /\ wf_ctx sg g /\ tl_frames fs /\ n == L.length fs /\
                   L.for_all (V.is_value sg) vs)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_LetJoin #_ #_ #_ #_ #_ #_ #_ #_ #rr sq hdef hk ->
    let d' = (ts, t1, rr) :: d in
    let hk : typing sg ln g d' (plug fs (EJump n vs)) t1 rr = retm hk (plug fs (EJump n vs)) in
    let hdef : typing sg ln (push_vars g ts) d' e1 t1 rr = hdef in
    let ti = tl_typing_h hk in
    let ji = inv_jump ti.tl_hole in
    nth_append ti.pre d' n;
    let ja : exps_typing sg ln g [] rr vs ts = ji.j_args in
    let hw = typing_weaken_jps hdef ti.pre in
    let hs = typing_subst_values_h hw ja in
    reg ti.tl_hole;
    let hs = conv hs ti.tl_t ti.tl_r in
    let e2 = sub_tm (list_esub (L.rev vs)) (ren_jp (shift n) e1) in
    let hk' = ti.tl_fill e2 hs in
    let hl : typing sg ln g d (ELetJoin ts t1 e1 (plug fs e2)) t1 rr = T_LetJoin sq hdef hk' in
    conv hl t r
  | _ -> false_elim ()

let pres_join_value (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#ts: list typ) (#t1: typ)
  (#e1 #v: exp) (#t #r: typ) (h: typing sg ln g d (ELetJoin ts t1 e1 v) t r)
  : Pure (typing sg ln g d v t r)
         (requires sok sg /\ wf_ctx sg g /\ V.is_value sg v)
         (ensures fun _ -> True) =
  reg h;
  let cf = strip_conv h in
  match cf.cf_h with
  | T_LetJoin _ _ hk ->
    let hv = vt (retm hk v) d r in
    conv hv t r
  | _ -> false_elim ()

(* * The head rules *)

let pres_head (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout)) (#d: jctx)
  (#e #e': exp) (#t #r: typ)
  (h: typing sg ln (closed_ctx rs) d e t r) (ph: pure_head sg gi e (CTerm e'))
  : Ghost (typing sg ln (closed_ctx rs) d e' t r)
          (requires sok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi)
          (ensures fun _ -> True) =
  let g = closed_ctx rs in
  rctx_ok_wf_ctx sg rs;
  closed_ctx_consistent rs;
  match ph with
  | PH_Beta #_ #_ #t1 #r1 #body #v _ ->
    pres_beta #sg #ln #g #d #t1 #r1 #body #v (retm h (EApp (ELam t1 r1 body) v))
  | PH_TyBeta #_ #_ #k #v #s _ ->
    pres_tybeta #sg #ln #g #d #k #v #s (retm h (ETyApp (ETyLam k v) s))
  | PH_CBeta #_ #_ #c #v _ ->
    pres_cbeta #sg #ln #g #d #c #v (retm h (ECApp (ECLam c v)))
  | PH_OpenEffApp #_ #_ #r' #v #w _ ->
    pres_openeff_app #sg #ln #g #d #r' #v #w (retm h (EApp (EOpenEff r' v) w))
  | PH_OpenEffC #_ #_ #r' #v _ ->
    pres_openeffc #sg #ln #g #d #r' #v (retm h (EOpenEffC r' v))
  | PH_Let #_ #_ #t1 #v #body _ ->
    pres_let #sg #ln #g #d #t1 #v #body (retm h (ELet t1 v body))
  | PH_SelectHit #_ #_ #k #v1 #v2 _ ->
    pres_select_hit #sg #ln #g #d #k #v1 #v2 (retm h (ESelect k (EExtend k v1 v2)))
  | PH_SelectMiss #_ #_ #k #k' #v1 #v2 _ _ ->
    pres_select_miss #sg #ln #g #d #k #k' #v1 #v2 (retm h (ESelect k (EExtend k' v1 v2)))
  | PH_RestrictHit #_ #_ #k #v1 #v2 _ ->
    pres_restrict_hit #sg #ln #g #d #k #v1 #v2 (retm h (ERestrict k (EExtend k v1 v2)))
  | PH_RestrictMiss #_ #_ #k #k' #v1 #v2 _ _ ->
    pres_restrict_miss #sg #ln #g #d #k #k' #v1 #v2 (retm h (ERestrict k (EExtend k' v1 v2)))
  | PH_UpdateHit #_ #_ #k #v1 #v2 #v3 _ ->
    pres_update_hit #sg #ln #g #d #k #v1 #v2 #v3 (retm h (EUpdate k (EExtend k v1 v2) v3))
  | PH_UpdateMiss #_ #_ #k #k' #v1 #v2 #v3 _ _ ->
    pres_update_miss #sg #ln #g #d #k #k' #v1 #v2 #v3
      (retm h (EUpdate k (EExtend k' v1 v2) v3))
  | PH_MergeEmpty #_ #_ #v _ ->
    pres_merge_empty #sg #ln #g #d #v (retm h (EMerge ERecEmpty v))
  | PH_MergeExtend #_ #_ #k #v1 #v2 #v3 _ ->
    pres_merge_extend #sg #ln #g #d #k #v1 #v2 #v3 (retm h (EMerge (EExtend k v1 v2) v3))
  | PH_Unfold #_ #_ #q #ks #vi #v _ _ ->
    pres_unfold #sg #gi #ln #rs #d #q #ks vi v (retm h (EGlobal q ks))
  | PH_Foreign #_ #_ #e0 #q #ks #args #fe #o _ _ _ _ ->
    pres_foreign #sg #gi #ln #rs #d #e #t #r q ks args fe e' h
  | PH_Case #_ #_ #vs #dt _ ->
    pres_case #sg #ln #g #d #vs #dt (retm h (ECase vs dt))
  | PH_Leaf #_ #_ #th #e1 ->
    pres_leaf #sg #ln #g #d #th #e1 (retm h (EMatch th (DLeaf e1)))
  | PH_Bind #_ #_ #th #o #dt #v _ ->
    pres_bind #sg #ln #g #d #th #o #dt #v (retm h (EMatch th (DBind o dt)))
  | PH_GuardTrue #_ #_ #th #dt1 #dt2 ->
    pres_guard #sg #ln #g #d #th #true #dt1 #dt2
      (retm h (EMatch th (DGuard (bool_lit true) dt1 dt2)))
  | PH_GuardFalse #_ #_ #th #dt1 #dt2 ->
    pres_guard #sg #ln #g #d #th #false #dt1 #dt2
      (retm h (EMatch th (DGuard (bool_lit false) dt1 dt2)))
  | PH_SwitchCtor #_ #_ #th #o #bs #df #v #dt _ ->
    pres_switch_ctor #sg #ln #g #d #th #o #bs #df #v #dt
      (retm h (EMatch th (DSwitchCtor o bs df)))
  | PH_SwitchCtorDef #_ #_ #th #o #bs #dt0 #v _ ->
    pres_switch_ctor_def #sg #ln #g #d #th #o #bs #dt0
      (retm h (EMatch th (DSwitchCtor o bs (Some dt0))))
  | PH_SwitchLit #_ #_ #th #o #bs #dt0 #v #dt _ ->
    pres_switch_lit #sg #ln #g #d #th #o #bs #dt0 #v #dt
      (retm h (EMatch th (DSwitchLit o bs dt0)))
  | PH_SwitchLitDef #_ #_ #th #o #bs #dt0 #v _ ->
    pres_switch_lit_def #sg #ln #g #d #th #o #bs #dt0
      (retm h (EMatch th (DSwitchLit o bs dt0)))
  | PH_SwitchKey #_ #_ #th #o #bs #df #v #dt _ ->
    pres_switch_key #sg #ln #g #d #th #o #bs #df #v #dt
      (retm h (EMatch th (DSwitchKey o bs df)))
  | PH_SwitchKeyDef #_ #_ #th #o #bs #dt0 #v _ ->
    pres_switch_key_def #sg #ln #g #d #th #o #bs #dt0 #v
      (retm h (EMatch th (DSwitchKey o bs (Some dt0))))
  | PH_Join #_ #_ #ts #t1 #e1 #fs #n #vs _ _ ->
    pres_join #sg #ln #g #d #ts #t1 #e1 #fs #n #vs
      (retm h (ELetJoin ts t1 e1 (plug fs (EJump n vs))))
  | PH_JoinValue #_ #_ #ts #t1 #e1 #v _ ->
    pres_join_value #sg #ln #g #d #ts #t1 #e1 #v (retm h (ELetJoin ts t1 e1 v))

(* * Steps *)

let rec pres_step (#sg: sig) (#gi: genv) (#ln: lctx) (#rs: list (atom & layout))
  (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#e': exp)
  (#d: jctx) (#t #r: typ)
  (h: typing sg ln (closed_ctx rs) d e t r)
  (s: step sg gi ra st e ra' st' (CTerm e'))
  : Ghost (typing sg ln (closed_ctx rs) d e' t r)
          (requires sok sg /\ rctx_ok sg rs /\ lctx_ok sg rs ln /\ genv_ok sg ln rs gi /\
                    stage5_frag e)
          (ensures fun _ -> True)
          (decreases s) =
  match s with
  | S_Pure #_ #_ #_ #_ #e0 #c ph ->
    pres_head #sg #gi #ln #rs #d #e #e' #t #r h ph
  | S_Eff eh -> stage5_no_eff eh; false_elim ()
  | S_Ctx #_ #_ #_ #_ #e1 #_ #_ #e1' f _ s1 ->
    rctx_ok_wf_ctx sg rs;
    stage5_frag_plug1 f e1;
    if V.is_value sg e1 then begin
      value_no_step s1;
      false_elim ()
    end else begin
      let pi = plug1_typing_h #sg #ln #(closed_ctx rs) #d #f #e1 #t #r (retm h (plug1 f e1)) in
      let h1 = pres_step pi.hole s1 in
      step_plug1_cursor_kept f s1;
      pi.fill e1' h1
    end

(* * The theorems *)

let preservation #sg #gi #ln #rs #ra #st #e #ra' #st' #e' #d #t #r h s =
  sok_intro sg;
  pres_step h s

let preservation_typed #sg #gi ln rs #ra #st #e #ra' #st' #e' t s =
  let h = ID.indefinite_description_ghost
            (typing sg ln (closed_ctx rs) [] e t TRowEmpty) (fun _ -> True) in
  let h' = preservation h s in
  FStar.Classical.exists_intro (fun (_: typing sg ln (closed_ctx rs) [] e' t TRowEmpty) -> True) h'
