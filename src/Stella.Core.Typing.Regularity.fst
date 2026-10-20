(* Proof structure.

   One mutual induction over `typing`, `exps_typing`, `cells_typing`,
   `match_typing` and `dt_typing`. The branch, clause and `letrec` member
   judgements are by induction on themselves: their empty case kinds what
   they are indexed by, and none needs the regularity of a subterm.

   A rule whose premises kind its type and row needs nothing; a premise in
   the closed context is read in `g` by `check_closed_ctx`. Elsewhere a
   rule's kinding is assembled from its subderivations by a lemma of its
   own below, stated over kinding alone. The chain judgement is by
   induction on itself: each node extends `spine_args_ok` by one argument
   (`spine_args_ok_snoc`), and `spine_cursor_regular` kinds the instance
   of the cursor. A subderivation under an extended
   context is used once the extension is shown well formed
   (`Stella.Core.Typing.Wf`); under a term binder its conclusion is read
   back in the outer context, which kinds the same (`same_kinding`). *)
module Stella.Core.Typing.Regularity
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Facts
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Spine.Wf
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Wf
module L = FStar.List.Tot

(* The rules, over kinding. *)

let reg_lam (sg: sig) (g: ctx) (t1 r' t2: typ)
  : Lemma (requires prim_wf sg /\ check sg g t1 KType /\ check sg g r' (KRow EEffect) /\
                    check sg (push_var g t1) t2 KType)
          (ensures check sg g (t_fun t1 r' t2) KType) =
  same_kinding_push_var g t1;
  check_same_kinding sg g (push_var g t1) t2 KType;
  check_t_fun sg g t1 r' t2

let reg_app (sg: sig) (g: ctx) (t1 r t2: typ)
  : Lemma (requires prim_wf sg /\ check sg g (t_fun t1 r t2) KType) (ensures check sg g t2 KType) =
  check_t_fun sg g t1 r t2

let reg_tyapp (sg: sig) (g: ctx) (k: kind) (s t: typ)
  : Lemma (requires check sg g (TForall k t) KType /\ check sg g s k)
          (ensures check sg g (subst1_ty s t) KType) =
  check_forall sg g k t;
  check_subst1 sg g k s t KType

let reg_capp (sg: sig) (g: ctx) (c: constr) (t: typ)
  : Lemma (requires check sg g (TConstr c t) KType /\ entails (hyps g) c) (ensures check sg g t KType) =
  check_constr sg g c t;
  add_assump_assumps g c;
  check_cut sg g [c] t KType

(* Back from under a term binder. *)
let reg_push_var (sg: sig) (g: ctx) (t1 t: typ) (k: kind)
  : Lemma (requires check sg (push_var g t1) t k) (ensures check sg g t k) =
  same_kinding_push_var g t1;
  check_same_kinding sg g (push_var g t1) t k

let reg_push_vars (sg: sig) (g: ctx) (ts: list typ) (t: typ) (k: kind)
  : Lemma (requires check sg (push_vars g ts) t k) (ensures check sg g t k) =
  same_kinding_push_vars g ts;
  check_same_kinding sg g (push_vars g ts) t k

let reg_extend (sg: sig) (g: ctx) (k: key) (t r0: typ)
  : Lemma (requires prim_wf sg /\ check sg g t KType /\ check sg g (t_record r0) KType /\
                    key_ok sg g k EType /\ entails (hyps g) (CLacks k r0))
          (ensures check sg g (t_record (TRowExt (EntTy k t) r0)) KType) =
  check_t_record sg g r0;
  check_t_record sg g (TRowExt (EntTy k t) r0);
  key_ok_struct sg g k;
  check_ext_ty sg g k t r0

let reg_select (sg: sig) (g: ctx) (k: key) (t r0: typ)
  : Lemma (requires prim_wf sg /\ check sg g (t_record (TRowExt (EntTy k t) r0)) KType)
          (ensures check sg g t KType /\ check sg g (t_record r0) KType /\ struct_key k /\
                   entails (hyps g) (CLacks k r0)) =
  check_t_record sg g (TRowExt (EntTy k t) r0);
  check_t_record sg g r0;
  check_ext_ty sg g k t r0

let reg_update (sg: sig) (g: ctx) (k: key) (t t' r0: typ)
  : Lemma (requires prim_wf sg /\ check sg g (t_record (TRowExt (EntTy k t) r0)) KType /\
                    check sg g t' KType)
          (ensures check sg g (t_record (TRowExt (EntTy k t') r0)) KType) =
  reg_select sg g k t r0;
  check_t_record sg g r0;
  check_t_record sg g (TRowExt (EntTy k t') r0);
  check_ext_ty sg g k t' r0

let reg_merge (sg: sig) (g: ctx) (r1 r2: typ)
  : Lemma (requires prim_wf sg /\ check sg g (t_record r1) KType /\ check sg g (t_record r2) KType /\
                    entails (hyps g) (CDisj r1 r2))
          (ensures check sg g (t_record (TRowUnion r1 r2)) KType) =
  check_t_record sg g r1;
  check_t_record sg g r2;
  check_t_record sg g (TRowUnion r1 r2);
  check_union sg g r1 r2 EType

let reg_inject (sg: sig) (g: ctx) (k: key) (t r0: typ)
  : Lemma (requires prim_wf sg /\ check sg g t KType /\ check sg g r0 (KRow EType) /\
                    key_ok sg g k EType /\ entails (hyps g) (CLacks k r0))
          (ensures check sg g (t_variant (TRowExt (EntTy k t) r0)) KType) =
  check_t_variant sg g (TRowExt (EntTy k t) r0);
  key_ok_struct sg g k;
  check_ext_ty sg g k t r0

let reg_weaken (sg: sig) (g: ctx) (k: key) (t r0: typ)
  : Lemma (requires prim_wf sg /\ check sg g t KType /\ check sg g (t_variant r0) KType /\
                    key_ok sg g k EType /\ entails (hyps g) (CLacks k r0))
          (ensures check sg g (t_variant (TRowExt (EntTy k t) r0)) KType) =
  check_t_variant sg g r0;
  reg_inject sg g k t r0

let reg_absurd (sg: sig) (g: ctx)
  : Lemma (requires prim_wf sg) (ensures check sg g (t_variant TRowEmpty) KType) =
  check_t_variant sg g TRowEmpty

let reg_openeff (sg: sig) (g: ctx) (t1 r1 t2 r': typ)
  : Lemma (requires prim_wf sg /\ check sg g (t_fun t1 r1 t2) KType /\
                    entails (hyps g) (CDisj r1 r') /\ check sg g r' (KRow EEffect))
          (ensures check sg g (t_fun t1 (TRowUnion r1 r') t2) KType) =
  check_t_fun sg g t1 r1 t2;
  check_union sg g r1 r' EEffect;
  check_t_fun sg g t1 (TRowUnion r1 r') t2

(* The instance of the remainder of a chain with well-formed arguments. *)
let reg_chain (sg: sig) (g: ctx) (e: exp) (t: typ) (th: tsub)
  : Lemma (requires sig_ok sg /\ chain_args_ok sg g e /\ chain_cursor sg e == Some (t, th))
          (ensures check sg g (sub_ty th t) KType) =
  let Some (q, ks, args) = decompose_global_app e in
  spine_cursor_regular sg g q ks args t th

let reg_readcell (sg: sig) (g: ctx) (a: atom) (k: key) (lay: layout) (t: typ)
  : Lemma (requires wf_ctx sg g /\ L.assoc a g.regions == Some lay /\ L.assoc k lay == Some t)
          (ensures check sg g t KType) =
  regions_ok_assoc sg g g.regions a lay;
  layout_ok_assoc sg g lay k t

(* The judgements that need no regularity of a subterm. *)

let rec binds_typing_regular' (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs)
  : Lemma (ensures tys_ok sg g (L.map fst bs)) (decreases h) =
  match h with
  | TB_Nil -> ()
  | TB_Cons _ _ h' -> binds_typing_regular' h'

let rec ctor_brs_typing_regular' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx)
  (#om: octx) (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname)
  (#bs: list (qname & dtree)) (#t #r: typ) (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r)
  : Lemma (ensures check sg g t KType /\ check sg g r (KRow EEffect)) (decreases h) =
  match h with
  | TCB_Nil _ -> ()
  | TCB_Cons _ _ h' -> ctor_brs_typing_regular' h'

let rec lit_brs_typing_regular' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx)
  (#om: octx) (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r)
  : Lemma (ensures check sg g t KType /\ check sg g r (KRow EEffect)) (decreases h) =
  match h with
  | TLB_Nil _ -> ()
  | TLB_Cons _ _ h' -> lit_brs_typing_regular' h'

let rec key_brs_typing_regular' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx)
  (#om: octx) (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r)
  : Lemma (ensures check sg g t KType /\ check sg g r (KRow EEffect)) (decreases h) =
  match h with
  | TKB_Nil _ -> ()
  | TKB_Cons _ _ h' -> key_brs_typing_regular' h'

(* One argument after a chain with well-formed arguments, well formed
   against its cursor. *)
let chain_args_ok_arg (sg: sig) (g: ctx) (e: exp) (a: spine_arg)
  : Lemma (requires chain_args_ok sg g e /\
                    (match chain_cursor sg e with
                     | Some (t, th) -> arg_ok sg g t th a
                     | None -> False))
          (ensures chain_args_ok sg g (apply_arg e a)) =
  let Some (q, ks, args) = decompose_global_app e in
  decompose_apply_arg e a;
  spine_args_ok_snoc sg g q ks args a

let rec chain_typing_args_ok' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e)
  : Lemma (ensures chain_args_ok sg g e /\ check sg g r (KRow EEffect)) (decreases h) =
  match h with
  | TS_Head _ _ _ -> ()
  | TS_Ty #_ #_ #_ #_ #_ #e0 #s h0 _ _ -> chain_typing_args_ok' h0; chain_args_ok_arg sg g e0 (STy s)
  | TS_Constr #_ #_ #_ #_ #_ #e0 h0 _ _ -> chain_typing_args_ok' h0; chain_args_ok_arg sg g e0 SConstr
  | TS_Val #_ #_ #_ #_ #_ #e0 #v h0 _ _ -> chain_typing_args_ok' h0; chain_args_ok_arg sg g e0 (SVal v)

(* Well-formed arguments are consumed by the cursor. *)
let rec cursor_args_ok_some (sg: sig) (g: ctx) (t: typ) (th: tsub) (args: list spine_arg)
  : Lemma (requires cursor_args_ok sg g t th args) (ensures Some? (cursor sg t th args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: args' ->
    let Some (t', th') = cursor_step sg t th a in
    cursor_args_ok_some sg g t' th' args'

let chain_args_ok_cursor (sg: sig) (g: ctx) (e: exp)
  : Lemma (requires chain_args_ok sg g e) (ensures Some? (chain_cursor sg e)) =
  let Some (q, ks, args) = decompose_global_app e in
  let Some (_, _, t) = global_scheme sg q in
  cursor_args_ok_some sg g (kinst_ty ks t) tvar args

(* The mutual induction. *)

let rec typing_regular' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g)
          (ensures check sg g t KType /\ check sg g r (KRow EEffect))
          (decreases h) =
  match h with
  | T_Var #_ #_ #_ #_ #i _ _ -> tys_ok_nth sg g g.vars i t
  | T_Global #_ #_ #_ #_ #q #ks #nk #t0 _ _ _ -> check_global_inst sg g q ks nk t0
  | T_Lit #_ #_ #_ #_ #c _ -> check_lit_type sg g c
  | T_Lam #_ #_ #_ #_ #t1 #r' #_ #t2 _ _ hb ->
    wf_ctx_push_var sg g t1;
    typing_regular' hb;
    reg_lam sg g t1 r' t2
  | T_App #_ #_ #_ #_ #_ #_ #t1 #_ h1 _ ->
    typing_regular' h1;
    reg_app sg g t1 r t
  | T_Chain #_ #_ #_ #_ #e0 #t0 #th hc _ ->
    chain_typing_args_ok' hc;
    reg_chain sg g e0 t0 th
  | T_TyLam #_ #_ #_ #_ #k #_ #t0 _ _ _ hb ->
    wf_ctx_push_tvar sg g k;
    typing_regular' hb;
    check_forall sg g k t0
  | T_TyApp #_ #_ #_ #_ #_ #s #k #t0 h1 _ ->
    typing_regular' h1;
    reg_tyapp sg g k s t0
  | T_CLam #_ #_ #_ #_ #c #_ #t0 _ _ _ hb ->
    wf_ctx_add_assump sg g c;
    typing_regular' hb;
    check_constr sg g c t0
  | T_CApp #_ #_ #_ #_ #_ #c h1 _ ->
    typing_regular' h1;
    reg_capp sg g c t
  | T_Let #_ #_ #_ #_ #t1 _ h1 h2 ->
    wf_ctx_push_var sg g t1;
    typing_regular' h1;
    typing_regular' h2;
    reg_push_var sg g t1 t KType
  | T_LetRec #_ #_ #_ #_ #bs _ hbs hb ->
    let ts = L.map fst bs in
    binds_typing_regular' hbs;
    same_kinding_push_vars g ts;
    same_kinding_ext g (push_vars g ts);
    tys_ok_weaken sg (push_vars g ts) g ts;
    wf_ctx_push_vars sg g ts;
    typing_regular' hb;
    reg_push_vars sg g ts t KType;
    reg_push_vars sg g ts r (KRow EEffect)
  | T_Conv _ _ _ -> ()
  | T_Case #_ #_ #_ #_ #_ #_ #ts hes hdt ->
    exps_typing_regular' hes;
    octx_ok_scrut_occs sg g 0 ts;
    dt_typing_regular' hdt
  | T_LetJoin _ _ h2 -> typing_regular' h2
  | T_Jump _ _ _ -> ()
  | T_RecEmpty _ -> check_t_record sg g TRowEmpty
  | T_Extend #_ #_ #_ #_ #k #_ #_ #t1 #r0 h1 h2 _ ->
    typing_regular' h1;
    typing_regular' h2;
    reg_extend sg g k t1 r0
  | T_Select #_ #_ #_ #_ #k #_ #_ #r0 h1 _ ->
    typing_regular' h1;
    reg_select sg g k t r0
  | T_Restrict #_ #_ #_ #_ #k #_ #t1 #r0 h1 _ ->
    typing_regular' h1;
    reg_select sg g k t1 r0
  | T_Update #_ #_ #_ #_ #k #_ #_ #t1 #t' #r0 h1 h2 _ ->
    typing_regular' h1;
    typing_regular' h2;
    reg_update sg g k t1 t' r0
  | T_Merge #_ #_ #_ #_ #_ #_ #r1 #r2 h1 h2 _ ->
    typing_regular' h1;
    typing_regular' h2;
    reg_merge sg g r1 r2
  | T_Inject #_ #_ #_ #_ #k #r0 #_ #t1 h1 _ _ ->
    typing_regular' h1;
    reg_inject sg g k t1 r0
  | T_Weaken #_ #_ #_ #_ #k #t1 #_ #r0 h1 _ _ ->
    typing_regular' h1;
    reg_weaken sg g k t1 r0
  | T_VariantValue _ _ _ _ h1 _ -> typing_regular' h1
  | T_Absurd h1 _ -> typing_regular' h1; reg_absurd sg g
  | T_Perform #_ #_ #_ #_ #_ #op #ss #_ #_ #q #ei #os ts _ _ _ h1 ->
    typing_regular' h1;
    check_op_inst sg g q ei op os ts ss
  | T_Handle _ _ _ _ _ _ _ -> ()
  | T_OpenEff #_ #_ #_ #_ #r' #_ #t1 #r1 #t2 h1 _ ->
    typing_regular' h1;
    reg_openeff sg g t1 r1 t2 r'
  | T_Region _ _ _ _ -> ()
  | T_ReadCell #_ #_ #_ #_ #a #k #lay _ _ _ -> reg_readcell sg g a k lay t
  | T_WriteCell _ _ h1 -> typing_regular' h1; check_t_unit sg g
  | T_Match om hes _ hm hdt ->
    exps_typing_regular' hes;
    match_typing_regular' hm;
    dt_typing_regular' hdt
  | T_OpenEffC #_ #_ #_ #_ #r' #_ #_ #r0 h1 _ ->
    typing_regular' h1;
    check_union sg g r0 r' EEffect
  | T_Force _ _ -> check_closed_ctx sg g t KType
  | T_Fill _ _ h1 -> typing_regular' h1
  | T_RegionOpen #_ #_ #_ #_ #_ #_ #_ #_ #b0 _ _ _ _ _ ->
    check_closed_ctx sg g b0 KType;
    check_closed_ctx sg g r (KRow EEffect)
  | T_Opaque _ _ -> ()

and exps_typing_regular' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g)
          (ensures tys_ok sg g ts /\ check sg g r (KRow EEffect))
          (decreases h) =
  match h with
  | TE_Nil _ -> ()
  | TE_Cons h1 h2 -> typing_regular' h1; exps_typing_regular' h2

and cells_typing_regular' (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp))
  (#lay: layout) (h: cells_typing sg ln g cells lay)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g) (ensures tys_ok sg g (L.map snd lay))
          (decreases h) =
  match h with
  | TC_Nil -> ()
  | TC_Cons _ h1 h2 -> typing_regular' h1; cells_typing_regular' h2

and match_typing_regular' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (h: match_typing sg ln g d r th om)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g)
          (ensures octx_ok sg g om /\ check sg g r (KRow EEffect))
          (decreases h) =
  match h with
  | TM_Nil _ -> ()
  | TM_Cons _ h1 h2 -> typing_regular' h1; match_typing_regular' h2

and dt_typing_regular' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g /\ octx_ok sg g om)
          (ensures check sg g t KType /\ check sg g r (KRow EEffect))
          (decreases h) =
  match h with
  | TD_Leaf h1 -> typing_regular' h1
  | TD_Bind #_ #_ #_ #_ #_ #_ #_ #t_o ho hdt ->
    occ_typing_regular ho;
    wf_ctx_push_var sg g t_o;
    ctx_ext_push_var g t_o;
    octx_ok_weaken sg g (push_var g t_o) om;
    dt_typing_regular' hdt;
    reg_push_var sg g t_o t KType;
    reg_push_var sg g t_o r (KRow EEffect)
  | TD_SwitchCtor _ _ _ _ _ _ _ _ hbr -> ctor_brs_typing_regular' hbr
  | TD_SwitchCtorDef _ _ _ _ _ _ _ _ hbr _ -> ctor_brs_typing_regular' hbr
  | TD_SwitchLit _ _ _ _ hbr _ -> lit_brs_typing_regular' hbr
  | TD_SwitchKey _ _ _ _ _ _ hbr -> key_brs_typing_regular' hbr
  | TD_SwitchKeyDef _ _ _ _ _ _ _ hbr _ -> key_brs_typing_regular' hbr
  | TD_Guard _ h2 _ -> dt_typing_regular' h2

let typing_regular #sg #ln #g #d #e #t #r h = typing_regular' h

let chain_typing_args_ok #sg #ln #g #d #r #e h = chain_typing_args_ok' h

let chain_typing_regular #sg #ln #g #d #r #e h =
  chain_typing_args_ok' h;
  chain_args_ok_cursor sg g e;
  match chain_cursor sg e with
  | Some (t, th) -> reg_chain sg g e t th
  | None -> ()

let exps_typing_regular #sg #ln #g #d #r #es #ts h = exps_typing_regular' h

let binds_typing_regular #sg #ln #g #bs h = binds_typing_regular' h

let cells_typing_regular #sg #ln #g #cells #lay h = cells_typing_regular' h

let match_typing_regular #sg #ln #g #d #r #th #om h = match_typing_regular' h

let dt_typing_regular #sg #ln #g #d #om #dt #t #r h = dt_typing_regular' h

let ctor_brs_typing_regular #sg #ln #g #d #om #o #ks #ss #cs #bs #t #r h =
  ctor_brs_typing_regular' h

let lit_brs_typing_regular #sg #ln #g #d #om #lt #bs #t #r h = lit_brs_typing_regular' h

let key_brs_typing_regular #sg #ln #g #d #om #o #kts #bs #t #r h = key_brs_typing_regular' h

let rec clauses_typing_regular #sg #ln #g #ei #ts #r #b #cs h =
  match h with
  | TCL_Nil _ -> ()
  | TCL_Full _ _ _ _ h' -> clauses_typing_regular h'
  | TCL_Fast _ _ _ h' -> clauses_typing_regular h'

let case_octx_ok #sg #ln #g #d #r #es #ts h =
  exps_typing_regular' h;
  octx_ok_scrut_occs sg g 0 ts
