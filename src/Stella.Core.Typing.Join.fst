(* Proof structure.

   One mutual induction over the judgements that carry `Δ`. A non-tail
   subterm, under `Δ = []`, is renamed from `[]` to `[]`, which `jren_ok`
   allows for every renaming. The boundaries, under `Δ = []` too, are fixed
   by the renaming: the scope of the whole term
   (`typing_scoped`) makes them `jp_scoped 0`, and `ren_jp_scoped` fixes a
   term scoped below `0`. A `letrec`'s members are read through the term
   `ELetRec bs ERecEmpty`, which has no other join index. A value is fixed
   by `typing_value_ren_jp`; its renamed derivation is cast back to it.

   Every context of the induction has the regions of the first one, so the
   induction carries `layouts_struct g.regions`, which `wf_ctx` implies, and
   reads the scope facts in that form from the implementation of
   `Stella.Core.Typing.Scope`. *)
module Stella.Core.Typing.Join
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Spine
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Scope
open Stella.Core.Typing.Keys
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

friend Stella.Core.Typing.Scope

let jren_ok_up xi d d' jt = ()

let jren_ok_shift d jt = ()

let rec nth_lt (#a: Type) (l: list a) (i: nat)
  : Lemma (requires Some? (L.nth l i)) (ensures i < L.length l) (decreases l) =
  match l with
  | _ :: l' -> if i = 0 then () else nth_lt l' (i - 1)

(* Values. *)

let rec args_value (sg: sig) (args: list spine_arg) (v: exp)
  : Lemma (requires V.args_values sg args /\ L.mem v (value_args args)) (ensures V.is_value sg v)
          (decreases args) =
  match args with
  | SVal w :: args' -> if v = w then () else args_value sg args' v
  | _ :: args' -> args_value sg args' v

let chain_value_args (sg: sig) (v0: exp)
  : Lemma (requires V.is_value sg v0 /\ Some? (decompose_global_app v0))
          (ensures V.args_values sg (Mktuple3?._3 (Some?.v (decompose_global_app v0)))) =
  V.chain_values_view sg v0;
  match v0 with
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ()

let rec record_field_value (sg: sig) (k: key) (v0 v: exp)
  : Lemma (requires V.is_value sg v0 /\ record_field k v0 == Some v) (ensures V.is_value sg v)
          (decreases v0) =
  match v0 with
  | EExtend k' _ v2 -> if k' = k then () else record_field_value sg k v2 v

let rec variant_payload_value (sg: sig) (k: key) (v0 v: exp)
  : Lemma (requires V.is_value sg v0 /\ variant_payload k v0 == Some v) (ensures V.is_value sg v)
          (decreases v0) =
  match v0 with
  | EInject _ _ _ -> ()
  | EWeaken _ _ v1 -> variant_payload_value sg k v1 v

let rec nth_value (sg: sig) (th: list exp) (i: nat) (v: exp)
  : Lemma (requires L.for_all (V.is_value sg) th /\ L.nth th i == Some v) (ensures V.is_value sg v)
          (decreases th) =
  match th with
  | _ :: th' -> if i = 0 then () else nth_value sg th' (i - 1) v

let rec nth_mem (#a: eqtype) (l: list a) (i: nat) (x: a)
  : Lemma (requires L.nth l i == Some x) (ensures L.mem x l) (decreases l) =
  match l with
  | _ :: l' -> if i = 0 then () else nth_mem l' (i - 1) x

let rec proj_value sg th o v =
  match o with
  | OScrut i -> nth_value sg th i v
  | OCtor o' q j ->
    let Some v0 = proj sg th o' in
    proj_value sg th o' v0;
    let Some (_, _, args) = decompose_global_app v0 in
    nth_mem (value_args args) j v;
    chain_value_args sg v0;
    args_value sg args v
  | ORecord o' k ->
    let Some v0 = proj sg th o' in
    proj_value sg th o' v0;
    record_field_value sg k v0 v
  | OVariant o' k ->
    let Some v0 = proj sg th o' in
    proj_value sg th o' v0;
    variant_payload_value sg k v0 v

let rec values_ren_jp (sg: sig) (n: nat) (xi: ren) (th: list exp)
  : Lemma (requires L.for_all (V.is_value sg) th /\ V.jp_scoped_exps n th)
          (ensures ren_jp_exps xi th == th) (decreases th) =
  match th with
  | [] -> ()
  | v :: th' -> V.value_ren_jp sg n xi v; values_ren_jp sg n xi th'

(* Casts along an equality of terms. *)

let cast (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (e': exp{e' == e}) : typing sg ln g d e' t r = h

let cast_exps (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#es: list exp)
  (#ts: list typ) (h: exps_typing sg ln g d r es ts) (es': list exp{es' == es})
  : exps_typing sg ln g d r es' ts = h

(* The members of a `letrec`, under no join point, are fixed. *)
let binds_fixed (n: nat) (xi: ren) (bs: list (typ & exp))
  : Lemma (requires V.jp_scoped_binds 0 bs) (ensures ren_jp_binds xi bs == bs) =
  V.ren_jp_scoped 0 xi (ELetRec bs ERecEmpty)

(* The mutual induction. *)

let rec typing_ren_jp' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (xi: ren) (d': jctx)
  : Pure (typing sg ln g d' (ren_jp xi e) t r)
         (requires layouts_struct g.regions /\ jren_ok xi d d')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | T_Var sq1 sq2 -> T_Var sq1 sq2
  | T_Global sq1 sq2 sq3 -> T_Global sq1 sq2 sq3
  | T_Lit #_ #_ #_ #_ #c sq -> T_Lit #sg #ln #g #d' #c #r sq
  | T_Lam #_ #_ #_ #_ #_ #_ #body sq1 sq2 hb ->
    typing_scoped' h;
    V.ren_jp_scoped 0 xi body;
    T_Lam sq1 sq2 hb
  | T_App h1 h2 -> T_App (typing_ren_jp' h1 xi []) (typing_ren_jp' h2 xi [])
  | T_Chain #_ #_ #_ #_ #_ #t0 #th hc _ ->
    chain_cursor_ren_jp sg xi e;
    T_Chain #sg #ln #g #d' #(ren_jp xi e) #t0 #th #r (chain_typing_ren_jp' hc xi []) ()
  | T_TyLam #_ #_ #_ #_ #_ #body sq1 sq2 sq3 hb ->
    typing_scoped' h;
    V.ren_jp_scoped 0 xi body;
    T_TyLam sq1 sq2 sq3 hb
  | T_TyApp h1 sq -> T_TyApp (typing_ren_jp' h1 xi []) sq
  | T_CLam #_ #_ #_ #_ #_ #body sq1 sq2 sq3 hb ->
    typing_scoped' h;
    V.ren_jp_scoped 0 xi body;
    T_CLam sq1 sq2 sq3 hb
  | T_CApp h1 sq -> T_CApp (typing_ren_jp' h1 xi []) sq
  | T_Let sq h1 h2 -> T_Let sq (typing_ren_jp' h1 xi []) (typing_ren_jp' h2 xi d')
  | T_LetRec #_ #_ #_ #_ #bs sq hbs hb ->
    typing_scoped' h;
    binds_fixed 0 xi bs;
    push_vars_regions g (L.map fst bs);
    T_LetRec sq hbs (typing_ren_jp' hb xi d')
  | T_Conv h1 sq1 sq2 -> T_Conv (typing_ren_jp' h1 xi d') sq1 sq2
  | T_Case hes hdt -> T_Case (exps_typing_ren_jp' hes xi []) (dt_typing_ren_jp' hdt xi d')
  | T_LetJoin #_ #_ #_ #_ #ts #t1 sq h1 h2 ->
    let jt = (ts, t1, r) in
    jren_ok_up xi d d' jt;
    push_vars_regions g ts;
    T_LetJoin sq (typing_ren_jp' h1 (up_ren xi) (jt :: d'))
      (typing_ren_jp' h2 (up_ren xi) (jt :: d'))
  | T_Jump #_ #_ #_ #_ #j #_ #ts #t1 _ sq2 hes ->
    nth_lt d j;
    T_Jump #sg #ln #g #d' #(xi j) #(ren_jp_exps xi _) #ts #t1 #r () sq2
      (exps_typing_ren_jp' hes xi [])
  | T_RecEmpty sq -> T_RecEmpty sq
  | T_Extend h1 h2 sq -> T_Extend (typing_ren_jp' h1 xi []) (typing_ren_jp' h2 xi []) sq
  | T_Select h1 sq -> T_Select (typing_ren_jp' h1 xi []) sq
  | T_Restrict h1 sq -> T_Restrict (typing_ren_jp' h1 xi []) sq
  | T_Update h1 h2 sq -> T_Update (typing_ren_jp' h1 xi []) (typing_ren_jp' h2 xi []) sq
  | T_Merge h1 h2 sq -> T_Merge (typing_ren_jp' h1 xi []) (typing_ren_jp' h2 xi []) sq
  | T_Inject h1 sq1 sq2 -> T_Inject (typing_ren_jp' h1 xi []) sq1 sq2
  | T_Weaken h1 sq1 sq2 -> T_Weaken (typing_ren_jp' h1 xi []) sq1 sq2
  | T_VariantValue #_ #_ #_ #_ #_ #k #v vr0 vr h1 sq1 h2 sq2 ->
    typing_value_ren_jp' h1 xi;
    variant_view_value sg e k v;
    typing_value_ren_jp' h2 xi;
    let h1' = cast (typing_ren_jp' h1 xi []) e in
    let h2' = cast (typing_ren_jp' h2 xi []) v in
    cast (T_VariantValue vr0 vr h1' sq1 h2' sq2) (ren_jp xi e)
  | T_Absurd h1 sq -> T_Absurd (typing_ren_jp' h1 xi []) sq
  | T_Perform ts sq1 sq2 sq3 h1 -> T_Perform ts sq1 sq2 sq3 (typing_ren_jp' h1 xi [])
  | T_Handle sq1 sq2 sq3 sq4 h1 h2 hcl ->
    typing_scoped' h;
    V.ren_jp_scoped 0 xi e;
    cast (T_Handle sq1 sq2 sq3 sq4 h1 h2 hcl) (ren_jp xi e)
  | T_OpenEff h1 sq -> T_OpenEff (typing_ren_jp' h1 xi []) sq
  | T_Region #_ #_ #_ #_ #_ #_ #body sq1 sq2 hes hbody ->
    typing_scoped' h;
    V.ren_jp_scoped 0 xi body;
    T_Region sq1 sq2 (exps_typing_ren_jp' hes xi []) hbody
  | T_ReadCell sq1 sq2 sq3 -> T_ReadCell sq1 sq2 sq3
  | T_WriteCell sq1 sq2 h1 -> T_WriteCell sq1 sq2 (typing_ren_jp' h1 xi [])
  | T_Match #_ #_ #_ #_ #th om hes sq hm hdt ->
    typing_scoped' h;
    values_ren_jp sg (L.length d) xi th;
    T_Match om (cast_exps (exps_typing_ren_jp' hes xi []) th) sq (match_typing_ren_jp' hm xi [])
      (dt_typing_ren_jp' hdt xi d')
  | T_OpenEffC h1 sq -> T_OpenEffC (typing_ren_jp' h1 xi []) sq
  | T_Force sq1 sq2 -> T_Force sq1 sq2
  | T_Fill #_ #_ #_ #_ #_ #e1 sq1 sq2 h1 ->
    typing_scoped' h;
    V.ren_jp_scoped 0 xi e1;
    T_Fill sq1 sq2 h1
  | T_RegionOpen sq1 sq2 sq3 hc hb ->
    typing_scoped' h;
    V.ren_jp_scoped 0 xi e;
    cast (T_RegionOpen sq1 sq2 sq3 hc hb) (ren_jp xi e)
  | T_Opaque #_ #_ #_ #_ #w sq1 sq2 -> T_Opaque #sg #ln #g #d' #w #t #r sq1 sq2

and exps_typing_ren_jp' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (xi: ren) (d': jctx)
  : Pure (exps_typing sg ln g d' r (ren_jp_exps xi es) ts)
         (requires layouts_struct g.regions /\ jren_ok xi d d')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TE_Nil sq -> TE_Nil sq
  | TE_Cons h1 h2 -> TE_Cons (typing_ren_jp' h1 xi d') (exps_typing_ren_jp' h2 xi d')

and chain_typing_ren_jp' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (xi: ren) (d': jctx)
  : Pure (chain_typing sg ln g d' r (ren_jp xi e))
         (requires layouts_struct g.regions /\ jren_ok xi d d')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TS_Head sq1 sq2 sq3 -> TS_Head sq1 sq2 sq3
  | TS_Ty #_ #_ #_ #_ #_ #e0 #s #k #t0 #th h0 _ sq2 ->
    chain_cursor_ren_jp sg xi e0;
    TS_Ty #sg #ln #g #d' #r #(ren_jp xi e0) #s #k #t0 #th (chain_typing_ren_jp' h0 xi d') () sq2
  | TS_Constr #_ #_ #_ #_ #_ #e0 #c #t0 #th h0 _ sq2 ->
    chain_cursor_ren_jp sg xi e0;
    TS_Constr #sg #ln #g #d' #r #(ren_jp xi e0) #c #t0 #th (chain_typing_ren_jp' h0 xi d') () sq2
  | TS_Val #_ #_ #_ #_ #_ #e0 #v #t0 #th #t1 #r1 #t2 h0 _ hv ->
    chain_cursor_ren_jp sg xi e0;
    TS_Val #sg #ln #g #d' #r #(ren_jp xi e0) #(ren_jp xi v) #t0 #th #t1 #r1 #t2
      (chain_typing_ren_jp' h0 xi d') () (typing_ren_jp' hv xi d')

and match_typing_ren_jp' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (h: match_typing sg ln g d r th om) (xi: ren) (d': jctx)
  : Pure (match_typing sg ln g d' r th om)
         (requires layouts_struct g.regions /\ jren_ok xi d d' /\ L.for_all (V.is_value sg) th)
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TM_Nil sq -> TM_Nil sq
  | TM_Cons #_ #_ #_ #_ #_ #_ #o #_ #_ #v sq h1 h2 ->
    proj_value sg th o v;
    typing_value_ren_jp' h1 xi;
    TM_Cons sq (cast (typing_ren_jp' h1 xi d') v) (match_typing_ren_jp' h2 xi d')

and dt_typing_ren_jp' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (xi: ren) (d': jctx)
  : Pure (dt_typing sg ln g d' om (ren_jp_dt xi dt) t r)
         (requires layouts_struct g.regions /\ jren_ok xi d d')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TD_Leaf h1 -> TD_Leaf (typing_ren_jp' h1 xi d')
  | TD_Bind ho hdt -> TD_Bind ho (dt_typing_ren_jp' hdt xi d')
  | TD_SwitchCtor #_ #_ #_ #_ #_ #_ #bs tq ks ss cs ho sq1 sq2 _ hbr ->
    ren_jp_brs_labels xi bs;
    TD_SwitchCtor tq ks ss cs ho sq1 sq2 () (ctor_brs_ren_jp' hbr xi d')
  | TD_SwitchCtorDef #_ #_ #_ #_ #_ #_ #bs tq ks ss cs ho sq1 sq2 _ hbr hdf ->
    ren_jp_brs_labels xi bs;
    TD_SwitchCtorDef tq ks ss cs ho sq1 sq2 () (ctor_brs_ren_jp' hbr xi d')
      (dt_typing_ren_jp' hdf xi d')
  | TD_SwitchLit #_ #_ #_ #_ #_ #_ #bs lq ho sq1 _ hbr hdf ->
    ren_jp_brs_labels xi bs;
    TD_SwitchLit lq ho sq1 () (lit_brs_ren_jp' hbr xi d') (dt_typing_ren_jp' hdf xi d')
  | TD_SwitchKey #_ #_ #_ #_ #_ #_ #bs vr kts ho sq1 _ sq3 hbr ->
    ren_jp_brs_labels xi bs;
    TD_SwitchKey vr kts ho sq1 () sq3 (key_brs_ren_jp' hbr xi d')
  | TD_SwitchKeyDef #_ #_ #_ #_ #_ #_ #bs vr vr' kts ho sq1 _ sq3 hbr hdf ->
    ren_jp_brs_labels xi bs;
    TD_SwitchKeyDef vr vr' kts ho sq1 () sq3 (key_brs_ren_jp' hbr xi d')
      (dt_typing_ren_jp' hdf xi d')
  | TD_Guard h1 h2 h3 ->
    TD_Guard (typing_ren_jp' h1 xi []) (dt_typing_ren_jp' h2 xi d') (dt_typing_ren_jp' h3 xi d')

and ctor_brs_ren_jp' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#o: occ)
  (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree)) (#t #r: typ)
  (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (xi: ren) (d': jctx)
  : Pure (ctor_brs_typing sg ln g d' om o ks ss cs (ren_jp_brs xi bs) t r)
         (requires layouts_struct g.regions /\ jren_ok xi d d')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCB_Nil sq -> TCB_Nil sq
  | TCB_Cons sq hdt h2 -> TCB_Cons sq (dt_typing_ren_jp' hdt xi d') (ctor_brs_ren_jp' h2 xi d')

and lit_brs_ren_jp' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#lt: typ)
  (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (xi: ren) (d': jctx)
  : Pure (lit_brs_typing sg ln g d' om lt (ren_jp_brs xi bs) t r)
         (requires layouts_struct g.regions /\ jren_ok xi d d')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TLB_Nil sq -> TLB_Nil sq
  | TLB_Cons sq hdt h2 -> TLB_Cons sq (dt_typing_ren_jp' hdt xi d') (lit_brs_ren_jp' h2 xi d')

and key_brs_ren_jp' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#o: occ)
  (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (xi: ren) (d': jctx)
  : Pure (key_brs_typing sg ln g d' om o kts (ren_jp_brs xi bs) t r)
         (requires layouts_struct g.regions /\ jren_ok xi d d')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TKB_Nil sq -> TKB_Nil sq
  | TKB_Cons sq hdt h2 -> TKB_Cons sq (dt_typing_ren_jp' hdt xi d') (key_brs_ren_jp' h2 xi d')

(* The stated theorems. *)

let typing_ren_jp #sg #ln #g #d #e #t #r h xi d' =
  wf_ctx_layouts_struct sg g;
  typing_ren_jp' h xi d'

let exps_typing_ren_jp #sg #ln #g #d #r #es #ts h xi d' =
  wf_ctx_layouts_struct sg g;
  exps_typing_ren_jp' h xi d'

let chain_typing_ren_jp #sg #ln #g #d #r #e h xi d' =
  wf_ctx_layouts_struct sg g;
  chain_typing_ren_jp' h xi d'

let match_typing_ren_jp #sg #ln #g #d #r #th #om h xi d' =
  wf_ctx_layouts_struct sg g;
  match_typing_ren_jp' h xi d'

let dt_typing_ren_jp #sg #ln #g #d #om #dt #t #r h xi d' =
  wf_ctx_layouts_struct sg g;
  dt_typing_ren_jp' h xi d'

let typing_weaken_jp #sg #ln #g #d #e #t #r h jt =
  jren_ok_shift d jt;
  typing_ren_jp h (shift 1) (jt :: d)

let typing_jp_nil #sg #ln #g #e #t #r h d =
  typing_scoped h;
  V.ren_jp_scoped 0 id_ren e;
  cast (typing_ren_jp h id_ren d) e
