(* Proof structure.

   One mutual recursion, on the value and then on the derivation: the
   measure of `value_typing` is `%[v; 1; h]` and that of
   `value_chain_typing` is `%[e; 0; hc]`. A rule for a value form is
   re-applied with the new row; `T_Conv` and `T_VariantValue` recurse on
   their premise for the same term (and on the payload, a subterm,
   `variant_view_precedes`). A chain is normalized, which leaves the value
   at the same measure with a smaller second component; its value
   arguments are subterms. The normalized chain is typed by `T_Chain` at
   the instance of its cursor and converted back to its type, which is
   kinded by regularity. *)
module Stella.Core.Typing.Values
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Regularity
open Stella.Core.Typing.Chain
open Stella.Core.Typing.Join
module L = FStar.List.Tot
module V = Stella.Core.Value

let rec variant_view_precedes (e: exp)
  : Lemma (requires Some? (variant_view e)) (ensures snd (Some?.v (variant_view e)) << e)
          (decreases e) =
  match e with
  | EInject _ _ _ -> ()
  | EWeaken _ _ e' -> variant_view_precedes e'

let chain_value_facts (sg: sig) (v: exp)
  : Lemma (requires V.is_value sg v /\ (EGlobal? v \/ EApp? v \/ ETyApp? v \/ ECApp? v))
          (ensures V.value_head sg v /\ V.chain_values sg v) =
  match v with
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ()

let chain_typing_shape (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (hc: chain_typing sg ln g d r e)
  : Lemma (EGlobal? e \/ EApp? e \/ ETyApp? e \/ ECApp? e) =
  match hc with
  | TS_Head _ _ _ | TS_Ty _ _ _ | TS_Constr _ _ _ | TS_Val _ _ _ -> ()

let value_extend (sg: sig) (k: key) (v1 v2: exp)
  : Lemma (requires V.is_value sg (EExtend k v1 v2)) (ensures V.is_value sg v1 /\ V.is_value sg v2) = ()

let value_inject (sg: sig) (k: key) (t: typ) (v: exp)
  : Lemma (requires V.is_value sg (EInject k t v)) (ensures V.is_value sg v) = ()

let value_weaken (sg: sig) (k: key) (t: typ) (v: exp)
  : Lemma (requires V.is_value sg (EWeaken k t v)) (ensures V.is_value sg v) = ()

let value_openeff (sg: sig) (t: typ) (v: exp)
  : Lemma (requires V.is_value sg (EOpenEff t v)) (ensures V.is_value sg v) = ()

let value_shape (sg: sig) (v: exp)
  : Lemma (requires V.is_value sg v)
          (ensures ELit? v \/ ELam? v \/ ERecEmpty? v \/ EOpaque? v \/ ETyLam? v \/ ECLam? v \/
                   EInject? v \/ EWeaken? v \/ EOpenEff? v \/ EExtend? v \/ EGlobal? v \/
                   EApp? v \/ ETyApp? v \/ ECApp? v) =
  match v with
  | ELit _ | ELam _ _ _ | ERecEmpty | EOpaque _ _ | ETyLam _ _ | ECLam _ _ | EInject _ _ _
  | EWeaken _ _ _ | EOpenEff _ _ | EExtend _ _ _ | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ()

let rec value_typing #sg #ln #g #d #v #t #r h d' r'
  : Pure (typing sg ln g d' v t r')
         (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v /\ check sg g r' (KRow EEffect))
         (ensures fun _ -> True)
         (decreases %[v; 2; h]) =
  value_shape sg v;
  match h with
  | T_Global _ _ _ -> chain_value_typing h d' r'
  | T_App _ _ -> chain_value_typing h d' r'
  | T_TyApp _ _ -> chain_value_typing h d' r'
  | T_CApp _ _ -> chain_value_typing h d' r'
  | T_Chain hc _ -> chain_typing_shape hc; chain_value_typing h d' r'
  | T_Conv h1 _ _ ->
    ty_eq_refl r';
    T_Conv (value_typing h1 d' r') () ()
  | T_VariantValue #_ #_ #_ #_ #_ #k #vp vr0 vr h1 sq1 h2 sq2 ->
    variant_view_value sg v k vp;
    variant_view_precedes v;
    T_VariantValue vr0 vr (value_typing h1 [] r') sq1 (value_typing h2 [] r') sq2
  | T_Lit #_ #_ #_ #_ #c _ -> T_Lit #sg #ln #g #d' #c #r' ()
  | T_Lam sq1 _ hb -> T_Lam sq1 () hb
  | T_TyLam sq1 sq2 _ hb -> T_TyLam sq1 sq2 () hb
  | T_CLam sq1 sq2 _ hb -> T_CLam sq1 sq2 () hb
  | T_RecEmpty _ -> T_RecEmpty ()
  | T_Opaque #_ #_ #_ #_ #w sq1 _ -> T_Opaque #sg #ln #g #d' #w #t #r' sq1 ()
  | T_Extend #_ #_ #_ #_ #k #e1 #e2 h1 h2 sq ->
    value_extend sg k e1 e2;
    T_Extend (value_typing h1 [] r') (value_typing h2 [] r') sq
  | T_Inject #_ #_ #_ #_ #k #r0 #e1 h1 sq1 sq2 ->
    value_inject sg k r0 e1;
    T_Inject (value_typing h1 [] r') sq1 sq2
  | T_Weaken #_ #_ #_ #_ #k #t1 #e1 h1 sq1 sq2 ->
    value_weaken sg k t1 e1;
    T_Weaken (value_typing h1 [] r') sq1 sq2
  | T_OpenEff #_ #_ #_ #_ #r1 #e1 h1 sq ->
    value_openeff sg r1 e1;
    T_OpenEff (value_typing h1 [] r') sq
  | T_Var _ _ -> false_elim ()
  | T_Let _ _ _ -> false_elim ()
  | T_LetRec _ _ _ -> false_elim ()
  | T_Case _ _ -> false_elim ()
  | T_LetJoin _ _ _ -> false_elim ()
  | T_Jump _ _ _ -> false_elim ()
  | T_Select _ _ -> false_elim ()
  | T_Restrict _ _ -> false_elim ()
  | T_Update _ _ _ -> false_elim ()
  | T_Merge _ _ _ -> false_elim ()
  | T_Absurd _ _ -> false_elim ()
  | T_Perform _ _ _ _ _ -> false_elim ()
  | T_Handle _ _ _ _ _ _ _ -> false_elim ()
  | T_Region _ _ _ _ -> false_elim ()
  | T_ReadCell _ _ _ -> false_elim ()
  | T_WriteCell _ _ _ -> false_elim ()
  | T_Match _ _ _ _ _ -> false_elim ()
  | T_OpenEffC _ _ -> false_elim ()
  | T_Force _ _ -> false_elim ()
  | T_Fill _ _ _ -> false_elim ()
  | T_RegionOpen _ _ _ _ _ -> false_elim ()

and chain_value_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#v: exp)
  (#t #r: typ) (h: typing sg ln g d v t r) (d': jctx) (r': typ)
  : Pure (typing sg ln g d' v t r')
         (requires sig_ok sg /\ wf_ctx sg g /\ V.is_value sg v /\ check sg g r' (KRow EEffect) /\
                   (EGlobal? v \/ EApp? v \/ ETyApp? v \/ ECApp? v))
         (ensures fun _ -> True)
         (decreases %[v; 1; h]) =
  chain_value_facts sg v;
  value_chain_normalizes sg v;
  let hc = chain_normal h in
  let hc' = value_chain_typing hc [] r' in
  let Some (s, th) = chain_cursor sg v in
  typing_regular h;
  ty_eq_sym t (sub_ty th s);
  ty_eq_refl r';
  let h1 : typing sg ln g d' v (sub_ty th s) r' = T_Chain #sg #ln #g #d' #v #s #th #r' hc' () in
  T_Conv h1 () ()

and value_chain_typing #sg #ln #g #d #r #e hc d' r'
  : Pure (chain_typing sg ln g d' r' e)
         (requires sig_ok sg /\ wf_ctx sg g /\ V.chain_values sg e /\ check sg g r' (KRow EEffect))
         (ensures fun _ -> True)
         (decreases %[e; 0; hc]) =
  match hc with
  | TS_Head sq1 sq2 _ -> TS_Head sq1 sq2 ()
  | TS_Ty h0 sq1 sq2 -> TS_Ty (value_chain_typing h0 d' r') sq1 sq2
  | TS_Constr h0 sq1 sq2 -> TS_Constr (value_chain_typing h0 d' r') sq1 sq2
  | TS_Val h0 sq hv -> TS_Val (value_chain_typing h0 d' r') sq (value_typing hv d' r')

let rec values_typing #sg #ln #g #d #r #es #ts h d' r'
  : Pure (exps_typing sg ln g d' r' es ts)
         (requires sig_ok sg /\ wf_ctx sg g /\ L.for_all (V.is_value sg) es /\
                   check sg g r' (KRow EEffect))
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TE_Nil _ -> TE_Nil ()
  | TE_Cons h1 h2 -> TE_Cons (value_typing h1 d' r') (values_typing h2 d' r')

let rec values_match_typing #sg #ln #g #d #r #th #om h d' r'
  : Pure (match_typing sg ln g d' r' th om)
         (requires sig_ok sg /\ wf_ctx sg g /\ L.for_all (V.is_value sg) th /\
                   check sg g r' (KRow EEffect))
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TM_Nil _ -> TM_Nil ()
  | TM_Cons #_ #_ #_ #_ #_ #_ #o #_ #_ #v sq h1 h2 ->
    proj_value sg th o v;
    TM_Cons sq (value_typing h1 d' r') (values_match_typing h2 d' r')

let value_typing_exists #sg #ln #g #d #v #t #r h d' r' =
  let h' = value_typing h d' r' in
  FStar.Classical.exists_intro (fun (_: typing sg ln g d' v t r') -> True) h'
