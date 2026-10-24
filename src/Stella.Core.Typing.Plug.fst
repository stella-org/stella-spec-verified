(* Proof structure.

   Cursors. The cursor of `apply_arg e0 a` is one step from that of `e0`
   (`chain_cursor_apply_arg`), and a step at a value argument does not
   read it. A saturated foreign prefix has no further step, so the prefix
   of a chain with a cursor is no foreign redex (`prefix_not_foreign_redex`),
   and `step_chain_cursor` recurses into it. No pure head rule but the
   foreign one rewrites a chain with a cursor (`pure_head_no_cursor`), an
   effect rule rewrites a `handle`, which has none (`eff_step_shape`), and
   a rule of regions and cells a `region` or an open region frame, which
   have none either (`region_step_shape`).

   One frame. `plug1_typing` strips the conversions (`strip_conv`), splits
   the conversion-free derivation with one helper per frame (`pi_*`), and
   converts the filled derivation back (`plug1_inv_conv`, the facts on the
   hole by `hole_conv`). A helper matches the rule of its frame; every
   other rule is excluded by the shape of the term, `T_Chain` by the term
   having no cursor and `T_VariantValue` by the term being no value. For
   the frames of a chain, `T_Chain` is a second case: the hole is a value
   argument, typed by the `TS_Val` premise, or a prefix, typed by `T_Chain`
   at its own cursor. A new prefix is normalized (`chain_normal`). The
   chain's cursor being kept, the argument steps the new prefix's cursor,
   so its remainder has the shape the argument consumes, and the type
   equality `chain_normal` gives between the two instances carries the
   argument's premise over: the domain, the kind, the constraint
   (`fill_app_fun`, `fill_tyapp`, `fill_capp`). The lists of `case`,
   `jump` and `region` are split at the hole by `exps_split`.

   Tail contexts. By induction on the frames, outermost last: the hole of
   `plug fs (plug1 f e)` is split by the induction, then by `plug1_typing`
   at `f`, whose join point goes in front. *)
module Stella.Core.Typing.Plug
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Spine.Wf
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Regularity
open Stella.Core.Typing.Inversion
open Stella.Core.Typing.Chain
open Stella.Core.Typing.Values
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module V = Stella.Core.Value

(* * Cursors *)

(* Only the frames of a chain build a chain. *)
let plug1_chain_frame (f: frame) (e: exp)
  : Lemma (requires Some? (decompose_global_app (plug1 f e)))
          (ensures FAppArg? f \/ FAppFun? f \/ FTyApp? f \/ FCApp? f) =
  match f with
  | FAppArg _ | FAppFun _ | FTyApp _ | FCApp -> ()
  | FOpenEff _ | FOpenEffC _ | FExtendL _ _ | FExtendR _ _ | FUpdateL _ _ | FUpdateR _ _
  | FMergeL _ | FMergeR _ | FSelect _ | FRestrict _ | FInject _ _ | FWeaken _ _ | FAbsurd _
  | FLet _ _ | FCase _ _ _ | FGuard _ _ _ | FLetJoin _ _ _ | FJump _ _ _ | FPerform _ _ _
  | FHandle _ | FRegion _ _ _ _ | FRegionOpen _ _ | FWriteCell _ _ | FFill _ -> ()

let chain_cursor_replace_val sg fn x y =
  if Some? (decompose_global_app fn) then begin
    chain_cursor_apply_arg sg fn (SVal x);
    chain_cursor_apply_arg sg fn (SVal y)
  end

(* A saturated remainder takes no further argument. *)
let saturated_no_step (sg: sig) (t: typ) (th: tsub) (a: spine_arg)
  : Lemma (requires saturated sg t) (ensures None? (cursor_step sg t th a)) = ()

let prefix_not_foreign_redex (sg: sig) (e0: exp) (a: spine_arg)
  : Lemma (requires Some? (chain_cursor sg (apply_arg e0 a)))
          (ensures Some? (decompose_global_app e0) /\ Some? (chain_cursor sg e0) /\
                   not (V.foreign_redex sg e0)) =
  decompose_prefix e0 a;
  chain_cursor_apply_arg sg e0 a;
  let Some (s0, th0) = chain_cursor sg e0 in
  if saturated sg s0 then saturated_no_step sg s0 th0 a

let pure_head_no_cursor (#sg: sig) (#gi: genv) (#e: exp) (#c: config) (ph: pure_head sg gi e c)
  : Lemma (requires Some? (chain_cursor sg e) /\ not (V.foreign_redex sg e)) (ensures False) =
  match ph with
  | PH_Unfold #_ #_ #q #ks _ _ -> chain_cursor_global sg q ks
  | _ -> ()

let rec step_chain_cursor #sg #gi #ra #st #e #ra' #st' #e' s
  : Lemma (requires Some? (chain_cursor sg e) /\ not (V.foreign_redex sg e))
          (ensures Some? (decompose_global_app e') /\ chain_cursor sg e' == chain_cursor sg e)
          (decreases s) =
  match s with
  | S_Pure ph -> pure_head_no_cursor ph
  | S_Eff eh -> eff_step_shape eh
  | S_Region rh -> region_step_shape rh
  | S_Ctx #_ #_ #_ #_ #e0 #_ #_ #e0' f _ s0 ->
    (match f with
     | FAppArg fn -> chain_cursor_replace_val sg fn e0 e0'
     | FAppFun v ->
       prefix_not_foreign_redex sg e0 (SVal v);
       step_chain_cursor s0;
       chain_cursor_apply_arg sg e0 (SVal v);
       chain_cursor_apply_arg sg e0' (SVal v)
     | FTyApp t0 ->
       prefix_not_foreign_redex sg e0 (STy t0);
       step_chain_cursor s0;
       chain_cursor_apply_arg sg e0 (STy t0);
       chain_cursor_apply_arg sg e0' (STy t0)
     | FCApp ->
       prefix_not_foreign_redex sg e0 SConstr;
       step_chain_cursor s0;
       chain_cursor_apply_arg sg e0 SConstr;
       chain_cursor_apply_arg sg e0' SConstr
     | _ -> plug1_chain_frame f e0)

(* A foreign prefix with a further argument position is unsaturated, so a
   value once its value arguments are. *)
let unsaturated_prefix_value (sg: sig) (e0: exp) (a: spine_arg)
  : Lemma (requires V.foreign_redex sg (apply_arg e0 a) /\ V.chain_values sg e0)
          (ensures V.is_value sg e0) =
  let Some (q, ks, args) = decompose_global_app (apply_arg e0 a) in
  decompose_prefix e0 a;
  decompose_apply_arg e0 a;
  let Some (_, _, args0) = decompose_global_app e0 in
  spine_cursor_snoc sg q ks args0 a;
  let Some (s0, th0) = spine_cursor sg q ks args0 in
  if saturated sg s0 then saturated_no_step sg s0 th0 a;
  assert (V.value_head sg e0);
  match e0 with
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ()

let plug1_not_foreign_redex sg f e =
  if Some? (decompose_global_app (plug1 f e)) then plug1_chain_frame f e;
  match f with
  | FAppArg _ -> ()
  | FAppFun v -> if V.foreign_redex sg (EApp e v) then unsaturated_prefix_value sg e (SVal v)
  | FTyApp t -> if V.foreign_redex sg (ETyApp e t) then unsaturated_prefix_value sg e (STy t)
  | FCApp -> if V.foreign_redex sg (ECApp e) then unsaturated_prefix_value sg e SConstr
  | _ -> ()

let step_plug1_cursor_kept #sg #gi #ra #st #e #ra' #st' #e' f s =
  match f with
  | FAppArg fn -> chain_cursor_replace_val sg fn e e'
  | FAppFun v ->
    if Some? (chain_cursor sg (EApp e v)) then begin
      prefix_not_foreign_redex sg e (SVal v);
      step_chain_cursor s;
      chain_cursor_apply_arg sg e (SVal v);
      chain_cursor_apply_arg sg e' (SVal v)
    end
  | FTyApp t0 ->
    if Some? (chain_cursor sg (ETyApp e t0)) then begin
      prefix_not_foreign_redex sg e (STy t0);
      step_chain_cursor s;
      chain_cursor_apply_arg sg e (STy t0);
      chain_cursor_apply_arg sg e' (STy t0)
    end
  | FCApp ->
    if Some? (chain_cursor sg (ECApp e)) then begin
      prefix_not_foreign_redex sg e SConstr;
      step_chain_cursor s;
      chain_cursor_apply_arg sg e SConstr;
      chain_cursor_apply_arg sg e' SConstr
    end
  | _ -> if Some? (decompose_global_app (plug1 f e)) then plug1_chain_frame f e

(* * Tail contexts: lists *)

(* * One frame *)

(* The conversions stripped from a derivation of `f[e]` are put back after
   filling. *)
let hole_conv (f: frame) (d: jctx) (t0 r0 t r: typ) (hd: jctx) (ht hr: typ)
  : Lemma (requires hole_jctx f d t0 hd ht hr /\ hole_row f r0 hr /\ ty_eq t0 t /\ ty_eq r0 r)
          (ensures hole_jctx f d t hd ht hr /\ hole_row f r hr) =
  match f with
  | FHandle h -> ty_eq_ext_cong h.h_ent h.h_ent r0 r
  | FRegionOpen a _ -> ty_eq_ext_cong (EntRegion (RFree a)) (EntRegion (RFree a)) r0 r
  | _ -> ()

let plug1_inv_conv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#f: frame) (#e: exp)
  (#t0 #r0: typ) (p: plug1_inv sg ln g d f e t0 r0) (t r: typ)
  : Pure (plug1_inv sg ln g d f e t r)
         (requires ty_eq t0 t /\ ty_eq r0 r /\ check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  hole_conv f d t0 r0 t r p.hd p.ht p.hr;
  { hd = p.hd; ht = p.ht; hr = p.hr; hole = p.hole; hole_ctx = ();
    fill = (fun (e': exp) (h': typing sg ln g p.hd e' p.ht p.hr) ->
              T_Conv #sg #ln #g #d #(plug1 f e') #t0 #r0 #t #r (p.fill e' h') () ()) }

(* The lists of `case`, `jump` and `region`, split at the hole. *)
noeq type exps_hole (sg: sig) (ln: lctx) (g: ctx) (d: jctx) (r: typ) (vs: list exp) (e: exp)
  (es: list exp) (ts: list typ) = {
  xh_t: typ;
  xh_h: typing sg ln g d e xh_t r;
  xh_fill: e': exp -> typing sg ln g d e' xh_t r -> exps_typing sg ln g d r (L.append vs (e' :: es)) ts;
}

let rec exps_split (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (vs: list exp) (e: exp)
  (es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r (L.append vs (e :: es)) ts)
  : Tot (exps_hole sg ln g d r vs e es ts) (decreases vs) =
  match vs with
  | [] ->
    (match h with
     | TE_Cons #_ #_ #_ #_ #_ #_ #_ #t1 #_ h1 hrest ->
       { xh_t = t1; xh_h = h1;
         xh_fill = (fun (e': exp) (h': typing sg ln g d e' t1 r) -> TE_Cons h' hrest) })
  | v :: vs' ->
    (match h with
     | TE_Cons #_ #_ #_ #_ #_ #_ #_ #_ #_ h1 hrest ->
       let p = exps_split vs' e es hrest in
       { xh_t = p.xh_t; xh_h = p.xh_h;
         xh_fill = (fun (e': exp) (h': typing sg ln g d e' p.xh_t r) -> TE_Cons h1 (p.xh_fill e' h')) })

(* The domains of two arrows are equal when their instances are. *)
let fun_dom_eq (sg: sig) (th0: tsub) (s0 a1 rho1 b1: typ) (th1: tsub) (s1 a2 rho2 b2: typ)
  : Lemma (requires prim_wf sg /\ as_function sg s0 == Some (a1, rho1, b1) /\
                    as_function sg s1 == Some (a2, rho2, b2) /\
                    ty_eq (sub_ty th0 s0) (sub_ty th1 s1))
          (ensures ty_eq (sub_ty th0 a1) (sub_ty th1 a2)) =
  as_function_sub sg th0 s0 a1 rho1 b1;
  as_function_sub sg th1 s1 a2 rho2 b2;
  as_function_t_fun sg (sub_ty th0 s0) (sub_ty th0 a1) (sub_ty th0 rho1) (sub_ty th0 b1);
  as_function_t_fun sg (sub_ty th1 s1) (sub_ty th1 a2) (sub_ty th1 rho2) (sub_ty th1 b2);
  ty_eq_fun_ty prim_function prim_function (sub_ty th0 a1) (sub_ty th0 rho1) (sub_ty th0 b1)
    (sub_ty th1 a2) (sub_ty th1 rho2) (sub_ty th1 b2)

let chain_fun_regular (sg: sig) (g: ctx) (e0: exp) (s0: typ) (th0: tsub) (a1 rho1 b1: typ)
  : Lemma (requires sig_ok sg /\ chain_args_ok sg g e0 /\ chain_cursor sg e0 == Some (s0, th0) /\
                    as_function sg s0 == Some (a1, rho1, b1))
          (ensures check sg g (sub_ty th0 a1) KType) =
  let Some (q, ks, args) = decompose_global_app e0 in
  spine_cursor_fun_regular sg g q ks args s0 th0 a1 rho1 b1

(* ** The frames of a chain *)

let fill_app_arg (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (fn e: exp) (s: typ)
  (th: tsub) (#s0: typ) (#th0: tsub) (#a1 #rho1 #b1: typ)
  (hc0: chain_typing sg ln g [] r fn)
  (sq0: squash (chain_cursor sg fn == Some (s0, th0) /\ as_function sg s0 == Some (a1, rho1, b1)))
  (e': exp) (hv': typing sg ln g [] e' (sub_ty th0 a1) r)
  : Pure (typing sg ln g d (EApp fn e') (sub_ty th s) r)
         (requires chain_cursor sg (EApp fn e) == Some (s, th)) (ensures fun _ -> True) =
  chain_cursor_replace_val sg fn e e';
  T_Chain #sg #ln #g #d #(EApp fn e') #s #th #r
    (TS_Val #sg #ln #g #[] #r #fn #e' #s0 #th0 #a1 #rho1 #b1 hc0 sq0 hv') ()

let pi_app_arg (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (fn e: exp) (#t #r: typ)
  (h: typing sg ln g d (EApp fn e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FAppArg fn) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_App #_ #_ #_ #_ #_ #_ #t1 #_ #_ h1 h2 ->
    { hd = []; ht = t1; hr = r; hole = h2; hole_ctx = ();
      fill = (fun (e': exp) (h2': typing sg ln g [] e' t1 r) -> T_App #sg #ln #g #d h1 h2') }
  | T_Chain #_ #_ #_ #_ #_ #s #th #_ hc _ ->
    (match hc with
     | TS_Val #_ #_ #_ #_ #_ #_ #_ #s0 #th0 #a1 #rho1 #b1 hc0 sq0 hv ->
       { hd = []; ht = sub_ty th0 a1; hr = r; hole = hv; hole_ctx = ();
         fill = fill_app_arg #sg #ln #g #d #r fn e s th #s0 #th0 #a1 #rho1 #b1 hc0 sq0 }
     | _ -> false_elim ())
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let fill_app_fun (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (v e: exp) (s: typ)
  (th: tsub) (s0: typ) (th0: tsub) (a1 rho1 b1: typ)
  (hv: typing sg ln g [] v (sub_ty th0 a1) r)
  (e': exp) (h': typing sg ln g [] e' (sub_ty th0 s0) r)
  : Pure (typing sg ln g d (EApp e' v) (sub_ty th s) r)
         (requires sig_ok sg /\ chain_cursor sg (EApp e v) == Some (s, th) /\
                   as_function sg s0 == Some (a1, rho1, b1) /\
                   cursor_kept sg (EApp e v) (EApp e' v))
         (ensures fun _ -> True) =
  decompose_prefix e' (SVal v);
  chain_cursor_apply_arg sg e' (SVal v);
  let hc' = chain_normal h' in
  let Some (s1, th1) = chain_cursor sg e' in
  let Some (a2, rho2, b2) = as_function sg s1 in
  fun_dom_eq sg th0 s0 a1 rho1 b1 th1 s1 a2 rho2 b2;
  chain_typing_args_ok hc';
  chain_fun_regular sg g e' s1 th1 a2 rho2 b2;
  let hv' : typing sg ln g [] v (sub_ty th1 a2) r = T_Conv hv () () in
  T_Chain #sg #ln #g #d #(EApp e' v) #s #th #r
    (TS_Val #sg #ln #g #[] #r #e' #v #s1 #th1 #a2 #rho2 #b2 hc' () hv') ()

let pi_app_fun (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (v e: exp) (#t #r: typ)
  (h: typing sg ln g d (EApp e v) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FAppFun v) e t r) (requires sig_ok sg) (ensures fun _ -> True) =
  match h with
  | T_App #_ #_ #_ #_ #_ #_ #t1 #t2 #_ h1 h2 ->
    { hd = []; ht = t_fun t1 r t2; hr = r; hole = h1; hole_ctx = ();
      fill = (fun (e': exp) (h1': typing sg ln g [] e' (t_fun t1 r t2) r) ->
                T_App #sg #ln #g #d h1' h2) }
  | T_Chain #_ #_ #_ #_ #_ #s #th #_ hc _ ->
    (match hc with
     | TS_Val #_ #_ #_ #_ #_ #_ #_ #s0 #th0 #a1 #rho1 #b1 hc0 _ hv ->
       { hd = []; ht = sub_ty th0 s0; hr = r;
         hole = T_Chain #sg #ln #g #[] #e #s0 #th0 #r hc0 (); hole_ctx = ();
         fill = fill_app_fun #sg #ln #g #d #r v e s th s0 th0 a1 rho1 b1 hv }
     | _ -> false_elim ())
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let fill_tyapp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (sa: typ) (e: exp) (s: typ)
  (th: tsub) (k: kind) (b: typ) (th0: tsub) (sqk: squash (check sg g sa k))
  (e': exp) (h': typing sg ln g [] e' (sub_ty th0 (TForall k b)) r)
  : Pure (typing sg ln g d (ETyApp e' sa) (sub_ty th s) r)
         (requires sig_ok sg /\ chain_cursor sg (ETyApp e sa) == Some (s, th) /\
                   cursor_kept sg (ETyApp e sa) (ETyApp e' sa))
         (ensures fun _ -> True) =
  decompose_prefix e' (STy sa);
  chain_cursor_apply_arg sg e' (STy sa);
  let hc' = chain_normal h' in
  let Some (s1, th1) = chain_cursor sg e' in
  let TForall k1 b1 = s1 in
  ty_eq_forall_inv k k1 (sub_ty (up_tsub th0) b) (sub_ty (up_tsub th1) b1);
  T_Chain #sg #ln #g #d #(ETyApp e' sa) #s #th #r
    (TS_Ty #sg #ln #g #[] #r #e' #sa #k1 #b1 #th1 hc' () sqk) ()

let pi_tyapp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (sa: typ) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (ETyApp e sa) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FTyApp sa) e t r) (requires sig_ok sg) (ensures fun _ -> True) =
  match h with
  | T_TyApp #_ #_ #_ #_ #_ #_ #k #t0 #_ h1 sq ->
    { hd = []; ht = TForall k t0; hr = r; hole = h1; hole_ctx = ();
      fill = (fun (e': exp) (h1': typing sg ln g [] e' (TForall k t0) r) ->
                T_TyApp #sg #ln #g #d h1' sq) }
  | T_Chain #_ #_ #_ #_ #_ #s #th #_ hc _ ->
    (match hc with
     | TS_Ty #_ #_ #_ #_ #_ #_ #_ #k #b #th0 hc0 _ sqk ->
       { hd = []; ht = sub_ty th0 (TForall k b); hr = r;
         hole = T_Chain #sg #ln #g #[] #e #(TForall k b) #th0 #r hc0 (); hole_ctx = ();
         fill = fill_tyapp #sg #ln #g #d #r sa e s th k b th0 sqk }
     | _ -> false_elim ())
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let fill_capp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (e: exp) (s: typ)
  (th: tsub) (c: constr) (b: typ) (th0: tsub) (sqc: squash (entails (hyps g) (sub_constr th0 c)))
  (e': exp) (h': typing sg ln g [] e' (sub_ty th0 (TConstr c b)) r)
  : Pure (typing sg ln g d (ECApp e') (sub_ty th s) r)
         (requires sig_ok sg /\ chain_cursor sg (ECApp e) == Some (s, th) /\
                   cursor_kept sg (ECApp e) (ECApp e'))
         (ensures fun _ -> True) =
  decompose_prefix e' SConstr;
  chain_cursor_apply_arg sg e' SConstr;
  let hc' = chain_normal h' in
  let Some (s1, th1) = chain_cursor sg e' in
  let TConstr c1 b1 = s1 in
  ty_eq_constr_inv (sub_constr th0 c) (sub_constr th1 c1) (sub_ty th0 b) (sub_ty th1 b1);
  entails_constr_eq (hyps g) (sub_constr th0 c) (sub_constr th1 c1);
  T_Chain #sg #ln #g #d #(ECApp e') #s #th #r
    (TS_Constr #sg #ln #g #[] #r #e' #c1 #b1 #th1 hc' () ()) ()

let pi_capp (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (ECApp e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d FCApp e t r) (requires sig_ok sg) (ensures fun _ -> True) =
  match h with
  | T_CApp #_ #_ #_ #_ #_ #c #t0 #_ h1 sq ->
    { hd = []; ht = TConstr c t0; hr = r; hole = h1; hole_ctx = ();
      fill = (fun (e': exp) (h1': typing sg ln g [] e' (TConstr c t0) r) ->
                T_CApp #sg #ln #g #d h1' sq) }
  | T_Chain #_ #_ #_ #_ #_ #s #th #_ hc _ ->
    (match hc with
     | TS_Constr #_ #_ #_ #_ #_ #_ #c #b #th0 hc0 _ sqc ->
       { hd = []; ht = sub_ty th0 (TConstr c b); hr = r;
         hole = T_Chain #sg #ln #g #[] #e #(TConstr c b) #th0 #r hc0 (); hole_ctx = ();
         fill = fill_capp #sg #ln #g #d #r e s th c b th0 sqc }
     | _ -> false_elim ())
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

(* ** The other frames *)

let mk_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#f: frame) (#e: exp) (#t #r: typ)
  (#hd: jctx) (#ht #hr: typ) (hole: typing sg ln g hd e ht hr)
  (sq: squash (hole_jctx f d t hd ht hr /\ hole_row f r hr)) (fill: plug1_fill sg ln g d f e t r hd ht hr)
  : plug1_inv sg ln g d f e t r =
  { hd = hd; ht = ht; hr = hr; hole = hole; hole_ctx = sq; fill = fill }

let pi_openeff (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (r': typ) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (EOpenEff r' e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FOpenEff r') e t r)
         (requires not (V.is_value sg (EOpenEff r' e))) (ensures fun _ -> True) =
  match h with
  | T_OpenEff h1 sq -> mk_inv h1 () (fun e' h1' -> T_OpenEff h1' sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_openeffc (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (r': typ) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (EOpenEffC r' e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FOpenEffC r') e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_OpenEffC h1 sq -> mk_inv h1 () (fun e' h1' -> T_OpenEffC h1' sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_extend_l (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (k: key) (e2 e: exp) (#t #r: typ)
  (h: typing sg ln g d (EExtend k e e2) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FExtendL k e2) e t r)
         (requires not (V.is_value sg (EExtend k e e2))) (ensures fun _ -> True) =
  match h with
  | T_Extend h1 h2 sq -> mk_inv h1 () (fun e' h1' -> T_Extend h1' h2 sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_extend_r (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (k: key) (v1 e: exp) (#t #r: typ)
  (h: typing sg ln g d (EExtend k v1 e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FExtendR k v1) e t r)
         (requires not (V.is_value sg (EExtend k v1 e))) (ensures fun _ -> True) =
  match h with
  | T_Extend h1 h2 sq -> mk_inv h2 () (fun e' h2' -> T_Extend h1 h2' sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_update_l (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (k: key) (e2 e: exp) (#t #r: typ)
  (h: typing sg ln g d (EUpdate k e e2) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FUpdateL k e2) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Update h1 h2 sq -> mk_inv h1 () (fun e' h1' -> T_Update h1' h2 sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_update_r (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (k: key) (v1 e: exp) (#t #r: typ)
  (h: typing sg ln g d (EUpdate k v1 e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FUpdateR k v1) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Update h1 h2 sq -> mk_inv h2 () (fun e' h2' -> T_Update h1 h2' sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_merge_l (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (e2 e: exp) (#t #r: typ)
  (h: typing sg ln g d (EMerge e e2) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FMergeL e2) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Merge h1 h2 sq -> mk_inv h1 () (fun e' h1' -> T_Merge h1' h2 sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_merge_r (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (v1 e: exp) (#t #r: typ)
  (h: typing sg ln g d (EMerge v1 e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FMergeR v1) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Merge h1 h2 sq -> mk_inv h2 () (fun e' h2' -> T_Merge h1 h2' sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_select (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (k: key) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (ESelect k e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FSelect k) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Select h1 sq -> mk_inv h1 () (fun e' h1' -> T_Select h1' sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_restrict (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (k: key) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (ERestrict k e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FRestrict k) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Restrict h1 sq -> mk_inv h1 () (fun e' h1' -> T_Restrict h1' sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_inject (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (k: key) (r0: typ) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (EInject k r0 e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FInject k r0) e t r)
         (requires not (V.is_value sg (EInject k r0 e))) (ensures fun _ -> True) =
  match h with
  | T_Inject h1 sq1 sq2 -> mk_inv h1 () (fun e' h1' -> T_Inject h1' sq1 sq2)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_weaken (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (k: key) (t1: typ) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (EWeaken k t1 e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FWeaken k t1) e t r)
         (requires not (V.is_value sg (EWeaken k t1 e))) (ensures fun _ -> True) =
  match h with
  | T_Weaken h1 sq1 sq2 -> mk_inv h1 () (fun e' h1' -> T_Weaken h1' sq1 sq2)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_absurd (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (t1: typ) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (EAbsurd t1 e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FAbsurd t1) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Absurd h1 sq -> mk_inv h1 () (fun e' h1' -> T_Absurd h1' sq)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_let (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (t1: typ) (e2 e: exp) (#t #r: typ)
  (h: typing sg ln g d (ELet t1 e e2) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FLet t1 e2) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Let sq h1 h2 -> mk_inv h1 () (fun e' h1' -> T_Let sq h1' h2)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_case (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (vs es: list exp) (dt: dtree) (e: exp)
  (#t #r: typ) (h: typing sg ln g d (ECase (L.append vs (e :: es)) dt) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FCase vs es dt) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Case hes hdt ->
    let p = exps_split vs e es hes in
    mk_inv p.xh_h () (fun e' h' -> T_Case (p.xh_fill e' h') hdt)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_guard (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (th: list exp) (dt1 dt2: dtree) (e: exp)
  (#t #r: typ) (h: typing sg ln g d (EMatch th (DGuard e dt1 dt2)) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FGuard th dt1 dt2) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Match om hes sqv hm hdt ->
    (match hdt with
     | TD_Guard he h1 h2 ->
       mk_inv he () (fun e' he' -> T_Match om hes sqv hm (TD_Guard he' h1 h2))
     | _ -> false_elim ())
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_letjoin (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (ts: list typ) (t1: typ) (e1 e: exp)
  (#t #r: typ) (h: typing sg ln g d (ELetJoin ts t1 e1 e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FLetJoin ts t1 e1) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_LetJoin sq h1 h2 -> mk_inv h2 () (fun e' h2' -> T_LetJoin sq h1 h2')
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_jump (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (j: nat) (vs es: list exp) (e: exp)
  (#t #r: typ) (h: typing sg ln g d (EJump j (L.append vs (e :: es))) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FJump j vs es) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Jump sq1 sq2 hes ->
    let p = exps_split vs e es hes in
    mk_inv p.xh_h () (fun e' h' -> T_Jump sq1 sq2 (p.xh_fill e' h'))
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_perform (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (k: key) (op: opname) (ss: list typ)
  (e: exp) (#t #r: typ) (h: typing sg ln g d (EPerform k op ss e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FPerform k op ss) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Perform ts sq1 sq2 sq3 h1 -> mk_inv h1 () (fun e' h1' -> T_Perform ts sq1 sq2 sq3 h1')
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_handle (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (hh: handler) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (EHandle e hh) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FHandle hh) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Handle sq1 sq2 sq3 sq4 he hret hcl ->
    mk_inv he () (fun e' he' -> T_Handle sq1 sq2 sq3 sq4 he' hret hcl)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_region (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (lay: list (key & typ)) (vs es: list exp)
  (body e: exp) (#t #r: typ)
  (h: typing sg ln g d (ERegion lay (L.append vs (e :: es)) body) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FRegion lay vs es body) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Region sq1 sq2 hes hb ->
    let p = exps_split vs e es hes in
    mk_inv p.xh_h () (fun e' h' -> T_Region sq1 sq2 (p.xh_fill e' h') hb)
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_region_open (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (a: atom) (cells: list (key & exp))
  (e: exp) (#t #r: typ) (h: typing sg ln g d (ERegionOpen a cells e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FRegionOpen a cells) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_RegionOpen sq1 sq2 sq3 hc hb -> mk_inv hb () (fun e' hb' -> T_RegionOpen sq1 sq2 sq3 hc hb')
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_write_cell (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (rr: region_ref) (k: key) (e: exp)
  (#t #r: typ) (h: typing sg ln g d (EWriteCell rr k e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FWriteCell rr k) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_WriteCell sq1 sq2 h1 -> mk_inv h1 () (fun e' h1' -> T_WriteCell sq1 sq2 h1')
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

let pi_fill (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (nu: atom) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (EFill nu e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d (FFill nu) e t r) (requires True) (ensures fun _ -> True) =
  match h with
  | T_Fill sq1 sq2 h1 -> mk_inv h1 () (fun e' h1' -> T_Fill sq1 sq2 h1')
  | T_Chain _ _ -> false_elim ()
  | T_VariantValue _ _ _ _ _ _ -> false_elim ()
  | _ -> false_elim ()

(* ** Every frame *)

let plug1_cf (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (f: frame) (e: exp) (#t #r: typ)
  (h: typing sg ln g d (plug1 f e) t r{~(T_Conv? h)})
  : Pure (plug1_inv sg ln g d f e t r)
         (requires sig_ok sg /\ not (V.is_value sg (plug1 f e)))
         (ensures fun _ -> True) =
  match f with
  | FAppArg fn -> pi_app_arg fn e h
  | FAppFun v -> pi_app_fun v e h
  | FTyApp sa -> pi_tyapp sa e h
  | FCApp -> pi_capp e h
  | FOpenEff r' -> pi_openeff r' e h
  | FOpenEffC r' -> pi_openeffc r' e h
  | FExtendL k e2 -> pi_extend_l k e2 e h
  | FExtendR k v1 -> pi_extend_r k v1 e h
  | FUpdateL k e2 -> pi_update_l k e2 e h
  | FUpdateR k v1 -> pi_update_r k v1 e h
  | FMergeL e2 -> pi_merge_l e2 e h
  | FMergeR v1 -> pi_merge_r v1 e h
  | FSelect k -> pi_select k e h
  | FRestrict k -> pi_restrict k e h
  | FInject k r0 -> pi_inject k r0 e h
  | FWeaken k t1 -> pi_weaken k t1 e h
  | FAbsurd t1 -> pi_absurd t1 e h
  | FLet t1 e2 -> pi_let t1 e2 e h
  | FCase vs es dt -> pi_case vs es dt e h
  | FGuard th dt1 dt2 -> pi_guard th dt1 dt2 e h
  | FLetJoin ts t1 e1 -> pi_letjoin ts t1 e1 e h
  | FJump j vs es -> pi_jump j vs es e h
  | FPerform k op ss -> pi_perform k op ss e h
  | FHandle hh -> pi_handle hh e h
  | FRegion lay vs es body -> pi_region lay vs es body e h
  | FRegionOpen a cells -> pi_region_open a cells e h
  | FWriteCell rr k -> pi_write_cell rr k e h
  | FFill nu -> pi_fill nu e h

let plug1_typing #sg #ln #g #d #f #e #t #r h =
  if V.is_value sg (plug1 f e) then plug1_not_value sg f e;
  typing_regular h;
  let cf = strip_conv h in
  plug1_inv_conv (plug1_cf f e cf.cf_h) t r

(* * Tail contexts *)

let rec tl_jctx_length fs pre =
  match fs, pre with
  | [], [] -> ()
  | _ :: fs', _ :: pre' -> tl_jctx_length fs' pre'

let tl_frames_cons (f: frame) (fs: list frame)
  : Lemma (requires tl_frames (f :: fs)) (ensures FLetJoin? f /\ tl_frames fs) = ()

(* No `letjoin` is a chain, so every term keeps its cursor. *)
let letjoin_cursor_kept (sg: sig) (ts: list typ) (t: typ) (e1 e e': exp)
  : Lemma (cursor_kept sg (ELetJoin ts t e1 e) (ELetJoin ts t e1 e')) = ()

let letjoin_not_value (sg: sig) (ts: list typ) (t: typ) (e1 e: exp)
  : Lemma (not (V.is_value sg (plug1 (FLetJoin ts t e1) e))) = ()

let rec tl_typing #sg #ln #g #d #fs #e #t #r h
  : Pure (tl_inv sg ln g d fs e t r)
         (requires sig_ok sg /\ wf_ctx sg g /\ tl_frames fs)
         (ensures fun _ -> True)
         (decreases fs) =
  match fs with
  | [] ->
    { pre = []; tl_t = t; tl_r = r; tl_hole = h; tl_pre = ();
      tl_fill = (fun (e': exp) (h': typing sg ln g d e' t r) -> h') }
  | f :: fs' ->
    tl_frames_cons f fs';
    let FLetJoin ts t1 e1 = f in
    letjoin_not_value sg ts t1 e1 e;
    let h0 : typing sg ln g d (plug fs' (plug1 f e)) t r = h in
    let p1 = tl_typing #sg #ln #g #d #fs' #(plug1 f e) #t #r h0 in
    let p2 = plug1_typing #sg #ln #g #(L.append p1.pre d) #f #e #p1.tl_t #p1.tl_r p1.tl_hole in
    let pre = (ts, t1, p2.hr) :: p1.pre in
    let hole : typing sg ln g (L.append pre d) e p2.ht p2.hr = p2.hole in
    { pre = pre; tl_t = p2.ht; tl_r = p2.hr; tl_hole = hole; tl_pre = ();
      tl_fill = (fun (e': exp) (h': typing sg ln g (L.append pre d) e' p2.ht p2.hr) ->
                   let h2 : typing sg ln g p2.hd e' p2.ht p2.hr = h' in
                   letjoin_cursor_kept sg ts t1 e1 e e';
                   let h3 : typing sg ln g (L.append p1.pre d) (plug1 f e') p1.tl_t p1.tl_r =
                     p2.fill e' h2 in
                   let h4 : typing sg ln g d (plug fs' (plug1 f e')) t r = p1.tl_fill (plug1 f e') h3 in
                   (h4 <: typing sg ln g d (plug fs e') t r)) }

let rec nth_append pre d n =
  match pre with
  | [] -> ()
  | _ :: pre' -> if n = 0 then () else nth_append pre' d (n - 1)

(* * Inversions *)

let inv_global #sg #ln #g #d #q #ks #t #r h vi =
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Global _ _ _ -> ty_eq_sym (kinst_ty ks vi.vl_ty) t
  | T_Chain _ _ -> chain_cursor_global sg q ks
  | _ -> ()

let inv_jump #sg #ln #g #d #n #es #t #r h =
  let cf = strip_conv h in
  match cf.cf_h with
  | T_Jump #_ #_ #_ #_ #_ #_ #ts #t0 #r0 _ _ hes ->
    { j_ts = ts; j_t = t0; j_r = r0; j_args = hes; j_facts = () }

let row_empty_ok (sg: sig) (g: ctx) : Lemma (check sg g TRowEmpty (KRow EEffect)) = ()

let foreign_redex_typing #sg #ln #g #d #e #t #r h s th =
  let hc = chain_normal h in
  row_empty_ok sg g;
  let hc' = value_chain_typing hc [] TRowEmpty in
  T_Chain #sg #ln #g #[] #e #s #th #TRowEmpty hc' ()

let foreign_redex_typed #sg #ln #g #d #e #t #r h s th =
  let h' = foreign_redex_typing h s th in
  FStar.Classical.exists_intro (fun (_: typing sg ln g [] e (sub_ty th s) TRowEmpty) -> True) h'
