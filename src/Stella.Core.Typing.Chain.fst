(* Proof structure.

   Applications of type constructors are compared through their head and
   their arguments: `canon` keeps both, so `ty_eq_app_inv` and
   `ty_eq_con_inv` peel one application at a time.

   Normalization is by induction on the derivation. At a node over a
   prefix `e0`, the derivation of the prefix normalizes, giving its cursor
   `⟨ σ0 ; θ0 ⟩` with `θ0(σ0)` equal to the type the node's rule reads. The
   rule reads a `forall`, a constrained type or a function type there, so
   `σ0` is one too (`remainder_*`): when the chain's cursor is defined the
   step consumes it, and in a constructor chain every other remainder is an
   instance of a data type (`ctor_chain_saturated`), which is none of
   them. The type equality then splits by the inversion lemmas, and a
   value argument is converted to the instance of the domain, kinded by
   `spine_cursor_fun_regular`. *)
module Stella.Core.Typing.Chain
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
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
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Regularity
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

(* Type equality of applications. *)

let rec app_head (t: typ) : Tot (option (qname & list kind)) (decreases t) =
  match t with
  | TCon q ks -> Some (q, ks)
  | TApp f _ -> app_head f
  | _ -> None

let rec app_args (t: typ) : Tot (list typ) (decreases t) =
  match t with
  | TApp f x -> L.append (app_args f) [x]
  | _ -> []

let rec tys_eq_append (a a' b b': list typ)
  : Lemma (requires tys_eq a a' /\ tys_eq b b') (ensures tys_eq (L.append a b) (L.append a' b'))
          (decreases a) =
  match a, a' with
  | [], [] -> ()
  | _ :: a1, _ :: a1' -> tys_eq_append a1 a1' b b'

let rec ty_eq_app_view (a b: typ)
  : Lemma (requires ty_eq a b /\ Some? (app_head a) /\ Some? (app_head b))
          (ensures app_head a == app_head b /\ tys_eq (app_args a) (app_args b))
          (decreases a) =
  match a, b with
  | TCon q ks, TCon q' ks' -> ty_eq_con_inv q q' ks ks'
  | TApp f x, TApp f' x' ->
    ty_eq_app_inv f x f' x';
    ty_eq_app_view f f';
    tys_eq_append (app_args f) (app_args f') [x] [x']
  | _ -> ty_eq_head a b

let rec tapps_view (h: typ) (ss: list typ)
  : Lemma (requires TCon? h \/ TApp? h)
          (ensures (TCon? (tapps h ss) \/ TApp? (tapps h ss)) /\
                   app_head (tapps h ss) == app_head h /\
                   app_args (tapps h ss) == L.append (app_args h) ss)
          (decreases ss) =
  match ss with
  | [] -> LP.append_l_nil (app_args h)
  | s :: ss' ->
    tapps_view (TApp h s) ss';
    LP.append_assoc (app_args h) [s] ss'

let ty_eq_tapps_inv q q' ks ks' ss ss' =
  tapps_view (TCon q ks) ss;
  tapps_view (TCon q' ks') ss';
  ty_eq_app_view (tapps (TCon q ks) ss) (tapps (TCon q' ks') ss')

let ty_eq_tapps_binder q ks ss t =
  tapps_view (TCon q ks) ss;
  if ty_eq (tapps (TCon q ks) ss) t then ty_eq_head (tapps (TCon q ks) ss) t

(* Rows of chains. *)

let chain_fun_regular (sg: sig) (g: ctx) (e0: exp) (s0: typ) (th0: tsub) (a1 rho1 b1: typ)
  : Lemma (requires sig_ok sg /\ chain_args_ok sg g e0 /\ chain_cursor sg e0 == Some (s0, th0) /\
                    as_function sg s0 == Some (a1, rho1, b1))
          (ensures check sg g (sub_ty th0 a1) KType /\ check sg g (sub_ty th0 b1) KType /\
                   ty_eq (sub_ty th0 rho1) TRowEmpty) =
  let Some (q, ks, args) = decompose_global_app e0 in
  spine_cursor_fun_regular sg g q ks args s0 th0 a1 rho1 b1

let rec chain_typing_conv #sg #ln #g #d #r1 #e hc r2
  : Pure (chain_typing sg ln g d r2 e)
         (requires sig_ok sg /\ ty_eq r1 r2 /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) (decreases hc) =
  match hc with
  | TS_Head sq1 sq2 _ -> TS_Head sq1 sq2 ()
  | TS_Ty h0 sq1 sq2 -> TS_Ty (chain_typing_conv h0 r2) sq1 sq2
  | TS_Constr h0 sq1 sq2 -> TS_Constr (chain_typing_conv h0 r2) sq1 sq2
  | TS_Val #_ #_ #_ #_ #_ #e0 #v #s0 #th0 #a1 #rho1 #b1 h0 sq hv ->
    chain_typing_args_ok h0;
    chain_fun_regular sg g e0 s0 th0 a1 rho1 b1;
    ty_eq_refl (sub_ty th0 a1);
    let hv' : typing sg ln g d v (sub_ty th0 a1) r2 = T_Conv hv () () in
    TS_Val #sg #ln #g #d #r2 #e0 #v #s0 #th0 #a1 #rho1 #b1 (chain_typing_conv h0 r2) sq hv'

(* The prefix of a chain to normalize normalizes. *)
let prefix_normal (sg: sig) (e0: exp) (a: spine_arg)
  : Lemma (requires Some? (decompose_global_app (apply_arg e0 a)) /\
                    (Some? (chain_cursor sg (apply_arg e0 a)) \/ ctor_headed sg (apply_arg e0 a)))
          (ensures Some? (decompose_global_app e0) /\
                   (Some? (chain_cursor sg e0) \/ ctor_headed sg e0) /\
                   ctor_headed sg (apply_arg e0 a) == ctor_headed sg e0 /\
                   chain_cursor sg (apply_arg e0 a) ==
                   (match chain_cursor sg e0 with
                    | Some (t', th') -> cursor_step sg t' th' a
                    | None -> None)) =
  assert (Some? (decompose_global_app e0));
  decompose_apply_arg e0 a;
  chain_cursor_apply_arg sg e0 a

(* A constructor chain at a saturated remainder has an instance of its data
   type, which is no function type. *)
let ctor_saturated_inst (sg: sig) (e0: exp) (s0: typ) (th0: tsub)
  : Lemma (requires sig_ok sg /\ ctor_headed sg e0 /\ chain_cursor sg e0 == Some (s0, th0) /\
                    saturated sg s0)
          (ensures (exists (q: qname) (ks: list kind) (ss: list typ).
                     sub_ty th0 s0 == tapps (TCon q ks) ss /\ q =!= prim_function)) =
  let Some (c, ks, args) = decompose_global_app e0 in
  let Some ci = sg.ctors c in
  ctor_chain_saturated sg e0 c ks args ci s0 th0;
  assert (ctor_ok sg c ci);
  assert (sg.tycons prim_function <> None);
  assert (ci.ct_owner =!= prim_function)

let t_fun_tapps (t1 r t2: typ)
  : Lemma (t_fun t1 r t2 == tapps (TCon prim_function []) [t1; r; t2]) =
  assert_norm (t_fun t1 r t2 == tapps (TCon prim_function []) [t1; r; t2])

let remainder_fun (sg: sig) (e0: exp) (v: exp) (s0: typ) (th0: tsub) (t1 r t2: typ)
  : Lemma (requires sig_ok sg /\ chain_cursor sg e0 == Some (s0, th0) /\
                    ty_eq (t_fun t1 r t2) (sub_ty th0 s0) /\
                    (Some? (cursor_step sg s0 th0 (SVal v)) \/ ctor_headed sg e0))
          (ensures Some? (as_function sg s0)) =
  if None? (as_function sg s0) then begin
    match s0 with
    | TForall _ _ | TConstr _ _ -> ty_eq_head (t_fun t1 r t2) (sub_ty th0 s0)
    | _ ->
      ctor_saturated_inst sg e0 s0 th0;
      t_fun_tapps t1 r t2;
      FStar.Classical.forall_intro_3 (fun q ks ss ->
        FStar.Classical.move_requires
          (ty_eq_tapps_inv prim_function q [] ks [t1; r; t2]) ss)
  end

let remainder_binder (sg: sig) (e0: exp) (a: spine_arg) (s0: typ) (th0: tsub) (t: typ)
  : Lemma (requires sig_ok sg /\ chain_cursor sg e0 == Some (s0, th0) /\ ty_eq t (sub_ty th0 s0) /\
                    (Some? (cursor_step sg s0 th0 a) \/ ctor_headed sg e0) /\
                    ((STy? a /\ TForall? t) \/ (SConstr? a /\ TConstr? t)))
          (ensures (STy? a ==> TForall? s0) /\ (SConstr? a ==> TConstr? s0)) =
  match a, s0 with
  | STy _, TForall _ _ | SConstr, TConstr _ _ -> ()
  | _ ->
    match as_function sg s0 with
    | Some (a1, rho1, b1) ->
      as_function_sub sg th0 s0 a1 rho1 b1;
      ty_eq_head t (sub_ty th0 s0)
    | None ->
      match s0 with
      | TForall _ _ | TConstr _ _ -> ty_eq_head t (sub_ty th0 s0)
      | _ ->
        ctor_saturated_inst sg e0 s0 th0;
        ty_eq_sym t (sub_ty th0 s0);
        FStar.Classical.forall_intro_3 (fun q ks ss ->
          FStar.Classical.move_requires (ty_eq_tapps_binder q ks ss) t)

let global_type_scheme (sg: sig) (q: qname) (nk: nat) (t: typ)
  : Lemma (requires global_type sg q == Some (nk, t) /\ Some? (global_scheme sg q))
          (ensures (let Some (_, nk', t') = global_scheme sg q in nk' == nk /\ t' == t)) = ()

let variant_view_no_chain (e: exp)
  : Lemma (requires Some? (variant_view e)) (ensures None? (decompose_global_app e)) =
  match e with
  | EInject _ _ _ | EWeaken _ _ _ -> ()

(* Normalization. *)

let rec chain_normal #sg #ln #g #d #e #t #r h
  : Pure (chain_typing sg ln g [] r e)
         (requires sig_ok sg /\ Some? (decompose_global_app e) /\
                   (Some? (chain_cursor sg e) \/ ctor_headed sg e))
         (ensures fun _ ->
           match chain_cursor sg e with
           | Some (s, th) -> ty_eq t (sub_ty th s)
           | None -> False)
         (decreases h) =
  match h with
  | T_Global #_ #_ #_ #_ #q #ks #nk #t0 _ sq2 sq3 ->
    let Some (c, nk', t') = global_scheme sg q in
    global_type_scheme sg q nk t0;
    chain_cursor_global sg q ks;
    sub_ty_tvar (kinst_ty ks t0);
    ty_eq_refl (kinst_ty ks t0);
    TS_Head #sg #ln #g #[] #r #q #ks #c #nk #t0 () sq2 sq3
  | T_App #_ #_ #_ #_ #e1 #e2 #t1 #t2 h1 h2 ->
    prefix_normal sg e1 (SVal e2);
    let hc1 = chain_normal h1 in
    let Some (s1, th1) = chain_cursor sg e1 in
    remainder_fun sg e1 e2 s1 th1 t1 r t2;
    let Some (a1, rho1, b1) = as_function sg s1 in
    as_function_sub sg th1 s1 a1 rho1 b1;
    as_function_t_fun sg (sub_ty th1 s1) (sub_ty th1 a1) (sub_ty th1 rho1) (sub_ty th1 b1);
    let f = TCon prim_function [] in
    ty_eq_app_inv (TApp (TApp f t1) r) t2 (TApp (TApp f (sub_ty th1 a1)) (sub_ty th1 rho1))
      (sub_ty th1 b1);
    ty_eq_app_inv (TApp f t1) r (TApp f (sub_ty th1 a1)) (sub_ty th1 rho1);
    ty_eq_app_inv f t1 f (sub_ty th1 a1);
    chain_typing_args_ok hc1;
    chain_fun_regular sg g e1 s1 th1 a1 rho1 b1;
    ty_eq_refl r;
    let h2' : typing sg ln g [] e2 (sub_ty th1 a1) r = T_Conv h2 () () in
    TS_Val #sg #ln #g #[] #r #e1 #e2 #s1 #th1 #a1 #rho1 #b1 hc1 () h2'
  | T_TyApp #_ #_ #_ #_ #e0 #s #k #t0 h1 _ ->
    prefix_normal sg e0 (STy s);
    let hc0 = chain_normal h1 in
    let Some (s0, th0) = chain_cursor sg e0 in
    remainder_binder sg e0 (STy s) s0 th0 (TForall k t0);
    let TForall k' b = s0 in
    ty_eq_forall_inv k k' t0 (sub_ty (up_tsub th0) b);
    ty_eq_sub (scons s tvar) t0 (sub_ty (up_tsub th0) b);
    cursor_instance_forall s th0 b;
    TS_Ty #sg #ln #g #[] #r #e0 #s #k' #b #th0 hc0 () ()
  | T_CApp #_ #_ #_ #_ #e0 #c #t0 h1 _ ->
    prefix_normal sg e0 SConstr;
    let hc0 = chain_normal h1 in
    let Some (s0, th0) = chain_cursor sg e0 in
    remainder_binder sg e0 SConstr s0 th0 (TConstr c t0);
    let TConstr c' b = s0 in
    ty_eq_constr_inv c (sub_constr th0 c') t0 (sub_ty th0 b);
    entails_constr_eq (hyps g) c (sub_constr th0 c');
    TS_Constr #sg #ln #g #[] #r #e0 #c' #b #th0 hc0 () ()
  | T_Chain #_ #_ #_ #_ #_ #t0 #th0 hc _ -> ty_eq_refl (sub_ty th0 t0); hc
  | T_Conv #_ #_ #_ #_ #_ #t1 #r1 h1 _ _ ->
    let hc = chain_normal h1 in
    let Some (s, th) = chain_cursor sg e in
    ty_eq_sym t1 t;
    ty_eq_trans t t1 (sub_ty th s);
    chain_typing_conv hc r
  | T_VariantValue _ _ _ _ _ _ -> variant_view_no_chain e; false_elim ()
  | T_Var _ _ -> false_elim ()
  | T_Lit _ -> false_elim ()
  | T_Lam _ _ _ -> false_elim ()
  | T_TyLam _ _ _ _ -> false_elim ()
  | T_CLam _ _ _ _ -> false_elim ()
  | T_Let _ _ _ -> false_elim ()
  | T_LetRec _ _ _ -> false_elim ()
  | T_Case _ _ -> false_elim ()
  | T_LetJoin _ _ _ -> false_elim ()
  | T_Jump _ _ _ -> false_elim ()
  | T_RecEmpty _ -> false_elim ()
  | T_Extend _ _ _ -> false_elim ()
  | T_Select _ _ -> false_elim ()
  | T_Restrict _ _ -> false_elim ()
  | T_Update _ _ _ -> false_elim ()
  | T_Merge _ _ _ -> false_elim ()
  | T_Inject _ _ _ -> false_elim ()
  | T_Weaken _ _ _ -> false_elim ()
  | T_Absurd _ _ -> false_elim ()
  | T_Perform _ _ _ _ _ -> false_elim ()
  | T_Handle _ _ _ _ _ _ _ -> false_elim ()
  | T_OpenEff _ _ -> false_elim ()
  | T_Region _ _ _ _ -> false_elim ()
  | T_ReadCell _ _ _ -> false_elim ()
  | T_WriteCell _ _ _ -> false_elim ()
  | T_Match _ _ _ _ _ -> false_elim ()
  | T_OpenEffC _ _ -> false_elim ()
  | T_Force _ _ -> false_elim ()
  | T_Fill _ _ _ -> false_elim ()
  | T_RegionOpen _ _ _ _ _ -> false_elim ()
  | T_Opaque _ _ -> false_elim ()

let chain_normal_exists #sg #ln #g #d #e #t #r h =
  let hc = chain_normal h in
  FStar.Classical.exists_intro (fun (_: chain_typing sg ln g [] r e) -> True) hc

let value_chain_normalizes sg e = ()
