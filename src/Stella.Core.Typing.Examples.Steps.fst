(* Each derivation is built bottom-up, as in `Stella.Core.Typing.Examples`.
   A chain is built node by node by the helpers below, which read the
   cursor by matching on it; the facts they require are closed and hold by
   normalization.

   The frame at a type variable has no type: every derivation of it ends
   in `T_RegionOpen` under conversions, so its row is `ty_eq` to a type
   kinded in the closed context, which every substitution fixes. Two
   substitutions sending the variable to two rows that differ would then
   make them equal. *)
module Stella.Core.Typing.Examples.Steps
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Region
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Facts
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Examples
module L = FStar.List.Tot
module V = Stella.Core.Value

let retype (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t1 #r1: typ) (t2 r2: typ)
           (h: typing ex_sig [] g d tl e t1 r1)
  : Pure (typing ex_sig [] g d tl e t2 r2) (requires t1 == t2 /\ r1 == r2) (ensures fun _ -> True) =
  h

(* * Building chains *)

let chain_head (g: ctx) (d: jctx) (r: typ) (q: qname)
  : Pure (chain_typing ex_sig [] g d r (EGlobal q []))
         (requires check ex_sig g r (KRow EEffect) /\
                   (match global_scheme ex_sig q with Some (_, nk, _) -> nk == 0 | None -> False))
         (ensures fun _ -> True) =
  match global_scheme ex_sig q with
  | Some (c, nk, t) -> TS_Head #ex_sig #[] #g #d #r #q #[] #c #nk #t () () ()

let chain_ty (#g: ctx) (#d: jctx) (#r: typ) (#e: exp) (s: typ) (h: chain_typing ex_sig [] g d r e)
  : Pure (chain_typing ex_sig [] g d r (ETyApp e s))
         (requires (match chain_cursor ex_sig e with
                    | Some (TForall k _, _) -> check ex_sig g s k
                    | _ -> False))
         (ensures fun _ -> True) =
  match chain_cursor ex_sig e with
  | Some (TForall k t, th) -> TS_Ty #ex_sig #[] #g #d #r #e #s #k #t #th h () ()

let chain_val (#g: ctx) (#d: jctx) (#r: typ) (#e: exp) (#v: exp) (t1: typ)
  (h: chain_typing ex_sig [] g d r e) (hv: typing ex_sig [] g d false v t1 r)
  : Pure (chain_typing ex_sig [] g d r (EApp e v))
         (requires (match chain_cursor ex_sig e with
                    | Some (t, th) ->
                      (match as_function ex_sig t with
                       | Some (a, _, _) -> sub_ty th a == t1
                       | None -> False)
                    | None -> False))
         (ensures fun _ -> True) =
  match chain_cursor ex_sig e with
  | Some (t, th) ->
    (match as_function ex_sig t with
     | Some (a, ra, b) ->
       TS_Val #ex_sig #[] #g #d #r #e #v #t #th #a #ra #b h () hv)

let chain_typed (#g: ctx) (#d: jctx) (#r: typ) (#e: exp) (tl: bool) (t: typ)
  (h: chain_typing ex_sig [] g d r e)
  : Pure (typing ex_sig [] g d tl e t r)
         (requires (match chain_cursor ex_sig e with
                    | Some (s, th) -> sub_ty th s == t
                    | None -> False))
         (ensures fun _ -> True) =
  match chain_cursor ex_sig e with
  | Some (s, th) -> retype t r (T_Chain #ex_sig #[] #g #d #tl #e #s #th #r h ())

let lit_typing (g: ctx) (d: jctx) (tl: bool) (c: lit) (t r: typ)
  : Pure (typing ex_sig [] g d tl (ELit c) t r)
         (requires lit_type c == t /\ check ex_sig g r (KRow EEffect))
         (ensures fun _ -> True) =
  retype t r (T_Lit #ex_sig #[] #g #d #tl #c #r ())

(* * Chains at a non-empty row *)

let g0 : ctx = decl_ctx 0

let just_int (r: typ)
  : Pure (chain_typing ex_sig [] g0 [] r (ETyApp (EGlobal (prelude "Just") []) t_int))
         (requires check ex_sig g0 r (KRow EEffect)) (ensures fun _ -> True) =
  assert_norm (match global_scheme ex_sig (prelude "Just") with
               | Some (_, nk, _) -> nk == 0
               | None -> False);
  let h0 = chain_head g0 [] r (prelude "Just") in
  assert_norm (match chain_cursor ex_sig (EGlobal (prelude "Just") []) with
               | Some (TForall k _, _) -> check ex_sig g0 t_int k
               | _ -> False);
  chain_ty t_int h0

let just_one_chain (r: typ)
  : Pure (chain_typing ex_sig [] g0 [] r just_one)
         (requires check ex_sig g0 r (KRow EEffect)) (ensures fun _ -> True) =
  let h1 = just_int r in
  assert_norm (match chain_cursor ex_sig (ETyApp (EGlobal (prelude "Just") []) t_int) with
               | Some (t, th) ->
                 (match as_function ex_sig t with
                  | Some (a, _, _) -> sub_ty th a == t_int
                  | None -> False)
               | None -> False);
  chain_val t_int h1 (lit_typing g0 [] false (LInt 1l) t_int r)

let just_one_at (tl: bool) (r: typ)
  : Pure (typing ex_sig [] g0 [] tl just_one (maybe_ty t_int) r)
         (requires check ex_sig g0 r (KRow EEffect)) (ensures fun _ -> True) =
  assert_norm (match chain_cursor ex_sig just_one with
               | Some (s, th) -> sub_ty th s == maybe_ty t_int
               | None -> False);
  chain_typed tl (maybe_ty t_int) (just_one_chain r)

let open_just_one_typing =
  assert_norm (check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g0 partial_row (KRow EEffect));
  assert_norm (check ex_sig g0 (maybe_ty t_int) KType);
  assert_norm (entails (hyps g0) (CDisj TRowEmpty partial_row));
  assert_norm (ty_eq (TRowUnion TRowEmpty partial_row) partial_row);
  ty_eq_refl (maybe_ty t_int);
  let h : typing ex_sig [] g0 [] true open_just_one (maybe_ty t_int) (TRowUnion TRowEmpty partial_row) =
    T_OpenEffC (just_one_at false TRowEmpty) ()
  in
  T_Conv h () ()

let just_one_typing =
  assert_norm (check ex_sig g0 partial_row (KRow EEffect));
  just_one_at true partial_row

let konst_one_value () = assert_norm (V.is_value ex_sig konst_one)

let konst_int (r: typ)
  : Pure (chain_typing ex_sig [] g0 [] r (ETyApp (EGlobal (prelude "konst") []) t_int))
         (requires check ex_sig g0 r (KRow EEffect)) (ensures fun _ -> True) =
  assert_norm (match global_scheme ex_sig (prelude "konst") with
               | Some (_, nk, _) -> nk == 0
               | None -> False);
  let h0 = chain_head g0 [] r (prelude "konst") in
  assert_norm (match chain_cursor ex_sig (EGlobal (prelude "konst") []) with
               | Some (TForall k _, _) -> check ex_sig g0 t_int k
               | _ -> False);
  chain_ty t_int h0

let konst_one_chain (r: typ)
  : Pure (chain_typing ex_sig [] g0 [] r konst_one)
         (requires check ex_sig g0 r (KRow EEffect)) (ensures fun _ -> True) =
  let h1 = konst_int r in
  assert_norm (match chain_cursor ex_sig (ETyApp (EGlobal (prelude "konst") []) t_int) with
               | Some (t, th) ->
                 (match as_function ex_sig t with
                  | Some (a, _, _) -> sub_ty th a == t_int
                  | None -> False)
               | None -> False);
  chain_val t_int h1 (lit_typing g0 [] false (LInt 1l) t_int r)

let konst_one_typing =
  assert_norm (check ex_sig g0 partial_row (KRow EEffect));
  assert_norm (match chain_cursor ex_sig konst_one with
               | Some (s, th) -> sub_ty th s == t_fun t_int TRowEmpty t_int
               | None -> False);
  chain_typed true (t_fun t_int TRowEmpty t_int) (konst_one_chain partial_row)

let konst_one_two_redex () = assert_norm (V.foreign_redex ex_sig konst_one_two)

let konst_one_two_typing =
  assert_norm (check ex_sig g0 partial_row (KRow EEffect));
  assert_norm (match chain_cursor ex_sig konst_one with
               | Some (t, th) ->
                 (match as_function ex_sig t with
                  | Some (a, _, _) -> sub_ty th a == t_int
                  | None -> False)
               | None -> False);
  let h = chain_val t_int (konst_one_chain partial_row)
            (lit_typing g0 [] false (LInt 2l) t_int partial_row) in
  assert_norm (match chain_cursor ex_sig konst_one_two with
               | Some (s, th) -> sub_ty th s == t_int
               | None -> False);
  chain_typed true t_int h

(* * Region frames *)

(* The frame at a type variable. *)

let rec frame_row_closed (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t #r: typ)
  (a: atom) (cs: list (key & exp)) (b: exp) (h: typing ex_sig [] g d tl e t r)
  : Lemma (requires e == ERegionOpen a cs b)
          (ensures exists (r0: typ). ty_eq r0 r /\ check ex_sig (closed_ctx g.regions) r0 (KRow EEffect))
          (decreases h) =
  match h with
  | T_RegionOpen _ _ _ _ _ -> ty_eq_refl r
  | T_Conv #_ #_ #_ #_ #_ #_ #_ #r1 h' _ _ ->
    frame_row_closed a cs b h';
    introduce forall (r0: typ). ty_eq r0 r1 ==> ty_eq r0 r
    with introduce _ ==> _
    with ty_eq_trans r0 r1 r

let rec lam_frame_row_closed (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t #r: typ)
  (t1 r': typ) (a: atom) (cs: list (key & exp)) (b: exp) (h: typing ex_sig [] g d tl e t r)
  : Lemma (requires e == ELam t1 r' (ERegionOpen a cs b))
          (ensures exists (r0: typ). ty_eq r0 r' /\ check ex_sig (closed_ctx g.regions) r0 (KRow EEffect))
          (decreases h) =
  match h with
  | T_Lam _ _ hb -> frame_row_closed a cs b hb
  | T_Conv h' _ _ -> lam_frame_row_closed t1 r' a cs b h'

let rec tylam_frame_row_closed (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t #r: typ)
  (k: kind) (t1 r': typ) (a: atom) (cs: list (key & exp)) (b: exp) (h: typing ex_sig [] g d tl e t r)
  : Lemma (requires e == ETyLam k (ELam t1 r' (ERegionOpen a cs b)))
          (ensures exists (r0: typ).
                     ty_eq r0 r' /\ check ex_sig (closed_ctx (push_tvar g k).regions) r0 (KRow EEffect))
          (decreases h) =
  match h with
  | T_TyLam _ _ _ hb -> lam_frame_row_closed t1 r' a cs b hb
  | T_Conv h' _ _ -> tylam_frame_row_closed k t1 r' a cs b h'

(* A closed row is no type variable: two substitutions fix it and send the
   variable to `()` and to `( Partial )`. *)
let closed_not_var (rs: list (atom & layout)) (r0: typ) (i: nat)
  : Lemma (requires check ex_sig (closed_ctx rs) r0 (KRow EEffect) /\ ty_eq r0 (TVar i))
          (ensures False) =
  let s1 : tsub = fun _ -> TRowEmpty in
  let s2 : tsub = fun _ -> partial_row in
  check_closed_sub ex_sig rs r0 (KRow EEffect) s1;
  check_closed_sub ex_sig rs r0 (KRow EEffect) s2;
  ty_eq_sub s1 r0 (TVar i);
  ty_eq_sub s2 r0 (TVar i);
  assert (ty_eq r0 TRowEmpty /\ ty_eq r0 partial_row);
  ty_eq_sym r0 TRowEmpty;
  ty_eq_trans TRowEmpty r0 partial_row;
  assert_norm (not (ty_eq TRowEmpty partial_row))

let frame_at_var_untypable #d #tl #t #r h =
  tylam_frame_row_closed (KRow EEffect) t_unit (TVar 0) reg_a [] (EGlobal prim_unit_ctor []) h;
  let rs = (push_tvar g_run (KRow EEffect)).regions in
  introduce forall (r0: typ). ty_eq r0 (TVar 0) /\ check ex_sig (closed_ctx rs) r0 (KRow EEffect) ==> False
  with introduce _ ==> _
  with closed_not_var rs r0 0

(* The contexts of the body of `frame_fn`, under `r` and `u`, and of its
   instance, under `u`. *)
let g_tv : ctx = push_tvar g_run (KRow EEffect)

let g_tv_u : ctx = push_var g_tv t_unit

let g_u : ctx = push_var g_run t_unit

(* The frame, in a context whose regions are those of `g_run`. *)
let frame_in (g: ctx)
  : Pure (typing ex_sig [] g [] false frame t_unit TRowEmpty)
         (requires g.regions == [(reg_a, [])] /\ check ex_sig g region_row (KRow EEffect))
         (ensures fun _ -> True) =
  assert_norm (check ex_sig (closed_ctx [(reg_a, [])]) t_unit KType);
  assert_norm (check ex_sig (closed_ctx [(reg_a, [])]) TRowEmpty (KRow EEffect));
  assert_norm (~(L.mem reg_a (frn_ty t_unit @ frn_ty TRowEmpty)));
  assert_norm (global_type ex_sig prim_unit_ctor == Some (0, t_unit));
  assert_norm (kinst_ty [] t_unit == t_unit);
  assert_norm (region_row == TRowExt (EntRegion (RFree reg_a)) TRowEmpty);
  let hb : typing ex_sig [] g [] true (EGlobal prim_unit_ctor []) (kinst_ty [] t_unit) region_row =
    T_Global #ex_sig #[] #g #[] #true #prim_unit_ctor #[] #0 #t_unit #region_row () () ()
  in
  T_RegionOpen #ex_sig #[] #g #[] #false #reg_a #[] #(EGlobal prim_unit_ctor []) #[] #t_unit
    #TRowEmpty () () () TC_Nil (retype t_unit region_row hb)

let frame_contractum_inst () =
  assert_norm (subst1_ty_exp region_row frame_fn == frame_contractum)

let frame_typing_under_var =
  assert_norm (g_tv_u.regions == [(reg_a, [])]);
  assert_norm (check ex_sig g_tv_u region_row (KRow EEffect));
  frame_in g_tv_u

let frame_typing_inst =
  assert_norm (g_u.regions == [(reg_a, [])]);
  assert_norm (check ex_sig g_u region_row (KRow EEffect));
  frame_in g_u

(* `openEffC [ρ] frame : Unit ! ρ`, `ρ` disjoint from `()`. *)
let open_frame (g: ctx) (r: typ) (hf: typing ex_sig [] g [] false frame t_unit TRowEmpty)
  : Pure (typing ex_sig [] g [] true (EOpenEffC r frame) t_unit r)
         (requires entails (hyps g) (CDisj TRowEmpty r) /\ check ex_sig g r (KRow EEffect) /\
                   check ex_sig g t_unit KType)
         (ensures fun _ -> True) =
  let h : typing ex_sig [] g [] true (EOpenEffC r frame) t_unit (TRowUnion TRowEmpty r) =
    T_OpenEffC hf ()
  in
  ty_eq_refl t_unit;
  union_empty_l r;
  T_Conv h () ()

let frame_fn_typing
  : typing ex_sig [] g_tv [] true frame_fn (t_fun t_unit (TVar 0) t_unit) TRowEmpty =
  assert_norm (entails (hyps g_tv_u) (CDisj TRowEmpty (TVar 0)));
  assert_norm (check ex_sig g_tv_u (TVar 0) (KRow EEffect));
  assert_norm (check ex_sig g_tv_u t_unit KType);
  assert_norm (check ex_sig g_tv t_unit KType /\ check ex_sig g_tv (TVar 0) (KRow EEffect));
  assert_norm (check ex_sig g_tv TRowEmpty (KRow EEffect));
  T_Lam () () (open_frame g_tv_u (TVar 0) frame_typing_under_var)

let frame_redex_typing =
  assert_norm (kind_wf g_run.nk (KRow EEffect) /\ qkind g_run.nk (KRow EEffect));
  assert_norm (value_form ex_sig frame_fn);
  assert_norm (check ex_sig g_run TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g_run region_row (KRow EEffect));
  assert_norm (subst1_ty region_row (t_fun t_unit (TVar 0) t_unit) == t_fun t_unit region_row t_unit);
  let hl : typing ex_sig [] g_run [] false (ETyLam (KRow EEffect) frame_fn)
             (TForall (KRow EEffect) (t_fun t_unit (TVar 0) t_unit)) TRowEmpty =
    T_TyLam () () () frame_fn_typing
  in
  retype (t_fun t_unit region_row t_unit) TRowEmpty (T_TyApp hl ())

let frame_contractum_typing =
  assert_norm (entails (hyps g_u) (CDisj TRowEmpty region_row));
  assert_norm (check ex_sig g_u region_row (KRow EEffect));
  assert_norm (check ex_sig g_u t_unit KType);
  assert_norm (check ex_sig g_run t_unit KType /\ check ex_sig g_run region_row (KRow EEffect));
  assert_norm (check ex_sig g_run TRowEmpty (KRow EEffect));
  T_Lam () () (open_frame g_u region_row frame_typing_inst)

(* * A variant value at its residual type *)

let row_yx : typ = TRowExt (EntTy key_y t_bool) row_xi

let om_case : octx = scrut_occs 0 [t_variant row_yx]

let inj_y_typing : typing ex_sig [] g0 [] false inj_y (t_variant row_yx) TRowEmpty =
  assert_norm (check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (key_ok ex_sig g0 key_y EType /\ entails (hyps g0) (CLacks key_y row_xi));
  assert_norm (check ex_sig g0 row_xi (KRow EType));
  T_Inject (lit_typing g0 [] false (LBool true) t_bool TRowEmpty) () ()

(* The branch `x -> inject y [()] false`. *)
let case_branch
  : dt_typing ex_sig [] g0 [] true ((OVariant (OScrut 0) key_x, t_int) :: om_case)
      (DLeaf (EInject key_y TRowEmpty (ELit (LBool false)))) (t_variant row_yb) TRowEmpty =
  assert_norm (check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (key_ok ex_sig g0 key_y EType /\ entails (hyps g0) (CLacks key_y TRowEmpty));
  assert_norm (check ex_sig g0 TRowEmpty (KRow EType));
  TD_Leaf (T_Inject (lit_typing g0 [] false (LBool false) t_bool TRowEmpty) () ())

(* The default `bind z = s0 in z`, `s0` at the residual. *)
let case_default
  : dt_typing ex_sig [] g0 [] true ((OScrut 0, t_variant row_yb) :: om_case)
      (DBind (OScrut 0) (DLeaf (EVar 0))) (t_variant row_yb) TRowEmpty =
  let om' = (OScrut 0, t_variant row_yb) :: om_case in
  let g' = push_var g0 (t_variant row_yb) in
  assert_norm (L.assoc (OScrut 0) om' == Some (t_variant row_yb));
  assert_norm (L.nth g'.vars 0 == Some (t_variant row_yb));
  assert_norm (check ex_sig g' TRowEmpty (KRow EEffect));
  let ho : occ_typing ex_sig g0 om' (OScrut 0) (t_variant row_yb) = TO_Lookup () in
  TD_Bind ho (TD_Leaf (T_Var () ()))

let case_inj_typing =
  assert_norm (check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g0 (t_variant row_yb) KType);
  assert_norm (check ex_sig g0 t_int KType);
  assert_norm (L.assoc (OScrut 0) om_case == Some (t_variant row_yx));
  assert_norm (check ex_sig g0 row_yx (KRow EType) /\ check ex_sig g0 row_yb (KRow EType));
  assert_norm (L.noRepeats [key_x]);
  assert_norm (key_split row_yx [(key_x, t_int)] row_yb);
  ty_eq_refl (t_variant row_yx);
  let ho : occ_typing ex_sig g0 om_case (OScrut 0) (t_variant row_yx) = TO_Lookup () in
  let hbr : key_brs_typing ex_sig [] g0 [] true om_case (OScrut 0) [(key_x, t_int)]
              [(key_x, DLeaf (EInject key_y TRowEmpty (ELit (LBool false))))] (t_variant row_yb)
              TRowEmpty =
    TKB_Cons () case_branch (TKB_Nil ())
  in
  let hdt : dt_typing ex_sig [] g0 [] true om_case
              (DSwitchKey (OScrut 0)
                 [(key_x, DLeaf (EInject key_y TRowEmpty (ELit (LBool false))))]
                 (Some (DBind (OScrut 0) (DLeaf (EVar 0)))))
              (t_variant row_yb) TRowEmpty =
    TD_SwitchKeyDef row_yx row_yb [(key_x, t_int)] ho () () () hbr case_default
  in
  let hes : exps_typing ex_sig [] g0 [] false TRowEmpty [inj_y] [t_variant row_yx] =
    TE_Cons inj_y_typing (TE_Nil ())
  in
  assert_norm (om_case == scrut_occs 0 [t_variant row_yx]);
  T_Case hes hdt

let inj_y_residual_typing =
  assert_norm (check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (V.is_value ex_sig inj_y /\ variant_view inj_y == Some (key_y, ELit (LBool true)));
  assert_norm (check ex_sig g0 (t_variant row_yb) KType /\ check ex_sig g0 t_bool KType /\
               L.mem (key_y, PTy (canon t_bool)) (row_entries (canon row_yb)));
  T_VariantValue #ex_sig #[] #g0 #[] #false #inj_y #key_y #(ELit (LBool true)) #t_bool #TRowEmpty
    row_yx row_yb inj_y_typing () (lit_typing g0 [] false (LBool true) t_bool TRowEmpty) ()

(* A variant with a dangling region reference: the only rule that
   reads its annotation is `T_Inject`, whose kinding of it fails, since a
   kinded type is locally closed; `T_Conv` and `T_VariantValue` rest on a
   derivation of the same term. *)
let rec inj_dangling_inv (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t #r: typ)
  (h: typing ex_sig [] g d tl e t r)
  : Lemma (requires e == inj_dangling) (ensures False) (decreases h) =
  match h with
  | T_Inject _ _ _ ->
    check_lc ex_sig g row_dangling (KRow EType);
    assert_norm (not (lc_ty row_dangling))
  | T_Conv h' _ _ -> inj_dangling_inv h'
  | T_VariantValue _ _ h' _ _ _ -> inj_dangling_inv h'

let inj_dangling_untypable #g #d #tl #t #r h = inj_dangling_inv h

(* * `switchKey` under a substitution *)

(* A term binder changes nothing kinding reads. *)
let push_var_kinding (g: ctx) (t: typ)
  : Lemma (forall (u: typ) (k: kind). check ex_sig (push_var g t) u k == check ex_sig g u k) =
  same_kinding_push_var g t;
  introduce forall (u: typ) (k: kind). check ex_sig (push_var g t) u k == check ex_sig g u k
  with check_same_kinding ex_sig g (push_var g t) u k

(* `switch_fn c : Variant ( y : Int | c ) -> Int` in a context `g` that
   kinds `( y : Int | c )`. *)
let switch_fn_typing (g: ctx) (c: typ)
  : Pure (typing ex_sig [] g [] true (switch_fn c)
            (t_fun (t_variant (TRowExt (EntTy key_y t_int) c)) TRowEmpty t_int) TRowEmpty)
         (requires check ex_sig g (TRowExt (EntTy key_y t_int) c) (KRow EType) /\
                   check ex_sig g c (KRow EType) /\ check ex_sig g TRowEmpty (KRow EEffect) /\
                   check ex_sig g t_int KType /\
                   check ex_sig g (t_variant (TRowExt (EntTy key_y t_int) c)) KType)
         (ensures fun _ -> True) =
  let vr = TRowExt (EntTy key_y t_int) c in
  let gx = push_var g (t_variant vr) in
  let om = scrut_occs 0 [t_variant vr] in
  push_var_kinding g (t_variant vr);
  let hx : typing ex_sig [] gx [] false (EVar 0) (t_variant vr) TRowEmpty = T_Var () () in
  let hes : exps_typing ex_sig [] gx [] false TRowEmpty [EVar 0] [t_variant vr] =
    TE_Cons hx (TE_Nil ())
  in
  let ho : occ_typing ex_sig gx om (OScrut 0) (t_variant vr) = TO_Lookup () in
  let hbr : key_brs_typing ex_sig [] gx [] true om (OScrut 0) [(key_y, t_int)]
              [(key_y, DLeaf (lit_int 0l))] t_int TRowEmpty =
    TKB_Cons () (TD_Leaf (lit_typing gx [] true (LInt 0l) t_int TRowEmpty)) (TKB_Nil ())
  in
  let om' = (OScrut 0, t_variant c) :: om in
  let gz = push_var gx (t_variant c) in
  push_var_kinding gx (t_variant c);
  let hoz : occ_typing ex_sig gx om' (OScrut 0) (t_variant c) = TO_Lookup () in
  let hdf : dt_typing ex_sig [] gx [] true om' (DBind (OScrut 0) (DLeaf (lit_int 1l))) t_int
              TRowEmpty =
    TD_Bind hoz (TD_Leaf (lit_typing gz [] true (LInt 1l) t_int TRowEmpty))
  in
  assert_norm (L.noRepeats [key_y]);
  assert_norm (brs_row [(key_y, t_int)] c == vr);
  ty_eq_refl vr;
  ty_eq_refl (t_variant vr);
  let hdt : dt_typing ex_sig [] gx [] true om
              (DSwitchKey (OScrut 0) [(key_y, DLeaf (lit_int 0l))]
                 (Some (DBind (OScrut 0) (DLeaf (lit_int 1l)))))
              t_int TRowEmpty =
    TD_SwitchKeyDef vr c [(key_y, t_int)] ho () () () hbr hdf
  in
  T_Lam () () (T_Case hes hdt)

let switch_contractum_inst () =
  assert_norm (subst1_ty_exp row_yi (ECLam (lacks_y (TVar 0)) (switch_fn (TVar 0))) ==
               switch_contractum)

(* `Variant ( y : Int | r ) -> Int` *)
let switch_fn_ty : typ = t_fun (t_variant (TRowExt (EntTy key_y t_int) (TVar 0))) TRowEmpty t_int

(* Under `r : Row Type` and `y ∉ r`. *)
let g_r : ctx = push_tvar g0 (KRow EType)

let g_ra : ctx = add_assump g_r (lacks_y (TVar 0))

let switch_redex_typing =
  assert_norm (check ex_sig g_ra (TRowExt (EntTy key_y t_int) (TVar 0)) (KRow EType) /\
               check ex_sig g_ra (TVar 0) (KRow EType) /\ check ex_sig g_ra TRowEmpty (KRow EEffect) /\
               check ex_sig g_ra t_int KType /\
               check ex_sig g_ra (t_variant (TRowExt (EntTy key_y t_int) (TVar 0))) KType);
  assert_norm (constr_ok ex_sig g_r (lacks_y (TVar 0)));
  assert_norm (value_form ex_sig (switch_fn (TVar 0)));
  assert_norm (value_form ex_sig (ECLam (lacks_y (TVar 0)) (switch_fn (TVar 0))));
  assert_norm (check ex_sig g_r TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (kind_wf g0.nk (KRow EType) /\ qkind g0.nk (KRow EType));
  assert_norm (check ex_sig g0 row_yi (KRow EType));
  let hc : typing ex_sig [] g_r [] true (ECLam (lacks_y (TVar 0)) (switch_fn (TVar 0)))
             (TConstr (lacks_y (TVar 0)) switch_fn_ty) TRowEmpty =
    T_CLam () () () (switch_fn_typing g_ra (TVar 0))
  in
  let hl : typing ex_sig [] g0 [] false
             (ETyLam (KRow EType) (ECLam (lacks_y (TVar 0)) (switch_fn (TVar 0))))
             (TForall (KRow EType) (TConstr (lacks_y (TVar 0)) switch_fn_ty)) TRowEmpty =
    T_TyLam () () () hc
  in
  assert_norm (subst1_ty row_yi (TConstr (lacks_y (TVar 0)) switch_fn_ty) == switch_ty);
  retype switch_ty TRowEmpty (T_TyApp hl ())

(* Under `y ∉ ( y : Int )`. *)
let g_c : ctx = add_assump g0 (lacks_y row_yi)

let switch_contractum_typing =
  assert_norm (check ex_sig g_c (TRowExt (EntTy key_y t_int) row_yi) (KRow EType) /\
               check ex_sig g_c row_yi (KRow EType) /\ check ex_sig g_c TRowEmpty (KRow EEffect) /\
               check ex_sig g_c t_int KType /\
               check ex_sig g_c (t_variant (TRowExt (EntTy key_y t_int) row_yi)) KType);
  assert_norm (constr_ok ex_sig g0 (lacks_y row_yi));
  assert_norm (value_form ex_sig (switch_fn row_yi));
  assert_norm (check ex_sig g0 TRowEmpty (KRow EEffect));
  T_CLam () () () (switch_fn_typing g_c row_yi)
