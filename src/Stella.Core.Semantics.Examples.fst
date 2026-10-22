(* Each step is built from its rule, whose conclusion is stated with the
   operations of the rule (substitution, plugging, `foreign_config`); the
   closed facts it needs, and the equation between that conclusion and the
   term written in the interface, hold by normalization.

   `sig_ok ex_sig` is checked one table at a time, each closed fact by
   normalization. Conformance is shown before any region or location
   (`genv_ok_closed`): the definition `1` is typed by the literal rule, and
   for a typed saturated call of `length` the cursor instance is `Int`
   whatever the arguments, so the literal `δ_length` returns has the type
   condition (3) asks. A call inside the precondition of `length` is a call
   on a list, on which `δ_length` returns an outcome. *)
module Stella.Core.Semantics.Examples
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Kinst
open Stella.Core.Sig.Examples
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
module L = FStar.List.Tot
module I32 = FStar.Int32
module V = Stella.Core.Value

(* * sig_ok *)

let ex_tycons_wf () : Lemma (tycons_wf ex_sig) =
  assert_norm (tycon_ok { tc_nk = 0;
                          tc_kind = KArrow KType (KArrow (KRow EEffect) (KArrow KType KType));
                          tc_class = TcIntrinsic ClsFunction });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KArrow (KRow EType) KType;
                          tc_class = TcIntrinsic ClsRecord });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KArrow (KRow EType) KType;
                          tc_class = TcIntrinsic ClsVariant });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KType; tc_class = TcIntrinsic ClsLiteral });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KArrow KType KType; tc_class = TcIntrinsic ClsOpaque });
  assert_norm (tycon_ok { tc_nk = 0; tc_kind = KType; tc_class = TcData [prim_unit_ctor] });
  assert_norm (tycon_ok list_info);
  assert_norm (tycon_ok proxy_info);
  assert_norm (tycon_ok task_info)

let ex_effects_wf () : Lemma (effects_wf ex_sig) = assert_norm (effect_ok ex_sig console_info)

let ex_ctors_wf () : Lemma (ctors_wf ex_sig) =
  assert_norm (scheme_ok ex_sig unit_info.ct_nk unit_info.ct_ty);
  assert_norm (scheme_ok ex_sig nil_info.ct_nk nil_info.ct_ty);
  assert_norm (scheme_ok ex_sig cons_info.ct_nk cons_info.ct_ty);
  assert_norm (scheme_ok ex_sig mkproxy_info.ct_nk mkproxy_info.ct_ty);
  assert_norm (scheme_ok ex_sig mktask_info.ct_nk mktask_info.ct_ty)

let ex_foreigns_wf () : Lemma (foreigns_wf ex_sig) =
  assert_norm (scheme_ok ex_sig length_info.fr_nk length_info.fr_ty);
  assert_norm (scheme_ok ex_sig boom_info.fr_nk boom_info.fr_ty)

let ex_values_wf () : Lemma (values_wf ex_sig) =
  assert_norm (scheme_ok ex_sig one_info.vl_nk one_info.vl_ty)

let ex_globals_disjoint () : Lemma (globals_disjoint ex_sig) =
  assert_norm (ex_sig.foreigns prim_unit_ctor == None);
  assert_norm (ex_sig.foreigns (base "Nil") == None);
  assert_norm (ex_sig.foreigns (base "Cons") == None);
  assert_norm (ex_sig.foreigns (base "MkProxy") == None);
  assert_norm (ex_sig.foreigns (base "MkTask") == None);
  assert_norm (ex_sig.values prim_unit_ctor == None);
  assert_norm (ex_sig.values (base "Nil") == None);
  assert_norm (ex_sig.values (base "Cons") == None);
  assert_norm (ex_sig.values (base "MkProxy") == None);
  assert_norm (ex_sig.values (base "MkTask") == None);
  assert_norm (ex_sig.values (base "length") == None);
  assert_norm (ex_sig.values (base "boom") == None)

let ex_prim_wf () : Lemma (prim_wf ex_sig) =
  assert_norm (prim_tycon ex_sig prim_function
                 (KArrow KType (KArrow (KRow EEffect) (KArrow KType KType))) (TcIntrinsic ClsFunction));
  assert_norm (prim_tycon ex_sig prim_record (KArrow (KRow EType) KType) (TcIntrinsic ClsRecord));
  assert_norm (prim_tycon ex_sig prim_variant (KArrow (KRow EType) KType) (TcIntrinsic ClsVariant));
  assert_norm (prim_tycon ex_sig prim_int KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_number KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_string KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_char KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_boolean KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon ex_sig prim_io (KArrow KType KType) (TcIntrinsic ClsOpaque));
  assert_norm (prim_tycon ex_sig prim_unit KType (TcData [prim_unit_ctor]));
  assert_norm (ex_sig.ctors prim_unit_ctor == Some unit_info)

let ex_globals_ok () : Lemma (globals_ok ex_sig) =
  assert_norm (ctor_ok ex_sig prim_unit_ctor unit_info);
  assert_norm (ctor_ok ex_sig (base "Nil") nil_info);
  assert_norm (ctor_ok ex_sig (base "Cons") cons_info);
  assert_norm (ctor_ok ex_sig (base "MkProxy") mkproxy_info);
  assert_norm (ctor_ok ex_sig (base "MkTask") mktask_info);
  assert_norm (data_ok ex_sig prim_unit [prim_unit_ctor]);
  assert_norm (data_ok ex_sig (base "List") [base "Nil"; base "Cons"]);
  assert_norm (data_ok ex_sig (base "Proxy") [base "MkProxy"]);
  assert_norm (data_ok ex_sig (base "Task") [base "MkTask"]);
  assert_norm (arrows_pure length_info.fr_ty);
  assert_norm (arrows_pure boom_info.fr_ty)

let ex_sig_ok () =
  ex_tycons_wf (); ex_effects_wf (); ex_ctors_wf (); ex_foreigns_wf (); ex_values_wf ();
  ex_globals_disjoint (); ex_prim_wf (); ex_globals_ok ()

(* * Conformance *)

let length_q : qname = base "length"

let boom_q : qname = base "boom"

let one_q : qname = base "one"

let length_body : typ = t_fun (list_ty (TVar 0)) TRowEmpty t_int

(* The cursor of a saturated chain of `length` is `Int`: `forall a.`
   takes a type, the arrow a value, and `Int` nothing more. *)
#push-options "--fuel 3 --ifuel 1"
let length_sat (ks: list kind) (args: list spine_arg)
  : Lemma (requires spine_saturated ex_sig length_q ks args)
          (ensures (match spine_cursor ex_sig length_q ks args with
                    | Some (t, _) -> t == t_int
                    | None -> False)) =
  assert_norm (global_scheme ex_sig length_q == Some (GForeign, 0, length_info.fr_ty));
  assert_norm (kinst_ty [] length_info.fr_ty == length_info.fr_ty);
  assert_norm (as_function ex_sig length_body == Some (list_ty (TVar 0), TRowEmpty, t_int));
  assert_norm (as_function ex_sig t_int == None);
  assert_norm (as_function ex_sig length_info.fr_ty == None);
  assert_norm (saturated ex_sig t_int);
  assert_norm (not (saturated ex_sig length_body));
  assert_norm (not (saturated ex_sig length_info.fr_ty));
  match args with
  | [] -> ()
  | [a] -> ()
  | [a; b] -> ()
  | a :: b :: c :: rest ->
    (match a, b with
     | STy s, SVal _ ->
       assert (cursor ex_sig length_info.fr_ty tvar [a; b] == Some (t_int, scons s tvar))
     | _ -> ())
#pop-options

let lit_typed (ln: lctx) (g: ctx) (n: I32.t)
  : Lemma (requires check ex_sig g TRowEmpty (KRow EEffect))
          (ensures V.is_value ex_sig (ELit (LInt n)) /\ typed ex_sig ln g (ELit (LInt n)) t_int) =
  let h : typing ex_sig ln g [] (ELit (LInt n)) (lit_type (LInt n)) TRowEmpty = T_Lit () in
  let h : typing ex_sig ln g [] (ELit (LInt n)) t_int TRowEmpty = h in
  assert (typed ex_sig ln g (ELit (LInt n)) t_int)

let lit_typed_closed (ln: lctx) (rs: list (atom & layout)) (n: I32.t)
  : Lemma (V.is_value ex_sig (ELit (LInt n)) /\ typed ex_sig ln (closed_ctx rs) (ELit (LInt n)) t_int) =
  assert_norm (check ex_sig (closed_ctx rs) TRowEmpty (KRow EEffect));
  lit_typed ln (closed_ctx rs) n

(* Inside its precondition, `δ_length` returns an `Int` literal. *)
let length_impl_out (vs: list exp)
  : Lemma (requires length_pre vs)
          (ensures (exists (n: I32.t). length_impl vs == Some (FOVal (ELit (LInt n))))) =
  match vs with
  | [l] ->
    (match list_len l with
     | Some n ->
       introduce exists (m: I32.t). length_impl vs == Some (FOVal (ELit (LInt m)))
       with (I32.int_to_t (clamp31 n)) and ()
     | None -> ())

let length_call_ok (ln': lctx) (rs': list (atom & layout)) (e: exp)
  (t: typ) (th: tsub) (ks: list kind) (args: list spine_arg)
  : Lemma (requires chain_cursor ex_sig e == Some (t, th) /\
                    decompose_global_app e == Some (length_q, ks, args) /\
                    V.foreign_redex ex_sig e /\ length_pre (value_args args))
          (ensures (match length_impl (value_args args) with
                    | Some o -> outcome_ok ex_sig ln' rs' length_q (sub_ty th t) o
                    | None -> False)) =
  assert_norm (global_scheme ex_sig length_q == Some (GForeign, (0 <: nat), length_info.fr_ty));
  assert (spine_saturated ex_sig length_q ks args);
  length_sat ks args;
  assert (t == t_int);
  assert_norm (sub_ty th t_int == t_int);
  length_impl_out (value_args args);
  eliminate exists (n: I32.t). length_impl (value_args args) == Some (FOVal (ELit (LInt n)))
  with lit_typed_closed ln' rs' n

let call_ok (ln': lctx) (rs': list (atom & layout)) (e: exp)
  : Lemma (foreign_call_ok ex_sig ex_genv ln' rs' e) =
  match chain_cursor ex_sig e, decompose_global_app e with
  | Some (t, th), Some (q, ks, args) ->
    if q = length_q then begin
      assert_norm (ex_genv.gimpl length_q == Some length_impl);
      introduce (V.foreign_redex ex_sig e /\ typed ex_sig ln' (closed_ctx rs') e (sub_ty th t) /\
                 ex_genv.gpre q (value_args args)) ==>
                (match length_impl (value_args args) with
                 | Some o -> outcome_ok ex_sig ln' rs' q (sub_ty th t) o
                 | None -> False)
      with length_call_ok ln' rs' e t th ks args
    end
    else if q = boom_q then begin
      assert_norm (ex_genv.gimpl boom_q == Some boom_impl);
      assert_norm (observ_none ex_sig boom_q == false)
    end
    else ()
  | _ -> ()

let gval_one_typed () : Lemma (gval_typed ex_sig [] [] ex_genv one_q) =
  assert_norm (ex_sig.values one_q == Some one_info);
  assert_norm (ex_genv.gvals one_q == Some (lit_int 1l));
  assert_norm (check ex_sig (decl_rctx 0 []) TRowEmpty (KRow EEffect));
  lit_typed [] (decl_rctx 0 []) 1l

let ex_genv_ok ln rs =
  introduce forall (rs': list (atom & layout)) (ln': lctx) (e: exp).
    rt_ext ex_sig [] [] ln' rs' ==> foreign_call_ok ex_sig ex_genv ln' rs' e
  with introduce _ ==> _ with call_ok ln' rs' e;
  introduce forall (q: qname). gval_typed ex_sig [] [] ex_genv q
  with (if q = one_q then gval_one_typed () else ());
  assert_norm (covers ex_sig ex_genv (lit_int 1l));
  assert (gvals_covered ex_sig ex_genv);
  genv_ok_closed ex_sig ex_genv ln rs

let premises_inhabited () =
  ex_sig_ok ();
  assert_norm (rctx_ok ex_sig rs1);
  assert_norm (lctx_ok ex_sig rs1 ln1);
  ex_genv_ok ln1 rs1

let retype (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#c: config)
  (e2: exp) (c2: config) (h: step ex_sig ex_genv ra st e ra' st' c)
  : Pure (step ex_sig ex_genv ra st e2 ra' st' c2) (requires e == e2 /\ c == c2)
         (ensures fun _ -> True) =
  h
(* * β *)

let beta_step =
  assert_norm (V.is_value ex_sig (lit_int 1l));
  let h = S_Pure #ex_sig #ex_genv #[] #[]
            (PH_Beta #ex_sig #ex_genv #t_int #TRowEmpty #(EVar 0) #(lit_int 1l) ()) in
  assert_norm (subst1_tm (lit_int 1l) (EVar 0) == lit_int 1l);
  retype beta_redex (CTerm (lit_int 1l)) h

let arg_first_step =
  assert_norm (V.is_value ex_sig (lit_int 2l));
  let h = S_Pure #ex_sig #ex_genv #[] #[]
            (PH_Beta #ex_sig #ex_genv #t_int #TRowEmpty #(EVar 0) #(lit_int 2l) ()) in
  let h' = S_Ctx (FAppArg id_int) () h in
  assert_norm (subst1_tm (lit_int 2l) (EVar 0) == lit_int 2l);
  retype arg_first (CTerm (EApp id_int (lit_int 2l))) h'

(* * Join points *)

let join0_step =
  assert_norm (L.for_all (V.is_value ex_sig) [lit_int 1l]);
  let h = PH_Join #ex_sig #ex_genv #[t_int] #t_int #(EVar 0) #[] #0 #[lit_int 1l] () () in
  assert_norm (ELetJoin [t_int] t_int (EVar 0) (plug [] (EJump 0 [lit_int 1l])) == join0);
  assert_norm (plug [] (sub_tm (list_esub (L.rev [lit_int 1l])) (ren_jp (shift 0) (EVar 0))) ==
               lit_int 1l);
  retype join0 (CTerm (ELetJoin [t_int] t_int (EVar 0) (lit_int 1l))) (S_Pure #_ #_ #[] #[] h)

let join1_step =
  let fs = [FLetJoin [] t_int (lit_int 0l)] in
  assert_norm (tl_frames fs);
  assert_norm (L.for_all (V.is_value ex_sig) [lit_int 5l]);
  let h = PH_Join #ex_sig #ex_genv #[t_int] #t_int #self_jump #fs #1 #[lit_int 5l] () () in
  assert_norm (ELetJoin [t_int] t_int self_jump (plug fs (EJump 1 [lit_int 5l])) == join1);
  assert_norm (ELetJoin [t_int] t_int self_jump
                 (plug fs (sub_tm (list_esub (L.rev [lit_int 5l])) (ren_jp (shift 1) self_jump))) ==
               join1);
  retype join1 (CTerm join1) (S_Pure #_ #_ #[] #[] h)

(* * Top-level values *)

let unfold_step =
  assert_norm (value_scheme ex_sig one_q == Some one_info);
  assert_norm (ex_genv.gvals one_q == Some (lit_int 1l));
  assert_norm (kinst_exp [] (lit_int 1l) == lit_int 1l);
  let h = PH_Unfold #ex_sig #ex_genv #one_q #[] #one_info #(lit_int 1l) () () in
  retype one_ref (CTerm (lit_int 1l)) (S_Pure #_ #_ #[] #[] h)

(* * Foreign calls *)

let length_call_redex () = assert_norm (V.foreign_redex ex_sig length_call)

let length_step =
  let args = [STy t_int; SVal int_list1] in
  let o = FOVal (ELit (LInt (I32.int_to_t 1))) in
  length_call_redex ();
  assert_norm (decompose_global_app length_call == Some (base "length", [], args));
  assert_norm (ex_genv.gimpl (base "length") == Some length_impl);
  assert_norm (value_args args == [int_list1]);
  assert_norm (list_len int_list1 == Some 1);
  assert_norm (length_impl [int_list1] == Some o);
  assert_norm (ex_genv.gpre (base "length") [int_list1]);
  let h =
    PH_Foreign #ex_sig #ex_genv #length_call #(base "length") #[] #args #length_impl #o () () ()
  in
  retype length_call (CTerm (ELit (LInt (I32.int_to_t 1)))) (S_Pure #_ #_ #[] #[] h)

let boom_step =
  let args = [SVal (lit_int 0l)] in
  let o = FOFault boom_fault in
  assert_norm (V.foreign_redex ex_sig boom_call);
  assert_norm (decompose_global_app boom_call == Some (base "boom", [], args));
  assert_norm (ex_genv.gimpl (base "boom") == Some boom_impl);
  assert_norm (ex_genv.gpre (base "boom") [lit_int 0l]);
  let h = PH_Foreign #ex_sig #ex_genv #boom_call #(base "boom") #[] #args #boom_impl #o () () () in
  retype boom_call (CFault (FAbi boom_fault)) (S_Pure #_ #_ #[] #[] h)

let boom_let_step =
  let h = S_CtxFault (FLet t_int (EVar 0)) () boom_step in
  retype boom_let (CFault (FAbi boom_fault)) h

(* * Preconditions

   A term is taken apart one frame at a time (`pre_ok_intro`): the frames
   a `let` or an application is plugged from are read off its node, and
   every hole other than the call is a value (`value_pre_ok`). *)

let plug1_let_inv (f: frame) (x: exp) (t: typ) (b body: exp)
  : Lemma (requires plug1 f x == ELet t b body) (ensures f == FLet t body /\ x == b) =
  match f with
  | FLet _ _ -> ()
  | _ -> ()

let plug1_app_inv (f: frame) (x: exp) (a b: exp)
  : Lemma (requires plug1 f x == EApp a b)
          (ensures (f == FAppArg a /\ x == b) \/ (f == FAppFun b /\ x == a)) =
  match f with
  | FAppArg _ | FAppFun _ -> ()
  | _ -> ()

let length_head : exp = ETyApp (EGlobal (base "length") []) t_int

(* The holes of the chain `length [Int] l` other than itself are `l` and
   `length [Int]`, which are values when `l` is. *)
let length_frames_pre_ok (l: exp)
  : Lemma (requires V.is_value ex_sig l /\ V.is_value ex_sig length_head)
          (ensures forall (f: frame) (x: exp).
                     (frame_ok ex_sig f /\ plug1 f x == EApp length_head l) ==> pre_ok ex_sig ex_genv x) =
  introduce forall (f: frame) (x: exp).
      (frame_ok ex_sig f /\ plug1 f x == EApp length_head l) ==> pre_ok ex_sig ex_genv x
  with introduce _ ==> _
  with (
    plug1_app_inv f x length_head l;
    value_pre_ok ex_sig ex_genv x
  )

let length_call_pre_ok () : Lemma (pre_ok ex_sig ex_genv length_call) =
  assert_norm (V.is_value ex_sig length_head);
  assert_norm (V.is_value ex_sig int_list1);
  length_call_redex ();
  assert_norm (foreign_pre_ok ex_genv length_call);
  length_frames_pre_ok int_list1;
  pre_ok_intro ex_sig ex_genv length_call

let length_let_pre_ok () =
  length_call_pre_ok ();
  assert_norm (not (V.foreign_redex ex_sig length_let));
  introduce forall (f: frame) (x: exp).
      (frame_ok ex_sig f /\ plug1 f x == length_let) ==> pre_ok ex_sig ex_genv x
  with introduce _ ==> _
  with plug1_let_inv f x t_int length_call (EVar 0);
  pre_ok_intro ex_sig ex_genv length_let

let length_lit_not_pre_ok () =
  assert_norm (V.foreign_redex ex_sig length_lit);
  assert_norm (~(foreign_pre_ok ex_genv length_lit));
  assert (plug [] length_lit == length_lit)

let length_lit_no_step #ra #st #ra' #st' #c h =
  assert_norm (V.is_value ex_sig length_head);
  assert_norm (V.is_value ex_sig (lit_int 0l));
  assert_norm (decompose_global_app length_lit ==
               Some (base "length", [], [STy t_int; SVal (lit_int 0l)]));
  assert_norm (~(ex_genv.gpre (base "length") [lit_int 0l]));
  match h with
  | S_Pure ph -> ()
  | S_Ctx #_ #_ #_ #_ #x #_ #_ #_ f _ h' ->
    plug1_app_inv f x length_head (lit_int 0l); value_no_step h'
  | S_CtxFault #_ #_ #_ #_ #x #_ #_ #_ f _ h' ->
    plug1_app_inv f x length_head (lit_int 0l); value_no_step h'

(* * A `switchKey` default *)

let switch_key_default_step =
  let bs = [(SymbolKey "x", DLeaf (lit_int 0l))] in
  assert_norm (proj ex_sig [inj_y] (OScrut 0) == Some inj_y);
  assert_norm (branch (carrier_key inj_y) bs == None);
  let h =
    PH_SwitchKeyDef #ex_sig #ex_genv #[inj_y] #(OScrut 0) #bs #(DLeaf (lit_int 1l)) #inj_y ()
  in
  retype (EMatch [inj_y] key_tree) (CTerm (EMatch [inj_y] (DLeaf (lit_int 1l))))
    (S_Pure #_ #_ #[] #[] h)

(* * Conformance of the empty environment *)

let empty_genv_ok sg ln rs =
  introduce forall (q: qname). gval_typed sg ln rs empty_genv q
  with ();
  introduce forall (rs': list (atom & layout)) (ln': lctx) (e: exp).
      rt_ext sg ln rs ln' rs' ==> foreign_call_ok sg empty_genv ln' rs' e
  with ()
