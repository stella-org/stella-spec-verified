(* `sig_ok eff_sig` is checked one table at a time, as `sig_ok ex_sig` is
   (`Stella.Core.Semantics.Examples`), each closed fact by normalization;
   the table of effects has `Poly` beside `Console`.

   Each step is built from its rule. The premises are closed facts about
   `eff_sig`, the handler and the term, and the reduct the rule computes
   (substitution, renaming and plugging) equals the term written in the
   interface; both hold by normalization. *)
module Stella.Core.Semantics.Examples.Eff
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Sig.Examples
open Stella.Core.Typing.Aux
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Ctx.Ren
open Stella.Core.Semantics.Step
open Stella.Core.Semantics.Examples
module L = FStar.List.Tot
module V = Stella.Core.Value

(* * `sig_ok` *)

let eff_tycons_wf () : Lemma (tycons_wf eff_sig) =
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

let eff_effects_wf () : Lemma (effects_wf eff_sig) =
  assert_norm (effect_ok eff_sig console_info);
  assert_norm (effect_ok eff_sig poly_info);
  assert_norm (poly_q <> base "Console")

let eff_ctors_wf () : Lemma (ctors_wf eff_sig) =
  assert_norm (scheme_ok eff_sig unit_info.ct_nk unit_info.ct_ty);
  assert_norm (scheme_ok eff_sig nil_info.ct_nk nil_info.ct_ty);
  assert_norm (scheme_ok eff_sig cons_info.ct_nk cons_info.ct_ty);
  assert_norm (scheme_ok eff_sig mkproxy_info.ct_nk mkproxy_info.ct_ty);
  assert_norm (scheme_ok eff_sig mktask_info.ct_nk mktask_info.ct_ty)

let eff_foreigns_wf () : Lemma (foreigns_wf eff_sig) =
  assert_norm (scheme_ok eff_sig length_info.fr_nk length_info.fr_ty);
  assert_norm (scheme_ok eff_sig boom_info.fr_nk boom_info.fr_ty);
  assert_norm (scheme_ok eff_sig pure_info.fr_nk pure_info.fr_ty);
  assert_norm (scheme_ok eff_sig mknil_info.fr_nk mknil_info.fr_ty);
  assert_norm (scheme_ok eff_sig ident_info.fr_nk ident_info.fr_ty);
  assert_norm (scheme_ok eff_sig leak_info.fr_nk leak_info.fr_ty)

let eff_values_wf () : Lemma (values_wf eff_sig) =
  assert_norm (scheme_ok eff_sig one_info.vl_nk one_info.vl_ty);
  assert_norm (scheme_ok eff_sig missing_info.vl_nk missing_info.vl_ty)

let eff_globals_disjoint () : Lemma (globals_disjoint eff_sig) =
  assert_norm (eff_sig.foreigns prim_unit_ctor == None);
  assert_norm (eff_sig.foreigns (base "Nil") == None);
  assert_norm (eff_sig.foreigns (base "Cons") == None);
  assert_norm (eff_sig.foreigns (base "MkProxy") == None);
  assert_norm (eff_sig.foreigns (base "MkTask") == None);
  assert_norm (eff_sig.values prim_unit_ctor == None);
  assert_norm (eff_sig.values (base "Nil") == None);
  assert_norm (eff_sig.values (base "Cons") == None);
  assert_norm (eff_sig.values (base "MkProxy") == None);
  assert_norm (eff_sig.values (base "MkTask") == None);
  assert_norm (eff_sig.values (base "length") == None);
  assert_norm (eff_sig.values (base "boom") == None);
  assert_norm (eff_sig.values (base "pure") == None);
  assert_norm (eff_sig.values (base "mkNil") == None);
  assert_norm (eff_sig.values (base "ident") == None);
  assert_norm (eff_sig.values (base "leak") == None)

let eff_prim_wf () : Lemma (prim_wf eff_sig) =
  assert_norm (prim_tycon eff_sig prim_function
                 (KArrow KType (KArrow (KRow EEffect) (KArrow KType KType))) (TcIntrinsic ClsFunction));
  assert_norm (prim_tycon eff_sig prim_record (KArrow (KRow EType) KType) (TcIntrinsic ClsRecord));
  assert_norm (prim_tycon eff_sig prim_variant (KArrow (KRow EType) KType) (TcIntrinsic ClsVariant));
  assert_norm (prim_tycon eff_sig prim_int KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon eff_sig prim_number KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon eff_sig prim_string KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon eff_sig prim_char KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon eff_sig prim_boolean KType (TcIntrinsic ClsLiteral));
  assert_norm (prim_tycon eff_sig prim_io (KArrow KType KType) (TcIntrinsic ClsOpaque));
  assert_norm (prim_tycon eff_sig prim_unit KType (TcData [prim_unit_ctor]));
  assert_norm (eff_sig.ctors prim_unit_ctor == Some unit_info)

let eff_globals_ok () : Lemma (globals_ok eff_sig) =
  assert_norm (ctor_ok eff_sig prim_unit_ctor unit_info);
  assert_norm (ctor_ok eff_sig (base "Nil") nil_info);
  assert_norm (ctor_ok eff_sig (base "Cons") cons_info);
  assert_norm (ctor_ok eff_sig (base "MkProxy") mkproxy_info);
  assert_norm (ctor_ok eff_sig (base "MkTask") mktask_info);
  assert_norm (data_ok eff_sig prim_unit [prim_unit_ctor]);
  assert_norm (data_ok eff_sig (base "List") [base "Nil"; base "Cons"]);
  assert_norm (data_ok eff_sig (base "Proxy") [base "MkProxy"]);
  assert_norm (data_ok eff_sig (base "Task") [base "MkTask"]);
  assert_norm (arrows_pure length_info.fr_ty);
  assert_norm (arrows_pure boom_info.fr_ty);
  assert_norm (arrows_pure pure_info.fr_ty);
  assert_norm (arrows_pure mknil_info.fr_ty);
  assert_norm (arrows_pure ident_info.fr_ty);
  assert_norm (arrows_pure leak_info.fr_ty)

let eff_sig_ok () =
  eff_tycons_wf (); eff_effects_wf (); eff_ctors_wf (); eff_foreigns_wf (); eff_values_wf ();
  eff_globals_disjoint (); eff_prim_wf (); eff_globals_ok ()

let retype (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store) (#c: config)
  (e2: exp) (c2: config) (h: step eff_sig ex_genv ra st e ra' st' c)
  : Pure (step eff_sig ex_genv ra st e2 ra' st' c2) (requires e == e2 /\ c == c2)
         (ensures fun _ -> True) =
  h

(* `log : String ->* Unit` *)
let log_os : op_sig = { binders = []; arg = t_string; res = t_unit }

let console_facts () : Lemma (eff_sig.effects console_q == Some console_info /\
                               op_of console_info "log" == Some log_os) =
  assert_norm (eff_sig.effects console_q == Some console_info /\
               op_of console_info "log" == Some log_os)

let poly_facts () : Lemma (eff_sig.effects poly_q == Some poly_info /\
                            op_of poly_info "poly" == Some poly_sig) =
  assert_norm (eff_sig.effects poly_q == Some poly_info /\
               op_of poly_info "poly" == Some poly_sig)

let values () : Lemma (V.is_value eff_sig hi /\ V.is_value eff_sig unit_v /\
                        V.is_value eff_sig (lit_int 5l)) =
  assert_norm (V.is_value eff_sig hi /\ V.is_value eff_sig unit_v /\
               V.is_value eff_sig (lit_int 5l))

let log_kt_fun () : Lemma (as_function eff_sig (sub_ty (binders_tsub []) log_kt) ==
                            Some (t_unit, TRowEmpty, t_unit)) =
  assert_norm (as_function eff_sig (sub_ty (binders_tsub []) log_kt) ==
               Some (t_unit, TRowEmpty, t_unit))

(* * The return clause *)

let return_step =
  values ();
  let eh = EH_Return #eff_sig #ex_genv #unit_v #h_once () in
  assert_norm (subst1_tm unit_v h_once.h_ret == EApp idu unit_v);
  retype (EHandle unit_v h_once) (CTerm (EApp idu unit_v)) (S_Eff #_ #_ #[] #[] eh)

(* * `full` clauses for `log` at the root *)

(* The rule `full` for `perform Console.log "hi"` in the hole of `fs`,
   answered by a handler of `Console` whose clause for `log` is the
   `full` clause with body `body`. *)
let log_full (fs: list frame) (h: handler) (body: exp)
  : Pure (eff_head eff_sig ex_genv (EHandle (plug fs log_hi) h)
            (CTerm (full_reduct [] hi t_unit TRowEmpty fs h body)))
         (requires frames_ok eff_sig fs /\ ev_k console_key fs /\
                   h.h_ent == console_ent /\
                   clause_of "log" h.h_clauses == Some (CFull "log" 0 t_string log_kt body))
         (ensures fun _ -> True) =
  values (); console_facts (); log_kt_fun ();
  assert_norm (Stella.Core.Rows.ent_key console_ent == console_key);
  EH_Full #eff_sig #ex_genv #fs #console_key #"log" #[] #hi #h #None #console_q #[]
    #console_info #log_os #0 #t_string #log_kt #body #t_unit #TRowEmpty #t_unit () () () () ()

let once_body : exp = EApp (EVar 0) unit_v

let full_once_step =
  assert_norm (clause_of "log" h_once.h_clauses == Some (CFull "log" 0 t_string log_kt once_body));
  let eh = log_full [] h_once once_body in
  assert_norm (full_reduct [] hi t_unit TRowEmpty [] h_once once_body ==
               EApp (cont_unit h_once) unit_v);
  retype (EHandle log_hi h_once) (CTerm (EApp (cont_unit h_once) unit_v)) (S_Eff #_ #_ #[] #[] eh)

let twice_body : exp = EApp (EVar 0) (EApp (EVar 0) unit_v)

let full_twice_step =
  assert_norm (clause_of "log" h_twice.h_clauses == Some (CFull "log" 0 t_string log_kt twice_body));
  let eh = log_full [] h_twice twice_body in
  assert_norm (full_reduct [] hi t_unit TRowEmpty [] h_twice twice_body == twice_reduct);
  retype (EHandle log_hi h_twice) (CTerm twice_reduct) (S_Eff #_ #_ #[] #[] eh)

let twice_resume_step =
  values ();
  let ph = PH_Beta #eff_sig #ex_genv #t_unit #TRowEmpty #(EHandle (EVar 0) h_twice) #unit_v () in
  let h = S_Ctx (FAppArg (cont_unit h_twice)) () (S_Pure #_ #_ #[] #[] ph) in
  assert_norm (subst1_tm unit_v (EHandle (EVar 0) h_twice) == EHandle unit_v h_twice);
  retype twice_reduct (CTerm (EApp (cont_unit h_twice) (EHandle unit_v h_twice))) h

(* * A `fast` clause *)

let fast_step =
  values (); console_facts ();
  assert_norm (clause_of "log" h_fast.h_clauses == Some (CFast "log" 0 t_string unit_v));
  assert_norm (handler_key h_fast == console_key);
  let eh = EH_Fast #eff_sig #ex_genv #[] #console_key #"log" #[] #hi #h_fast #None #console_q #[]
             #console_info #log_os #0 #t_string #unit_v () () () () in
  assert_norm (fast_reduct [] [] log_os hi [] h_fast unit_v ==
               ELet t_unit unit_v (EHandle (EVar 0) h_fast));
  retype (EHandle log_hi h_fast) (CTerm (ELet t_unit unit_v (EHandle (EVar 0) h_fast)))
    (S_Eff #_ #_ #[] #[] eh)

(* * Two handlers of one key *)

let nested_same_step =
  let s = S_Ctx (FHandle h_out) () full_once_step in
  retype nested_same (CTerm (EHandle (EApp (cont_unit h_in) unit_v) h_out)) s

let nested_outer_excluded () =
  assert_norm (not (ev_k console_key [FHandle h_in]))

(* * A handler of another key on the way *)

let crossing_ev_k () =
  assert_norm (handler_key h_aux <> console_key /\ ev_k console_key [FHandle h_aux])

let crossing_step =
  crossing_ev_k ();
  assert_norm (frames_ok eff_sig [FHandle h_aux]);
  assert_norm (clause_of "log" h_once.h_clauses == Some (CFull "log" 0 t_string log_kt once_body));
  let eh = log_full [FHandle h_aux] h_once once_body in
  assert_norm (full_reduct [] hi t_unit TRowEmpty [FHandle h_aux] h_once once_body ==
               EApp (ELam t_unit TRowEmpty (EHandle (EHandle (EVar 0) h_aux) h_once)) unit_v);
  retype crossing
    (CTerm (EApp (ELam t_unit TRowEmpty (EHandle (EHandle (EVar 0) h_aux) h_once)) unit_v))
    (S_Eff #_ #_ #[] #[] eh)

(* * A context under a binder *)

let under_let_shift () =
  assert_norm (ren_frames (shift 1) [let_z] == [FLet t_unit (EVar 2)] /\
               ren_handler (shift 1) h_z == { h_z with h_ret = EVar 2 })

let under_let_step =
  assert_norm (frames_ok eff_sig [let_z] /\ ev_k console_key [let_z]);
  assert_norm (clause_of "log" h_z.h_clauses == Some (CFull "log" 0 t_string log_kt once_body));
  let eh = log_full [let_z] h_z once_body in
  assert_norm (full_reduct [] hi t_unit TRowEmpty [let_z] h_z once_body ==
               EApp (ELam t_unit TRowEmpty
                       (EHandle (ELet t_unit (EVar 0) (EVar 2)) { h_z with h_ret = EVar 2 }))
                    unit_v);
  retype under_let
    (CTerm (EApp (ELam t_unit TRowEmpty
                    (EHandle (ELet t_unit (EVar 0) (EVar 2)) { h_z with h_ret = EVar 2 }))
                 unit_v))
    (S_Eff #_ #_ #[] #[] eh)

(* * An operation with a type binder *)

let poly_kt_inst () =
  assert_norm (sub_ty (binders_tsub [t_int]) poly_kt == t_fun t_int TRowEmpty t_int /\
               as_function eff_sig (sub_ty (binders_tsub [t_int]) poly_kt) ==
                 Some (t_int, TRowEmpty, t_int))

let poly_body : exp = ELet (TVar 0) (EVar 1) (EApp (EVar 1) (EVar 0))

let poly_full_step =
  values (); poly_facts (); poly_kt_inst ();
  assert_norm (clause_of "poly" h_poly.h_clauses == Some (CFull "poly" 1 (TVar 0) poly_kt poly_body));
  assert_norm (handler_key h_poly == poly_key);
  let eh = EH_Full #eff_sig #ex_genv #[] #poly_key #"poly" #[t_int] #(lit_int 5l) #h_poly
             #None #poly_q #[] #poly_info #poly_sig #1 #(TVar 0) #poly_kt #poly_body
             #t_int #TRowEmpty #t_int () () () () () in
  assert_norm (full_reduct [t_int] (lit_int 5l) t_int TRowEmpty [] h_poly poly_body ==
               ELet t_int (lit_int 5l) (EApp cont_poly (EVar 0)));
  retype (EHandle poly_5 h_poly) (CTerm (ELet t_int (lit_int 5l) (EApp cont_poly (EVar 0))))
    (S_Eff #_ #_ #[] #[] eh)

let poly_fast_step =
  values (); poly_facts ();
  assert_norm (clause_of "poly" h_poly_fast.h_clauses == Some (CFast "poly" 1 (TVar 0) (EVar 0)));
  assert_norm (handler_key h_poly_fast == poly_key);
  let eh = EH_Fast #eff_sig #ex_genv #[] #poly_key #"poly" #[t_int] #(lit_int 5l) #h_poly_fast
             #None #poly_q #[] #poly_info #poly_sig #1 #(TVar 0) #(EVar 0) () () () () in
  assert_norm (fast_reduct [] [t_int] poly_sig (lit_int 5l) [] h_poly_fast (EVar 0) ==
               ELet t_int (lit_int 5l) (EHandle (EVar 0) h_poly_fast));
  retype (EHandle poly_5 h_poly_fast)
    (CTerm (ELet t_int (lit_int 5l) (EHandle (EVar 0) h_poly_fast)))
    (S_Eff #_ #_ #[] #[] eh)
