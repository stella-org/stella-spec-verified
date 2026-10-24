(* Each derivation is built bottom-up in `closed_ctx []`, every
   sub-derivation with its type written out; the kinding, entailment,
   row-membership and equality premises are closed facts established by
   normalization (`assert_norm`). Each step is built from its rule as in
   `Stella.Core.Semantics.Examples.Eff`, in the empty environment, and its
   reduct is the term of the interface by normalization. The reducts are
   typed by the theorems, never by hand, under the `Γ_R2` preservation
   gives, which is empty since no name is allocated (`rdom_in_nil`). *)
module Stella.Core.Safety.Examples.Eff
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Sig.Examples
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
open Stella.Core.Semantics.Examples
open Stella.Core.Semantics.Examples.Eff
open Stella.Core.Safety.Preservation
open Stella.Core.Safety.Covers
open Stella.Core.Safety.Progress.Eff
open Stella.Core.Safety.Progress
open Stella.Core.Safety.Effects
module L = FStar.List.Tot
module V = Stella.Core.Value

let g0 : ctx = closed_ctx []

let eff_premises () =
  eff_sig_ok ();
  assert_norm (rctx_ok eff_sig []);
  assert_norm (lctx_ok eff_sig [] []);
  empty_genv_ok eff_sig [] []

let retype (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ) (t' r': typ)
  (h: typing eff_sig [] g d e t r)
  : Pure (typing eff_sig [] g d e t' r') (requires t == t' /\ r == r') (ensures fun _ -> True) =
  h

let retype_step (#ra: list atom) (#st: store) (#e: exp) (#ra': list atom) (#st': store)
  (#c: config) (e2: exp) (c2: config) (h: step eff_sig empty_genv ra st e ra' st' c)
  : Pure (step eff_sig empty_genv ra st e2 ra' st' c2) (requires e == e2 /\ c == c2)
         (ensures fun _ -> True) =
  h

(* * Common pieces *)

(* `log : String ->* Unit` *)
let log_os : op_sig = { binders = []; arg = t_string; res = t_unit }

let console_facts () : Lemma (eff_sig.effects console_q == Some console_info /\
                               op_of console_info "log" == Some log_os /\
                               console_ent == EntEff None console_q [] /\
                               ent_key console_ent == console_key) =
  assert_norm (eff_sig.effects console_q == Some console_info /\
               op_of console_info "log" == Some log_os /\
               ent_key console_ent == console_key)

(* The row of the handled computation. *)
let row_in : typ = TRowExt console_ent TRowEmpty

let row_facts () : Lemma (check eff_sig g0 row_in (KRow EEffect) /\
                           check eff_sig g0 TRowEmpty (KRow EEffect) /\
                           check eff_sig g0 t_unit KType /\ check eff_sig g0 t_string KType /\
                           L.mem (console_key, PEff console_q (canon_tys []))
                             (row_entries (canon row_in))) =
  assert_norm (check eff_sig g0 row_in (KRow EEffect));
  assert_norm (check eff_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (check eff_sig g0 t_unit KType);
  assert_norm (check eff_sig g0 t_string KType);
  assert_norm (L.mem (console_key, PEff console_q (canon_tys [])) (row_entries (canon row_in)))

(* `Prim.Unit : Unit ! ρ` *)
let unit_typing (g: ctx) (d: jctx) (r: typ)
  : Pure (typing eff_sig [] g d unit_v t_unit r)
         (requires check eff_sig g r (KRow EEffect)) (ensures fun _ -> True) =
  assert_norm (global_type eff_sig prim_unit_ctor == Some (0, t_unit));
  assert_norm (kinst_ty [] t_unit == t_unit);
  assert_norm (qkinds_wf g.nk []);
  let h : typing eff_sig [] g d (EGlobal prim_unit_ctor []) (kinst_ty [] t_unit) r =
    T_Global #eff_sig #[] #g #d #prim_unit_ctor #[] #0 #t_unit #r () () ()
  in
  retype t_unit r h

(* `perform Console.log "hi" : Unit ! ( Console | () )` *)
let log_typing : typing eff_sig [] g0 [] log_hi t_unit row_in =
  console_facts ();
  row_facts ();
  assert_norm (lit_type (LString [104; 105]) == t_string);
  assert_norm (op_inst [] [] log_os.arg == t_string);
  assert_norm (op_inst [] [] log_os.res == t_unit);
  assert_norm (check_tys eff_sig g0 [] console_info.eff_params);
  assert_norm (check_tys eff_sig g0 [] log_os.binders);
  let ha : typing eff_sig [] g0 [] hi (lit_type (LString [104; 105])) row_in = T_Lit () in
  let ha = retype (op_inst [] [] log_os.arg) row_in ha in
  let hp : typing eff_sig [] g0 [] log_hi (op_inst [] [] log_os.res) row_in =
    T_Perform #eff_sig #[] #g0 #[] #console_key #"log" #[] #hi #row_in #console_q #console_info
      #log_os [] () () () ha
  in
  retype t_unit row_in hp

(* The return clause `return (x : Unit) -> idu x`. *)
let console_ret_typing : typing eff_sig [] (push_var g0 t_unit) [] (EApp idu (EVar 0)) t_unit TRowEmpty =
  let g1 = push_var g0 t_unit in
  let g2 = push_var g1 t_unit in
  assert_norm (check eff_sig g1 t_unit KType /\ check eff_sig g1 TRowEmpty (KRow EEffect));
  assert_norm (check eff_sig g2 TRowEmpty (KRow EEffect));
  assert_norm (L.nth g2.vars 0 == Some t_unit);
  assert_norm (L.nth g1.vars 0 == Some t_unit);
  let hx : typing eff_sig [] g2 [] (EVar 0) t_unit TRowEmpty = T_Var () () in
  let hid : typing eff_sig [] g1 [] idu (t_fun t_unit TRowEmpty t_unit) TRowEmpty = T_Lam () () hx in
  let hy : typing eff_sig [] g1 [] (EVar 0) t_unit TRowEmpty = T_Var () () in
  T_App hid hy

(* `handle (perform Console.log "hi") with h : β ! ()` from the clauses'
   derivation, for a handler of `Console` with the return type `Unit`. *)
let console_handle (h: handler) (b: typ)
  (hret: typing eff_sig [] (push_var g0 t_unit) [] h.h_ret b TRowEmpty)
  (hcl: clauses_typing eff_sig [] g0 console_info [] TRowEmpty b h.h_clauses)
  : Pure (typing eff_sig [] g0 [] (EHandle log_hi h) b TRowEmpty)
         (requires h.h_ent == console_ent /\ h.h_ret_ty == t_unit /\
                   check eff_sig g0 b KType /\ clauses_cover console_info h.h_clauses)
         (ensures fun _ -> True) =
  console_facts ();
  row_facts ();
  T_Handle #eff_sig #[] #g0 #[] #log_hi #h #b #TRowEmpty #None #console_q #[] #console_info
    () () () () log_typing hret hcl

(* The premises of `TCL_Full` and `TCL_Fast` on the types, for `log` with
   no binder, the outer row `()` and the answer type `b`. *)
let log_clause_facts (b kt: typ)
  : Lemma (requires kt == t_fun t_unit TRowEmpty b /\ check eff_sig g0 b KType)
          (ensures push_tvars g0 [] == g0 /\
                   check eff_sig (push_tvars g0 log_os.binders) t_string KType /\
                   ty_eq t_string (eff_inst 0 [] log_os.arg) /\
                   ty_eq t_unit (eff_inst 0 [] log_os.res) /\
                   eff_inst 0 [] log_os.res == t_unit /\
                   check eff_sig (push_tvars g0 log_os.binders) kt KType /\
                   ty_eq kt (t_fun (eff_inst 0 [] log_os.res) (ren_ty (shift 0) TRowEmpty)
                              (ren_ty (shift 0) b)) /\
                   ren_ty (shift 0) b == b /\ ren_ty (shift 0) TRowEmpty == TRowEmpty) =
  console_facts ();
  row_facts ();
  Stella.Core.Subst.Lemmas.Typ.ren_ty_shift0 b;
  assert_norm (push_tvars g0 [] == g0);
  assert_norm (eff_inst 0 [] log_os.arg == t_string);
  assert_norm (eff_inst 0 [] log_os.res == t_unit);
  assert_norm (ren_ty (shift 0) TRowEmpty == TRowEmpty);
  assert_norm (prim_wf eff_sig);
  Stella.Core.Kinding.Facts.check_t_fun eff_sig g0 t_unit TRowEmpty b

(* * A `full` clause resuming once *)

let once_body : exp = EApp (EVar 0) unit_v

let full_once_typing =
  let gk = push_var (push_var g0 t_string) log_kt in
  row_facts ();
  log_clause_facts t_unit log_kt;
  assert_norm (L.nth gk.vars 0 == Some log_kt);
  assert_norm (check eff_sig gk TRowEmpty (KRow EEffect));
  assert_norm (h_once.h_clauses == [CFull "log" 0 t_string log_kt once_body]);
  let hk : typing eff_sig [] gk [] (EVar 0) (t_fun t_unit TRowEmpty t_unit) TRowEmpty = T_Var () () in
  let hb : typing eff_sig [] gk [] once_body t_unit TRowEmpty = T_App hk (unit_typing gk [] TRowEmpty) in
  let hb = retype (ren_ty (shift 0) t_unit) (ren_ty (shift 0) TRowEmpty) hb in
  let hcl : clauses_typing eff_sig [] g0 console_info [] TRowEmpty t_unit h_once.h_clauses =
    TCL_Full #eff_sig #[] #g0 #console_info #[] #TRowEmpty #t_unit #"log" #0 #t_string #log_kt
      #once_body #[] #log_os () () () hb (TCL_Nil ())
  in
  assert_norm (clauses_cover console_info h_once.h_clauses);
  console_handle h_once t_unit console_ret_typing hcl

let log_kt_fun () : Lemma (as_function eff_sig (sub_ty (binders_tsub []) log_kt) ==
                            Some (t_unit, TRowEmpty, t_unit)) =
  assert_norm (as_function eff_sig (sub_ty (binders_tsub []) log_kt) ==
               Some (t_unit, TRowEmpty, t_unit))

let log_facts () : Lemma (V.is_value eff_sig hi /\ V.is_value eff_sig unit_v /\
                           frames_ok eff_sig [] /\ ev_k console_key []) =
  assert_norm (V.is_value eff_sig hi /\ V.is_value eff_sig unit_v);
  assert_norm (frames_ok eff_sig [] /\ ev_k console_key [])

let full_once_step_e =
  log_facts (); console_facts (); log_kt_fun ();
  assert_norm (handler_key h_once == console_key);
  assert_norm (clause_of "log" h_once.h_clauses == Some (CFull "log" 0 t_string log_kt once_body));
  let eh = EH_Full #eff_sig #empty_genv #[] #console_key #"log" #[] #hi #h_once #None #console_q
             #[] #console_info #log_os #0 #t_string #log_kt #once_body #t_unit #TRowEmpty #t_unit
             () () () () () in
  assert_norm (full_reduct [] hi t_unit TRowEmpty [] h_once once_body ==
               EApp (cont_unit h_once) unit_v);
  retype_step (EHandle log_hi h_once) (CTerm (EApp (cont_unit h_once) unit_v))
    (S_Eff #_ #_ #[] #[] eh)

(* A derivation under the empty `Γ_R2`. *)
let at_nil (#d: jctx) (#e: exp) (#t #r: typ) (rs: list (atom & layout))
  (h: typing eff_sig [] (closed_ctx rs) d e t r)
  : Pure (typing eff_sig [] (closed_ctx []) d e t r) (requires rs == []) (ensures fun _ -> True) =
  h

let full_once_reduct_typing () =
  eff_premises ();
  let p = preservation full_once_typing full_once_step_e in
  rdom_in_nil p.rs';
  at_nil p.rs' p.der

(* * A `fast` clause *)

let fast_typing =
  let gx = push_var g0 t_string in
  row_facts ();
  log_clause_facts t_unit log_kt;
  assert_norm (check eff_sig gx TRowEmpty (KRow EEffect));
  assert_norm (h_fast.h_clauses == [CFast "log" 0 t_string unit_v]);
  let hb = retype (eff_inst 0 [] log_os.res) (ren_ty (shift 0) TRowEmpty)
             (unit_typing gx [] TRowEmpty) in
  let hcl : clauses_typing eff_sig [] g0 console_info [] TRowEmpty t_unit h_fast.h_clauses =
    TCL_Fast #eff_sig #[] #g0 #console_info #[] #TRowEmpty #t_unit #"log" #0 #t_string #unit_v
      #[] #log_os () () hb (TCL_Nil ())
  in
  assert_norm (clauses_cover console_info h_fast.h_clauses);
  console_handle h_fast t_unit console_ret_typing hcl

let fast_step_e =
  log_facts (); console_facts ();
  assert_norm (clause_of "log" h_fast.h_clauses == Some (CFast "log" 0 t_string unit_v));
  assert_norm (handler_key h_fast == console_key);
  let eh = EH_Fast #eff_sig #empty_genv #[] #console_key #"log" #[] #hi #h_fast #None #console_q
             #[] #console_info #log_os #0 #t_string #unit_v () () () () in
  assert_norm (fast_reduct [] [] log_os hi [] h_fast unit_v ==
               ELet t_unit unit_v (EHandle (EVar 0) h_fast));
  retype_step (EHandle log_hi h_fast) (CTerm (ELet t_unit unit_v (EHandle (EVar 0) h_fast)))
    (S_Eff #_ #_ #[] #[] eh)

let fast_reduct_typing () =
  eff_premises ();
  let p = preservation fast_typing fast_step_e in
  rdom_in_nil p.rs';
  at_nil p.rs' p.der

(* * A continuation that leaves its clause *)

(* The return clause `return (x : Unit) -> λ (u : Unit) / (). x`. *)
let reify_ret_typing : typing eff_sig [] (push_var g0 t_unit) [] h_reify.h_ret reify_ty TRowEmpty =
  let g1 = push_var g0 t_unit in
  let g2 = push_var g1 t_unit in
  assert_norm (check eff_sig g1 t_unit KType /\ check eff_sig g1 TRowEmpty (KRow EEffect));
  assert_norm (check eff_sig g2 TRowEmpty (KRow EEffect));
  assert_norm (L.nth g2.vars 1 == Some t_unit);
  let hx : typing eff_sig [] g2 [] (EVar 1) t_unit TRowEmpty = T_Var () () in
  T_Lam () () hx

(* The clause body `λ (u : Unit) / (). k u u`. *)
let reify_body_typing
  : typing eff_sig [] (push_var (push_var g0 t_string) reify_kt) [] reify_body reify_ty TRowEmpty =
  let gk = push_var (push_var g0 t_string) reify_kt in
  let gu = push_var gk t_unit in
  assert_norm (check eff_sig gk t_unit KType /\ check eff_sig gk TRowEmpty (KRow EEffect));
  assert_norm (check eff_sig gu TRowEmpty (KRow EEffect));
  assert_norm (L.nth gu.vars 1 == Some reify_kt);
  assert_norm (L.nth gu.vars 0 == Some t_unit);
  let hk : typing eff_sig [] gu [] (EVar 1) (t_fun t_unit TRowEmpty reify_ty) TRowEmpty = T_Var () () in
  let hu : typing eff_sig [] gu [] (EVar 0) t_unit TRowEmpty = T_Var () () in
  let hku : typing eff_sig [] gu [] (EApp (EVar 1) (EVar 0)) (t_fun t_unit TRowEmpty t_unit) TRowEmpty =
    T_App hk hu in
  let hkuu : typing eff_sig [] gu [] (EApp (EApp (EVar 1) (EVar 0)) (EVar 0)) t_unit TRowEmpty =
    T_App hku hu in
  T_Lam () () hkuu

let reify_handle_typing : typing eff_sig [] g0 [] (EHandle log_hi h_reify) reify_ty TRowEmpty =
  row_facts ();
  assert_norm (prim_wf eff_sig);
  Stella.Core.Kinding.Facts.check_t_fun eff_sig g0 t_unit TRowEmpty t_unit;
  log_clause_facts reify_ty reify_kt;
  let hb = retype (ren_ty (shift 0) reify_ty) (ren_ty (shift 0) TRowEmpty) reify_body_typing in
  let hcl : clauses_typing eff_sig [] g0 console_info [] TRowEmpty reify_ty h_reify.h_clauses =
    TCL_Full #eff_sig #[] #g0 #console_info #[] #TRowEmpty #reify_ty #"log" #0 #t_string #reify_kt
      #reify_body #[] #log_os () () () hb (TCL_Nil ())
  in
  assert_norm (clauses_cover console_info h_reify.h_clauses);
  console_handle h_reify reify_ty reify_ret_typing hcl

let reify_prog_typing =
  row_facts ();
  T_App reify_handle_typing (unit_typing g0 [] TRowEmpty)

let reify_step_1 =
  log_facts (); console_facts ();
  assert_norm (as_function eff_sig (sub_ty (binders_tsub []) reify_kt) ==
               Some (t_unit, TRowEmpty, reify_ty));
  assert_norm (handler_key h_reify == console_key);
  assert_norm (clause_of "log" h_reify.h_clauses ==
               Some (CFull "log" 0 t_string reify_kt reify_body));
  let eh = EH_Full #eff_sig #empty_genv #[] #console_key #"log" #[] #hi #h_reify #None #console_q
             #[] #console_info #log_os #0 #t_string #reify_kt #reify_body #t_unit #TRowEmpty
             #reify_ty () () () () () in
  let s = S_Ctx (FAppFun unit_v) () (S_Eff #_ #_ #[] #[] eh) in
  assert_norm (plug1 (FAppFun unit_v) (full_reduct [] hi t_unit TRowEmpty [] h_reify reify_body) ==
               reify_1);
  retype_step reify_prog (CTerm reify_1) s

let reify_step_2 =
  log_facts ();
  let body = EApp (EApp cont_reify (EVar 0)) (EVar 0) in
  let ph = PH_Beta #eff_sig #empty_genv #t_unit #TRowEmpty #body #unit_v () in
  assert_norm (subst1_tm unit_v body == reify_2);
  retype_step reify_1 (CTerm reify_2) (S_Pure #_ #_ #[] #[] ph)

let reify_preserved () =
  eff_premises ();
  FStar.Classical.exists_intro
    (fun (_: typing eff_sig [] (closed_ctx []) [] reify_prog t_unit TRowEmpty) -> True)
    reify_prog_typing;
  preservation_typed [] [] t_unit reify_step_1;
  eliminate exists (rs1: list (atom & layout)).
    rctx_after eff_sig empty_genv [] [] [] rs1 /\ typed eff_sig [] (closed_ctx rs1) reify_1 t_unit
  with rdom_in_nil rs1;
  preservation_typed [] [] t_unit reify_step_2;
  eliminate exists (rs2: list (atom & layout)).
    rctx_after eff_sig empty_genv [] [] [] rs2 /\ typed eff_sig [] (closed_ctx rs2) reify_2 t_unit
  with rdom_in_nil rs2;
  assert_norm (covers eff_sig empty_genv reify_prog);
  preservation_covers reify_prog_typing reify_step_1;
  let p1 = preservation reify_prog_typing reify_step_1 in
  rdom_in_nil p1.rs';
  preservation_covers (at_nil p1.rs' p1.der) reify_step_2

(* * Progress *)

let empty_genv_pre_ok sg e =
  introduce forall (fs: list frame) (r: exp).
      (frames_ok sg fs /\ e == plug fs r /\ V.foreign_redex sg r) ==> foreign_pre_ok empty_genv r
  with introduce _ ==> _
  with (match decompose_global_app r with
        | Some _ -> ()
        | None -> ())

let handled_terms_ok () =
  assert_norm (stage6_frag (EHandle log_hi h_once));
  assert_norm (covers eff_sig empty_genv (EHandle log_hi h_once));
  assert_norm (stage6_frag reify_prog);
  assert_norm (covers eff_sig empty_genv reify_prog)

let handled_progress_steps () =
  assert_norm (not (V.is_value eff_sig (EHandle log_hi h_once)));
  assert_norm (not (V.is_value eff_sig reify_prog))

(* * Effect safety *)

let reify_effect_safe () =
  eff_premises ();
  effect_safety reify_prog_typing reify_run_0;
  effect_safety reify_prog_typing reify_run_1;
  effect_safety reify_prog_typing reify_run_2
