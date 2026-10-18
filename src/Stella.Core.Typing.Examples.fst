(* Each derivation is built bottom-up, every sub-derivation with its type
   written out. The kinding, entailment and equality premises are closed
   boolean facts about concrete terms, each established by normalization
   (`assert_norm`) before the rule that needs it. *)
module Stella.Core.Typing.Examples
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Typing.Aux
open Stella.Core.Typing
module L = FStar.List.Tot

(* A derivation read at a type and a row equal to its own. *)
let retype (#g: ctx) (#d: jctx) (#tl: bool) (#e: exp) (#t1 #r1: typ) (t2 r2: typ)
           (h: typing ex_sig [] g d tl e t1 r1)
  : Pure (typing ex_sig [] g d tl e t2 r2) (requires t1 == t2 /\ r1 == r2) (ensures fun _ -> True) =
  h

(* `M.x`, a global with an empty kind scheme. *)
let global0 (g: ctx) (d: jctx) (tl: bool) (q: qname) (t: typ) (r: typ)
  : Pure (typing ex_sig [] g d tl (EGlobal q []) t r)
         (requires global_type ex_sig q == Some (0, t) /\ kinst_ty [] t == t /\
                   check ex_sig g r (KRow EEffect))
         (ensures fun _ -> True) =
  let h : typing ex_sig [] g d tl (EGlobal q []) (kinst_ty [] t) r =
    T_Global #ex_sig #[] #g #d #tl #q #[] #0 #t #r () () ()
  in
  retype t r h

(* * The identity *)

let id_typing =
  let g = push_var (decl_ctx 0) t_int in
  assert_norm (check ex_sig (decl_ctx 0) t_int KType);
  assert_norm (check ex_sig (decl_ctx 0) TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g TRowEmpty (KRow EEffect));
  assert_norm (L.nth g.vars 0 == Some t_int);
  let hx : typing ex_sig [] g [] true (EVar 0) t_int TRowEmpty = T_Var () () in
  T_Lam () () hx

(* * A record *)

let select_typing =
  let g = decl_ctx 0 in
  let one = ELit (LInt 1l) in
  assert_norm (check ex_sig g TRowEmpty (KRow EEffect));
  assert_norm (key_ok ex_sig g key_x EType);
  assert_norm (entails (hyps g) (CLacks key_x TRowEmpty));
  assert_norm (lit_type (LInt 1l) == t_int);
  let h1 : typing ex_sig [] g [] false one (lit_type (LInt 1l)) TRowEmpty = T_Lit () in
  let h2 : typing ex_sig [] g [] false ERecEmpty (t_record TRowEmpty) TRowEmpty = T_RecEmpty () in
  let h3 : typing ex_sig [] g [] false (EExtend key_x one ERecEmpty)
               (t_record (TRowExt (EntTy key_x t_int) TRowEmpty)) TRowEmpty =
    T_Extend (retype t_int TRowEmpty h1) h2 ()
  in
  T_Select h3 ()

(* * A handler

   The contexts, from the outside in: `e`, then `Partial ∉ e`, then `a`,
   then `thunk`. *)

let g1 : ctx = push_tvar (decl_ctx 0) (KRow EEffect)

let g2 : ctx = add_assump g1 lacks_partial

let g3 : ctx = push_tvar g2 KType

let g4 : ctx = push_var g3 thunk_ty

(* The row inside the handler, `( Partial | e )`, and the answer type. *)
let row_in : typ = TRowExt partial_ent (TVar 1)

let answer : typ = maybe_ty (TVar 0)

(* `thunk Prim.Unit : a ! ( Partial | e )` *)
let d_handled : typing ex_sig [] g4 [] true (EApp (EVar 0) (EGlobal prim_unit_ctor [])) (TVar 0) row_in =
  assert_norm (L.nth g4.vars 0 == Some (t_fun t_unit row_in (TVar 0)));
  assert_norm (check ex_sig g4 row_in (KRow EEffect));
  assert_norm (global_type ex_sig prim_unit_ctor == Some (0, t_unit));
  assert_norm (kinst_ty [] t_unit == t_unit);
  let hf : typing ex_sig [] g4 [] false (EVar 0) (t_fun t_unit row_in (TVar 0)) row_in =
    T_Var () ()
  in
  T_App hf (global0 g4 [] false prim_unit_ctor t_unit row_in)

(* The return clause, under `x : a`, at `e`:
   `( openEff [e] ( Prelude.Just [a] ) ) x : Maybe a`. *)
let g_ret : ctx = push_var g4 (TVar 0)

let d_return : typing ex_sig [] g_ret [] true to_maybe_handler.h_ret answer (TVar 1) =
  let just = EGlobal (prelude "Just") [] in
  let just_a = ETyApp just (TVar 0) in
  let just_fn = t_fun (TVar 0) TRowEmpty answer in
  assert_norm (global_type ex_sig (prelude "Just") == Some (0, just_ty));
  assert_norm (kinst_ty [] just_ty == just_ty);
  assert_norm (check ex_sig g_ret (TVar 1) (KRow EEffect));
  assert_norm (check ex_sig g_ret (TVar 0) KType);
  assert_norm (subst1_ty (TVar 0) (t_fun (TVar 0) TRowEmpty (maybe_ty (TVar 0))) == just_fn);
  assert_norm (entails (hyps g_ret) (CDisj TRowEmpty (TVar 1)));
  assert_norm (ty_eq (t_fun (TVar 0) (TRowUnion TRowEmpty (TVar 1)) answer)
                     (t_fun (TVar 0) (TVar 1) answer));
  assert_norm (check ex_sig g_ret (t_fun (TVar 0) (TVar 1) answer) KType);
  assert_norm (ty_eq (TVar 1) (TVar 1));
  assert_norm (L.nth g_ret.vars 0 == Some (TVar 0));
  let hj : typing ex_sig [] g_ret [] false just just_ty (TVar 1) =
    global0 g_ret [] false (prelude "Just") just_ty (TVar 1)
  in
  let hja : typing ex_sig [] g_ret [] false just_a
              (subst1_ty (TVar 0) (t_fun (TVar 0) TRowEmpty (maybe_ty (TVar 0)))) (TVar 1) =
    T_TyApp hj ()
  in
  let hopen : typing ex_sig [] g_ret [] false (EOpenEff (TVar 1) just_a)
                (t_fun (TVar 0) (TRowUnion TRowEmpty (TVar 1)) answer) (TVar 1) =
    T_OpenEff (retype just_fn (TVar 1) hja) ()
  in
  let hconv : typing ex_sig [] g_ret [] false (EOpenEff (TVar 1) just_a)
                (t_fun (TVar 0) (TVar 1) answer) (TVar 1) =
    T_Conv hopen () ()
  in
  let hx : typing ex_sig [] g_ret [] false (EVar 0) (TVar 0) (TVar 1) = T_Var () () in
  T_App hconv hx

(* The `abort` clause. Under `b`, the outer row and answer are shifted:
   `Prelude.Nothing [a] : Maybe a ! e` with `a` and `e` at indices 1 and 2. *)
let clause_kt : typ = t_fun (TVar 0) (TVar 2) (maybe_ty (TVar 1))

let clause_body : exp = ETyApp (EGlobal (prelude "Nothing") []) (TVar 1)

let g_cl : ctx = push_var (push_var (push_tvars g4 abort_sig.binders) t_unit) clause_kt

let d_clause_body
  : typing ex_sig [] g_cl [] true clause_body (ren_ty (shift 1) answer) (ren_ty (shift 1) (TVar 1)) =
  let nothing = EGlobal (prelude "Nothing") [] in
  assert_norm (global_type ex_sig (prelude "Nothing") == Some (0, nothing_ty));
  assert_norm (kinst_ty [] nothing_ty == nothing_ty);
  assert_norm (check ex_sig g_cl (TVar 2) (KRow EEffect));
  assert_norm (check ex_sig g_cl (TVar 1) KType);
  assert_norm (subst1_ty (TVar 1) (maybe_ty (TVar 0)) == ren_ty (shift 1) answer);
  assert_norm (ren_ty (shift 1) (TVar 1) == TVar 2);
  let hn : typing ex_sig [] g_cl [] false nothing nothing_ty (TVar 2) =
    global0 g_cl [] false (prelude "Nothing") nothing_ty (TVar 2)
  in
  let hna : typing ex_sig [] g_cl [] true clause_body (subst1_ty (TVar 1) (maybe_ty (TVar 0))) (TVar 2) =
    T_TyApp hn ()
  in
  retype (ren_ty (shift 1) answer) (ren_ty (shift 1) (TVar 1)) hna

let d_clauses
  : clauses_typing ex_sig [] g4 partial_info [] (TVar 1) answer to_maybe_handler.h_clauses =
  assert_norm (op_of partial_info "abort" == Some abort_sig);
  assert_norm (check ex_sig (push_tvars g4 abort_sig.binders) t_unit KType);
  assert_norm (ty_eq t_unit (eff_inst 1 [] abort_sig.arg));
  assert_norm (check ex_sig (push_tvars g4 abort_sig.binders) clause_kt KType);
  assert_norm (ty_eq clause_kt
                 (t_fun (eff_inst 1 [] abort_sig.res) (ren_ty (shift 1) (TVar 1))
                    (ren_ty (shift 1) answer)));
  assert_norm (check ex_sig g4 answer KType /\ check ex_sig g4 (TVar 1) (KRow EEffect));
  TCL_Full #ex_sig #[] #g4 #partial_info #[] #(TVar 1) #answer
    #"abort" #1 #t_unit #clause_kt #clause_body #[] #abort_sig
    () () () d_clause_body (TCL_Nil ())

(* `handle ( thunk Prim.Unit ) with … : Maybe a ! e` *)
let d_handle : typing ex_sig [] g4 [] true to_maybe_handle answer (TVar 1) =
  assert_norm (ex_sig.effects (prelude "Partial") == Some partial_info);
  assert_norm (check ex_sig g4 (TRowExt partial_ent (TVar 1)) (KRow EEffect));
  assert_norm (check ex_sig g4 (TVar 0) KType);
  assert_norm (check ex_sig g4 answer KType);
  assert_norm (check ex_sig g4 (TVar 1) (KRow EEffect));
  assert_norm (clauses_cover partial_info to_maybe_handler.h_clauses);
  T_Handle #ex_sig #[] #g4 #[] #true #(EApp (EVar 0) (EGlobal prim_unit_ctor [])) #to_maybe_handler
    #answer #(TVar 1) #None #(prelude "Partial") #[] #partial_info
    () () () () d_handled d_return d_clauses

let to_maybe_typing =
  let lam = ELam thunk_ty (TVar 1) to_maybe_handle in
  let tylam_a = ETyLam KType lam in
  let clam = ECLam lacks_partial tylam_a in
  assert_norm (check ex_sig g3 thunk_ty KType);
  assert_norm (check ex_sig g3 (TVar 1) (KRow EEffect));
  assert_norm (check ex_sig g3 TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g2 TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g1 TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig (decl_ctx 0) TRowEmpty (KRow EEffect));
  assert_norm (constr_ok ex_sig g1 lacks_partial);
  assert_norm (value_form ex_sig lam);
  assert_norm (value_form ex_sig tylam_a);
  assert_norm (value_form ex_sig clam);
  let hlam : typing ex_sig [] g3 [] true lam (t_fun thunk_ty (TVar 1) answer) TRowEmpty =
    T_Lam () () d_handle
  in
  let ha : typing ex_sig [] g2 [] true tylam_a
             (TForall KType (t_fun thunk_ty (TVar 1) answer)) TRowEmpty =
    T_TyLam () () () hlam
  in
  let hc : typing ex_sig [] g1 [] true clam
             (TConstr lacks_partial (TForall KType (t_fun thunk_ty (TVar 1) answer))) TRowEmpty =
    T_CLam () () () ha
  in
  T_TyLam () () () hc

(* * The names of `Prim` *)

let ex_prim_wf () =
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
  assert_norm (ex_sig.ctors prim_unit_ctor ==
               Some ({ ct_owner = prim_unit; ct_tag = 0; ct_arity = 0; ct_nk = 0; ct_ty = t_unit }))
