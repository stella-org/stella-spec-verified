(* The derivations are built bottom-up, as in `Stella.Core.Typing.Examples`.

   The terms without a type are refuted by inversion. A `jump` is typed by
   `T_Jump` under conversions, so its index is below `|Δ|` (`jump_bound`).
   The rules on the path from the root to the `jump` fix `Δ` there: the
   bound side of a `let`, an application argument, the value argument of a
   chain and the operand of every boundary have `Δ = []`, and a `letjoin`
   definition has one join point more than its `letjoin`. A `region` body
   is read at one fresh atom; opening it keeps the `jump`.

   The β contractum is typed by `typing_beta` from the derivation of the
   λ body, at `Σ` well formed (`ex_sig_ok`) and `Γ` empty. *)
module Stella.Core.Typing.Examples.Join
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Region
open Stella.Core.Kinding
open Stella.Core.Prim
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Examples
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value
module SC = Stella.Core.Scope
module Inst = Stella.Core.Typing.Subst.Tm.Inst

let retype (#g: ctx) (#d: jctx) (#e: exp) (#t1 #r1: typ) (t2 r2: typ)
           (h: typing ex_sig [] g d e t1 r1)
  : Pure (typing ex_sig [] g d e t2 r2) (requires t1 == t2 /\ r1 == r2) (ensures fun _ -> True) =
  h

let lit_typing (g: ctx) (d: jctx) (c: lit) (t r: typ)
  : Pure (typing ex_sig [] g d (ELit c) t r)
         (requires lit_type c == t /\ check ex_sig g r (KRow EEffect))
         (ensures fun _ -> True) =
  retype t r (T_Lit #ex_sig #[] #g #d #c #r ())

let g0 : ctx = decl_ctx 0

(* The signature of a join point with no parameter, `() -> Int ! ()`. *)
let jt_int : list typ & typ & typ = ([], t_int, TRowEmpty)

(* * A local join point on the bound side of a `let` *)

let local_join_typing (g: ctx)
  : Pure (typing ex_sig [] g [] local_join t_int TRowEmpty)
         (requires check ex_sig g t_int KType /\ check ex_sig g TRowEmpty (KRow EEffect) /\
                   check ex_sig (push_vars g []) TRowEmpty (KRow EEffect))
         (ensures fun _ -> True) =
  assert_norm (lit_type (LInt 1l) == t_int);
  assert_norm (tys_ok ex_sig g [] == true);
  assert_norm (L.nth [jt_int] 0 == Some jt_int);
  let h1 : typing ex_sig [] (push_vars g []) [jt_int] (lit_int 1l) t_int TRowEmpty =
    lit_typing (push_vars g []) [jt_int] (LInt 1l) t_int TRowEmpty
  in
  let h2 : typing ex_sig [] g [jt_int] (EJump 0 []) t_int TRowEmpty =
    T_Jump #ex_sig #[] #g #[jt_int] #0 #[] #[] #t_int #TRowEmpty () () (TE_Nil ())
  in
  T_LetJoin #ex_sig #[] #g #[] #[] #t_int #(lit_int 1l) #(EJump 0 []) #TRowEmpty () h1 h2

let beta_body_inst () = assert_norm (subst1_tm unit_v local_join == local_join)

let beta_redex_typing =
  let gu = push_var g0 t_unit in
  let gy = push_var g0 t_int in
  assert_norm (check ex_sig gu t_int KType /\ check ex_sig gu TRowEmpty (KRow EEffect) /\
               check ex_sig (push_vars gu []) TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g0 t_unit KType /\ check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g0 t_int KType);
  assert_norm (global_type ex_sig prim_unit_ctor == Some (0, t_unit));
  assert_norm (kinst_ty [] t_unit == t_unit);
  assert_norm (L.nth gy.vars 0 == Some t_int);
  assert_norm (check ex_sig gy TRowEmpty (KRow EEffect));
  let hlam : typing ex_sig [] g0 [] (ELam t_unit TRowEmpty local_join)
               (t_fun t_unit TRowEmpty t_int) TRowEmpty =
    T_Lam () () (local_join_typing gu)
  in
  let hu : typing ex_sig [] g0 [] unit_v (kinst_ty [] t_unit) TRowEmpty =
    T_Global #ex_sig #[] #g0 #[] #prim_unit_ctor #[] #0 #t_unit #TRowEmpty () () ()
  in
  let happ : typing ex_sig [] g0 [] (EApp (ELam t_unit TRowEmpty local_join) unit_v) t_int
               TRowEmpty =
    T_App hlam (retype t_unit TRowEmpty hu)
  in
  let hy : typing ex_sig [] gy [] (EVar 0) t_int TRowEmpty = T_Var () () in
  T_Let () happ hy

(* The contractum of the application, `local_join` itself, by the
   substitution lemma: the λ body at `Prim.Unit`. *)
let beta_contractum_typing =
  let gu = push_var g0 t_unit in
  let gy = push_var g0 t_int in
  ex_sig_ok ();
  assert_norm (wf_ctx ex_sig g0);
  assert_norm (V.is_value ex_sig unit_v);
  assert_norm (check ex_sig gu t_int KType /\ check ex_sig gu TRowEmpty (KRow EEffect) /\
               check ex_sig (push_vars gu []) TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig g0 t_int KType /\ check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (global_type ex_sig prim_unit_ctor == Some (0, t_unit));
  assert_norm (kinst_ty [] t_unit == t_unit);
  assert_norm (L.nth gy.vars 0 == Some t_int);
  assert_norm (check ex_sig gy TRowEmpty (KRow EEffect));
  let hu : typing ex_sig [] g0 [] unit_v (kinst_ty [] t_unit) TRowEmpty =
    T_Global #ex_sig #[] #g0 #[] #prim_unit_ctor #[] #0 #t_unit #TRowEmpty () () ()
  in
  let hc : typing ex_sig [] g0 [] (subst1_tm unit_v local_join) t_int TRowEmpty =
    Inst.typing_beta (local_join_typing gu) (retype t_unit TRowEmpty hu) []
  in
  beta_body_inst ();
  let hy : typing ex_sig [] gy [] (EVar 0) t_int TRowEmpty = T_Var () () in
  T_Let () (retype t_int TRowEmpty hc) hy

(* * Join points in argument position, and recursive ones *)

(* `j : (Int) -> Int ! ()`. *)
let jt_n : list typ & typ & typ = ([t_int], t_int, TRowEmpty)

let join_in_arg_typing =
  let tf = t_int_fun in
  let gf = push_var g0 tf in
  let gn = push_vars gf [t_int] in
  let lj = ELetJoin [t_int] t_int (EVar 0) (EJump 0 [lit_int 1l]) in
  assert_norm (check ex_sig g0 tf KType /\ check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig gf TRowEmpty (KRow EEffect) /\ check ex_sig gf t_int KType);
  assert_norm (tys_ok ex_sig gf [t_int] == true);
  assert_norm (check ex_sig gn TRowEmpty (KRow EEffect));
  assert_norm (L.nth gn.vars 0 == Some t_int);
  assert_norm (L.nth gf.vars 0 == Some tf);
  assert_norm (lit_type (LInt 1l) == t_int);
  assert_norm (L.nth [jt_n] 0 == Some jt_n);
  let hdef : typing ex_sig [] gn [jt_n] (EVar 0) t_int TRowEmpty = T_Var () () in
  let h1 : typing ex_sig [] gf [] (lit_int 1l) t_int TRowEmpty =
    lit_typing gf [] (LInt 1l) t_int TRowEmpty
  in
  let hjump : typing ex_sig [] gf [jt_n] (EJump 0 [lit_int 1l]) t_int TRowEmpty =
    T_Jump #ex_sig #[] #gf #[jt_n] #0 #[lit_int 1l] #[t_int] #t_int #TRowEmpty () ()
      (TE_Cons h1 (TE_Nil ()))
  in
  let hlj : typing ex_sig [] gf [] lj t_int TRowEmpty =
    T_LetJoin #ex_sig #[] #gf #[] #[t_int] #t_int #(EVar 0) #(EJump 0 [lit_int 1l]) #TRowEmpty
      () hdef hjump
  in
  let hf : typing ex_sig [] gf [] (EVar 0) (t_fun t_int TRowEmpty t_int) TRowEmpty =
    T_Var () ()
  in
  T_Lam () () (T_App hf hlj)

let self_jump_typing =
  let gn = push_vars g0 [t_int] in
  assert_norm (check ex_sig g0 t_int KType /\ check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (tys_ok ex_sig g0 [t_int] == true);
  assert_norm (check ex_sig gn TRowEmpty (KRow EEffect) /\ check ex_sig gn t_int KType);
  assert_norm (L.nth gn.vars 0 == Some t_int);
  assert_norm (lit_type (LInt 1l) == t_int);
  assert_norm (L.nth [jt_n] 0 == Some jt_n);
  let hn : typing ex_sig [] gn [] (EVar 0) t_int TRowEmpty = T_Var () () in
  let hdef : typing ex_sig [] gn [jt_n] (EJump 0 [EVar 0]) t_int TRowEmpty =
    T_Jump #ex_sig #[] #gn #[jt_n] #0 #[EVar 0] #[t_int] #t_int #TRowEmpty () ()
      (TE_Cons hn (TE_Nil ()))
  in
  let h1 : typing ex_sig [] g0 [] (lit_int 1l) t_int TRowEmpty =
    lit_typing g0 [] (LInt 1l) t_int TRowEmpty
  in
  let hjump : typing ex_sig [] g0 [jt_n] (EJump 0 [lit_int 1l]) t_int TRowEmpty =
    T_Jump #ex_sig #[] #g0 #[jt_n] #0 #[lit_int 1l] #[t_int] #t_int #TRowEmpty () ()
      (TE_Cons h1 (TE_Nil ()))
  in
  T_LetJoin #ex_sig #[] #g0 #[] #[t_int] #t_int #(EJump 0 [EVar 0]) #(EJump 0 [lit_int 1l])
    #TRowEmpty () hdef hjump

(* * Jumps to an outer join point from a non-tail position *)

let rec nth_lt (#a: Type) (l: list a) (i: nat)
  : Lemma (requires Some? (L.nth l i)) (ensures i < L.length l) (decreases l) =
  match l with
  | _ :: l' -> if i = 0 then () else nth_lt l' (i - 1)

(* A typed `jump` targets a join point of `Δ`. *)
let rec jump_bound (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == EJump j es) (ensures j < L.length d) (decreases h) =
  match h with
  | T_Jump _ _ _ -> nth_lt d j
  | T_Conv h' _ _ -> jump_bound j es h'

(* The definition of a `letjoin` has one join point more than it. *)
let rec letjoin_def_jump (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (ts: list typ) (t1: typ) (j: nat) (es: list exp) (e2: exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == ELetJoin ts t1 (EJump j es) e2) (ensures j < L.length d + 1)
          (decreases h) =
  match h with
  | T_LetJoin _ h1 _ -> jump_bound j es h1
  | T_Conv h' _ _ -> letjoin_def_jump ts t1 j es e2 h'

(* The bound side of a `let` has no join point. *)
let rec let_bound_jump (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (t0: typ) (ts: list typ) (t1: typ) (j: nat) (es: list exp) (e2 body: exp)
  (h: typing sg ln g d e t r)
  : Lemma (requires e == ELet t0 (ELetJoin ts t1 (EJump j es) e2) body) (ensures j < 1)
          (decreases h) =
  match h with
  | T_Let _ h1 _ -> letjoin_def_jump ts t1 j es e2 h1
  | T_Conv h' _ _ -> let_bound_jump t0 ts t1 j es e2 body h'

let rec jump_from_inner_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r)
  : Lemma (requires e == jump_from_inner) (ensures False) (decreases h) =
  match h with
  | T_LetJoin _ _ h2 ->
    let_bound_jump t_int [] t_int 1 [] (EJump 0 []) (EVar 0) h2
  | T_Conv h' _ _ -> jump_from_inner_inv h'

let jump_from_inner_untypable #sg #ln #g #d #t #r h = jump_from_inner_inv h

(* The value argument of a chain stands under the `Δ` of the chain
   judgement. *)
let chain_arg_jump (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (f: exp) (j: nat) (es: list exp) (hc: chain_typing sg ln g d r e)
  : Lemma (requires e == EApp f (EJump j es)) (ensures j < L.length d) =
  match hc with
  | TS_Val _ _ hv -> jump_bound j es hv

(* An application argument has no join point, whether the application is
   typed by `T_App` or as a chain by `T_Chain`. *)
let rec jump_in_arg_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (f: exp) (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == EApp f (EJump j es)) (ensures False) (decreases h) =
  match h with
  | T_App _ h2 -> jump_bound j es h2
  | T_Chain hc _ -> chain_arg_jump f j es hc
  | T_Conv h' _ _ -> jump_in_arg_inv f j es h'
  | T_VariantValue _ _ _ _ _ _ -> ()

let jump_in_arg_untypable #sg #ln #g #d #t #r f j es h = jump_in_arg_inv f j es h

let rec jump_from_arg_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r)
  : Lemma (requires e == jump_from_arg) (ensures False) (decreases h) =
  match h with
  | T_LetJoin _ _ h2 -> jump_in_arg_inv (ELam t_int TRowEmpty (EVar 0)) 0 [] h2
  | T_Conv h' _ _ -> jump_from_arg_inv h'

let jump_from_arg_untypable #sg #ln #g #d #t #r h = jump_from_arg_inv h

(* * Jumps to an outer join point from tail-transparent positions *)

(* `j1 : (Int) -> Int ! ()`, in front of `j0`. *)
let jt1 : list typ & typ & typ = ([t_int], t_int, TRowEmpty)

let d10 : jctx = [jt1; jt_int]

(* The tree under `y : Int`:
   `guard true (leaf (jump j1 (y))) (leaf (jump j0 ()))`. *)
let tree_typing
  : dt_typing ex_sig [] (push_var g0 t_int) d10 (scrut_occs 0 [])
      (DGuard (ELit (LBool true)) (DLeaf (EJump 0 [EVar 0])) (DLeaf (EJump 1 []))) t_int TRowEmpty =
  let gy = push_var g0 t_int in
  assert_norm (lit_type (LBool true) == t_bool);
  assert_norm (check ex_sig gy TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig gy t_int KType);
  assert_norm (L.nth gy.vars 0 == Some t_int);
  assert_norm (L.nth d10 0 == Some jt1);
  assert_norm (L.nth d10 1 == Some jt_int);
  let hc : typing ex_sig [] gy [] (ELit (LBool true)) t_bool TRowEmpty =
    lit_typing gy [] (LBool true) t_bool TRowEmpty
  in
  let hy : typing ex_sig [] gy [] (EVar 0) t_int TRowEmpty = T_Var () () in
  let hj1 : typing ex_sig [] gy d10 (EJump 0 [EVar 0]) t_int TRowEmpty =
    T_Jump #ex_sig #[] #gy #d10 #0 #[EVar 0] #[t_int] #t_int #TRowEmpty () ()
      (TE_Cons hy (TE_Nil ()))
  in
  let hj0 : typing ex_sig [] gy d10 (EJump 1 []) t_int TRowEmpty =
    T_Jump #ex_sig #[] #gy #d10 #1 #[] #[] #t_int #TRowEmpty () () (TE_Nil ())
  in
  TD_Guard hc (TD_Leaf hj1) (TD_Leaf hj0)

let jump_from_tail_typing =
  let gx = push_vars g0 [t_int] in
  let gy = push_var g0 t_int in
  let body = ELet t_int (lit_int 2l)
               (ECase [] (DGuard (ELit (LBool true)) (DLeaf (EJump 0 [EVar 0]))
                                 (DLeaf (EJump 1 [])))) in
  assert_norm (check ex_sig g0 t_int KType /\ check ex_sig g0 TRowEmpty (KRow EEffect));
  assert_norm (tys_ok ex_sig g0 [] == true /\ tys_ok ex_sig g0 [t_int] == true);
  assert_norm (lit_type (LInt 1l) == t_int /\ lit_type (LInt 2l) == t_int);
  assert_norm (check ex_sig (push_vars g0 []) TRowEmpty (KRow EEffect));
  assert_norm (check ex_sig gx TRowEmpty (KRow EEffect) /\ check ex_sig gx t_int KType);
  assert_norm (check ex_sig gy TRowEmpty (KRow EEffect));
  assert_norm (L.nth d10 1 == Some jt_int);
  (* `case () of …`: no scrutinee. *)
  let hcase : typing ex_sig [] gy d10
                (ECase [] (DGuard (ELit (LBool true)) (DLeaf (EJump 0 [EVar 0]))
                             (DLeaf (EJump 1 []))))
                t_int TRowEmpty =
    T_Case #ex_sig #[] #gy #d10 #[] #_ #[] #t_int #TRowEmpty (TE_Nil ()) tree_typing
  in
  let hbody : typing ex_sig [] g0 d10 body t_int TRowEmpty =
    T_Let () (lit_typing g0 [] (LInt 2l) t_int TRowEmpty) hcase
  in
  (* The definition of `j1`, under `x : Int`, jumps to `j0`. *)
  let hdef1 : typing ex_sig [] gx d10 (EJump 1 []) t_int TRowEmpty =
    T_Jump #ex_sig #[] #gx #d10 #1 #[] #[] #t_int #TRowEmpty () () (TE_Nil ())
  in
  let hj1 : typing ex_sig [] g0 [jt_int] (ELetJoin [t_int] t_int (EJump 1 []) body) t_int
              TRowEmpty =
    T_LetJoin #ex_sig #[] #g0 #[jt_int] #[t_int] #t_int #(EJump 1 []) #body #TRowEmpty () hdef1
      hbody
  in
  let hdef0 : typing ex_sig [] (push_vars g0 []) [jt_int] (lit_int 1l) t_int TRowEmpty =
    lit_typing (push_vars g0 []) [jt_int] (LInt 1l) t_int TRowEmpty
  in
  T_LetJoin #ex_sig #[] #g0 #[] #[] #t_int #(lit_int 1l) #_ #TRowEmpty () hdef0 hj1

(* * Jumps out of a boundary *)

let rec lam_jump_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (t1 r1: typ) (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == ELam t1 r1 (EJump j es)) (ensures False) (decreases h) =
  match h with
  | T_Lam _ _ hb -> jump_bound j es hb
  | T_Conv h' _ _ -> lam_jump_inv t1 r1 j es h'

let jump_under_lam_untypable #sg #ln #g #d #t #r t1 r1 j es h = lam_jump_inv t1 r1 j es h

let rec tylam_jump_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (k: kind) (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == ETyLam k (EJump j es)) (ensures False) (decreases h) =
  match h with
  | T_TyLam _ _ _ hb -> jump_bound j es hb
  | T_Conv h' _ _ -> tylam_jump_inv k j es h'

let jump_under_tylam_untypable #sg #ln #g #d #t #r k j es h = tylam_jump_inv k j es h

let rec handled_jump_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (hd: handler) (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == EHandle (EJump j es) hd) (ensures False) (decreases h) =
  match h with
  | T_Handle _ _ _ _ h1 _ _ -> jump_bound j es h1
  | T_Conv h' _ _ -> handled_jump_inv hd j es h'

let jump_handled_untypable #sg #ln #g #d #t #r hd j es h = handled_jump_inv hd j es h

let rec return_jump_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e0: exp) (#t #r: typ)
  (e: exp) (hd: handler) (j: nat) (es: list exp) (h: typing sg ln g d e0 t r)
  : Lemma (requires e0 == EHandle e hd /\ hd.h_ret == EJump j es) (ensures False) (decreases h) =
  match h with
  | T_Handle _ _ _ _ _ h2 _ -> jump_bound j es h2
  | T_Conv h' _ _ -> return_jump_inv e hd j es h'

let jump_in_return_clause_untypable #sg #ln #g #d #t #r e hd j es h = return_jump_inv e hd j es h

let rec region_jump_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (lay: layout) (es0: list exp) (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == ERegion lay es0 (EJump j es)) (ensures False) (decreases h) =
  match h with
  | T_Region #_ #_ #_ #_ #_ #_ #body _ _ _ hbody ->
    let a = SC.fresh_atom (L.append (rdom g) (frn_exp body)) in
    LP.append_mem (rdom g) (frn_exp body) a;
    jump_bound j (rmap_exps (open_rr a) 0 es) (hbody a)
  | T_Conv h' _ _ -> region_jump_inv lay es0 j es h'

let jump_in_region_untypable #sg #ln #g #d #t #r lay es0 j es h = region_jump_inv lay es0 j es h

let rec region_open_jump_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (a: atom) (cells: list (key & exp)) (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == ERegionOpen a cells (EJump j es)) (ensures False) (decreases h) =
  match h with
  | T_RegionOpen _ _ _ _ hb -> jump_bound j es hb
  | T_Conv h' _ _ -> region_open_jump_inv a cells j es h'

let jump_in_region_open_untypable #sg #ln #g #d #t #r a cells j es h =
  region_open_jump_inv a cells j es h

let rec letrec_jump_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (s: typ) (bs: list (typ & exp)) (body: exp) (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == ELetRec ((s, EJump j es) :: bs) body) (ensures False) (decreases h) =
  match h with
  | T_LetRec _ hbs _ -> let TB_Cons _ h1 _ = hbs in jump_bound j es h1
  | T_Conv h' _ _ -> letrec_jump_inv s bs body j es h'

let jump_in_letrec_untypable #sg #ln #g #d #t #r s bs body j es h =
  letrec_jump_inv s bs body j es h

let rec fill_jump_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (nu: atom) (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == EFill nu (EJump j es)) (ensures False) (decreases h) =
  match h with
  | T_Fill _ _ h1 -> jump_bound j es h1
  | T_Conv h' _ _ -> fill_jump_inv nu j es h'

let jump_in_fill_untypable #sg #ln #g #d #t #r nu j es h = fill_jump_inv nu j es h

let rec openeffc_jump_inv (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (r1: typ) (j: nat) (es: list exp) (h: typing sg ln g d e t r)
  : Lemma (requires e == EOpenEffC r1 (EJump j es)) (ensures False) (decreases h) =
  match h with
  | T_OpenEffC h1 _ -> jump_bound j es h1
  | T_Conv h' _ _ -> openeffc_jump_inv r1 j es h'

let jump_in_openeffc_untypable #sg #ln #g #d #t #r r1 j es h = openeffc_jump_inv r1 j es h
