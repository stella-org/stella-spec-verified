module Stella.Core.Init.Examples
open Stella.Core.Syntax
open Stella.Core.Sig
open Stella.Core.Init
open Stella.Core.Init.Lemmas
module L = FStar.List.Tot
module I32 = FStar.Int32

(* Constructors of derivations, with the subexpression the rule reads
   through given explicitly. *)

let i_spine (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
            (b: exp) (d: reads_imm sg g ve je b m)
  : Pure (reads_imm sg g ve je e m) (requires L.memP b (spine_parts sg g e)) (ensures fun _ -> True) =
  ISpine () d

let i_default (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
              (b: exp) (d: reads_imm sg g ve je b m)
  : Pure (reads_imm sg g ve je e m) (requires L.memP b (default_parts sg g e)) (ensures fun _ -> True) =
  IDefault () d

let i_default_lat (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                  (b: exp) (d: reads_lat sg g ve je b m)
  : Pure (reads_imm sg g ve je e m) (requires L.memP b (default_parts sg g e)) (ensures fun _ -> True) =
  IDefaultLat () d

let l_build (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
            (b: exp) (d: reads_lat sg g ve je b m)
  : Pure (reads_lat sg g ve je e m) (requires L.memP b (builds e)) (ensures fun _ -> True) =
  LBuild () d

let l_take (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
           (b: exp) (d: reads_lat sg g ve je b m)
  : Pure (reads_lat sg g ve je e m) (requires takes e == Some b) (ensures fun _ -> True) =
  LTake () d

let l_member (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#i: nat) (#m: nat)
             (k: nat) (r: exp) (d: reads_lat sg g g.genv [] r m)
  : Pure (reads_lat sg g ve je (EVar i) m)
         (requires vlook ve i == VMem k /\ rhs g k == Some r) (ensures fun _ -> True) =
  LMember #sg #g #ve #je #i #k #r #m () () d

(* A derivation for a member written at or after the right-hand side that
   reads it contradicts the rule. *)
let refuse (sg: sig) (g: group) (i: nat) (r: exp) (m: nat) (d: reads_imm sg g g.genv [] r m)
  : Lemma (requires rhs g i == Some r /\ i <= m) (ensures ~ (init_safe sg g)) =
  introduce init_safe sg g ==> False
  with eliminate forall (i: nat) (r: exp) (m: nat) (d: reads_imm sg g g.genv [] r m).
                      rhs g i == Some r ==> m < i
          with i r m d

(* `init_safe` from a proof, for each right-hand side, that it reads now
   only members written before it. *)
let safe_by (sg: sig) (g: group)
             (k: (i: nat) -> (r: exp) -> (m: nat) -> reads_imm sg g g.genv [] r m ->
                 Lemma (requires rhs g i == Some r) (ensures m < i))
  : Lemma (init_safe sg g) =
  introduce forall (i: nat) (r: exp) (m: nat) (d: reads_imm sg g g.genv [] r m).
              rhs g i == Some r ==> m < i
  with introduce rhs g i == Some r ==> m < i
       with k i r m d

(* `Tuple a b` is an application within the chain of `Tuple` at both of
   its value arguments, its head being no member. *)
let tuple_spine (g: group) (t: typ) (a b: exp)
  : Lemma (requires None? (g.gmem (ex "Tuple")))
          (ensures spine_app ex_sig g (tuple t a b) /\
                   spine_app ex_sig g (EApp (ETyApp (ETyApp (EGlobal (ex "Tuple") []) (ty "Int")) t) a)) =
  assert_norm (spine_app ex_sig g (tuple t a b) == None? (g.gmem (ex "Tuple")));
  assert_norm (spine_app ex_sig g (EApp (ETyApp (ETyApp (EGlobal (ex "Tuple") []) (ty "Int")) t) a) ==
               None? (g.gmem (ex "Tuple")))

(* `Tuple a b` reads now only what `a` and `b` do. *)
let tuple_no_imm (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                 (t: typ) (a b: exp) (d: reads_imm ex_sig g ve je e m)
  : Lemma (requires e == tuple t a b /\ None? (g.gmem (ex "Tuple")) /\
                    reads_nothing_now a /\ reads_nothing_now b)
          (ensures False) =
  tuple_spine g t a b;
  let h0 = EGlobal (ex "Tuple") [] in
  let h1 = ETyApp h0 (ty "Int") in
  let h2 = ETyApp h1 t in
  let f = EApp h2 a in
  let n0 (d0: reads_imm ex_sig g ve je h0 m) : Lemma False = imm_global (ex "Tuple") [] d0 in
  let n1 (d1: reads_imm ex_sig g ve je h1 m) : Lemma False = imm_through h0 n0 d1 in
  let n2 (d2: reads_imm ex_sig g ve je h2 m) : Lemma False = imm_through h1 n1 d2 in
  let na (da: reads_imm ex_sig g ve je a m) : Lemma False = imm_nothing da in
  let nf (df: reads_imm ex_sig g ve je f m) : Lemma False = imm_spine_app h2 a n2 na df in
  let nb (db: reads_imm ex_sig g ve je b m) : Lemma False = imm_nothing db in
  imm_spine_app f b nf nb d

(* `{ next: \_ -> e }` reads nothing now. *)
let next_no_imm (#sg: sig) (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                (t: typ) (b: exp) (d: reads_imm sg g ve je e m)
  : Lemma (requires e == next_rec (lam t b)) (ensures False) =
  let nb (b1: exp{L.memP b1 (builds e)}) (d1: reads_imm sg g ve je b1 m) : Lemma False =
    imm_nothing d1
  in
  imm_build nb d

(* x = Tuple 1 x *)

let g_tuple_self : group = local_group tuple_self

let tuple_self_reads =
  assert_norm (L.memP (EVar 0) (spine_parts ex_sig g_tuple_self tuple_self_rhs));
  assert_norm (vlook (member_env 1) 0 == VMem 0);
  i_spine (EVar 0) (IMember ())

let tuple_self_refused () =
  assert_norm (g_tuple_self.genv == member_env 1 /\ rhs g_tuple_self 0 == Some tuple_self_rhs);
  refuse ex_sig g_tuple_self 0 tuple_self_rhs 0 tuple_self_reads

(* x = x *)

let self_reads =
  assert_norm (vlook (member_env 1) 0 == VMem 0);
  IMember ()

let g_self : group = local_group self

let self_refused () =
  assert_norm (g_self.genv == member_env 1 /\ rhs g_self 0 == Some self_rhs);
  refuse ex_sig g_self 0 self_rhs 0 self_reads

(* x = Tuple 1 x, at top level *)

let g_top_tuple_self : group = top_group top_tuple_self

let top_tuple_self_reads =
  assert_norm (L.memP (EGlobal (ex "x") []) (spine_parts ex_sig g_top_tuple_self top_tuple_self_rhs));
  assert_norm (g_top_tuple_self.gmem (ex "x") == Some 0);
  i_spine (EGlobal (ex "x") []) (IMemberGlobal ())

let top_tuple_self_refused () =
  assert_norm (g_top_tuple_self.genv == [] /\ rhs g_top_tuple_self 0 == Some top_tuple_self_rhs);
  refuse ex_sig g_top_tuple_self 0 top_tuple_self_rhs 0 top_tuple_self_reads

(* fibAnd = Tuple "fib" (\n -> … snd fibAnd …) *)

let fib_rhs_no_imm (#g: group) (#ve: venv) (#je: jenv) (#e: exp) (#m: nat)
                   (r: exp) (d: reads_imm ex_sig g ve je e m)
  : Lemma (requires e == fib_rhs r /\ None? (g.gmem (ex "Tuple"))) (ensures False) =
  tuple_no_imm (arr (ty "Int") (ty "Int")) (ELit (LString [102; 105; 98]))
               (lam (ty "Int") (fib_body r)) d

let g_fib_and : group = local_group fib_and

let fib_and_safe () =
  assert_norm (g_fib_and.grhs == [fib_rhs (EVar 1)] /\ g_fib_and.gmem (ex "Tuple") == None);
  let k (i: nat) (r: exp) (m: nat) (d: reads_imm ex_sig g_fib_and g_fib_and.genv [] r m)
    : Lemma (requires rhs g_fib_and i == Some r) (ensures m < i) =
    fib_rhs_no_imm (EVar 1) d
  in
  safe_by ex_sig g_fib_and k

let g_top_fib_and : group = top_group top_fib_and

let top_fib_and_safe () =
  assert_norm (g_top_fib_and.grhs == [fib_rhs (EGlobal (ex "fibAnd") [])] /\
               g_top_fib_and.gmem (ex "Tuple") == None);
  let k (i: nat) (r: exp) (m: nat) (d: reads_imm ex_sig g_top_fib_and g_top_fib_and.genv [] r m)
    : Lemma (requires rhs g_top_fib_and i == Some r) (ensures m < i) =
    fib_rhs_no_imm (EGlobal (ex "fibAnd") []) d
  in
  safe_by ex_sig g_top_fib_and k

(* a = { next: \_ -> b }; b = { next: \_ -> a } *)

let g_next_ab : group = local_group next_ab

let next_ab_safe () =
  assert_norm (g_next_ab.grhs ==
               [next_rec (lam (ty "Unit") (EVar 1)); next_rec (lam (ty "Unit") (EVar 2))]);
  let k (i: nat) (r: exp) (m: nat) (d: reads_imm ex_sig g_next_ab g_next_ab.genv [] r m)
    : Lemma (requires rhs g_next_ab i == Some r) (ensures m < i) =
    if i = 0 then next_no_imm (ty "Unit") (EVar 1) d
    else next_no_imm (ty "Unit") (EVar 2) d
  in
  safe_by ex_sig g_next_ab k

(* xs = Cons 1 ys; ys = Cons 2 xs *)

let g_cons_cycle : group = local_group cons_cycle

let cons_cycle_reads =
  assert_norm (L.memP (EVar 0) (spine_parts ex_sig g_cons_cycle cons_xs_rhs));
  assert_norm (vlook (member_env 2) 0 == VMem 1);
  i_spine (EVar 0) (IMember ())

let cons_cycle_refused () =
  assert_norm (g_cons_cycle.genv == member_env 2 /\ rhs g_cons_cycle 0 == Some cons_xs_rhs);
  refuse ex_sig g_cons_cycle 0 cons_xs_rhs 1 cons_cycle_reads

(* x = (\_ -> x) () *)

let g_apply_self : group = local_group apply_self

let apply_self_reads =
  assert_norm (L.memP (lam (ty "Unit") (EVar 1)) (default_parts ex_sig g_apply_self apply_self_rhs));
  assert_norm (vlook (VNone :: member_env 1) 1 == VMem 0);
  i_default_lat (lam (ty "Unit") (EVar 1)) (LLam (IMember ()))

let apply_self_refused () =
  assert_norm (g_apply_self.genv == member_env 1 /\ rhs g_apply_self 0 == Some apply_self_rhs);
  refuse ex_sig g_apply_self 0 apply_self_rhs 0 apply_self_reads

(* a = { next: \_ -> b }; b = (select next a) Prim.Unit *)

let g_select_ab : group = local_group select_ab

let select_a_rhs : exp = next_rec (lam (ty "Unit") (EVar 1))

let select_ab_reads =
  assert_norm (L.memP (ESelect (SymbolKey "next") (EVar 1))
                      (default_parts ex_sig g_select_ab select_b_rhs));
  assert_norm (vlook (member_env 2) 1 == VMem 0);
  assert_norm (rhs g_select_ab 0 == Some select_a_rhs);
  assert_norm (vlook (VNone :: g_select_ab.genv) 1 == VMem 1);
  i_default_lat (ESelect (SymbolKey "next") (EVar 1))
    (l_take (EVar 1)
      (l_member 0 select_a_rhs
        (l_build (lam (ty "Unit") (EVar 1)) (LLam (IMember ())))))

let select_ab_refused () =
  assert_norm (g_select_ab.genv == member_env 2 /\ rhs g_select_ab 1 == Some select_b_rhs);
  refuse ex_sig g_select_ab 1 select_b_rhs 1 select_ab_reads

(* a = g 1; g x = c x; c y = a + y *)

let g_call_chain : group = local_group call_chain

let call_g_rhs : exp = lam (ty "Int") (EApp (EVar 1) (EVar 0))

let call_c_body : exp = EApp (EApp (EGlobal (ex "add") []) (EVar 3)) (EVar 0)

let call_c_rhs : exp = lam (ty "Int") call_c_body

let call_chain_reads_c =
  assert_norm (L.memP (EVar 1) (default_parts ex_sig g_call_chain call_a_rhs));
  assert_norm (vlook (member_env 3) 1 == VMem 1);
  assert_norm (rhs g_call_chain 1 == Some call_g_rhs);
  assert_norm (L.memP (EVar 1) (default_parts ex_sig g_call_chain (EApp (EVar 1) (EVar 0))));
  assert_norm (vlook (VNone :: g_call_chain.genv) 1 == VMem 2);
  i_default_lat (EVar 1) (l_member 1 call_g_rhs (LLam (i_default (EVar 1) (IMember ()))))

let call_chain_reads_a =
  assert_norm (L.memP (EVar 1) (default_parts ex_sig g_call_chain call_a_rhs));
  assert_norm (vlook (member_env 3) 1 == VMem 1);
  assert_norm (rhs g_call_chain 1 == Some call_g_rhs);
  assert_norm (L.memP (EVar 1) (default_parts ex_sig g_call_chain (EApp (EVar 1) (EVar 0))));
  assert_norm (vlook (VNone :: g_call_chain.genv) 1 == VMem 2);
  assert_norm (rhs g_call_chain 2 == Some call_c_rhs);
  assert_norm (L.memP (EApp (EGlobal (ex "add") []) (EVar 3))
                      (spine_parts ex_sig g_call_chain call_c_body));
  assert_norm (L.memP (EVar 3)
                      (spine_parts ex_sig g_call_chain (EApp (EGlobal (ex "add") []) (EVar 3))));
  assert_norm (vlook (VNone :: g_call_chain.genv) 3 == VMem 0);
  i_default_lat (EVar 1)
    (l_member 1 call_g_rhs
      (LLam (i_default_lat (EVar 1)
        (l_member 2 call_c_rhs
          (LLam (i_spine (EApp (EGlobal (ex "add") []) (EVar 3))
                  (i_spine (EVar 3) (IMember ()))))))))

let call_chain_refused () =
  assert_norm (g_call_chain.genv == member_env 3 /\ rhs g_call_chain 0 == Some call_a_rhs);
  refuse ex_sig g_call_chain 0 call_a_rhs 2 call_chain_reads_c

(* g x = f x; f = g *)

let g_g_then_f : group = local_group g_then_f

let g_then_f_safe () =
  assert_norm (g_g_then_f.grhs == [lam (ty "Int") (EApp (EVar 1) (EVar 0)); EVar 1]);
  assert_norm (vlook g_g_then_f.genv 1 == VMem 0);
  let k (i: nat) (r: exp) (m: nat) (d: reads_imm ex_sig g_g_then_f g_g_then_f.genv [] r m)
    : Lemma (requires rhs g_g_then_f i == Some r) (ensures m < i) =
    if i = 0 then imm_nothing d else imm_var 1 d
  in
  safe_by ex_sig g_g_then_f k

(* f = g; g x = f x *)

let f_then_g_reads =
  assert_norm (vlook (member_env 2) 0 == VMem 1);
  IMember ()

let g_f_then_g : group = local_group f_then_g

let f_then_g_refused () =
  assert_norm (g_f_then_g.genv == member_env 2 /\ rhs g_f_then_g 0 == Some (EVar 0));
  refuse ex_sig g_f_then_g 0 (EVar 0) 1 f_then_g_reads
