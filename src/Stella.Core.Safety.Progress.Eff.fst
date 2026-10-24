(* Proof structure.

   `kinded_fun_as_function` walks the three applications of
   `t_fun a r b = TApp (TApp (TApp (TCon Function []) a) r) b`. Each
   left part of `t` synthesizes a kind (it heads an application kinded at
   `Type`), so it is no row former, and `ty_eq_head` gives it the head of
   the corresponding part of `t_fun`; `ty_eq_app_inv` and `ty_eq_con_inv`
   descend. `prim_wf` makes `Function` a function constructor.

   `handled_perform_redex` follows `op_redex_inv` of
   `Stella.Core.Safety.Preservation`: `inv_handle`, `plug_typing` of the
   handled computation, `inv_perform` in the hole, and `handled_entry`,
   which makes the effect the `perform` reads the handler's. The clause
   comes from `clauses_cover` (`cover_clause_of`). For a `full` clause the
   instantiated continuation type is kinded (`check_sub` through
   `ty_sub_ok_tys`) and equal to a function type (`ty_eq_sub`), so
   `as_function` reads it (`kinded_fun_as_function`).

   `unhandled_perform_untypable` reads the `perform`'s entry in the hole's
   row (`inv_perform`), which `p_rows` of `plug_typing` puts in `()`. *)
module Stella.Core.Safety.Progress.Eff
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Runtime
open Stella.Core.Typing.Closed
open Stella.Core.Typing.Subst.Tys
open Stella.Core.Typing.Eff
open Stella.Core.Semantics.Env
open Stella.Core.Semantics.Ctx
open Stella.Core.Semantics.Step
open Stella.Core.Safety.Hidden
module L = FStar.List.Tot
module V = Stella.Core.Value

(* * Function types *)

let synth_not_row (sg: sig) (g: ctx) (t: typ)
  : Lemma (requires Some? (synth_kind sg g t)) (ensures not (is_row_former t)) =
  match t with
  | TRowEmpty | TRowExt _ _ | TRowUnion _ _ -> ()
  | _ -> ()

let check_type_synth (sg: sig) (g: ctx) (t: typ)
  : Lemma (requires check sg g t KType) (ensures synth_kind sg g t == Some KType) =
  match t with
  | TRowEmpty | TRowExt _ _ | TRowUnion _ _ -> ()
  | _ -> ()

let t_fun_shape (a r b: typ)
  : Lemma (t_fun a r b == TApp (TApp (TApp (TCon prim_function []) a) r) b) =
  assert_norm (t_fun a r b == TApp (TApp (TApp (TCon prim_function []) a) r) b)

(* A type that synthesizes a kind and equals `TCon q []` is `TCon q []`. *)
let con_part (sg: sig) (g: ctx) (t: typ) (q: qname)
  : Lemma (requires Some? (synth_kind sg g t) /\ ty_eq t (TCon q []))
          (ensures t == TCon q []) =
  synth_not_row sg g t;
  ty_eq_head t (TCon q []);
  match t with
  | TCon q' ks -> ty_eq_con_inv q' q ks []

(* A type that synthesizes a kind and equals `TApp a b` is an application
   of a part equal to `a` that synthesizes a kind. *)
let app_part (sg: sig) (g: ctx) (t a b: typ)
  : Lemma (requires Some? (synth_kind sg g t) /\ ty_eq t (TApp a b))
          (ensures TApp? t /\ Some? (synth_kind sg g (TApp?._0 t)) /\ ty_eq (TApp?._0 t) a) =
  synth_not_row sg g t;
  ty_eq_head t (TApp a b);
  match t with
  | TApp t1 t2 -> ty_eq_app_inv t1 t2 a b

let kinded_fun_as_function sg g t a r b =
  check_type_synth sg g t;
  t_fun_shape a r b;
  app_part sg g t (TApp (TApp (TCon prim_function []) a) r) b;
  let TApp t1 _ = t in
  app_part sg g t1 (TApp (TCon prim_function []) a) r;
  let TApp t2 _ = t1 in
  app_part sg g t2 (TCon prim_function []) a;
  let TApp t3 _ = t2 in
  con_part sg g t3 prim_function

(* * Clauses *)

let rec ops_covered_mem (ops: list (opname & op_sig)) (names: list opname) (op: opname)
  (os: op_sig)
  : Lemma (requires ops_covered ops names /\ L.assoc op ops == Some os) (ensures L.mem op names)
          (decreases ops) =
  match ops with
  | (op', _) :: ops' -> if op' = op then () else ops_covered_mem ops' names op os

let rec clause_of_mem_ops (op: opname) (cs: list clause)
  : Lemma (requires L.mem op (clause_ops cs)) (ensures Some? (clause_of op cs)) (decreases cs) =
  match cs with
  | c :: cs' -> if clause_op c = op then () else clause_of_mem_ops op cs'

(* The clauses of a handler cover each operation of its effect. *)
let cover_clause_of (ei: effect_info) (cs: list clause) (op: opname) (os: op_sig)
  : Lemma (requires clauses_cover ei cs /\ op_of ei op == Some os)
          (ensures Some? (clause_of op cs)) =
  ops_covered_mem ei.eff_ops (clause_ops cs) op os;
  clause_of_mem_ops op cs

(* * The handled `perform` *)

let perform_not_value (sg: sig) (k: key) (op: opname) (ss: list typ) (v: exp)
  : Lemma (not (V.is_value sg (EPerform k op ss v))) =
  assert_norm (not (V.is_value sg (EPerform k op ss v)))

let sub_t_fun (sigma: tsub) (a r b: typ)
  : Lemma (sub_ty sigma (t_fun a r b) == t_fun (sub_ty sigma a) (sub_ty sigma r) (sub_ty sigma b)) =
  assert_norm (sub_ty sigma (t_fun a r b) == t_fun (sub_ty sigma a) (sub_ty sigma r) (sub_ty sigma b))

(* The facts of the redex that the rules ask for, read off its derivation. *)
noeq type redex_facts (sg: sig) (ln: lctx) (g: ctx) (fs: list frame) (k: key) (op: opname)
  (ss: list typ) (v: exp) (hd: handler) (t r: typ) = {
  rf_h: handle_inv sg ln g (plug fs (EPerform k op ss v)) hd t r;
  rf_os: op_sig;
  rf_facts: squash (op_of rf_h.hi_ei op == Some rf_os /\ check_tys sg g ss rf_os.binders /\
                    L.length ss == L.length rf_os.binders /\
                    Some? (clause_of op hd.h_clauses));
}

let redex_facts_of (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#fs: list frame) (#k: key)
  (#op: opname) (#ss: list typ) (#v: exp) (#hd: handler) (#t #r: typ)
  (h: typing sg ln g d (EHandle (plug fs (EPerform k op ss v)) hd) t r)
  : Pure (redex_facts sg ln g fs k op ss v hd t r)
         (requires sig_ok sg /\ wf_ctx sg g /\ not (inconsistent (hyps g)) /\ ev_k k fs /\
                   handler_key hd == k)
         (ensures fun _ -> True) =
  let p = EPerform k op ss v in
  let hi = inv_handle h in
  let _ = hi.hi_facts in
  perform_not_value sg k op ss v;
  let pi = plug_typing #sg #ln #g #[] #fs #p #hd.h_ret_ty #(TRowExt hd.h_ent hi.hi_r) hi.hi_body in
  let _ = pi.p_rows in
  let pf = inv_perform #sg #ln #g #pi.p_d #k #op #ss #v #pi.p_t #pi.p_r pi.p_hole in
  let _ = pf.pf_facts in
  assert (eff_entries_in k pi.p_r (TRowExt hd.h_ent hi.hi_r));
  handled_entry sg g hd.h_ent hi.hi_r pi.p_r k hi.hi_lbl hi.hi_q pf.pf_q hi.hi_ts pf.pf_ts;
  check_tys_length sg g ss pf.pf_os.binders;
  cover_clause_of hi.hi_ei hd.h_clauses op pf.pf_os;
  { rf_h = hi; rf_os = pf.pf_os; rf_facts = () }

(* The continuation type of a `full` clause, instantiated, is a function
   type. *)
let full_kt_fun (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#op: opname) (#nb: nat) (#s #kt: typ) (#body: exp)
  (fc: full_clause_inv sg ln g ei ts r b op nb s kt body) (ss: list typ) (os: op_sig)
  : Lemma (requires sig_ok sg /\ op_of ei op == Some os /\ check_tys sg g ss os.binders)
          (ensures Some? (as_function sg (sub_ty (binders_tsub ss) kt))) =
  let _ = fc.fc_facts in
  let sigma = binders_tsub ss in
  let a0 = eff_inst nb ts os.res in
  let r0 = ren_ty (shift nb) r in
  let b0 = ren_ty (shift nb) b in
  ty_sub_ok_tys sg g ss os.binders;
  check_sub sg sigma (push_tvars g os.binders) g kt KType;
  ty_eq_sub sigma kt (t_fun a0 r0 b0);
  sub_t_fun sigma a0 r0 b0;
  kinded_fun_as_function sg g (sub_ty sigma kt) (sub_ty sigma a0) (sub_ty sigma r0) (sub_ty sigma b0)

let handled_perform_redex #sg #gi #ln #rs #d #fs #k #op #ss #v #hd #t #r h =
  let g = closed_ctx rs in
  rctx_ok_wf_ctx sg rs;
  closed_ctx_consistent rs;
  let o = redex_facts_of #sg #ln #g #d #fs #k #op #ss #v #hd #t #r h in
  let hi = o.rf_h in
  let _ = hi.hi_facts in
  let _ = o.rf_facts in
  let os = o.rf_os in
  let Some c = clause_of op hd.h_clauses in
  clause_of_mem op hd.h_clauses c;
  match c with
  | CFull _ nb s kt body ->
    let fc = full_clause_typing hi.hi_cls op nb s kt body in
    let _ = fc.fc_facts in
    full_kt_fun fc ss os;
    let Some (tp, rho, bt) = as_function sg (sub_ty (binders_tsub ss) kt) in
    (| CTerm (full_reduct ss v tp rho fs hd body),
       EH_Full #sg #gi #fs #k #op #ss #v #hd #hi.hi_lbl #hi.hi_q #hi.hi_ts #hi.hi_ei #os #nb #s
         #kt #body #tp #rho #bt () () () () () |)
  | CFast _ nb s body ->
    let sc = fast_clause_typing hi.hi_cls op nb s body in
    let _ = sc.sc_facts in
    (| CTerm (fast_reduct hi.hi_ts ss os v fs hd body),
       EH_Fast #sg #gi #fs #k #op #ss #v #hd #hi.hi_lbl #hi.hi_q #hi.hi_ts #hi.hi_ei #os #nb #s
         #body () () () () |)

(* * The unhandled `perform` *)

let perform_untypable (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t: typ)
  (h: typing sg ln g d e t TRowEmpty) (fs: list frame) (k: key) (op: opname) (ss: list typ)
  (v: exp)
  : Lemma (requires sig_ok sg /\ wf_ctx sg g /\ e == plug fs (EPerform k op ss v) /\ ev_k k fs)
          (ensures False) =
  let p = EPerform k op ss v in
  perform_not_value sg k op ss v;
  let pi = plug_typing #sg #ln #g #d #fs #p #t #TRowEmpty (retm h (plug fs p)) in
  let _ = pi.p_rows in
  let pf = inv_perform #sg #ln #g #pi.p_d #k #op #ss #v #pi.p_t #pi.p_r pi.p_hole in
  let _ = pf.pf_facts in
  assert (eff_entries_in k pi.p_r TRowEmpty);
  assert_norm (row_entries (canon TRowEmpty) == [])

let unhandled_perform_untypable #sg #ln #g #d #e #t h =
  introduce forall (fs: list frame) (k: key) (op: opname) (ss: list typ) (v: exp).
      ~(e == plug fs (EPerform k op ss v) /\ ev_k k fs /\ frames_ok sg fs)
  with introduce (e == plug fs (EPerform k op ss v) /\ ev_k k fs /\ frames_ok sg fs) ==> False
  with perform_untypable h fs k op ss v
