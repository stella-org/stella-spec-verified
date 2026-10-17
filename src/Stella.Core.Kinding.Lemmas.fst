(* Proof structure.

   `synth_result` is by induction on the type: a constructor's kind
   produces `Type` by `tycons_wf` and kind instantiation keeps that
   (`kinst_result`); the function of an application has an arrow kind
   producing `Type`, either from `Σ` or, for a variable, because its kind is
   a `qkind`. A row of kind `Row e` that is not a row former therefore has
   synthesized `Row e`, which does not produce `Type`, so it is a variable;
   `check_row_tails` follows by induction on the row, the tails of an
   extension or a union being those of its parts (`view_nrow`). *)
module Stella.Core.Kinding.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.OrdSet
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
module L = FStar.List.Tot

let rec kinst_result (ks: list kind) (k: kind)
  : Lemma (requires result k = KType) (ensures result (kinst_kind ks k) = KType) (decreases k) =
  match k with
  | KArrow _ k2 -> kinst_result ks k2
  | _ -> ()

let tycons_wf_at (sg: sig) (q: qname)
  : Lemma (requires tycons_wf sg /\ Some? (sg.tycons q))
          (ensures tycon_ok (Some?.v (sg.tycons q))) = ()

let rec qkinds_wf_nth (nk: nat) (ks: list kind) (i: nat)
  : Lemma (requires qkinds_wf nk ks /\ Some? (L.nth ks i))
          (ensures qkind nk (Some?.v (L.nth ks i))) (decreases ks) =
  match ks with
  | _ :: ks -> if i = 0 then () else qkinds_wf_nth nk ks (i - 1)

let rec synth_result (sg: sig) (g: ctx) (t: typ) =
  match t with
  | TCon q ks -> tycons_wf_at sg q; kinst_result ks (Some?.v (sg.tycons q)).tc_kind
  | TApp t1 _ ->
    synth_result sg g t1;
    (match t1 with
     | TVar i -> qkinds_wf_nth g.nk g.tvars i
     | _ -> ())
  | _ -> ()

let rec check_row_tails (sg: sig) (g: ctx) (r: typ) (e: elt_kind) =
  match r with
  | TRowEmpty -> ()
  | TRowExt en r1 ->
    check_row_tails sg g r1 e;
    view_nrow (canon_ent en :: row_entries (canon r1)) (row_tails (canon r1))
  | TRowUnion r1 r2 ->
    check_row_tails sg g r1 e;
    check_row_tails sg g r2 e;
    let v1 = view_row (canon r1) in
    let v2 = view_row (canon r2) in
    view_nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2));
    FStar.List.Tot.Properties.append_mem_forall (snd v1) (snd v2)
  | _ -> synth_result sg g r

let rec var_tails_intro (ts: list ctyp)
  : Lemma (requires forall (c: ctyp). L.mem c ts ==> CVar? c) (ensures var_tails ts)
          (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts -> var_tails_intro ts

let check_row_var_tails (sg: sig) (g: ctx) (r: typ) (e: elt_kind)
  : Lemma (requires tycons_wf sg /\ tvars_wf g /\ check sg g r (KRow e))
          (ensures var_tails (row_tails (canon r))) =
  check_row_tails sg g r e;
  var_tails_intro (row_tails (canon r))

let constr_ok_var_tailed (sg: sig) (g: ctx) (c: constr) =
  match c with
  | CLacks _ r ->
    if check sg g r (KRow EType) then check_row_var_tails sg g r EType
    else check_row_var_tails sg g r EEffect
  | CDisj r1 r2 ->
    if check sg g r1 (KRow EType) && check sg g r2 (KRow EType) then begin
      check_row_var_tails sg g r1 EType;
      check_row_var_tails sg g r2 EType
    end else begin
      check_row_var_tails sg g r1 EEffect;
      check_row_var_tails sg g r2 EEffect
    end

let rec constrs_ok_var_tailed (sg: sig) (g: ctx) (cs: list constr)
  : Lemma (requires tycons_wf sg /\ tvars_wf g /\ constrs_ok sg g cs)
          (ensures var_tailed_all cs) (decreases cs) =
  match cs with
  | [] -> ()
  | c :: cs -> constr_ok_var_tailed sg g c; constrs_ok_var_tailed sg g cs

let wf_hyps_var_tailed (sg: sig) (g: ctx) = constrs_ok_var_tailed sg g (hyps g)

let ex_falso_app (sg: sig) (g: ctx) (q: qname) (k: kind) = ()

let rec nth_none (#a: Type) (l: list a) (i: nat)
  : Lemma (requires L.length l <= i) (ensures L.nth l i == None) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> nth_none l (i - 1)

let ex_falso_unbound (sg: sig) (g: ctx) (i: nat) (k: kind) = nth_none g.tvars i

let ex_falso_sharpness (sg: sig) (g: ctx) (k: key) (t: typ) = ()
