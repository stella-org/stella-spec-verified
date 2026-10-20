(* Proof structure.

   Each instance is `Stella.Core.Typing.Subst.Tm` at one substitution from
   `push_vars g ts` to `g`: index `i < |ts|` takes the value at position `i`
   of the reversed values, which has the type at position `i` of the
   reversed telescope, and an index above them is the variable of `g` it
   stood for. The values are retyped at `()`, under no join point
   (`Stella.Core.Typing.Values`), and their scope in `g`
   (`Stella.Core.Typing.Scope`) gives the syntactic conditions. A single
   value is the telescope of one binder, `subst1_tm v` being pointwise
   `list_esub [v]`. The contractum of β is substituted under no join
   point, then moved to the `Δ` of the redex
   (`Stella.Core.Typing.Join.typing_jp_nil`). *)
module Stella.Core.Typing.Subst.Tm.Inst
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Tm
open Stella.Core.Region
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Wf
open Stella.Core.Typing.Regularity
open Stella.Core.Typing.Scope
open Stella.Core.Typing.Join
open Stella.Core.Typing.Values
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Subst.Tm
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

(* Lists. *)

let rec nth_append (#a: Type) (l1 l2: list a) (i: nat)
  : Lemma (ensures L.nth (L.append l1 l2) i ==
                   (if i < L.length l1 then L.nth l1 i else L.nth l2 (i - L.length l1)))
          (decreases l1) =
  match l1 with
  | [] -> ()
  | _ :: l1' -> if i = 0 then () else nth_append l1' l2 (i - 1)

let rec nth_index (#a: Type) (l: list a) (i: nat)
  : Lemma (requires i < L.length l) (ensures L.nth l i == Some (L.index l i)) (decreases l) =
  match l with
  | _ :: l' -> if i = 0 then () else nth_index l' (i - 1)

let rec index_append_left (#a: Type) (l1 l2: list a) (i: nat)
  : Lemma (requires i < L.length l1)
          (ensures i < L.length (L.append l1 l2) /\ L.index (L.append l1 l2) i == L.index l1 i)
          (decreases l1) =
  LP.append_length l1 l2;
  match l1 with
  | _ :: l1' -> if i = 0 then () else index_append_left l1' l2 (i - 1)

let rec index_append_last (#a: Type) (l1: list a) (x: a)
  : Lemma (ensures L.length (L.append l1 [x]) == L.length l1 + 1 /\
                   L.index (L.append l1 [x]) (L.length l1) == x)
          (decreases l1) =
  LP.append_length l1 [x];
  match l1 with
  | [] -> ()
  | _ :: l1' -> index_append_last l1' x

let rev_cons (#a: Type) (x: a) (l: list a) : Lemma (L.rev (x :: l) == L.append (L.rev l) [x]) =
  LP.rev_rev' (x :: l);
  LP.rev_rev' l

(* The context of a telescope. *)

let rec push_vars_shape (g: ctx) (ts: list typ)
  : Lemma (ensures push_vars g ts == { g with vars = L.append (L.rev ts) g.vars }) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' ->
    push_vars_shape (push_var g t) ts';
    rev_cons t ts';
    LP.append_assoc (L.rev ts') [t] g.vars

let push_vars_ext (g: ctx) (ts: list typ)
  : Lemma (ctx_ext (push_vars g ts) g /\ layouts_ext (push_vars g ts) g) =
  push_vars_shape g ts;
  introduce forall (h: constr). L.mem h (hyps (push_vars g ts)) ==> entails (hyps g) h
  with introduce _ ==> _
  with entails_hyp (hyps g) h

(* The values, read from the end. *)

let rec exps_length (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts)
  : Lemma (ensures L.length es == L.length ts) (decreases h) =
  match h with
  | TE_Nil _ -> ()
  | TE_Cons _ h2 -> exps_length h2

let rec rev_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#vs: list exp) (#ts: list typ) (h: exps_typing sg ln g d r vs ts) (i: nat)
  : Pure (typing sg ln g d (L.index (L.rev vs) i) (L.index (L.rev ts) i) r)
         (requires L.for_all (V.is_value sg) vs /\ i < L.length vs /\
                   L.length (L.rev vs) == L.length vs /\ L.length (L.rev ts) == L.length ts /\
                   L.length vs == L.length ts)
         (ensures fun _ -> V.is_value sg (L.index (L.rev vs) i))
         (decreases h) =
  match h with
  | TE_Cons #_ #_ #_ #_ #_ #v #vs' #t #ts' h1 h2 ->
    rev_cons v vs';
    rev_cons t ts';
    LP.rev_length vs';
    LP.rev_length ts';
    exps_length h2;
    if i < L.length vs' then begin
      index_append_left (L.rev vs') [v] i;
      index_append_left (L.rev ts') [t] i;
      rev_typing h2 i
    end else begin
      index_append_last (L.rev vs') v;
      index_append_last (L.rev ts') t;
      h1
    end

(* The substitution of a telescope of values. *)

let values_sub_ok (#sg: sig) (#ln: lctx) (#g: ctx) (#d0: jctx) (#r0: typ)
  (#vs: list exp) (#ts: list typ) (hvs: exps_typing sg ln g d0 r0 vs ts)
  : Pure (tm_sub_ok sg ln (list_esub (L.rev vs)) (push_vars g ts) g)
         (requires sig_ok sg /\ wf_ctx sg g /\ L.for_all (V.is_value sg) vs)
         (ensures fun _ -> True) =
  let n = L.length vs in
  let sigma = list_esub (L.rev vs) in
  exps_length hvs;
  LP.rev_length vs;
  LP.rev_length ts;
  push_vars_shape g ts;
  push_vars_ext g ts;
  let ent (i: nat{i < n})
    : Pure (sub_entry sg ln g (sigma i) (L.index (L.rev ts) i))
           (requires True) (ensures fun _ -> V.jp_scoped 0 (sigma i) /\ lc_exp (sigma i)) =
    let hv = rev_typing hvs i in
    typing_scoped hv;
    V.value_jp_scoped sg (L.length d0) (sigma i);
    SE_Val () (value_typing hv [] TRowEmpty)
  in
  introduce forall (i: nat). V.jp_scoped 0 (sigma i) /\ lc_exp (sigma i)
  with (if i < n then let _ = ent i in () else ());
  let f (i: nat) (t: typ) (_: squash (L.nth (push_vars g ts).vars i == Some t))
    : sub_entry sg ln g (sigma i) t =
    nth_append (L.rev ts) g.vars i;
    if i < n then begin
      nth_index (L.rev ts) i;
      ent i
    end else SE_Var (i - n) ()
  in
  TmSubOk () f

let singleton_typing (#sg: sig) (#ln: lctx) (#g: ctx) (#d0: jctx) (#v: exp)
  (#t1 #r0: typ) (hv: typing sg ln g d0 v t1 r0)
  : Pure (exps_typing sg ln g d0 r0 [v] [t1])
         (requires sig_ok sg /\ wf_ctx sg g) (ensures fun _ -> True) =
  typing_regular hv;
  TE_Cons hv (TE_Nil ())

let subst1_list (v: exp) : Lemma (forall (i: nat). list_esub (L.rev [v]) i == scons v evar i) =
  assert_norm (L.rev [v] == [v])

let sub_tm_dt_ext (sigma sigma': esub) (dt: dtree)
  : Lemma (requires forall (i: nat). sigma i == sigma' i)
          (ensures sub_tm_dt sigma dt == sub_tm_dt sigma' dt) =
  sub_id_tm_dt evar dt;
  sub_sub_tm_dt sigma evar sigma' dt

(* The instances. *)

let typing_subst1_value #sg #ln #g #t1 #d #e #t #r h #d0 #v #r0 hv =
  let hs = values_sub_ok (singleton_typing hv) in
  subst1_list v;
  sub_tm_ext (list_esub (L.rev [v])) (scons v evar) e;
  typing_sub_tm h hs

let typing_beta #sg #ln #g #t1 #body #t2 #r' hb #d0 #v #r0 hv d =
  typing_jp_nil (typing_subst1_value hb hv) d

let typing_let_value #sg #ln #g #t1 #d #e2 #t #r h2 #v hv = typing_subst1_value h2 hv

let typing_subst_values #sg #ln #g #ts #d #e #t #r h #d0 #r0 #vs hvs =
  typing_sub_tm h (values_sub_ok hvs)

let dt_typing_bind_value #sg #ln #g #t_o #d #om #dt #t #r h #d0 #v #r0 hv =
  let hs = values_sub_ok (singleton_typing hv) in
  subst1_list v;
  sub_tm_dt_ext (list_esub (L.rev [v])) (scons v evar) dt;
  dt_typing_sub_tm h hs
