(* Proof structure.

   A telescope is instantiated one binder at a time from the outside in:
   `push_tvars g (κ :: κ̄) = push_tvars (push_tvar g κ) κ̄`, and each binder
   puts its substitute in front of the substitution so far (`scons`). The
   step is `ty_sub_ok_scons`, proved as `ty_sub_ok_subst1` is, with an
   arbitrary substitution behind the new substitute: the stored types of
   `push_tvar g κ` are those of `g` shifted by one, and `scons s σ` after
   `↑1` is `σ` (`sub_ren_*`). The substitution the steps build
   (`stack σ̄ tvar`) agrees pointwise with `list_tsub (rev σ̄)`
   (`stack_index`), and `ty_sub_ok` reads a substitution pointwise
   (`ty_sub_ok_ext`).

   `op_inst τ̄ σ̄` and `eff_inst m τ̄` are substitutions by lists; the
   effect's arguments enter them pointwise, so arguments with equal
   canonical forms give equal instances (`ty_eq_sub_pointwise`). *)
module Stella.Core.Typing.Subst.Tys
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Entail
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Facts
open Stella.Core.Typing.Aux
open Stella.Core.Typing
open Stella.Core.Typing.Subst.Ty
open Stella.Core.Typing.Rename.Facts
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

(* Lists. *)

let rec nth_map (#a #b: Type) (f: a -> b) (l: list a) (i: nat)
  : Lemma (ensures L.nth (L.map f l) i == map_opt f (L.nth l i)) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> if i = 0 then () else nth_map f l (i - 1)

let rec assoc_ren_regions (xi: ren) (rs: list (atom & layout)) (a: atom)
  : Lemma (ensures L.assoc a (L.map (ren_region xi) rs) == map_opt (ren_layout xi) (L.assoc a rs))
          (decreases rs) =
  match rs with
  | [] -> ()
  | _ :: rs -> assoc_ren_regions xi rs a

let rec map_wit (#a #b: eqtype) (f: a -> b) (l: list a) (y: b)
  : Pure a (requires L.mem y (L.map f l)) (ensures fun x -> L.mem x l /\ f x == y) (decreases l) =
  match l with
  | x :: tl -> if f x = y then x else map_wit f tl y

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

let rec rev_index (#a: Type) (l: list a) (i: nat)
  : Lemma (requires i < L.length l)
          (ensures L.length (L.rev l) == L.length l /\
                   L.index (L.rev l) i == L.index l (L.length l - 1 - i))
          (decreases l) =
  LP.rev_length l;
  match l with
  | x :: l' ->
    rev_cons x l';
    LP.rev_length l';
    if i < L.length l' then begin
      index_append_left (L.rev l') [x] i;
      rev_index l' i
    end else index_append_last (L.rev l') x

(* One binder. *)

let ty_sub_ok_scons sg sigma g g' k s =
  let th = scons s sigma in
  hyps_push_tvar g k;
  rdom_push_tvar g k;
  check_lc sg g' s k;
  introduce forall (h: constr).
    L.mem h (hyps (push_tvar g k)) ==> entails (hyps g') (sub_constr th h)
  with introduce _ ==> _
  with begin
    let h0 = map_wit (ren_constr (shift 1)) (hyps g) h in
    sub_ren_constr th (shift 1) sigma h0
  end;
  introduce forall (i: nat).
    (match L.nth (push_tvar g k).tvars i with
     | Some ki -> check sg g' (th i) ki
     | None -> True)
  with (if i = 0 then () else assert (L.nth (push_tvar g k).tvars i == L.nth g.tvars (i - 1)));
  introduce forall (i: nat). lc_ty (th i)
  with (if i = 0 then () else ());
  introduce forall (i: nat). (match L.nth (push_tvar g k).vars i with
                              | Some t -> L.nth g'.vars i == Some (sub_ty th t)
                              | None -> True)
  with begin
    nth_map (ren_ty (shift 1)) g.vars i;
    match L.nth g.vars i with
    | Some t -> sub_ren_ty th (shift 1) sigma t
    | None -> ()
  end;
  introduce forall (a: atom). (match L.assoc a (push_tvar g k).regions with
                               | Some l -> L.assoc a g'.regions == Some (sub_layout th l)
                               | None -> True)
  with begin
    assoc_ren_regions (shift 1) g.regions a;
    match L.assoc a g.regions with
    | Some l -> sub_ren_layout th (shift 1) sigma l
    | None -> ()
  end

(* The telescope. *)

let rec stack (ss: list typ) (sigma: tsub) : Tot tsub (decreases ss) =
  match ss with
  | [] -> sigma
  | s :: ss -> stack ss (scons s sigma)

let rec ty_sub_ok_stack (sg: sig) (sigma: tsub) (g g': ctx) (ss: list typ) (ks: list kind)
  : Lemma (requires ty_sub_ok sg sigma g g' /\ check_tys sg g' ss ks)
          (ensures ty_sub_ok sg (stack ss sigma) (push_tvars g ks) g')
          (decreases ss) =
  match ss, ks with
  | [], [] -> ()
  | s :: ss', k :: ks' ->
    ty_sub_ok_scons sg sigma g g' k s;
    ty_sub_ok_stack sg (scons s sigma) (push_tvar g k) g' ss' ks'

let rec stack_index (ss: list typ) (sigma: tsub) (i: nat)
  : Lemma (ensures L.length (L.rev ss) == L.length ss /\
                   stack ss sigma i ==
                   (if i < L.length ss then L.index (L.rev ss) i else sigma (i - L.length ss)))
          (decreases ss) =
  LP.rev_length ss;
  match ss with
  | [] -> ()
  | s :: ss' ->
    stack_index ss' (scons s sigma) i;
    rev_cons s ss';
    LP.rev_length ss';
    if i < L.length ss' then index_append_left (L.rev ss') [s] i
    else if i = L.length ss' then index_append_last (L.rev ss') s
    else ()

let ty_sub_ok_id (sg: sig) (g: ctx) : Lemma (ty_sub_ok sg tvar g g) =
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps g) (sub_constr tvar h)
  with introduce _ ==> _
  with begin
    sub_id_constr tvar h;
    Stella.Core.Entail.Lemmas.entails_hyp (hyps g) h
  end;
  introduce forall (i: nat). (match L.nth g.vars i with
                              | Some t -> L.nth g.vars i == Some (sub_ty tvar t)
                              | None -> True)
  with (match L.nth g.vars i with Some t -> sub_ty_tvar t | None -> ());
  introduce forall (a: atom). (match L.assoc a g.regions with
                               | Some l -> L.assoc a g.regions == Some (sub_layout tvar l)
                               | None -> True)
  with (match L.assoc a g.regions with Some l -> sub_id_layout tvar l | None -> ())

let ty_sub_ok_tys sg g ss ks =
  let sigma = list_tsub (L.rev ss) in
  ty_sub_ok_id sg g;
  ty_sub_ok_stack sg tvar g g ss ks;
  introduce forall (i: nat). sigma i == stack ss tvar i
  with stack_index ss tvar i;
  ty_sub_ok_ext sg (stack ss tvar) sigma (push_tvars g ks) g

(* The judgement. *)

let typing_subst_tys #sg #ln #g #ks #d #e #t #r h ss =
  ty_sub_ok_tys sg g ss ks;
  typing_sub_ty h (list_tsub (L.rev ss)) g

let rec push_vars_tvars (g: ctx) (ts: list typ)
  : Lemma (ensures (push_vars g ts).tvars == g.tvars /\ (push_vars g ts).nk == g.nk)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> push_vars_tvars (push_var g t) ts'

let typing_subst_tys_vars #sg #ln #g #ks #ts #d #e #t #r h ss =
  let sigma = list_tsub (L.rev ss) in
  ty_sub_ok_tys sg g ss ks;
  ty_sub_ok_push_vars sg sigma (push_tvars g ks) g ts;
  push_vars_tvars g (sub_tys sigma ts);
  typing_sub_ty h sigma (push_vars g (sub_tys sigma ts))

(* Types under the binders. *)

let rec check_tys_length sg g ss ks =
  match ss, ks with
  | [], [] -> ()
  | _ :: ss', _ :: ks' -> check_tys_length sg g ss' ks'

let sub_tys_shift ss n t =
  LP.rev_length ss;
  sub_ren_ty (list_tsub (L.rev ss)) (shift n) tvar t;
  sub_ty_tvar t

let sub_tys_eff_inst ss ts n t =
  let sigma = list_tsub (L.rev ss) in
  introduce forall (i: nat). upn_tsub 0 sigma i == sigma i
  with ren_ty_shift0 (sigma i);
  sub_ty_ext (upn_tsub 0 sigma) sigma (eff_inst n ts t)

let rec canon_tys_length (ts ts': list typ)
  : Lemma (requires canon_tys ts == canon_tys ts') (ensures L.length ts' == L.length ts)
          (decreases ts) =
  match ts, ts' with
  | [], [] -> ()
  | _ :: tl, _ :: tl' -> canon_tys_length tl tl'

let rec canon_tys_index (ts ts': list typ) (i: nat)
  : Lemma (requires canon_tys ts == canon_tys ts' /\ i < L.length ts)
          (ensures L.length ts' == L.length ts /\ canon (L.index ts i) == canon (L.index ts' i))
          (decreases ts) =
  canon_tys_length ts ts';
  match ts, ts' with
  | _ :: tl, _ :: tl' -> if i = 0 then () else canon_tys_index tl tl' (i - 1)

let op_inst_canon ts ts' ss t =
  let n = L.length ss in
  let a = list_tsub (L.rev ts) in
  let a' = list_tsub (L.rev ts') in
  canon_tys_length ts ts';
  LP.rev_length ts;
  LP.rev_length ts';
  introduce forall (j: nat). ty_eq (a j) (a' j)
  with begin
    if j < L.length ts then begin
      rev_index ts j;
      rev_index ts' j;
      canon_tys_index ts ts' (L.length ts - 1 - j)
    end else ()
  end;
  introduce forall (i: nat). ty_eq (upn_tsub n a i) (upn_tsub n a' i)
  with (if i < n then () else ty_eq_ren (shift n) (a (i - n)) (a' (i - n)));
  ty_eq_sub_pointwise (upn_tsub n a) (upn_tsub n a') t;
  ty_eq_sub (upn_tsub 0 (list_tsub (L.rev ss))) (eff_inst n ts t) (eff_inst n ts' t)
