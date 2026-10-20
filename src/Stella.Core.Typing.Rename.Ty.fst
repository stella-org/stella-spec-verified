(* Proof structure.

   The context lemmas take the kinding part from `Stella.Core.Kinding.Subst`
   (`ren_ok_up`, `ren_ok_assumps`, `ren_ok_shift`) and prove the two maps of
   stored types directly: a term variable's type and a region's layout are
   shifted on both sides under a type binder, and the σ-calculus law
   `↑1 ; up ξ = ξ ; ↑1` (`ren_shift_up`) relates them. A fact a region adds
   names a `Row Effect` variable, whose image has the same kind, so the
   image fact is among the facts the renamed region adds.

   The judgements are one mutual induction on the derivation. Each rule's
   premises are renamed by the induction hypothesis, its side conditions by
   the lemmas on kinding (`check_ren`), entailment, type equality
   (`ty_eq_ren`), rows and declared types (`Stella.Core.Typing.Rename.Facts`),
   and its conclusion is cast to the renamed indices, which are equal to
   the ones the rule builds. *)
module Stella.Core.Typing.Rename.Ty
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Region
open Stella.Core.Region.Lemmas
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Subst
open Stella.Core.Kinding.Facts
open Stella.Core.Prim
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Keys
open Stella.Core.Typing.Rename.Facts
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value
module IR = Stella.Core.Init.Rename

(* Lists. *)

let rec nth_map (#a #b: Type) (f: a -> b) (l: list a) (i: nat)
  : Lemma (ensures L.nth (L.map f l) i == map_opt f (L.nth l i)) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> if i = 0 then () else nth_map f l (i - 1)

let rec nth_length (#a: Type) (l: list a) (i: nat)
  : Lemma (requires Some? (L.nth l i)) (ensures i < L.length l) (decreases l) =
  match l with
  | _ :: tl -> if i = 0 then () else nth_length tl (i - 1)

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

(* Entailment by the renamed hypotheses. *)

let entails_into (xi: ren) (g g': ctx) (c: constr)
  : Lemma (requires ren_ok xi g g' /\ entails (hyps g) c)
          (ensures entails (hyps g') (ren_constr xi c)) =
  entails_ren xi (hyps g) c;
  introduce forall (h': constr). L.mem h' (L.map (ren_constr xi) (hyps g)) ==> entails (hyps g') h'
  with introduce _ ==> _
  with (let _ = map_wit (ren_constr xi) (hyps g) h' in ());
  entails_cut_all (L.map (ren_constr xi) (hyps g)) (hyps g') (ren_constr xi c)

(* The context morphism. *)

let ren_constr_ext (xi xi': ren) (c: constr)
  : Lemma (requires forall (i: nat). xi' i == xi i) (ensures ren_constr xi' c == ren_constr xi c) =
  ren_ren_constr xi id_ren xi' c;
  ren_id_constr id_ren c

let ren_layout_ext (xi xi': ren) (l: layout)
  : Lemma (requires forall (i: nat). xi' i == xi i) (ensures ren_layout xi' l == ren_layout xi l) =
  ren_ren_layout xi id_ren xi' l;
  ren_id_layout id_ren l

let ty_ren_ok_ext xi xi' g g' =
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps g') (ren_constr xi' h)
  with introduce _ ==> _
  with ren_constr_ext xi xi' h;
  introduce forall (i: nat). (match L.nth g.vars i with
                              | Some t -> L.nth g'.vars i == Some (ren_ty xi' t)
                              | None -> True)
  with (match L.nth g.vars i with
        | Some t -> ren_ty_ext xi xi' t
        | None -> ());
  introduce forall (a: atom). (match L.assoc a g.regions with
                               | Some l -> L.assoc a g'.regions == Some (ren_layout xi' l)
                               | None -> True)
  with (match L.assoc a g.regions with
        | Some l -> ren_layout_ext xi xi' l
        | None -> ())

let ty_ren_ok_up xi g g' k =
  ren_ok_up xi g g' k;
  introduce forall (i: nat). (match L.nth (push_tvar g k).vars i with
                              | Some t -> L.nth (push_tvar g' k).vars i
                                == Some (ren_ty (up_ren xi) t)
                              | None -> True)
  with begin
    nth_map (ren_ty (shift 1)) g.vars i;
    nth_map (ren_ty (shift 1)) g'.vars i;
    match L.nth g.vars i with
    | Some t -> ren_shift_up 1 xi t
    | None -> ()
  end;
  introduce forall (a: atom). (match L.assoc a (push_tvar g k).regions with
                               | Some l ->
                                 L.assoc a (push_tvar g' k).regions
                                   == Some (ren_layout (up_ren xi) l)
                               | None -> True)
  with begin
    assoc_ren_regions (shift 1) g.regions a;
    assoc_ren_regions (shift 1) g'.regions a;
    match L.assoc a g.regions with
    | Some l -> ren_layout_shift_up 1 xi l
    | None -> ()
  end

let rec ty_ren_ok_upn (xi: ren) (g g': ctx) (ks: list kind)
  : Lemma (requires ty_ren_ok xi g g')
          (ensures ty_ren_ok (upn_ren (L.length ks) xi) (push_tvars g ks) (push_tvars g' ks))
          (decreases ks) =
  match ks with
  | [] -> ty_ren_ok_ext xi (upn_ren 0 xi) g g'
  | k :: ks' ->
    ty_ren_ok_up xi g g' k;
    ty_ren_ok_upn (up_ren xi) (push_tvar g k) (push_tvar g' k) ks';
    ty_ren_ok_ext (upn_ren (L.length ks') (up_ren xi)) (upn_ren (L.length ks) xi)
      (push_tvars (push_tvar g k) ks') (push_tvars (push_tvar g' k) ks')

let ty_ren_ok_assumps xi g g' cs = ren_ok_assumps xi g g' cs

let ty_ren_ok_assump xi g g' c =
  add_assump_assumps g c;
  add_assump_assumps g' (ren_constr xi c);
  ty_ren_ok_assumps xi g g' [c]

let ty_ren_ok_push_var xi g g' t =
  let g1 = push_var g t in
  let g1' = push_var g' (ren_ty xi t) in
  assert (hyps g1 == hyps g /\ hyps g1' == hyps g');
  assert (rdom g1 == rdom g /\ rdom g1' == rdom g');
  introduce forall (i: nat). (match L.nth g1.vars i with
                              | Some t0 -> L.nth g1'.vars i == Some (ren_ty xi t0)
                              | None -> True)
  with (if i = 0 then () else assert (L.nth g.vars (i - 1) == L.nth g.vars (i - 1)))

let rec ty_ren_ok_push_vars (xi: ren) (g g': ctx) (ts: list typ)
  : Lemma (requires ty_ren_ok xi g g')
          (ensures ty_ren_ok xi (push_vars g ts) (push_vars g' (ren_tys xi ts)))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' ->
    ty_ren_ok_push_var xi g g' t;
    ty_ren_ok_push_vars xi (push_var g t) (push_var g' (ren_ty xi t)) ts'

(* The facts a region adds. *)

let rec region_facts_wit (a: atom) (d: nat) (ks: list kind) (h: constr)
  : Pure nat (requires L.mem h (region_facts a d ks))
         (ensures fun j -> h == CLacks (RegionKey (RFree a)) (TVar (d + j)) /\
                           L.nth ks j == Some (KRow EEffect))
         (decreases ks) =
  match ks with
  | k :: ks' ->
    if k = KRow EEffect && h = CLacks (RegionKey (RFree a)) (TVar d) then 0
    else 1 + region_facts_wit a (d + 1) ks' h

let rec region_facts_intro (a: atom) (d: nat) (ks: list kind) (j: nat)
  : Lemma (requires L.nth ks j == Some (KRow EEffect))
          (ensures L.mem (CLacks (RegionKey (RFree a)) (TVar (d + j))) (region_facts a d ks))
          (decreases ks) =
  match ks with
  | _ :: ks' -> if j = 0 then () else region_facts_intro a (d + 1) ks' (j - 1)

let mem_hyps_enter_region (g: ctx) (a: atom) (l: layout) (h: constr)
  : Lemma (L.mem h (hyps (enter_region g a l)) <==>
           L.mem h (region_facts a 0 g.tvars) \/ L.mem h (hyps g)) =
  LP.append_mem (L.append (region_facts a 0 g.tvars) g.facts) g.assumps h;
  LP.append_mem (region_facts a 0 g.tvars) g.facts h;
  LP.append_mem g.facts g.assumps h

let ty_ren_ok_enter_region xi g g' a l =
  let g1 = enter_region g a l in
  let g1' = enter_region g' a (ren_layout xi l) in
  rdom_enter_region g a l;
  rdom_enter_region g' a (ren_layout xi l);
  assert (g1.tvars == g.tvars /\ g1'.tvars == g'.tvars /\ g1.vars == g.vars /\ g1'.vars == g'.vars);
  introduce forall (h: constr). L.mem h (hyps g') ==> L.mem h (hyps g1')
  with mem_hyps_enter_region g' a (ren_layout xi l) h;
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g1') (ren_constr xi h)
  with introduce _ ==> _
  with begin
    mem_hyps_enter_region g a l h;
    if L.mem h (region_facts a 0 g.tvars) then begin
      let j = region_facts_wit a 0 g.tvars h in
      nth_length g.tvars j;
      assert (L.nth g.tvars j == L.nth g.tvars j);
      region_facts_intro a 0 g'.tvars (xi j);
      mem_hyps_enter_region g' a (ren_layout xi l) (ren_constr xi h);
      entails_hyp (hyps g1') (ren_constr xi h)
    end
    else entails_weaken (hyps g') (hyps g1') (ren_constr xi h)
  end;
  introduce forall (b: atom). (match L.assoc b g1.regions with
                               | Some l0 -> L.assoc b g1'.regions == Some (ren_layout xi l0)
                               | None -> True)
  with (if b = a then () else assert (L.assoc b g.regions == L.assoc b g.regions))

let ty_ren_ok_fresh xi g g' a body = frn_ren_ty_exp xi body

let ty_ren_ok_shift g k =
  ren_ok_shift g k;
  introduce forall (i: nat). (match L.nth g.vars i with
                              | Some t -> L.nth (push_tvar g k).vars i == Some (ren_ty (shift 1) t)
                              | None -> True)
  with nth_map (ren_ty (shift 1)) g.vars i;
  introduce forall (a: atom). (match L.assoc a g.regions with
                               | Some l ->
                                 L.assoc a (push_tvar g k).regions == Some (ren_layout (shift 1) l)
                               | None -> True)
  with assoc_ren_regions (shift 1) g.regions a

(* Side conditions. *)

let rec tys_ok_ren (sg: sig) (xi: ren) (g g': ctx) (ts: list typ)
  : Lemma (requires ren_ok xi g g' /\ tys_ok sg g ts) (ensures tys_ok sg g' (ren_tys xi ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> check_ren sg xi g g' t KType; tys_ok_ren sg xi g g' ts

let regions_incl_of (g g': ctx)
  : Lemma (requires rdom_incl g g') (ensures regions_incl g.regions g'.regions) =
  introduce forall (a: atom). L.mem a (L.map fst g.regions) ==> L.mem a (L.map fst g'.regions)
  with introduce _ ==> _
  with assert (L.mem a (rdom g))

(* A closed type of a run-time form stays kinded, and is fixed. *)
let closed_ren (sg: sig) (xi: ren) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires rdom_incl g g' /\ check sg (closed_ctx g.regions) t k)
          (ensures check sg (closed_ctx g'.regions) t k /\ ren_ty xi t == t) =
  regions_incl_of g g';
  check_closed_mono sg g.regions g'.regions t k;
  check_closed_ren sg g.regions t k xi

let rec scrut_occs_ren (xi: ren) (i: nat) (ts: list typ)
  : Lemma (ensures ren_octx xi (scrut_occs i ts) == scrut_occs i (ren_tys xi ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts -> scrut_occs_ren xi (i + 1) ts

let rec field_occs_ren (xi: ren) (o: occ) (c: qname) (j: nat) (fs: list typ)
  : Lemma (ensures ren_octx xi (field_occs o c j fs) == field_occs o c j (ren_tys xi fs))
          (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs -> field_occs_ren xi o c (j + 1) fs

let rec ren_octx_append (xi: ren) (om1 om2: octx)
  : Lemma (ensures ren_octx xi (L.append om1 om2) == L.append (ren_octx xi om1) (ren_octx xi om2))
          (decreases om1) =
  match om1 with
  | [] -> ()
  | _ :: om1 -> ren_octx_append xi om1 om2

let rec assoc_ren_octx (xi: ren) (om: octx) (o: occ)
  : Lemma (ensures L.assoc o (ren_octx xi om) == map_opt (ren_ty xi) (L.assoc o om))
    (decreases om) =
  match om with
  | [] -> ()
  | _ :: om -> assoc_ren_octx xi om o

let rec nth_ren_jctx (xi: ren) (d: jctx) (j: nat)
  : Lemma (ensures L.nth (ren_jctx xi d) j == map_opt (ren_jt xi) (L.nth d j)) (decreases d) =
  match d with
  | [] -> ()
  | _ :: d -> if j = 0 then () else nth_ren_jctx xi d (j - 1)

let rec clause_ops_ren (xi: ren) (cs: list clause)
  : Lemma (ensures clause_ops (ren_ty_cls xi cs) == clause_ops cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ _ :: cs | CFast _ _ _ _ :: cs -> clause_ops_ren xi cs

let eff_params_length (sg: sig) (g: ctx) (lbl: option string) (q: qname) (ts: list typ) (r: typ)
  (ei: effect_info)
  : Lemma (requires check sg g (TRowExt (EntEff lbl q ts) r) (KRow EEffect) /\
      sg.effects q == Some ei)
          (ensures L.length ts == L.length ei.eff_params) =
  check_ext sg g (EntEff lbl q ts) r EEffect;
  check_tys_length sg g ts ei.eff_params

(* Casts along equalities of indices. *)

let cast (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (d': jctx{d' == d}) (e': exp{e' == e}) (t': typ{t' == t})
  (r': typ{r' == r})
  : typing sg ln g d' e' t' r' = h

let cast_dt (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#dt: dtree)
  (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (om': octx{om' == om}) (t': typ{t' == t})
  (r': typ{r' == r})
  : dt_typing sg ln g d om' dt t' r' = h

(* The rules, one builder each. A builder takes the renamed premises,
   in the form the induction produces them, and the indices of the
   conclusion with their equations to the rule's parts, and concludes the
   renamed judgement. *)

let tr (sg: sig) (ln: lctx) (g': ctx) (xi: ren) (d: jctx) (e: exp) (t r: typ) : Type =
  typing sg ln g' (ren_jctx xi d) (ren_ty_exp xi e) (ren_ty xi t) (ren_ty xi r)

let ren_perform_eq (xi: ren) (k: key) (op: opname) (ss: list typ) (e1: exp)
  : Lemma (ren_ty_exp xi (EPerform k op ss e1)
      == EPerform k op (ren_tys xi ss) (ren_ty_exp xi e1)) = ()

let ren_tyapp_eq (xi: ren) (e0: exp) (s: typ)
  : Lemma (ren_ty_exp xi (ETyApp e0 s) == ETyApp (ren_ty_exp xi e0) (ren_ty xi s)) = ()

let ren_capp_eq (xi: ren) (e0: exp) : Lemma (ren_ty_exp xi (ECApp e0) == ECApp (ren_ty_exp xi e0)) =
  ()

let ren_app_eq (xi: ren) (e0 v: exp)
  : Lemma (ren_ty_exp xi (EApp e0 v) == EApp (ren_ty_exp xi e0) (ren_ty_exp xi v)) = ()

let ren_let_eq (xi: ren) (t1: typ) (e1 e2: exp)
  : Lemma (ren_ty_exp xi (ELet t1 e1 e2) == ELet (ren_ty xi t1) (ren_ty_exp xi e1) (ren_ty_exp xi e2)) =
  ()

let ren_letjoin_eq (xi: ren) (ts: list typ) (t: typ) (e1 e2: exp)
  : Lemma (ren_ty_exp xi (ELetJoin ts t e1 e2) ==
           ELetJoin (ren_tys xi ts) (ren_ty xi t) (ren_ty_exp xi e1) (ren_ty_exp xi e2)) = ()

let ren_extend_eq (xi: ren) (k: key) (e1 e2: exp)
  : Lemma (ren_ty_exp xi (EExtend k e1 e2) == EExtend k (ren_ty_exp xi e1) (ren_ty_exp xi e2)) = ()

let ren_update_eq (xi: ren) (k: key) (e1 e2: exp)
  : Lemma (ren_ty_exp xi (EUpdate k e1 e2) == EUpdate k (ren_ty_exp xi e1) (ren_ty_exp xi e2)) = ()

let ren_merge_eq (xi: ren) (e1 e2: exp)
  : Lemma (ren_ty_exp xi (EMerge e1 e2) == EMerge (ren_ty_exp xi e1) (ren_ty_exp xi e2)) = ()

let ren_inject_eq (xi: ren) (k: key) (r0: typ) (e1: exp)
  : Lemma (ren_ty_exp xi (EInject k r0 e1) == EInject k (ren_ty xi r0) (ren_ty_exp xi e1)) = ()

let ren_weaken_eq (xi: ren) (k: key) (t1: typ) (e1: exp)
  : Lemma (ren_ty_exp xi (EWeaken k t1 e1) == EWeaken k (ren_ty xi t1) (ren_ty_exp xi e1)) = ()

let ren_openeff_eq (xi: ren) (r2: typ) (e1: exp)
  : Lemma (ren_ty_exp xi (EOpenEff r2 e1) == EOpenEff (ren_ty xi r2) (ren_ty_exp xi e1)) = ()

let ren_openeffc_eq (xi: ren) (r2: typ) (e1: exp)
  : Lemma (ren_ty_exp xi (EOpenEffC r2 e1) == EOpenEffC (ren_ty xi r2) (ren_ty_exp xi e1)) = ()

let ren_writecell_eq (xi: ren) (a: region_ref) (k: key) (e1: exp)
  : Lemma (ren_ty_exp xi (EWriteCell a k e1) == EWriteCell a k (ren_ty_exp xi e1)) = ()

let ren_handle_eq (xi: ren) (e1: exp) (hd: handler)
  : Lemma (ren_ty_exp xi (EHandle e1 hd) ==
           EHandle (ren_ty_exp xi e1)
             { h_ent = ren_ent xi hd.h_ent; h_ret_ty = ren_ty xi hd.h_ret_ty;
               h_ret = ren_ty_exp xi hd.h_ret; h_clauses = ren_ty_cls xi hd.h_clauses }) = ()

let ren_union_eq (xi: ren) (r1 r2: typ)
  : Lemma (ren_ty xi (TRowUnion r1 r2) == TRowUnion (ren_ty xi r1) (ren_ty xi r2)) = ()

let ren_rec_union (xi: ren) (r1 r2: typ)
  : Lemma (ren_ty xi (t_record (TRowUnion r1 r2)) == t_record (TRowUnion (ren_ty xi r1) (ren_ty xi r2))) =
  ren_t_record xi (TRowUnion r1 r2)

let ren_rec_ext (xi: ren) (k: key) (t r0: typ)
  : Lemma (ren_ty xi (t_record (TRowExt (EntTy k t) r0)) ==
           t_record (TRowExt (EntTy k (ren_ty xi t)) (ren_ty xi r0))) =
  ren_t_record xi (TRowExt (EntTy k t) r0)

let ren_var_ext (xi: ren) (k: key) (t r0: typ)
  : Lemma (ren_ty xi (t_variant (TRowExt (EntTy k t) r0)) ==
           t_variant (TRowExt (EntTy k (ren_ty xi t)) (ren_ty xi r0))) =
  ren_t_variant xi (TRowExt (EntTy k t) r0)

let b_var (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (i: nat)
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EVar i /\ L.nth g.vars i == Some t /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_ren sg xi g g' r (KRow EEffect);
  assert (L.nth g.vars i == L.nth g.vars i);
  T_Var #sg #ln #g' #(ren_jctx xi d) #i #(ren_ty xi t) #(ren_ty xi r) () ()

let b_global (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (q: qname) (ks: list kind) (nk: nat) (t0: typ)
  : Pure (tr sg ln g' xi d e t r)
         (requires sig_ok sg /\ ty_ren_ok xi g g' /\ e == EGlobal q ks /\ t == kinst_ty ks t0 /\
                   global_type sg q == Some (nk, t0) /\ L.length ks == nk /\ qkinds_wf g.nk ks /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_ren sg xi g g' r (KRow EEffect);
  global_inst_ren sg q nk t0 ks xi;
  T_Global #sg #ln #g' #(ren_jctx xi d) #q #ks #nk #t0 #(ren_ty xi r) () () ()

let b_lit (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (c: lit)
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ELit c /\ t == lit_type c /\
             check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_ren sg xi g g' r (KRow EEffect);
  ren_lit_type xi c;
  T_Lit #sg #ln #g' #(ren_jctx xi d) #c #(ren_ty xi r) ()

let b_lam (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1 r1: typ) (body: exp) (t2: typ)
  (hb: typing sg ln (push_var g' (ren_ty xi t1)) (ren_jctx xi []) (ren_ty_exp xi body)
         (ren_ty xi t2) (ren_ty xi r1))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ELam t1 r1 body /\ t == t_fun t1 r1 t2 /\
                   check sg g t1 KType /\ check sg g r1 (KRow EEffect) /\
                     check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_ren sg xi g g' t1 KType;
  check_ren sg xi g g' r1 (KRow EEffect);
  check_ren sg xi g g' r (KRow EEffect);
  ren_t_fun xi t1 r1 t2;
  T_Lam #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi t1) #(ren_ty xi r1) #(ren_ty_exp xi body)
    #(ren_ty xi t2) #(ren_ty xi r) () () hb

let b_app (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1 e2: exp) (t1 t2: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi (t_fun t1 r t2))
      (ren_ty xi r))
  (h2: typing sg ln g' [] (ren_ty_exp xi e2) (ren_ty xi t1) (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r) (requires e == EApp e1 e2 /\ t == t2) (ensures fun _ -> True) =
  ren_app_eq xi e1 e2;
  ren_t_fun xi t1 r t2;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1)
             (t_fun (ren_ty xi t1) (ren_ty xi r) (ren_ty xi t2)) (ren_ty xi r) = h1 in
  T_App h1 h2

let b_chain (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t0: typ) (th: tsub)
  (hc: chain_typing sg ln g' [] (ren_ty xi r) (ren_ty_exp xi e))
  : Pure (tr sg ln g' xi d e t r)
         (requires sig_ok sg /\ chain_cursor sg e == Some (t0, th) /\ t == sub_ty th t0)
         (ensures fun _ -> True) =
  chain_cursor_ren_ty sg xi e t0 th;
  let Some (_, th') = chain_cursor sg (ren_ty_exp xi e) in
  T_Chain #sg #ln #g' #(ren_jctx xi d) #(ren_ty_exp xi e) #t0 #th' #(ren_ty xi r) hc ()

let b_tylam (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: kind) (body: exp) (t0: typ)
  (hb: typing sg ln (push_tvar g' k) (ren_jctx (up_ren xi) []) (ren_ty_exp (up_ren xi) body)
         (ren_ty (up_ren xi) t0) (ren_ty (up_ren xi) TRowEmpty))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ETyLam k body /\ t == TForall k t0 /\
                   kind_wf g.nk k /\ qkind g.nk k /\ value_form sg body /\
                     check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  value_form_ren_ty sg (up_ren xi) body;
  check_ren sg xi g g' r (KRow EEffect);
  let hb : typing sg ln (push_tvar g' k) [] (ren_ty_exp (up_ren xi) body)
    (ren_ty (up_ren xi) t0)
             TRowEmpty = hb in
  T_TyLam #sg #ln #g' #(ren_jctx xi d) #k #(ren_ty_exp (up_ren xi) body)
    #(ren_ty (up_ren xi) t0)
    #(ren_ty xi r) () () () hb

let b_tyapp (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1: exp) (s: typ) (k: kind) (t0: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi (TForall k t0))
      (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ETyApp e1 s /\ t == subst1_ty s t0 /\ check sg g s k)
         (ensures fun _ -> True) =
  check_ren sg xi g g' s k;
  ren_subst1 xi s t0;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1)
    (TForall k (ren_ty (up_ren xi) t0))
             (ren_ty xi r) = h1 in
  T_TyApp #sg #ln #g' #(ren_jctx xi d) #(ren_ty_exp xi e1) #(ren_ty xi s) h1 ()

let b_clam (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (c: constr) (body: exp) (t0: typ)
  (hb: typing sg ln (add_assump g' (ren_constr xi c)) (ren_jctx xi []) (ren_ty_exp xi body)
         (ren_ty xi t0) (ren_ty xi TRowEmpty))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ECLam c body /\ t == TConstr c t0 /\ constr_ok sg g c
             /\
                   value_form sg body /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  constr_ok_ren sg xi g g' c;
  value_form_ren_ty sg xi body;
  check_ren sg xi g g' r (KRow EEffect);
  let hb : typing sg ln (add_assump g' (ren_constr xi c)) [] (ren_ty_exp xi body)
    (ren_ty xi t0)
             TRowEmpty = hb in
  T_CLam #sg #ln #g' #(ren_jctx xi d) #(ren_constr xi c) #(ren_ty_exp xi body) #(ren_ty xi t0)
    #(ren_ty xi r) () () () hb

let b_capp (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1: exp) (c: constr)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi (TConstr c t))
      (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ECApp e1 /\ entails (hyps g) c)
         (ensures fun _ -> True) =
  entails_into xi g g' c;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1)
    (TConstr (ren_constr xi c) (ren_ty xi t))
             (ren_ty xi r) = h1 in
  T_CApp h1 ()

let b_let (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1: typ) (e1 e2: exp)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi t1) (ren_ty xi r))
  (h2: typing sg ln (push_var g' (ren_ty xi t1)) (ren_jctx xi d) (ren_ty_exp xi e2) (ren_ty xi t)
         (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ELet t1 e1 e2 /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  ren_let_eq xi t1 e1 e2;
  check_ren sg xi g g' t1 KType;
  T_Let () h1 h2

let b_letrec (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (bs: list (typ & exp)) (body: exp)
  (hbs: binds_typing sg ln (push_vars g' (ren_tys xi (L.map fst bs))) (ren_ty_binds xi bs))
  (hb: typing sg ln (push_vars g' (ren_tys xi (L.map fst bs))) (ren_jctx xi d)
      (ren_ty_exp xi body)
         (ren_ty xi t) (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires e == ELetRec bs body /\ Stella.Core.Init.init_safe_letrec sg bs)
         (ensures fun _ -> True) =
  IR.init_safe_ren_ty sg xi bs;
  ren_ty_binds_fst xi bs;
  T_LetRec #sg #ln #g' #(ren_jctx xi d) #(ren_ty_binds xi bs) #(ren_ty_exp xi body)
    #(ren_ty xi t)
    #(ren_ty xi r) () hbs hb

let b_conv (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1 r1: typ)
  (h1: typing sg ln g' (ren_jctx xi d) (ren_ty_exp xi e) (ren_ty xi t1) (ren_ty xi r1))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ ty_eq t1 t /\ ty_eq r1 r /\ check sg g t KType /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  ty_eq_ren xi t1 t; ty_eq_ren xi r1 r;
  check_ren sg xi g g' t KType; check_ren sg xi g g' r (KRow EEffect);
  T_Conv h1 () ()

let b_case (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (es: list exp) (dt: dtree) (ts: list typ)
  (hes: exps_typing sg ln g' [] (ren_ty xi r) (ren_ty_exps xi es)
      (ren_tys xi ts))
  (hdt: dt_typing sg ln g' (ren_jctx xi d) (ren_octx xi (scrut_occs 0 ts)) (ren_ty_dt xi dt)
          (ren_ty xi t) (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r) (requires e == ECase es dt) (ensures fun _ -> True) =
  scrut_occs_ren xi 0 ts;
  T_Case hes (cast_dt hdt (scrut_occs 0 (ren_tys xi ts)) (ren_ty xi t) (ren_ty xi r))

let b_letjoin (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (ts: list typ) (e1 e2: exp)
  (h1: typing sg ln (push_vars g' (ren_tys xi ts)) (ren_jctx xi ((ts, t, r) :: d))
         (ren_ty_exp xi e1) (ren_ty xi t) (ren_ty xi r))
  (h2: typing sg ln g' (ren_jctx xi ((ts, t, r) :: d)) (ren_ty_exp xi e2) (ren_ty xi t)
      (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ELetJoin ts t e1 e2 /\ tys_ok sg g ts /\
             check sg g t KType)
         (ensures fun _ -> True) =
  ren_letjoin_eq xi ts t e1 e2;
  tys_ok_ren sg xi g g' ts;
  check_ren sg xi g g' t KType;
  T_LetJoin #sg #ln #g' #(ren_jctx xi d) #(ren_tys xi ts) #(ren_ty xi t) #(ren_ty_exp xi e1)
    #(ren_ty_exp xi e2) #(ren_ty xi r) () h1 h2

let b_jump (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (j: nat) (es: list exp) (ts: list typ)
  (hes: exps_typing sg ln g' [] (ren_ty xi r) (ren_ty_exps xi es)
      (ren_tys xi ts))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EJump j es /\
             L.nth d j == Some (ts, t, r) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  nth_ren_jctx xi d j;
  check_ren sg xi g g' t KType; check_ren sg xi g g' r (KRow EEffect);
  T_Jump #sg #ln #g' #(ren_jctx xi d) #j #(ren_ty_exps xi es) #(ren_tys xi ts) #(ren_ty xi t)
    #(ren_ty xi r) () () hes

let b_recempty (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ERecEmpty /\ t == t_record TRowEmpty /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  ren_t_record xi TRowEmpty;
  check_ren sg xi g g' r (KRow EEffect);
  T_RecEmpty #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi r) ()

let b_extend (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (e1 e2: exp) (t1 r0: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi t1) (ren_ty xi r))
  (h2: typing sg ln g' [] (ren_ty_exp xi e2) (ren_ty xi (t_record r0))
      (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EExtend k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t1) r0) /\ key_ok sg g k EType /\
                   entails (hyps g) (CLacks k r0))
         (ensures fun _ -> True) =
  ren_extend_eq xi k e1 e2;
  ren_rec_ext xi k t1 r0;
  ren_t_record xi (TRowExt (EntTy k t1) r0);
  assert (ren_ty xi (TRowExt (EntTy k t1) r0) == TRowExt (EntTy k (ren_ty xi t1)) (ren_ty xi r0));
  key_ok_rdom sg g g' k EType;
  entails_into xi g g' (CLacks k r0);
  let h2 : typing sg ln g' [] (ren_ty_exp xi e2) (t_record (ren_ty xi r0))
             (ren_ty xi r) = h2 in
  T_Extend #sg #ln #g' #(ren_jctx xi d) #k h1 h2 ()

let b_select (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1)
         (ren_ty xi (t_record (TRowExt (EntTy k t) r0))) (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ESelect k e1 /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  ren_rec_ext xi k t r0;
  key_ok_rdom sg g g' k EType;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1)
             (t_record (TRowExt (EntTy k (ren_ty xi t)) (ren_ty xi r0))) (ren_ty xi r) = h1 in
  T_Select h1 ()

let b_restrict (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (e1: exp) (t1 r0: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1)
         (ren_ty xi (t_record (TRowExt (EntTy k t1) r0))) (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ERestrict k e1 /\ t == t_record r0 /\
             key_ok sg g k EType)
         (ensures fun _ -> True) =
  ren_rec_ext xi k t1 r0;
  key_ok_rdom sg g g' k EType;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1)
             (t_record (TRowExt (EntTy k (ren_ty xi t1)) (ren_ty xi r0))) (ren_ty xi r) = h1 in
  T_Restrict h1 ()

let b_update (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (e1 e2: exp) (t1 t2 r0: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1)
         (ren_ty xi (t_record (TRowExt (EntTy k t1) r0))) (ren_ty xi r))
  (h2: typing sg ln g' [] (ren_ty_exp xi e2) (ren_ty xi t2) (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EUpdate k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t2) r0) /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  ren_update_eq xi k e1 e2;
  ren_rec_ext xi k t1 r0; ren_rec_ext xi k t2 r0;
  key_ok_rdom sg g g' k EType;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1)
             (t_record (TRowExt (EntTy k (ren_ty xi t1)) (ren_ty xi r0))) (ren_ty xi r) = h1 in
  T_Update h1 h2 ()

let b_merge (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1 e2: exp) (r1 r2: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi (t_record r1))
      (ren_ty xi r))
  (h2: typing sg ln g' [] (ren_ty_exp xi e2) (ren_ty xi (t_record r2))
      (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EMerge e1 e2 /\ t == t_record (TRowUnion r1 r2) /\
                   entails (hyps g) (CDisj r1 r2))
         (ensures fun _ -> True) =
  ren_merge_eq xi e1 e2;
  ren_rec_union xi r1 r2; ren_t_record xi r1; ren_t_record xi r2;
  entails_into xi g g' (CDisj r1 r2);
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1) (t_record (ren_ty xi r1))
             (ren_ty xi r) = h1 in
  let h2 : typing sg ln g' [] (ren_ty_exp xi e2) (t_record (ren_ty xi r2))
             (ren_ty xi r) = h2 in
  T_Merge h1 h2 ()

let b_inject (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (r0: typ) (e1: exp) (t1: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi t1) (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EInject k r0 e1 /\
             t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\
                     check sg g r0 (KRow EType))
         (ensures fun _ -> True) =
  ren_inject_eq xi k r0 e1;
  ren_var_ext xi k t1 r0;
  key_ok_rdom sg g g' k EType;
  entails_into xi g g' (CLacks k r0);
  check_ren sg xi g g' r0 (KRow EType);
  T_Inject #sg #ln #g' #(ren_jctx xi d) #k #(ren_ty xi r0) h1 () ()

let b_weaken (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (t1: typ) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi (t_variant r0))
      (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EWeaken k t1 e1 /\
             t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  ren_weaken_eq xi k t1 e1;
  ren_var_ext xi k t1 r0;
  key_ok_rdom sg g g' k EType;
  entails_into xi g g' (CLacks k r0);
  check_ren sg xi g g' t1 KType;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1) (t_variant (ren_ty xi r0))
             (ren_ty xi r) = h1 in
  T_Weaken #sg #ln #g' #(ren_jctx xi d) #k #(ren_ty xi t1) h1 () ()

let b_variant_value (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (v: exp) (pt vr0 vr: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e) (ren_ty xi (t_variant vr0))
      (ren_ty xi r))
  (h2: typing sg ln g' [] (ren_ty_exp xi v) (ren_ty xi pt) (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ t == t_variant vr /\ V.is_value sg e /\
                   variant_view e == Some (k, v) /\ check sg g (t_variant vr) KType /\
                   check sg g pt KType /\ L.mem (k, PTy (canon pt)) (row_entries (canon vr)))
         (ensures fun _ -> True) =
  ren_t_variant xi vr; ren_t_variant xi vr0;
  is_value_ren_ty sg xi e;
  variant_view_ren_ty xi e;
  check_ren sg xi g g' (t_variant vr) KType;
  check_ren sg xi g g' pt KType;
  entries_ren_ty xi vr k pt;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e) (t_variant (ren_ty xi vr0))
             (ren_ty xi r) = h1 in
  T_VariantValue #sg #ln #g' #(ren_jctx xi d) #(ren_ty_exp xi e) #k #(ren_ty_exp xi v)
    #(ren_ty xi pt)
    #(ren_ty xi r) (ren_ty xi vr0) (ren_ty xi vr) h1 () h2 ()

let b_absurd (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1: exp)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi (t_variant TRowEmpty))
         (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EAbsurd t e1 /\ check sg g t KType)
         (ensures fun _ -> True) =
  ren_t_variant xi TRowEmpty;
  check_ren sg xi g g' t KType;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1) (t_variant TRowEmpty)
    (ren_ty xi r) =
    h1 in
  T_Absurd #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi t) h1 ()

let b_perform (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: key) (op: opname) (ss: list typ) (e1: exp) (q: qname) (ei: effect_info) (os: op_sig)
  (ts: list typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi (op_inst ts ss os.arg))
         (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires sig_ok sg /\ ty_ren_ok xi g g' /\ e == EPerform k op ss e1 /\
                   t == op_inst ts ss os.res /\
                   L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)) /\
                   sg.effects q == Some ei /\ op_of ei op == Some os /\
                   check_tys sg g ts ei.eff_params /\ check_tys sg g ss os.binders)
         (ensures fun _ -> True) =
  ren_perform_eq xi k op ss e1;
  entries_ren_eff xi r k q ts;
  check_tys_ren sg xi g g' ts ei.eff_params;
  check_tys_ren sg xi g g' ss os.binders;
  check_tys_length sg g ts ei.eff_params;
  check_tys_length sg g ss os.binders;
  op_inst_ren_sig sg q ei op os ts ss xi;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1)
             (op_inst (ren_tys xi ts) (ren_tys xi ss) os.arg) (ren_ty xi r) = h1 in
  T_Perform #sg #ln #g' #(ren_jctx xi d) #k #op #(ren_tys xi ss) #(ren_ty_exp xi e1)
    #(ren_ty xi r)
    #q #ei #os (ren_tys xi ts) () () () h1

let ren_handler (xi: ren) (hd: handler) : handler =
  { h_ent = ren_ent xi hd.h_ent; h_ret_ty = ren_ty xi hd.h_ret_ty;
    h_ret = ren_ty_exp xi hd.h_ret; h_clauses = ren_ty_cls xi hd.h_clauses }

let b_handle (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1: exp) (hd: handler) (lbl: option string) (q: qname) (ts: list typ) (ei: effect_info)
  (h1: typing sg ln g' (ren_jctx xi []) (ren_ty_exp xi e1) (ren_ty xi hd.h_ret_ty)
         (ren_ty xi (TRowExt hd.h_ent r)))
  (h2: typing sg ln (push_var g' (ren_ty xi hd.h_ret_ty)) (ren_jctx xi [])
      (ren_ty_exp xi hd.h_ret)
         (ren_ty xi t) (ren_ty xi r))
  (hcl: clauses_typing sg ln g' ei (ren_tys xi ts) (ren_ty xi r) (ren_ty xi t)
      (ren_ty_cls xi hd.h_clauses))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EHandle e1 hd /\ hd.h_ent == EntEff lbl q ts /\
                   sg.effects q == Some ei /\
                   check sg g (TRowExt hd.h_ent r) (KRow EEffect) /\ check sg g hd.h_ret_ty KType /\
                   check sg g t KType /\ check sg g r (KRow EEffect) /\
                     clauses_cover ei hd.h_clauses)
         (ensures fun _ -> True) =
  ren_handle_eq xi e1 hd;
  let hd' = ren_handler xi hd in
  check_ren sg xi g g' (TRowExt hd.h_ent r) (KRow EEffect);
  check_ren sg xi g g' hd.h_ret_ty KType;
  check_ren sg xi g g' t KType;
  check_ren sg xi g g' r (KRow EEffect);
  clause_ops_ren xi hd.h_clauses;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1) hd'.h_ret_ty
    (TRowExt hd'.h_ent (ren_ty xi r)) = h1 in
  let h2 : typing sg ln (push_var g' hd'.h_ret_ty) [] hd'.h_ret (ren_ty xi t)
    (ren_ty xi r) = h2 in
  let hcl : clauses_typing sg ln g' ei (ren_tys xi ts) (ren_ty xi r)
    (ren_ty xi t) hd'.h_clauses = hcl in
  T_Handle #sg #ln #g' #(ren_jctx xi d) #(ren_ty_exp xi e1) #hd' #(ren_ty xi t)
    #(ren_ty xi r) #lbl #q
    #(ren_tys xi ts) #ei () () () () h1 h2 hcl

let b_openeff (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (r2: typ) (e1: exp) (t1 r1 t2: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi (t_fun t1 r1 t2))
      (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EOpenEff r2 e1 /\ t == t_fun t1 (TRowUnion r1 r2) t2 /\
                   entails (hyps g) (CDisj r1 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  ren_union_eq xi r1 r2;
  ren_openeff_eq xi r2 e1;
  entails_into xi g g' (CDisj r1 r2);
  check_ren sg xi g g' r2 (KRow EEffect);
  ren_t_fun xi t1 r1 t2;
  ren_t_fun xi t1 (TRowUnion r1 r2) t2;
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1)
             (t_fun (ren_ty xi t1) (ren_ty xi r1) (ren_ty xi t2)) (ren_ty xi r) = h1 in
  T_OpenEff #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi r2) h1 ()

let b_region (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (lay: layout) (es: list exp) (body: exp)
  (hes: exps_typing sg ln g' [] (ren_ty xi r) (ren_ty_exps xi es)
          (ren_tys xi (L.map snd lay)))
  (hb: (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp (ren_ty_exp xi body)))} ->
        typing sg ln (enter_region g' a (ren_layout xi lay)) (ren_jctx xi [])
          (ren_ty_exp xi (open_region a body)) (ren_ty xi t)
          (ren_ty xi (TRowExt (EntRegion (RFree a)) r))))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ERegion lay es body /\
                   check sg g (layout_row lay) (KRow EType) /\ L.noRepeats (L.map fst lay) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  let lay' = ren_layout xi lay in
  let body' = ren_ty_exp xi body in
  ren_layout_row xi lay;
  ren_layout_keys xi lay;
  ren_layout_snd xi lay;
  check_ren sg xi g g' (layout_row lay) (KRow EType);
  check_ren sg xi g g' t KType;
  check_ren sg xi g g' r (KRow EEffect);
  let hes : exps_typing sg ln g' [] (ren_ty xi r) (ren_ty_exps xi es)
    (L.map snd lay') =
    hes in
  let hb' (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp body'))})
    : typing sg ln (enter_region g' a lay') [] (open_region a body') (ren_ty xi t)
        (TRowExt (EntRegion (RFree a)) (ren_ty xi r)) =
    open_region_ren_ty_exp 0 a xi body;
    hb a
  in
  T_Region #sg #ln #g' #(ren_jctx xi d) #lay' #(ren_ty_exps xi es) #body' #(ren_ty xi t)
    #(ren_ty xi r)
    () () hes hb'

let b_readcell (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (a: atom) (k: key) (lay: layout)
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EReadCell (RFree a) k /\
             L.assoc a g.regions == Some lay /\
                   L.assoc k lay == Some t /\ L.mem (RegionKey (RFree a)) (known_keys r) /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  ren_layout_assoc xi lay k;
  known_keys_ren xi r (RegionKey (RFree a));
  check_ren sg xi g g' r (KRow EEffect);
  T_ReadCell #sg #ln #g' #(ren_jctx xi d) #a #k #(ren_layout xi lay) #(ren_ty xi t)
    #(ren_ty xi r)
    () () ()

let b_writecell (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ)
  (a: atom) (k: key) (e1: exp) (lay: layout) (t1: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi t1) (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EWriteCell (RFree a) k e1 /\ t == t_unit /\
                   L.assoc a g.regions == Some lay /\ L.assoc k lay == Some t1 /\
                   L.mem (RegionKey (RFree a)) (known_keys r))
         (ensures fun _ -> True) =
  ren_writecell_eq xi (RFree a) k e1;
  assert (L.assoc a g.regions == L.assoc a g.regions);
  ren_layout_assoc xi lay k;
  known_keys_ren xi r (RegionKey (RFree a));
  T_WriteCell #sg #ln #g' #(ren_jctx xi d) #a #k #(ren_ty_exp xi e1) #(ren_layout xi lay)
    #(ren_ty xi t1) #(ren_ty xi r) () () h1

let b_match (#sg: sig) (#ln: lctx) (xi: ren) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (th: list exp) (dt: dtree) (ts: list typ) (om: octx)
  (hes: exps_typing sg ln g' [] (ren_ty xi r) (ren_ty_exps xi th)
      (ren_tys xi ts))
  (hm: match_typing sg ln g' [] (ren_ty xi r) (ren_ty_exps xi th) (ren_octx xi om))
  (hdt: dt_typing sg ln g' (ren_jctx xi d) (ren_octx xi om) (ren_ty_dt xi dt) (ren_ty xi t)
          (ren_ty xi r))
  : Pure (tr sg ln g' xi d e t r)
         (requires e == EMatch th dt /\ L.for_all (V.is_value sg) th)
         (ensures fun _ -> True) =
  values_ren_ty sg xi th;
  T_Match (ren_octx xi om) hes () hm hdt

let b_openeffc (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (r2: typ) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (ren_ty_exp xi e1) (ren_ty xi t) (ren_ty xi r0))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EOpenEffC r2 e1 /\ r == TRowUnion r0 r2 /\
                   entails (hyps g) (CDisj r0 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  ren_union_eq xi r0 r2;
  ren_openeffc_eq xi r2 e1;
  entails_into xi g g' (CDisj r0 r2);
  check_ren sg xi g g' r2 (KRow EEffect);
  T_OpenEffC #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi r2) h1 ()

let b_force (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (nu: atom)
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EForce nu /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  closed_ren sg xi g g' t KType;
  check_ren sg xi g g' r (KRow EEffect);
  T_Force #sg #ln #g' #(ren_jctx xi d) #nu #t #(ren_ty xi r) () ()

let b_fill (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (nu: atom) (e1: exp)
  (h1: typing sg ln g' (ren_jctx xi []) (ren_ty_exp xi e1) (ren_ty xi t)
      (ren_ty xi TRowEmpty))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EFill nu e1 /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  closed_ren sg xi g g' t KType;
  check_ren sg xi g g' r (KRow EEffect);
  let h1 : typing sg ln g' [] (ren_ty_exp xi e1) t TRowEmpty = h1 in
  T_Fill #sg #ln #g' #(ren_jctx xi d) #nu #(ren_ty_exp xi e1) #t #(ren_ty xi r) () () h1

let b_region_open (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ)
  (a: atom) (cells: list (key & exp)) (body: exp) (lay: layout)
  (hc: cells_typing sg ln g' (ren_ty_cells xi cells) (ren_layout xi lay))
  (hb: typing sg ln g' (ren_jctx xi []) (ren_ty_exp xi body) (ren_ty xi t)
         (ren_ty xi (TRowExt (EntRegion (RFree a)) r)))
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == ERegionOpen a cells body /\
             L.assoc a g.regions == Some lay /\
                   check sg (closed_ctx g.regions) t KType /\
                   check sg (closed_ctx g.regions) r (KRow EEffect) /\
                   ~(L.mem a (frn_ty t @ frn_ty r)))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  closed_ren sg xi g g' t KType;
  closed_ren sg xi g g' r (KRow EEffect);
  let hb : typing sg ln g' [] (ren_ty_exp xi body) t (TRowExt (EntRegion (RFree a)) r) = hb in
  T_RegionOpen #sg #ln #g' #(ren_jctx xi d) #a #(ren_ty_cells xi cells) #(ren_ty_exp xi body)
    #(ren_layout xi lay) #t #r () () () hc hb

let b_opaque (#sg: sig) (#ln: lctx) (xi: ren) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (w: nat)
  : Pure (tr sg ln g' xi d e t r)
         (requires ty_ren_ok xi g g' /\ e == EOpaque w t /\ opaque_type sg t /\ check sg g t KType
             /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  ty_head_ren xi t;
  check_ren sg xi g g' t KType;
  check_ren sg xi g g' r (KRow EEffect);
  T_Opaque #sg #ln #g' #(ren_jctx xi d) #w #(ren_ty xi t) #(ren_ty xi r) () ()

(* The mutual induction. *)

let rec typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (xi: ren) (g': ctx)
  : Pure (typing sg ln g' (ren_jctx xi d) (ren_ty_exp xi e) (ren_ty xi t) (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | T_Var #_ #_ #_ #_ #i _ _ -> b_var xi g g' d e t r i
  | T_Global #_ #_ #_ #_ #q #ks #nk #t0 _ _ _ -> b_global xi g g' d e t r q ks nk t0
  | T_Lit #_ #_ #_ #_ #c _ -> b_lit xi g g' d e t r c
  | T_Lam #_ #_ #_ #_ #t1 #r1 #body #t2 _ _ hb ->
    ty_ren_ok_push_var xi g g' t1;
    b_lam xi g g' d e t r t1 r1 body t2 (typing_ren_ty' hb xi (push_var g' (ren_ty xi t1)))
  | T_App #_ #_ #_ #_ #e1 #e2 #t1 #t2 h1 h2 ->
    b_app xi g' d e t r e1 e2 t1 t2 (typing_ren_ty' h1 xi g') (typing_ren_ty' h2 xi g')
  | T_Chain #_ #_ #_ #_ #_ #t0 #th hc _ ->
    b_chain xi g' d e t r t0 th (chain_typing_ren_ty' hc xi g')
  | T_TyLam #_ #_ #_ #_ #k #body #t0 _ _ _ hb ->
    ty_ren_ok_up xi g g' k;
    b_tylam xi g g' d e t r k body t0 (typing_ren_ty' hb (up_ren xi) (push_tvar g' k))
  | T_TyApp #_ #_ #_ #_ #e1 #s #k #t0 h1 _ ->
    b_tyapp xi g g' d e t r e1 s k t0 (typing_ren_ty' h1 xi g')
  | T_CLam #_ #_ #_ #_ #c #body #t0 _ _ _ hb ->
    ty_ren_ok_assump xi g g' c;
    b_clam xi g g' d e t r c body t0 (typing_ren_ty' hb xi (add_assump g' (ren_constr xi c)))
  | T_CApp #_ #_ #_ #_ #e1 #c h1 _ ->
    b_capp xi g g' d e t r e1 c (typing_ren_ty' h1 xi g')
  | T_Let #_ #_ #_ #_ #t1 #e1 #e2 _ h1 h2 ->
    ty_ren_ok_push_var xi g g' t1;
    b_let xi g g' d e t r t1 e1 e2 (typing_ren_ty' h1 xi g')
      (typing_ren_ty' h2 xi (push_var g' (ren_ty xi t1)))
  | T_LetRec #_ #_ #_ #_ #bs #body _ hbs hb ->
    ty_ren_ok_push_vars xi g g' (L.map fst bs);
    let gb' = push_vars g' (ren_tys xi (L.map fst bs)) in
    b_letrec xi g' d e t r bs body (binds_typing_ren_ty' hbs xi gb') (typing_ren_ty' hb xi gb')
  | T_Conv #_ #_ #_ #_ #_ #t1 #r1 h1 _ _ ->
    b_conv xi g g' d e t r t1 r1 (typing_ren_ty' h1 xi g')
  | T_Case #_ #_ #_ #_ #es #dt #ts hes hdt ->
    b_case xi g' d e t r es dt ts (exps_typing_ren_ty' hes xi g') (dt_typing_ren_ty' hdt xi g')
  | T_LetJoin #_ #_ #_ #_ #ts #_ #e1 #e2 _ h1 h2 ->
    ty_ren_ok_push_vars xi g g' ts;
    b_letjoin xi g g' d e t r ts e1 e2 (typing_ren_ty' h1 xi (push_vars g' (ren_tys xi ts)))
      (typing_ren_ty' h2 xi g')
  | T_Jump #_ #_ #_ #_ #j #es #ts _ _ hes ->
    b_jump xi g g' d e t r j es ts (exps_typing_ren_ty' hes xi g')
  | T_RecEmpty _ -> b_recempty xi g g' d e t r
  | T_Extend #_ #_ #_ #_ #k #e1 #e2 #t1 #r0 h1 h2 _ ->
    b_extend xi g g' d e t r k e1 e2 t1 r0 (typing_ren_ty' h1 xi g') (typing_ren_ty' h2 xi g')
  | T_Select #_ #_ #_ #_ #k #e1 #_ #r0 h1 _ ->
    b_select xi g g' d e t r k e1 r0 (typing_ren_ty' h1 xi g')
  | T_Restrict #_ #_ #_ #_ #k #e1 #t1 #r0 h1 _ ->
    b_restrict xi g g' d e t r k e1 t1 r0 (typing_ren_ty' h1 xi g')
  | T_Update #_ #_ #_ #_ #k #e1 #e2 #t1 #t2 #r0 h1 h2 _ ->
    b_update xi g g' d e t r k e1 e2 t1 t2 r0 (typing_ren_ty' h1 xi g') (typing_ren_ty' h2 xi g')
  | T_Merge #_ #_ #_ #_ #e1 #e2 #r1 #r2 h1 h2 _ ->
    b_merge xi g g' d e t r e1 e2 r1 r2 (typing_ren_ty' h1 xi g') (typing_ren_ty' h2 xi g')
  | T_Inject #_ #_ #_ #_ #k #r0 #e1 #t1 h1 _ _ ->
    b_inject xi g g' d e t r k r0 e1 t1 (typing_ren_ty' h1 xi g')
  | T_Weaken #_ #_ #_ #_ #k #t1 #e1 #r0 h1 _ _ ->
    b_weaken xi g g' d e t r k t1 e1 r0 (typing_ren_ty' h1 xi g')
  | T_VariantValue #_ #_ #_ #_ #_ #k #v #pt vr0 vr h1 _ h2 _ ->
    b_variant_value xi g g' d e t r k v pt vr0 vr (typing_ren_ty' h1 xi g')
      (typing_ren_ty' h2 xi g')
  | T_Absurd #_ #_ #_ #_ #_ #e1 h1 _ ->
    b_absurd xi g g' d e t r e1 (typing_ren_ty' h1 xi g')
  | T_Perform #_ #_ #_ #_ #k #op #ss #e1 #_ #q #ei #os ts _ _ _ h1 ->
    b_perform xi g g' d e t r k op ss e1 q ei os ts (typing_ren_ty' h1 xi g')
  | T_Handle #_ #_ #_ #_ #e1 #hd #_ #_ #lbl #q #ts #ei _ _ _ _ h1 h2 hcl ->
    eff_params_length sg g lbl q ts r ei;
    ty_ren_ok_push_var xi g g' hd.h_ret_ty;
    b_handle xi g g' d e t r e1 hd lbl q ts ei (typing_ren_ty' h1 xi g')
      (typing_ren_ty' h2 xi (push_var g' (ren_ty xi hd.h_ret_ty)))
        (clauses_typing_ren_ty' hcl q xi g')
  | T_OpenEff #_ #_ #_ #_ #r2 #e1 #t1 #r1 #t2 h1 _ ->
    b_openeff xi g g' d e t r r2 e1 t1 r1 t2 (typing_ren_ty' h1 xi g')
  | T_Region #_ #_ #_ #_ #lay #es #body _ _ hes hbody ->
    let lay' = ren_layout xi lay in
    let hb' (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp (ren_ty_exp xi body)))})
      : typing sg ln (enter_region g' a lay') (ren_jctx xi [])
        (ren_ty_exp xi (open_region a body))
          (ren_ty xi t) (ren_ty xi (TRowExt (EntRegion (RFree a)) r)) =
      ty_ren_ok_fresh xi g g' a body;
      ty_ren_ok_enter_region xi g g' a lay;
      typing_ren_ty' (hbody a) xi (enter_region g' a lay')
    in
    b_region xi g g' d e t r lay es body (exps_typing_ren_ty' hes xi g') hb'
  | T_ReadCell #_ #_ #_ #_ #a #k #lay _ _ _ -> b_readcell xi g g' d e t r a k lay
  | T_WriteCell #_ #_ #_ #_ #a #k #e1 #lay #t1 _ _ h1 ->
    b_writecell xi g g' d e t r a k e1 lay t1 (typing_ren_ty' h1 xi g')
  | T_Match #_ #_ #_ #_ #th #dt #ts om hes _ hm hdt ->
    b_match xi g' d e t r th dt ts om (exps_typing_ren_ty' hes xi g')
      (match_typing_ren_ty' hm xi g')
      (dt_typing_ren_ty' hdt xi g')
  | T_OpenEffC #_ #_ #_ #_ #r2 #e1 #_ #r0 h1 _ ->
    b_openeffc xi g g' d e t r r2 e1 r0 (typing_ren_ty' h1 xi g')
  | T_Force #_ #_ #_ #_ #nu _ _ -> b_force xi g g' d e t r nu
  | T_Fill #_ #_ #_ #_ #nu #e1 _ _ h1
    -> b_fill xi g g' d e t r nu e1 (typing_ren_ty' h1 xi g')
  | T_RegionOpen #_ #_ #_ #_ #a #cells #body #lay _ _ _ hc hb ->
    b_region_open xi g g' d e t r a cells body lay (cells_typing_ren_ty' hc xi g')
      (typing_ren_ty' hb xi g')
  | T_Opaque #_ #_ #_ #_ #w _ _ -> b_opaque xi g g' d e t r w

and exps_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (xi: ren) (g': ctx)
  : Pure (exps_typing sg ln g' (ren_jctx xi d) (ren_ty xi r) (ren_ty_exps xi es) (ren_tys xi ts))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TE_Nil _ -> check_ren sg xi g g' r (KRow EEffect); TE_Nil ()
  | TE_Cons h1 h2 -> TE_Cons (typing_ren_ty' h1 xi g') (exps_typing_ren_ty' h2 xi g')

and chain_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (xi: ren) (g': ctx)
  : Pure (chain_typing sg ln g' (ren_jctx xi d) (ren_ty xi r) (ren_ty_exp xi e))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TS_Head #_ #_ #_ #_ #_ #q #ks #c #nk #t0 _ _ _ ->
    check_ren sg xi g g' r (KRow EEffect);
    TS_Head #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi r) #q #ks #c #nk #t0 () () ()
  | TS_Ty #_ #_ #_ #_ #_ #e0 #s #k #t0 #th h0 _ _ ->
    chain_cursor_ren_ty sg xi e0 (TForall k t0) th;
    ren_tyapp_eq xi e0 s;
    let Some (_, th') = chain_cursor sg (ren_ty_exp xi e0) in
    check_ren sg xi g g' s k;
    TS_Ty #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi r) #(ren_ty_exp xi e0) #(ren_ty xi s) #k #t0 #th'
      (chain_typing_ren_ty' h0 xi g') () ()
  | TS_Constr #_ #_ #_ #_ #_ #e0 #c #t0 #th h0 _ _ ->
    chain_cursor_ren_ty sg xi e0 (TConstr c t0) th;
    ren_capp_eq xi e0;
    let Some (_, th') = chain_cursor sg (ren_ty_exp xi e0) in
    entails_into xi g g' (sub_constr th c);
    TS_Constr #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi r) #(ren_ty_exp xi e0) #c #t0 #th'
      (chain_typing_ren_ty' h0 xi g') () ()
  | TS_Val #_ #_ #_ #_ #_ #e0 #v #t0 #th #t1 #r1 #t2 h0 _ hv ->
    chain_cursor_ren_ty sg xi e0 t0 th;
    ren_app_eq xi e0 v;
    let Some (_, th') = chain_cursor sg (ren_ty_exp xi e0) in
    let hv' = cast (typing_ren_ty' hv xi g') (ren_jctx xi d) (ren_ty_exp xi v) (sub_ty th' t1)
      (ren_ty xi r) in
    TS_Val #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi r) #(ren_ty_exp xi e0)
      #(ren_ty_exp xi v) #t0 #th' #t1 #r1 #t2
      (chain_typing_ren_ty' h0 xi g') () hv'

and binds_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (xi: ren) (g': ctx)
  : Pure (binds_typing sg ln g' (ren_ty_binds xi bs))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TB_Nil -> TB_Nil
  | TB_Cons #_ #_ #_ #t0 #e0 #_ _ h1 h2 ->
    check_ren sg xi g g' t0 KType;
    let h1' = cast (typing_ren_ty' h1 xi g') [] (ren_ty_exp xi e0) (ren_ty xi t0) TRowEmpty in
    TB_Cons () h1' (binds_typing_ren_ty' h2 xi g')

and cells_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay) (xi: ren) (g': ctx)
  : Pure (cells_typing sg ln g' (ren_ty_cells xi cells) (ren_layout xi lay))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TC_Nil -> TC_Nil
  | TC_Cons #_ #_ #_ #k #v #t0 #cs0 #lay0 _ h1 h2 ->
    is_value_ren_ty sg xi v;
    let h1' = cast (typing_ren_ty' h1 xi g') [] (ren_ty_exp xi v) (ren_ty xi t0) TRowEmpty in
    TC_Cons #sg #ln #g' #k #(ren_ty_exp xi v) #(ren_ty xi t0) #(ren_ty_cells xi cs0)
      #(ren_layout xi lay0) () h1'
      (cells_typing_ren_ty' h2 xi g')

and match_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (h: match_typing sg ln g d r th om) (xi: ren) (g': ctx)
  : Pure (match_typing sg ln g' (ren_jctx xi d) (ren_ty xi r) (ren_ty_exps xi th) (ren_octx xi om))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TM_Nil _ -> check_ren sg xi g g' r (KRow EEffect); TM_Nil ()
  | TM_Cons #_ #_ #_ #_ #_ #_ #o #t0 #_ #v _ h1 h2 ->
    proj_ren_ty sg xi th o;
    TM_Cons #sg #ln #g' #(ren_jctx xi d) #(ren_ty xi r) #(ren_ty_exps xi th) #o #(ren_ty xi t0)
      #(ren_octx xi _) #(ren_ty_exp xi v) () (typing_ren_ty' h1 xi g')
        (match_typing_ren_ty' h2 xi g')

and dt_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (xi: ren) (g': ctx)
  : Pure (dt_typing sg ln g' (ren_jctx xi d) (ren_octx xi om) (ren_ty_dt xi dt) (ren_ty xi t)
            (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TD_Leaf h1 -> TD_Leaf (typing_ren_ty' h1 xi g')
  | TD_Bind #_ #_ #_ #_ #_ #o #dt0 #t_o #_ #_ ho hdt ->
    ty_ren_ok_push_var xi g g' t_o;
    TD_Bind (occ_typing_ren_ty' ho xi g') (dt_typing_ren_ty' hdt xi (push_var g' (ren_ty xi t_o)))
  | TD_SwitchCtor #_ #_ #_ #_ #_ #o #bs #t_o #_ #_ tq ks ss cs ho _ _ _ hbr ->
    ren_tapps xi (TCon tq ks) ss;
    ty_eq_ren xi t_o (tapps (TCon tq ks) ss);
    check_ren sg xi g g' (tapps (TCon tq ks) ss) KType;
    ren_ty_brs_labels xi bs;
    TD_SwitchCtor tq ks (ren_tys xi ss) cs (occ_typing_ren_ty' ho xi g') () () ()
      (ctor_brs_typing_ren_ty' hbr xi g')
  | TD_SwitchCtorDef #_ #_ #_ #_ #_ #o #bs #df #t_o #_ #_ tq ks ss cs ho _ _ _ hbr hdf ->
    ren_tapps xi (TCon tq ks) ss;
    ty_eq_ren xi t_o (tapps (TCon tq ks) ss);
    check_ren sg xi g g' (tapps (TCon tq ks) ss) KType;
    ren_ty_brs_labels xi bs;
    TD_SwitchCtorDef tq ks (ren_tys xi ss) cs (occ_typing_ren_ty' ho xi g') () () ()
      (ctor_brs_typing_ren_ty' hbr xi g') (dt_typing_ren_ty' hdf xi g')
  | TD_SwitchLit #_ #_ #_ #_ #_ #o #bs #df #t_o #_ #_ lq ho _ _ hbr hdf ->
    ty_eq_ren xi t_o (TCon lq []);
    ren_ty_brs_labels xi bs;
    let hbr' = lit_brs_typing_ren_ty' hbr xi g' in
    TD_SwitchLit lq (occ_typing_ren_ty' ho xi g') () () hbr' (dt_typing_ren_ty' hdf xi g')
  | TD_SwitchKey #_ #_ #_ #_ #_ #o #bs #t_o #_ #_ vr kts ho _ _ _ hbr ->
    ren_t_variant xi vr;
    ty_eq_ren xi t_o (t_variant vr);
    check_ren sg xi g g' vr (KRow EType);
    ren_ty_brs_labels xi bs;
    key_split_ren xi vr kts TRowEmpty;
    TD_SwitchKey (ren_ty xi vr) (ren_layout xi kts) (occ_typing_ren_ty' ho xi g') () () ()
      (key_brs_typing_ren_ty' hbr xi g')
  | TD_SwitchKeyDef #_ #_ #_ #_ #_ #o #bs #df #t_o #_ #_ vr vr' kts ho _ _ _ hbr hdf ->
    ren_t_variant xi vr;
    ren_t_variant xi vr';
    ty_eq_ren xi t_o (t_variant vr);
    check_ren sg xi g g' vr (KRow EType);
    check_ren sg xi g g' vr' (KRow EType);
    ren_ty_brs_labels xi bs;
    key_split_ren xi vr kts vr';
    let hdf' = cast_dt (dt_typing_ren_ty' hdf xi g')
      ((o, t_variant (ren_ty xi vr')) :: ren_octx xi om) (ren_ty xi t) (ren_ty xi r) in
    TD_SwitchKeyDef (ren_ty xi vr) (ren_ty xi vr') (ren_layout xi kts) (occ_typing_ren_ty' ho xi g')
      () () ()
      (key_brs_typing_ren_ty' hbr xi g') hdf'
  | TD_Guard h1 h2 h3 ->
    TD_Guard (typing_ren_ty' h1 xi g') (dt_typing_ren_ty' h2 xi g') (dt_typing_ren_ty' h3 xi g')

and ctor_brs_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ) (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (xi: ren) (g': ctx)
  : Pure (ctor_brs_typing sg ln g' (ren_jctx xi d) (ren_octx xi om) o ks (ren_tys xi ss) cs
            (ren_ty_brs xi bs) (ren_ty xi t) (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCB_Nil _ ->
    check_ren sg xi g g' t KType; check_ren sg xi g g' r (KRow EEffect);
    TCB_Nil ()
  | TCB_Cons #_ #_ #_ #_ #_ #_ #_ #_ #_ #c #dt0 #bs0 #_ #_ #fs _ hdt h2 ->
    ctor_fields_ren sg c ks ss xi;
    field_occs_ren xi o c 0 fs;
    ren_octx_append xi (field_occs o c 0 fs) om;
    let hdt' = cast_dt (dt_typing_ren_ty' hdt xi g')
                 (L.append (field_occs o c 0 (ren_tys xi fs)) (ren_octx xi om)) (ren_ty xi t)
                   (ren_ty xi r) in
    TCB_Cons #sg #ln #g' #(ren_jctx xi d) #(ren_octx xi om) #o #ks #(ren_tys xi ss) #cs #c
      #(ren_ty_dt xi dt0) #(ren_ty_brs xi bs0) #(ren_ty xi t) #(ren_ty xi r) #(ren_tys xi fs)
      () hdt' (ctor_brs_typing_ren_ty' h2 xi g')

and lit_brs_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (xi: ren) (g': ctx)
  : Pure (lit_brs_typing sg ln g' (ren_jctx xi d) (ren_octx xi om) (ren_ty xi lt)
            (ren_ty_brs xi bs) (ren_ty xi t) (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TLB_Nil _ ->
    check_ren sg xi g g' t KType; check_ren sg xi g g' r (KRow EEffect);
    TLB_Nil ()
  | TLB_Cons #_ #_ #_ #_ #_ #_ #c #_ #_ #_ #_ _ hdt h2 ->
    ren_lit_type xi c;
    ty_eq_ren xi (lit_type c) lt;
    TLB_Cons #sg #ln #g' #(ren_jctx xi d) #(ren_octx xi om) #(ren_ty xi lt) #c ()
      (dt_typing_ren_ty' hdt xi g') (lit_brs_typing_ren_ty' h2 xi g')

and key_brs_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (xi: ren) (g': ctx)
  : Pure (key_brs_typing sg ln g' (ren_jctx xi d) (ren_octx xi om) o (ren_layout xi kts)
            (ren_ty_brs xi bs) (ren_ty xi t) (ren_ty xi r))
         (requires sig_ok sg /\ ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TKB_Nil _ ->
    check_ren sg xi g g' t KType; check_ren sg xi g g' r (KRow EEffect);
    TKB_Nil ()
  | TKB_Cons #_ #_ #_ #_ #_ #_ #k #pt #_ #_ #_ #_ #_ _ hdt h2 ->
    check_ren sg xi g g' pt KType;
    TKB_Cons () (dt_typing_ren_ty' hdt xi g') (key_brs_typing_ren_ty' h2 xi g')

and clauses_typing_ren_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause) (h: clauses_typing sg ln g ei ts r b cs) (q: qname) (xi: ren)
  (g': ctx)
  : Pure (clauses_typing sg ln g' ei (ren_tys xi ts) (ren_ty xi r) (ren_ty xi b) (ren_ty_cls xi cs))
         (requires sig_ok sg /\ ty_ren_ok xi g g' /\ sg.effects q == Some ei /\
                   L.length ts == L.length ei.eff_params)
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCL_Nil _ ->
    check_ren sg xi g g' b KType; check_ren sg xi g g' r (KRow EEffect);
    TCL_Nil ()
  | TCL_Full #_ #_ #_ #_ #_ #_ #_ #op #nb #s #kt #body #cs0 #os _ _ _ hb hcs ->
    let xu = upn_ren nb xi in
    let gb = push_tvars g os.binders in
    let gb' = push_tvars g' os.binders in
    ty_ren_ok_upn xi g g' os.binders;
    eff_inst_ren_sig sg q ei op os ts xi;
    check_ren sg xu gb gb' s KType;
    ty_eq_ren xu s (eff_inst nb ts os.arg);
    check_ren sg xu gb gb' kt KType;
    ty_eq_ren xu kt (t_fun (eff_inst nb ts os.res) (ren_ty (shift nb) r) (ren_ty (shift nb) b));
    ren_t_fun xu (eff_inst nb ts os.res) (ren_ty (shift nb) r) (ren_ty (shift nb) b);
    ren_shift_up nb xi r;
    ren_shift_up nb xi b;
    ty_ren_ok_push_var xu gb gb' s;
    ty_ren_ok_push_var xu (push_var gb s) (push_var gb' (ren_ty xu s)) kt;
    let hb' = cast (typing_ren_ty' hb xu (push_var (push_var gb' (ren_ty xu s)) (ren_ty xu kt))) []
                (ren_ty_exp xu body) (ren_ty (shift nb) (ren_ty xi b))
                  (ren_ty (shift nb) (ren_ty xi r)) in
    TCL_Full #sg #ln #g' #ei #(ren_tys xi ts) #(ren_ty xi r) #(ren_ty xi b) #op #nb #(ren_ty xu s)
      #(ren_ty xu kt) #(ren_ty_exp xu body) #(ren_ty_cls xi cs0) #os () () () hb'
      (clauses_typing_ren_ty' hcs q xi g')
  | TCL_Fast #_ #_ #_ #_ #_ #_ #_ #op #nb #s #body #cs0 #os _ _ hb hcs ->
    let xu = upn_ren nb xi in
    let gb = push_tvars g os.binders in
    let gb' = push_tvars g' os.binders in
    ty_ren_ok_upn xi g g' os.binders;
    eff_inst_ren_sig sg q ei op os ts xi;
    check_ren sg xu gb gb' s KType;
    ty_eq_ren xu s (eff_inst nb ts os.arg);
    ren_shift_up nb xi r;
    ty_ren_ok_push_var xu gb gb' s;
    let hb' = cast (typing_ren_ty' hb xu (push_var gb' (ren_ty xu s))) [] (ren_ty_exp xu body)
                (eff_inst nb (ren_tys xi ts) os.res) (ren_ty (shift nb) (ren_ty xi r)) in
    TCL_Fast #sg #ln #g' #ei #(ren_tys xi ts) #(ren_ty xi r) #(ren_ty xi b) #op #nb #(ren_ty xu s)
      #(ren_ty_exp xu body) #(ren_ty_cls xi cs0) #os () () hb' (clauses_typing_ren_ty' hcs q xi g')

and occ_typing_ren_ty' (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t) (xi: ren) (g': ctx)
  : Pure (occ_typing sg g' (ren_octx xi om) o (ren_ty xi t))
         (requires ty_ren_ok xi g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TO_Lookup _ -> assoc_ren_octx xi om o; TO_Lookup ()
  | TO_Field #_ #_ #_ #o0 #k #t_o #_ r0 ho _ _ ->
    ren_t_record xi r0;
    ty_eq_ren xi t_o (t_record r0);
    check_ren sg xi g g' r0 (KRow EType);
    check_ren sg xi g g' t KType;
    entries_ren_ty xi r0 k t;
    TO_Field #sg #g' #(ren_octx xi om) #o0 #k #(ren_ty xi t_o) #(ren_ty xi t) (ren_ty xi r0)
      (occ_typing_ren_ty' ho xi g') () ()

(* The stated theorems. *)

let occ_typing_ren_ty #sg #g #om #o #t h xi g' = occ_typing_ren_ty' h xi g'

let typing_ren_ty #sg #ln #g #d #e #t #r h xi g' = typing_ren_ty' h xi g'

let exps_typing_ren_ty #sg #ln #g #d #r #es #ts h xi g' = exps_typing_ren_ty' h xi g'

let chain_typing_ren_ty #sg #ln #g #d #r #e h xi g' = chain_typing_ren_ty' h xi g'

let binds_typing_ren_ty #sg #ln #g #bs h xi g' = binds_typing_ren_ty' h xi g'

let cells_typing_ren_ty #sg #ln #g #cells #lay h xi g' = cells_typing_ren_ty' h xi g'

let match_typing_ren_ty #sg #ln #g #d #r #th #om h xi g' = match_typing_ren_ty' h xi g'

let dt_typing_ren_ty #sg #ln #g #d #om #dt #t #r h xi g' = dt_typing_ren_ty' h xi g'

let ctor_brs_typing_ren_ty #sg #ln #g #d #om #o #ks #ss #cs #bs #t #r h xi g' =
  ctor_brs_typing_ren_ty' h xi g'

let lit_brs_typing_ren_ty #sg #ln #g #d #om #lt #bs #t #r h xi g' =
  lit_brs_typing_ren_ty' h xi g'

let key_brs_typing_ren_ty #sg #ln #g #d #om #o #kts #bs #t #r h xi g' =
  key_brs_typing_ren_ty' h xi g'

let clauses_typing_ren_ty #sg #ln #g #ei #ts #r #b #cs h q xi g' = clauses_typing_ren_ty' h q xi g'
