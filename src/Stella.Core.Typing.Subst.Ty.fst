(* Proof structure.

   The context lemmas take the kinding part from `Stella.Core.Kinding.Subst`
   (`sub_ok_up`, `sub_ok_assumps`, `sub_ok_subst1`) and prove the two maps
   of stored types directly: a term variable's type and a region's layout
   are shifted on both sides under a type binder, and the σ-calculus law
   `↑1 ; up σ = σ ; ren ↑1` (`sub_shift_up`) relates them. A lifted
   substitute is a shifted one, and shifting keeps local closure. A fact a
   region adds names a `Row Effect` variable `j`, and its image
   `RegionKey a ∉ σ j` is entailed by the facts the region adds in `Γ'`
   (`region_lacks_row`).

   The judgements are one mutual induction on the derivation, as for
   renaming (`Stella.Core.Typing.Rename.Ty`). Each rule's premises are
   substituted by the induction hypothesis, its side conditions by the
   lemmas on kinding (`check_sub`), entailment (`entails_sub` and cut by
   the entailed images of the hypotheses), type equality (`ty_eq_sub`),
   rows and declared types (`Stella.Core.Typing.Subst.Ty.Facts`), and its
   conclusion is cast to the substituted indices, which are equal to the
   ones the rule builds. The kinds of the type variables of `Γ'` stay
   quantifiable under every binder: a `Λ` checks its kind, and a clause's
   binders have kinds with no kind variable (`effects_wf`). *)
module Stella.Core.Typing.Subst.Ty
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
open Stella.Core.Spine.Wf
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Keys
open Stella.Core.Typing.Rename.Facts
open Stella.Core.Typing.Subst.Ty.Facts
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

(* Entailment by the substituted hypotheses. *)

let entails_into (sg: sig) (sigma: tsub) (g g': ctx) (c: constr)
  : Lemma (requires sub_ok sg sigma g g' /\ entails (hyps g) c)
          (ensures entails (hyps g') (sub_constr sigma c)) =
  entails_sub sigma (hyps g) c;
  introduce forall (h': constr). L.mem h' (L.map (sub_constr sigma) (hyps g)) ==> entails (hyps g') h'
  with introduce _ ==> _
  with (let _ = map_wit (sub_constr sigma) (hyps g) h' in ());
  entails_cut_all (L.map (sub_constr sigma) (hyps g)) (hyps g') (sub_constr sigma c)

(* The quantifiable kinds of the type variables of `Γ'`. *)

let rec tvars_wf_push_tvars (g: ctx) (ks: list kind)
  : Lemma (requires tvars_wf g /\ qkinds_wf 0 ks) (ensures tvars_wf (push_tvars g ks)) (decreases ks) =
  match ks with
  | [] -> ()
  | k :: ks' ->
    qkinds_wf_mono 0 g.nk [k];
    tvars_wf_push_tvar g k;
    tvars_wf_push_tvars (push_tvar g k) ks'

let rec ops_ok_assoc (sg: sig) (params: list kind) (ops: list (opname & op_sig)) (op: opname)
  (os: op_sig)
  : Lemma (requires ops_ok sg params ops /\ L.assoc op ops == Some os) (ensures op_ok sg params os)
          (decreases ops) =
  match ops with
  | (op', _) :: ops' -> if op = op' then () else ops_ok_assoc sg params ops' op os

let binders_closed (sg: sig) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  : Lemma (requires effects_wf sg /\ sg.effects q == Some ei /\ op_of ei op == Some os)
          (ensures qkinds_wf 0 os.binders) =
  assert (match sg.effects q with Some ei -> effect_ok sg ei | None -> True);
  ops_ok_assoc sg ei.eff_params ei.eff_ops op os

(* The context morphism. *)

let sub_constr_ext (sigma sigma': tsub) (c: constr)
  : Lemma (requires forall (i: nat). sigma' i == sigma i)
          (ensures sub_constr sigma' c == sub_constr sigma c) =
  sub_ren_constr sigma id_ren sigma' c;
  ren_id_constr id_ren c

let sub_layout_ext (sigma sigma': tsub) (l: layout)
  : Lemma (requires forall (i: nat). sigma' i == sigma i)
          (ensures sub_layout sigma' l == sub_layout sigma l) =
  sub_ren_layout sigma id_ren sigma' l;
  ren_id_layout id_ren l

let ty_sub_ok_ext sg sigma sigma' g g' =
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps g') (sub_constr sigma' h)
  with introduce _ ==> _
  with sub_constr_ext sigma sigma' h;
  introduce forall (i: nat). (match L.nth g.vars i with
                              | Some t -> L.nth g'.vars i == Some (sub_ty sigma' t)
                              | None -> True)
  with (match L.nth g.vars i with
        | Some t -> sub_ty_ext sigma sigma' t
        | None -> ());
  introduce forall (a: atom). (match L.assoc a g.regions with
                               | Some l -> L.assoc a g'.regions == Some (sub_layout sigma' l)
                               | None -> True)
  with (match L.assoc a g.regions with
        | Some l -> sub_layout_ext sigma sigma' l
        | None -> ())

let ty_sub_ok_up sg sigma g g' k =
  sub_ok_up sg sigma g g' k;
  introduce forall (i: nat). lc_ty (up_tsub sigma i)
  with (if i = 0 then () else lc_ren_ty 0 (shift 1) (sigma (i - 1)));
  introduce forall (i: nat). (match L.nth (push_tvar g k).vars i with
                              | Some t -> L.nth (push_tvar g' k).vars i
                                == Some (sub_ty (up_tsub sigma) t)
                              | None -> True)
  with begin
    nth_map (ren_ty (shift 1)) g.vars i;
    nth_map (ren_ty (shift 1)) g'.vars i;
    match L.nth g.vars i with
    | Some t -> sub_shift_up 1 sigma t
    | None -> ()
  end;
  introduce forall (a: atom). (match L.assoc a (push_tvar g k).regions with
                               | Some l ->
                                 L.assoc a (push_tvar g' k).regions
                                   == Some (sub_layout (up_tsub sigma) l)
                               | None -> True)
  with begin
    assoc_ren_regions (shift 1) g.regions a;
    assoc_ren_regions (shift 1) g'.regions a;
    match L.assoc a g.regions with
    | Some l -> sub_layout_shift_up 1 sigma l
    | None -> ()
  end

let rec ty_sub_ok_upn (sg: sig) (sigma: tsub) (g g': ctx) (ks: list kind)
  : Lemma (requires ty_sub_ok sg sigma g g')
          (ensures ty_sub_ok sg (upn_tsub (L.length ks) sigma) (push_tvars g ks) (push_tvars g' ks))
          (decreases ks) =
  match ks with
  | [] ->
    introduce forall (i: nat). upn_tsub 0 sigma i == sigma i
    with ren_ty_shift0 (sigma i);
    ty_sub_ok_ext sg sigma (upn_tsub 0 sigma) g g'
  | k :: ks' ->
    ty_sub_ok_up sg sigma g g' k;
    ty_sub_ok_upn sg (up_tsub sigma) (push_tvar g k) (push_tvar g' k) ks';
    introduce forall (i: nat). upn_tsub (L.length ks) sigma i
                               == upn_tsub (L.length ks') (up_tsub sigma) i
    with upn_tsub_succ (L.length ks') sigma i;
    ty_sub_ok_ext sg (upn_tsub (L.length ks') (up_tsub sigma)) (upn_tsub (L.length ks) sigma)
      (push_tvars (push_tvar g k) ks') (push_tvars (push_tvar g' k) ks')

let ty_sub_ok_assumps sg sigma g g' cs = sub_ok_assumps sg sigma g g' cs

let ty_sub_ok_assump sg sigma g g' c =
  add_assump_assumps g c;
  add_assump_assumps g' (sub_constr sigma c);
  ty_sub_ok_assumps sg sigma g g' [c]

let ty_sub_ok_push_var sg sigma g g' t =
  let g1 = push_var g t in
  let g1' = push_var g' (sub_ty sigma t) in
  assert (hyps g1 == hyps g /\ hyps g1' == hyps g');
  assert (rdom g1 == rdom g /\ rdom g1' == rdom g');
  same_kinding_push_var g' (sub_ty sigma t);
  introduce forall (i: nat). (match L.nth g.tvars i with
                              | Some k -> check sg g1' (sigma i) k
                              | None -> True)
  with (match L.nth g.tvars i with
        | Some k -> check_same_kinding sg g' g1' (sigma i) k
        | None -> ());
  introduce forall (i: nat). (match L.nth g1.vars i with
                              | Some t0 -> L.nth g1'.vars i == Some (sub_ty sigma t0)
                              | None -> True)
  with (if i = 0 then () else assert (L.nth g.vars (i - 1) == L.nth g.vars (i - 1)))

let rec ty_sub_ok_push_vars (sg: sig) (sigma: tsub) (g g': ctx) (ts: list typ)
  : Lemma (requires ty_sub_ok sg sigma g g')
          (ensures ty_sub_ok sg sigma (push_vars g ts) (push_vars g' (sub_tys sigma ts)))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' ->
    ty_sub_ok_push_var sg sigma g g' t;
    ty_sub_ok_push_vars sg sigma (push_var g t) (push_var g' (sub_ty sigma t)) ts'

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

let mem_hyps_enter_region (g: ctx) (a: atom) (l: layout) (h: constr)
  : Lemma (L.mem h (hyps (enter_region g a l)) <==>
           L.mem h (region_facts a 0 g.tvars) \/ L.mem h (hyps g)) =
  LP.append_mem (L.append (region_facts a 0 g.tvars) g.facts) g.assumps h;
  LP.append_mem (region_facts a 0 g.tvars) g.facts h;
  LP.append_mem g.facts g.assumps h

let ty_sub_ok_enter_region sg sigma g g' a l =
  let g1 = enter_region g a l in
  let g1' = enter_region g' a (sub_layout sigma l) in
  rdom_enter_region g a l;
  rdom_enter_region g' a (sub_layout sigma l);
  assert (g1.tvars == g.tvars /\ g1'.tvars == g'.tvars /\ g1.vars == g.vars /\ g1'.vars == g'.vars);
  ctx_ext_enter_region g' a (sub_layout sigma l);
  introduce forall (i: nat). (match L.nth g1.tvars i with
                              | Some k -> check sg g1' (sigma i) k
                              | None -> True)
  with (match L.nth g.tvars i with
        | Some k -> check_weaken sg g' g1' (sigma i) k
        | None -> ());
  introduce forall (h: constr). L.mem h (hyps g') ==> L.mem h (hyps g1')
  with mem_hyps_enter_region g' a (sub_layout sigma l) h;
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g1') (sub_constr sigma h)
  with introduce _ ==> _
  with begin
    mem_hyps_enter_region g a l h;
    if L.mem h (region_facts a 0 g.tvars) then begin
      let j = region_facts_wit a 0 g.tvars h in
      assert (L.nth g.tvars j == Some (KRow EEffect));
      assert (check sg g' (sigma j) (KRow EEffect));
      region_lacks_row sg g' a (sub_layout sigma l) (sigma j)
    end
    else entails_weaken (hyps g') (hyps g1') (sub_constr sigma h)
  end;
  introduce forall (b: atom). (match L.assoc b g1.regions with
                               | Some l0 -> L.assoc b g1'.regions == Some (sub_layout sigma l0)
                               | None -> True)
  with (if b = a then () else assert (L.assoc b g.regions == L.assoc b g.regions))

let ty_sub_ok_fresh sg sigma g g' a body =
  FStar.Classical.move_requires (frn_sub_ty_exp sigma body) a

let ty_sub_ok_subst1 sg g k s =
  sub_ok_subst1 sg g k s;
  check_lc sg g s k;
  introduce forall (i: nat). lc_ty (scons s tvar i)
  with (if i = 0 then () else ());
  introduce forall (i: nat). (match L.nth (push_tvar g k).vars i with
                              | Some t -> L.nth g.vars i == Some (sub_ty (scons s tvar) t)
                              | None -> True)
  with begin
    nth_map (ren_ty (shift 1)) g.vars i;
    match L.nth g.vars i with
    | Some t -> sub_ren_ty (scons s tvar) (shift 1) tvar t; sub_ty_tvar t
    | None -> ()
  end;
  introduce forall (a: atom). (match L.assoc a (push_tvar g k).regions with
                               | Some l -> L.assoc a g.regions == Some (sub_layout (scons s tvar) l)
                               | None -> True)
  with begin
    assoc_ren_regions (shift 1) g.regions a;
    match L.assoc a g.regions with
    | Some l ->
      sub_ren_layout (scons s tvar) (shift 1) tvar l;
      sub_id_layout tvar l
    | None -> ()
  end

(* Side conditions. *)

let rec tys_ok_sub (sg: sig) (sigma: tsub) (g g': ctx) (ts: list typ)
  : Lemma (requires sub_ok sg sigma g g' /\ tys_ok sg g ts) (ensures tys_ok sg g' (sub_tys sigma ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> check_sub sg sigma g g' t KType; tys_ok_sub sg sigma g g' ts

let regions_incl_of (g g': ctx)
  : Lemma (requires rdom_incl g g') (ensures regions_incl g.regions g'.regions) =
  introduce forall (a: atom). L.mem a (L.map fst g.regions) ==> L.mem a (L.map fst g'.regions)
  with introduce _ ==> _
  with assert (L.mem a (rdom g))

(* A closed type of a run-time form stays kinded, and is fixed. *)
let closed_sub (sg: sig) (sigma: tsub) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires rdom_incl g g' /\ check sg (closed_ctx g.regions) t k)
          (ensures check sg (closed_ctx g'.regions) t k /\ sub_ty sigma t == t) =
  regions_incl_of g g';
  check_closed_mono sg g.regions g'.regions t k;
  check_closed_sub sg g.regions t k sigma

let rec scrut_occs_sub (sigma: tsub) (i: nat) (ts: list typ)
  : Lemma (ensures sub_octx sigma (scrut_occs i ts) == scrut_occs i (sub_tys sigma ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts -> scrut_occs_sub sigma (i + 1) ts

let rec field_occs_sub (sigma: tsub) (o: occ) (c: qname) (j: nat) (fs: list typ)
  : Lemma (ensures sub_octx sigma (field_occs o c j fs) == field_occs o c j (sub_tys sigma fs))
          (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs -> field_occs_sub sigma o c (j + 1) fs

let rec sub_octx_append (sigma: tsub) (om1 om2: octx)
  : Lemma (ensures sub_octx sigma (L.append om1 om2)
                   == L.append (sub_octx sigma om1) (sub_octx sigma om2))
          (decreases om1) =
  match om1 with
  | [] -> ()
  | _ :: om1 -> sub_octx_append sigma om1 om2

let rec assoc_sub_octx (sigma: tsub) (om: octx) (o: occ)
  : Lemma (ensures L.assoc o (sub_octx sigma om) == map_opt (sub_ty sigma) (L.assoc o om))
          (decreases om) =
  match om with
  | [] -> ()
  | _ :: om -> assoc_sub_octx sigma om o

let rec nth_sub_jctx (sigma: tsub) (d: jctx) (j: nat)
  : Lemma (ensures L.nth (sub_jctx sigma d) j == map_opt (sub_jt sigma) (L.nth d j)) (decreases d) =
  match d with
  | [] -> ()
  | _ :: d -> if j = 0 then () else nth_sub_jctx sigma d (j - 1)

let rec clause_ops_sub (sigma: tsub) (cs: list clause)
  : Lemma (ensures clause_ops (sub_ty_cls sigma cs) == clause_ops cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ _ :: cs | CFast _ _ _ _ :: cs -> clause_ops_sub sigma cs

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

(* The rules, one builder each. A builder takes the substituted premises,
   in the form the induction produces them, and the indices of the
   conclusion with their equations to the rule's parts, and concludes the
   substituted judgement. *)

let tr (sg: sig) (ln: lctx) (g': ctx) (sigma: tsub) (d: jctx) (e: exp) (t r: typ) : Type =
  typing sg ln g' (sub_jctx sigma d) (sub_ty_exp sigma e) (sub_ty sigma t) (sub_ty sigma r)

let sub_rec_ext (sigma: tsub) (k: key) (t r0: typ)
  : Lemma (sub_ty sigma (t_record (TRowExt (EntTy k t) r0)) ==
           t_record (TRowExt (EntTy k (sub_ty sigma t)) (sub_ty sigma r0))) =
  sub_t_record sigma (TRowExt (EntTy k t) r0)

let sub_var_ext (sigma: tsub) (k: key) (t r0: typ)
  : Lemma (sub_ty sigma (t_variant (TRowExt (EntTy k t) r0)) ==
           t_variant (TRowExt (EntTy k (sub_ty sigma t)) (sub_ty sigma r0))) =
  sub_t_variant sigma (TRowExt (EntTy k t) r0)

let sub_perform_eq (sigma: tsub) (k: key) (op: opname) (ss: list typ) (e1: exp)
  : Lemma (sub_ty_exp sigma (EPerform k op ss e1)
           == EPerform k op (sub_tys sigma ss) (sub_ty_exp sigma e1)) = ()

let sub_union_eq (sigma: tsub) (r1 r2: typ)
  : Lemma (sub_ty sigma (TRowUnion r1 r2) == TRowUnion (sub_ty sigma r1) (sub_ty sigma r2)) = ()

let sub_ext_eq (sigma: tsub) (en: entry) (r: typ)
  : Lemma (sub_ty sigma (TRowExt en r) == TRowExt (sub_ent sigma en) (sub_ty sigma r)) = ()

let sub_handle_eq (sigma: tsub) (e1: exp) (hd: handler)
  : Lemma (sub_ty_exp sigma (EHandle e1 hd) ==
           EHandle (sub_ty_exp sigma e1)
             { h_ent = sub_ent sigma hd.h_ent; h_ret_ty = sub_ty sigma hd.h_ret_ty;
               h_ret = sub_ty_exp sigma hd.h_ret; h_clauses = sub_ty_cls sigma hd.h_clauses }) = ()

let sub_region_eq (sigma: tsub) (l: layout) (es: list exp) (body: exp)
  : Lemma (sub_ty_exp sigma (ERegion l es body)
           == ERegion (sub_layout sigma l) (sub_ty_exps sigma es) (sub_ty_exp sigma body)) = ()

let sub_region_open_eq (sigma: tsub) (a: atom) (cells: list (key & exp)) (body: exp)
  : Lemma (sub_ty_exp sigma (ERegionOpen a cells body)
           == ERegionOpen a (sub_ty_cells sigma cells) (sub_ty_exp sigma body)) = ()

let sub_tyapp_eq (sigma: tsub) (e0: exp) (s: typ)
  : Lemma (sub_ty_exp sigma (ETyApp e0 s) == ETyApp (sub_ty_exp sigma e0) (sub_ty sigma s)) = ()

let sub_capp_eq (sigma: tsub) (e0: exp) : Lemma (sub_ty_exp sigma (ECApp e0) == ECApp (sub_ty_exp sigma e0)) =
  ()

let sub_app_eq (sigma: tsub) (e0 v: exp)
  : Lemma (sub_ty_exp sigma (EApp e0 v) == EApp (sub_ty_exp sigma e0) (sub_ty_exp sigma v)) = ()

let sub_let_eq (sigma: tsub) (t1: typ) (e1 e2: exp)
  : Lemma (sub_ty_exp sigma (ELet t1 e1 e2)
           == ELet (sub_ty sigma t1) (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)) = ()

let sub_letjoin_eq (sigma: tsub) (ts: list typ) (t: typ) (e1 e2: exp)
  : Lemma (sub_ty_exp sigma (ELetJoin ts t e1 e2) ==
           ELetJoin (sub_tys sigma ts) (sub_ty sigma t) (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)) =
  ()

let sub_extend_eq (sigma: tsub) (k: key) (e1 e2: exp)
  : Lemma (sub_ty_exp sigma (EExtend k e1 e2)
           == EExtend k (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)) = ()

let sub_update_eq (sigma: tsub) (k: key) (e1 e2: exp)
  : Lemma (sub_ty_exp sigma (EUpdate k e1 e2)
           == EUpdate k (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)) = ()

let sub_merge_eq (sigma: tsub) (e1 e2: exp)
  : Lemma (sub_ty_exp sigma (EMerge e1 e2) == EMerge (sub_ty_exp sigma e1) (sub_ty_exp sigma e2)) = ()

let sub_inject_eq (sigma: tsub) (k: key) (r0: typ) (e1: exp)
  : Lemma (sub_ty_exp sigma (EInject k r0 e1) == EInject k (sub_ty sigma r0) (sub_ty_exp sigma e1)) =
  ()

let sub_weaken_eq (sigma: tsub) (k: key) (t1: typ) (e1: exp)
  : Lemma (sub_ty_exp sigma (EWeaken k t1 e1) == EWeaken k (sub_ty sigma t1) (sub_ty_exp sigma e1)) =
  ()

let sub_openeff_eq (sigma: tsub) (r2: typ) (e1: exp)
  : Lemma (sub_ty_exp sigma (EOpenEff r2 e1) == EOpenEff (sub_ty sigma r2) (sub_ty_exp sigma e1)) = ()

let sub_openeffc_eq (sigma: tsub) (r2: typ) (e1: exp)
  : Lemma (sub_ty_exp sigma (EOpenEffC r2 e1) == EOpenEffC (sub_ty sigma r2) (sub_ty_exp sigma e1)) =
  ()

let sub_writecell_eq (sigma: tsub) (a: region_ref) (k: key) (e1: exp)
  : Lemma (sub_ty_exp sigma (EWriteCell a k e1) == EWriteCell a k (sub_ty_exp sigma e1)) = ()

let b_var (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (i: nat)
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EVar i /\ L.nth g.vars i == Some t /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_sub sg sigma g g' r (KRow EEffect);
  assert (L.nth g.vars i == L.nth g.vars i);
  T_Var #sg #ln #g' #(sub_jctx sigma d) #i #(sub_ty sigma t) #(sub_ty sigma r) () ()

let b_global (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (q: qname) (ks: list kind) (nk: nat) (t0: typ)
  : Pure (tr sg ln g' sigma d e t r)
         (requires sig_ok sg /\ ty_sub_ok sg sigma g g' /\ e == EGlobal q ks /\ t == kinst_ty ks t0 /\
                   global_type sg q == Some (nk, t0) /\ L.length ks == nk /\ qkinds_wf g.nk ks /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_sub sg sigma g g' r (KRow EEffect);
  global_inst_sub sg q nk t0 ks sigma;
  T_Global #sg #ln #g' #(sub_jctx sigma d) #q #ks #nk #t0 #(sub_ty sigma r) () () ()

let b_lit (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (c: lit)
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ELit c /\ t == lit_type c /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_sub sg sigma g g' r (KRow EEffect);
  sub_lit_type sigma c;
  T_Lit #sg #ln #g' #(sub_jctx sigma d) #c #(sub_ty sigma r) ()

let b_lam (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1 r1: typ) (body: exp) (t2: typ)
  (hb: typing sg ln (push_var g' (sub_ty sigma t1)) (sub_jctx sigma []) (sub_ty_exp sigma body)
         (sub_ty sigma t2) (sub_ty sigma r1))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ELam t1 r1 body /\ t == t_fun t1 r1 t2 /\
                   check sg g t1 KType /\ check sg g r1 (KRow EEffect) /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_sub sg sigma g g' t1 KType;
  check_sub sg sigma g g' r1 (KRow EEffect);
  check_sub sg sigma g g' r (KRow EEffect);
  sub_t_fun sigma t1 r1 t2;
  T_Lam #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma t1) #(sub_ty sigma r1)
    #(sub_ty_exp sigma body) #(sub_ty sigma t2) #(sub_ty sigma r) () () hb

let b_app (#sg: sig) (#ln: lctx) (sigma: tsub) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1 e2: exp) (t1 t2: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1)
         (sub_ty sigma (t_fun t1 r t2)) (sub_ty sigma r))
  (h2: typing sg ln g' [] (sub_ty_exp sigma e2) (sub_ty sigma t1)
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r) (requires e == EApp e1 e2 /\ t == t2) (ensures fun _ -> True) =
  sub_app_eq sigma e1 e2;
  sub_t_fun sigma t1 r t2;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (t_fun (sub_ty sigma t1) (sub_ty sigma r) (sub_ty sigma t2)) (sub_ty sigma r) = h1 in
  T_App h1 h2

let b_chain (#sg: sig) (#ln: lctx) (sigma: tsub) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t0: typ) (th: tsub)
  (hc: chain_typing sg ln g' [] (sub_ty sigma r) (sub_ty_exp sigma e))
  : Pure (tr sg ln g' sigma d e t r)
         (requires sig_ok sg /\ chain_cursor sg e == Some (t0, th) /\ t == sub_ty th t0)
         (ensures fun _ -> True) =
  chain_cursor_sub_ty sg sigma e t0 th;
  let Some (_, th') = chain_cursor sg (sub_ty_exp sigma e) in
  T_Chain #sg #ln #g' #(sub_jctx sigma d) #(sub_ty_exp sigma e) #t0 #th' #(sub_ty sigma r) hc ()

let b_tylam (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (k: kind) (body: exp) (t0: typ)
  (hb: typing sg ln (push_tvar g' k) (sub_jctx (up_tsub sigma) [])
         (sub_ty_exp (up_tsub sigma) body) (sub_ty (up_tsub sigma) t0)
         (sub_ty (up_tsub sigma) TRowEmpty))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ETyLam k body /\ t == TForall k t0 /\
                   kind_wf g.nk k /\ qkind g.nk k /\ value_form sg body /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  value_form_sub_ty sg (up_tsub sigma) body;
  check_sub sg sigma g g' r (KRow EEffect);
  let hb : typing sg ln (push_tvar g' k) [] (sub_ty_exp (up_tsub sigma) body)
             (sub_ty (up_tsub sigma) t0) TRowEmpty = hb in
  T_TyLam #sg #ln #g' #(sub_jctx sigma d) #k #(sub_ty_exp (up_tsub sigma) body)
    #(sub_ty (up_tsub sigma) t0) #(sub_ty sigma r) () () () hb

let b_tyapp (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (e1: exp) (s: typ) (k: kind) (t0: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1) (sub_ty sigma (TForall k t0))
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ETyApp e1 s /\ t == subst1_ty s t0 /\
                   check sg g s k)
         (ensures fun _ -> True) =
  check_sub sg sigma g g' s k;
  sub_subst1 sigma s t0;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (TForall k (sub_ty (up_tsub sigma) t0)) (sub_ty sigma r) = h1 in
  T_TyApp #sg #ln #g' #(sub_jctx sigma d) #(sub_ty_exp sigma e1) #(sub_ty sigma s) h1 ()

let b_clam (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (c: constr) (body: exp) (t0: typ)
  (hb: typing sg ln (add_assump g' (sub_constr sigma c)) (sub_jctx sigma [])
         (sub_ty_exp sigma body) (sub_ty sigma t0) (sub_ty sigma TRowEmpty))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ECLam c body /\ t == TConstr c t0 /\
                   constr_ok sg g c /\ value_form sg body /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  constr_ok_sub sg sigma g g' c;
  value_form_sub_ty sg sigma body;
  check_sub sg sigma g g' r (KRow EEffect);
  let hb : typing sg ln (add_assump g' (sub_constr sigma c)) [] (sub_ty_exp sigma body)
             (sub_ty sigma t0) TRowEmpty = hb in
  T_CLam #sg #ln #g' #(sub_jctx sigma d) #(sub_constr sigma c) #(sub_ty_exp sigma body)
    #(sub_ty sigma t0) #(sub_ty sigma r) () () () hb

let b_capp (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (e1: exp) (c: constr)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1) (sub_ty sigma (TConstr c t))
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ECApp e1 /\ entails (hyps g) c)
         (ensures fun _ -> True) =
  entails_into sg sigma g g' c;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (TConstr (sub_constr sigma c) (sub_ty sigma t)) (sub_ty sigma r) = h1 in
  T_CApp h1 ()

let b_let (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1: typ) (e1 e2: exp)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1) (sub_ty sigma t1)
         (sub_ty sigma r))
  (h2: typing sg ln (push_var g' (sub_ty sigma t1)) (sub_jctx sigma d) (sub_ty_exp sigma e2)
         (sub_ty sigma t) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ELet t1 e1 e2 /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  sub_let_eq sigma t1 e1 e2;
  check_sub sg sigma g g' t1 KType;
  T_Let () h1 h2

let b_letrec (#sg: sig) (#ln: lctx) (sigma: tsub) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (bs: list (typ & exp)) (body: exp)
  (hbs: binds_typing sg ln (push_vars g' (sub_tys sigma (L.map fst bs))) (sub_ty_binds sigma bs))
  (hb: typing sg ln (push_vars g' (sub_tys sigma (L.map fst bs))) (sub_jctx sigma d)
         (sub_ty_exp sigma body) (sub_ty sigma t) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires e == ELetRec bs body /\ Stella.Core.Init.init_safe_letrec sg bs)
         (ensures fun _ -> True) =
  IR.init_safe_sub_ty sg sigma bs;
  sub_ty_binds_fst sigma bs;
  T_LetRec #sg #ln #g' #(sub_jctx sigma d) #(sub_ty_binds sigma bs) #(sub_ty_exp sigma body)
    #(sub_ty sigma t) #(sub_ty sigma r) () hbs hb

let b_conv (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (t1 r1: typ)
  (h1: typing sg ln g' (sub_jctx sigma d) (sub_ty_exp sigma e) (sub_ty sigma t1) (sub_ty sigma r1))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ ty_eq t1 t /\ ty_eq r1 r /\ check sg g t KType /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  ty_eq_sub sigma t1 t; ty_eq_sub sigma r1 r;
  check_sub sg sigma g g' t KType; check_sub sg sigma g g' r (KRow EEffect);
  T_Conv h1 () ()

let b_case (#sg: sig) (#ln: lctx) (sigma: tsub) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (es: list exp) (dt: dtree) (ts: list typ)
  (hes: exps_typing sg ln g' [] (sub_ty sigma r) (sub_ty_exps sigma es)
          (sub_tys sigma ts))
  (hdt: dt_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma (scrut_occs 0 ts))
          (sub_ty_dt sigma dt) (sub_ty sigma t) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r) (requires e == ECase es dt) (ensures fun _ -> True) =
  scrut_occs_sub sigma 0 ts;
  T_Case hes (cast_dt hdt (scrut_occs 0 (sub_tys sigma ts)) (sub_ty sigma t) (sub_ty sigma r))

let b_letjoin (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (ts: list typ) (e1 e2: exp)
  (h1: typing sg ln (push_vars g' (sub_tys sigma ts)) (sub_jctx sigma ((ts, t, r) :: d))
         (sub_ty_exp sigma e1) (sub_ty sigma t) (sub_ty sigma r))
  (h2: typing sg ln g' (sub_jctx sigma ((ts, t, r) :: d)) (sub_ty_exp sigma e2) (sub_ty sigma t)
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ELetJoin ts t e1 e2 /\ tys_ok sg g ts /\
                   check sg g t KType)
         (ensures fun _ -> True) =
  sub_letjoin_eq sigma ts t e1 e2;
  tys_ok_sub sg sigma g g' ts;
  check_sub sg sigma g g' t KType;
  T_LetJoin #sg #ln #g' #(sub_jctx sigma d) #(sub_tys sigma ts) #(sub_ty sigma t)
    #(sub_ty_exp sigma e1) #(sub_ty_exp sigma e2) #(sub_ty sigma r) () h1 h2

let b_jump (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp) (t r: typ)
  (j: nat) (es: list exp) (ts: list typ)
  (hes: exps_typing sg ln g' [] (sub_ty sigma r) (sub_ty_exps sigma es)
          (sub_tys sigma ts))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EJump j es /\
                   L.nth d j == Some (ts, t, r) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  nth_sub_jctx sigma d j;
  check_sub sg sigma g g' t KType; check_sub sg sigma g g' r (KRow EEffect);
  T_Jump #sg #ln #g' #(sub_jctx sigma d) #j #(sub_ty_exps sigma es) #(sub_tys sigma ts)
    #(sub_ty sigma t) #(sub_ty sigma r) () () hes

let b_recempty (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ)
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ERecEmpty /\ t == t_record TRowEmpty /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  sub_t_record sigma TRowEmpty;
  check_sub sg sigma g g' r (KRow EEffect);
  T_RecEmpty #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma r) ()

let b_extend (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (e1 e2: exp) (t1 r0: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1) (sub_ty sigma t1)
         (sub_ty sigma r))
  (h2: typing sg ln g' [] (sub_ty_exp sigma e2) (sub_ty sigma (t_record r0))
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EExtend k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t1) r0) /\ key_ok sg g k EType /\
                   entails (hyps g) (CLacks k r0))
         (ensures fun _ -> True) =
  sub_extend_eq sigma k e1 e2;
  sub_rec_ext sigma k t1 r0;
  key_ok_rdom sg g g' k EType;
  entails_into sg sigma g g' (CLacks k r0);
  let h2 : typing sg ln g' [] (sub_ty_exp sigma e2)
             (t_record (sub_ty sigma r0)) (sub_ty sigma r) = h2 in
  T_Extend #sg #ln #g' #(sub_jctx sigma d) #k h1 h2 ()

let b_select (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1)
         (sub_ty sigma (t_record (TRowExt (EntTy k t) r0))) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ESelect k e1 /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  sub_rec_ext sigma k t r0;
  key_ok_rdom sg g g' k EType;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (t_record (TRowExt (EntTy k (sub_ty sigma t)) (sub_ty sigma r0))) (sub_ty sigma r) =
    h1 in
  T_Select h1 ()

let b_restrict (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (e1: exp) (t1 r0: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1)
         (sub_ty sigma (t_record (TRowExt (EntTy k t1) r0))) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ERestrict k e1 /\ t == t_record r0 /\
                   key_ok sg g k EType)
         (ensures fun _ -> True) =
  sub_rec_ext sigma k t1 r0;
  key_ok_rdom sg g g' k EType;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (t_record (TRowExt (EntTy k (sub_ty sigma t1)) (sub_ty sigma r0))) (sub_ty sigma r) =
    h1 in
  T_Restrict h1 ()

let b_update (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (e1 e2: exp) (t1 t2 r0: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1)
         (sub_ty sigma (t_record (TRowExt (EntTy k t1) r0))) (sub_ty sigma r))
  (h2: typing sg ln g' [] (sub_ty_exp sigma e2) (sub_ty sigma t2)
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EUpdate k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t2) r0) /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  sub_update_eq sigma k e1 e2;
  sub_rec_ext sigma k t1 r0; sub_rec_ext sigma k t2 r0;
  key_ok_rdom sg g g' k EType;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (t_record (TRowExt (EntTy k (sub_ty sigma t1)) (sub_ty sigma r0))) (sub_ty sigma r) =
    h1 in
  T_Update h1 h2 ()

let b_merge (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (e1 e2: exp) (r1 r2: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1) (sub_ty sigma (t_record r1))
         (sub_ty sigma r))
  (h2: typing sg ln g' [] (sub_ty_exp sigma e2) (sub_ty sigma (t_record r2))
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EMerge e1 e2 /\
                   t == t_record (TRowUnion r1 r2) /\ entails (hyps g) (CDisj r1 r2))
         (ensures fun _ -> True) =
  sub_merge_eq sigma e1 e2;
  sub_union_eq sigma r1 r2;
  sub_t_record sigma (TRowUnion r1 r2); sub_t_record sigma r1; sub_t_record sigma r2;
  entails_into sg sigma g g' (CDisj r1 r2);
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (t_record (sub_ty sigma r1)) (sub_ty sigma r) = h1 in
  let h2 : typing sg ln g' [] (sub_ty_exp sigma e2)
             (t_record (sub_ty sigma r2)) (sub_ty sigma r) = h2 in
  T_Merge h1 h2 ()

let b_inject (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (r0: typ) (e1: exp) (t1: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1) (sub_ty sigma t1)
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EInject k r0 e1 /\
                   t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\
                   check sg g r0 (KRow EType))
         (ensures fun _ -> True) =
  sub_inject_eq sigma k r0 e1;
  sub_var_ext sigma k t1 r0;
  key_ok_rdom sg g g' k EType;
  entails_into sg sigma g g' (CLacks k r0);
  check_sub sg sigma g g' r0 (KRow EType);
  T_Inject #sg #ln #g' #(sub_jctx sigma d) #k #(sub_ty sigma r0) h1 () ()

let b_weaken (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (t1: typ) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1)
         (sub_ty sigma (t_variant r0)) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EWeaken k t1 e1 /\
                   t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  sub_weaken_eq sigma k t1 e1;
  sub_var_ext sigma k t1 r0;
  key_ok_rdom sg g g' k EType;
  entails_into sg sigma g g' (CLacks k r0);
  check_sub sg sigma g g' t1 KType;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (t_variant (sub_ty sigma r0)) (sub_ty sigma r) = h1 in
  T_Weaken #sg #ln #g' #(sub_jctx sigma d) #k #(sub_ty sigma t1) h1 () ()

let b_variant_value (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (v: exp) (pt vr0 vr: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e)
         (sub_ty sigma (t_variant vr0)) (sub_ty sigma r))
  (h2: typing sg ln g' [] (sub_ty_exp sigma v) (sub_ty sigma pt)
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ t == t_variant vr /\ V.is_value sg e /\
                   variant_view e == Some (k, v) /\ check sg g (t_variant vr) KType /\
                   check sg g pt KType /\ L.mem (k, PTy (canon pt)) (row_entries (canon vr)))
         (ensures fun _ -> True) =
  sub_t_variant sigma vr; sub_t_variant sigma vr0;
  is_value_sub_ty sg sigma e;
  variant_view_sub_ty sigma e;
  check_sub sg sigma g g' (t_variant vr) KType;
  check_sub sg sigma g g' pt KType;
  entries_sub_ty sigma vr k pt;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e)
             (t_variant (sub_ty sigma vr0)) (sub_ty sigma r) = h1 in
  T_VariantValue #sg #ln #g' #(sub_jctx sigma d) #(sub_ty_exp sigma e) #k
    #(sub_ty_exp sigma v) #(sub_ty sigma pt) #(sub_ty sigma r) (sub_ty sigma vr0) (sub_ty sigma vr)
    h1 () h2 ()

let b_absurd (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (e1: exp)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1)
         (sub_ty sigma (t_variant TRowEmpty)) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EAbsurd t e1 /\ check sg g t KType)
         (ensures fun _ -> True) =
  sub_t_variant sigma TRowEmpty;
  check_sub sg sigma g g' t KType;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1) (t_variant TRowEmpty)
             (sub_ty sigma r) = h1 in
  T_Absurd #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma t) h1 ()

let b_perform (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (k: key) (op: opname) (ss: list typ) (e1: exp) (q: qname) (ei: effect_info)
  (os: op_sig) (ts: list typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1)
         (sub_ty sigma (op_inst ts ss os.arg)) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires sig_ok sg /\ ty_sub_ok sg sigma g g' /\ e == EPerform k op ss e1 /\
                   t == op_inst ts ss os.res /\
                   L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)) /\
                   sg.effects q == Some ei /\ op_of ei op == Some os /\
                   check_tys sg g ts ei.eff_params /\ check_tys sg g ss os.binders)
         (ensures fun _ -> True) =
  sub_perform_eq sigma k op ss e1;
  entries_sub_eff sigma r k q ts;
  check_tys_sub sg sigma g g' ts ei.eff_params;
  check_tys_sub sg sigma g g' ss os.binders;
  check_tys_length sg g ts ei.eff_params;
  check_tys_length sg g ss os.binders;
  op_inst_sub_sig sg q ei op os ts ss sigma;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (op_inst (sub_tys sigma ts) (sub_tys sigma ss) os.arg) (sub_ty sigma r) = h1 in
  T_Perform #sg #ln #g' #(sub_jctx sigma d) #k #op #(sub_tys sigma ss) #(sub_ty_exp sigma e1)
    #(sub_ty sigma r) #q #ei #os (sub_tys sigma ts) () () () h1

let sub_handler (sigma: tsub) (hd: handler) : handler =
  { h_ent = sub_ent sigma hd.h_ent; h_ret_ty = sub_ty sigma hd.h_ret_ty;
    h_ret = sub_ty_exp sigma hd.h_ret; h_clauses = sub_ty_cls sigma hd.h_clauses }

let b_handle (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (e1: exp) (hd: handler) (lbl: option string) (q: qname) (ts: list typ)
  (ei: effect_info)
  (h1: typing sg ln g' (sub_jctx sigma []) (sub_ty_exp sigma e1) (sub_ty sigma hd.h_ret_ty)
         (sub_ty sigma (TRowExt hd.h_ent r)))
  (h2: typing sg ln (push_var g' (sub_ty sigma hd.h_ret_ty)) (sub_jctx sigma [])
         (sub_ty_exp sigma hd.h_ret) (sub_ty sigma t) (sub_ty sigma r))
  (hcl: clauses_typing sg ln g' ei (sub_tys sigma ts) (sub_ty sigma r) (sub_ty sigma t)
          (sub_ty_cls sigma hd.h_clauses))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EHandle e1 hd /\ hd.h_ent == EntEff lbl q ts /\
                   sg.effects q == Some ei /\
                   check sg g (TRowExt hd.h_ent r) (KRow EEffect) /\
                   check sg g hd.h_ret_ty KType /\
                   check sg g t KType /\ check sg g r (KRow EEffect) /\
                   clauses_cover ei hd.h_clauses)
         (ensures fun _ -> True) =
  sub_handle_eq sigma e1 hd;
  sub_ext_eq sigma hd.h_ent r;
  let hd' = sub_handler sigma hd in
  check_sub sg sigma g g' (TRowExt hd.h_ent r) (KRow EEffect);
  check_sub sg sigma g g' hd.h_ret_ty KType;
  check_sub sg sigma g g' t KType;
  check_sub sg sigma g g' r (KRow EEffect);
  clause_ops_sub sigma hd.h_clauses;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1) hd'.h_ret_ty
             (TRowExt hd'.h_ent (sub_ty sigma r)) = h1 in
  let h2 : typing sg ln (push_var g' hd'.h_ret_ty) [] hd'.h_ret (sub_ty sigma t)
             (sub_ty sigma r) = h2 in
  let hcl : clauses_typing sg ln g' ei (sub_tys sigma ts) (sub_ty sigma r) (sub_ty sigma t)
              hd'.h_clauses = hcl in
  T_Handle #sg #ln #g' #(sub_jctx sigma d) #(sub_ty_exp sigma e1) #hd' #(sub_ty sigma t)
    #(sub_ty sigma r) #lbl #q #(sub_tys sigma ts) #ei () () () () h1 h2 hcl

let b_openeff (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (r2: typ) (e1: exp) (t1 r1 t2: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1)
         (sub_ty sigma (t_fun t1 r1 t2)) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EOpenEff r2 e1 /\
                   t == t_fun t1 (TRowUnion r1 r2) t2 /\
                   entails (hyps g) (CDisj r1 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  sub_openeff_eq sigma r2 e1;
  sub_union_eq sigma r1 r2;
  entails_into sg sigma g g' (CDisj r1 r2);
  check_sub sg sigma g g' r2 (KRow EEffect);
  sub_t_fun sigma t1 r1 t2;
  sub_t_fun sigma t1 (TRowUnion r1 r2) t2;
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1)
             (t_fun (sub_ty sigma t1) (sub_ty sigma r1) (sub_ty sigma t2)) (sub_ty sigma r) = h1 in
  T_OpenEff #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma r2) h1 ()

let b_region (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (lay: layout) (es: list exp) (body: exp)
  (hes: exps_typing sg ln g' [] (sub_ty sigma r) (sub_ty_exps sigma es)
          (sub_tys sigma (L.map snd lay)))
  (hb: (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp (sub_ty_exp sigma body)))} ->
        typing sg ln (enter_region g' a (sub_layout sigma lay)) (sub_jctx sigma [])
          (sub_ty_exp sigma (open_region a body)) (sub_ty sigma t)
          (sub_ty sigma (TRowExt (EntRegion (RFree a)) r))))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ERegion lay es body /\
                   check sg g (layout_row lay) (KRow EType) /\ L.noRepeats (L.map fst lay) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  sub_region_eq sigma lay es body;
  let lay' = sub_layout sigma lay in
  let body' = sub_ty_exp sigma body in
  sub_layout_row sigma lay;
  sub_layout_keys sigma lay;
  sub_layout_snd sigma lay;
  check_sub sg sigma g g' (layout_row lay) (KRow EType);
  check_sub sg sigma g g' t KType;
  check_sub sg sigma g g' r (KRow EEffect);
  let hes : exps_typing sg ln g' [] (sub_ty sigma r) (sub_ty_exps sigma es)
              (L.map snd lay') = hes in
  let hb' (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp body'))})
    : typing sg ln (enter_region g' a lay') [] (open_region a body') (sub_ty sigma t)
        (TRowExt (EntRegion (RFree a)) (sub_ty sigma r)) =
    open_region_sub_ty_exp 0 a sigma body;
    hb a
  in
  T_Region #sg #ln #g' #(sub_jctx sigma d) #lay' #(sub_ty_exps sigma es) #body'
    #(sub_ty sigma t) #(sub_ty sigma r) () () hes hb'

let b_readcell (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (a: atom) (k: key) (lay: layout)
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EReadCell (RFree a) k /\
                   L.assoc a g.regions == Some lay /\
                   L.assoc k lay == Some t /\ L.mem (RegionKey (RFree a)) (known_keys r) /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  sub_layout_assoc sigma lay k;
  known_keys_sub sigma (RegionKey (RFree a)) r;
  check_sub sg sigma g g' r (KRow EEffect);
  T_ReadCell #sg #ln #g' #(sub_jctx sigma d) #a #k #(sub_layout sigma lay) #(sub_ty sigma t)
    #(sub_ty sigma r) () () ()

let b_writecell (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (a: atom) (k: key) (e1: exp) (lay: layout) (t1: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1) (sub_ty sigma t1)
         (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EWriteCell (RFree a) k e1 /\ t == t_unit /\
                   L.assoc a g.regions == Some lay /\ L.assoc k lay == Some t1 /\
                   L.mem (RegionKey (RFree a)) (known_keys r))
         (ensures fun _ -> True) =
  sub_writecell_eq sigma (RFree a) k e1;
  assert (L.assoc a g.regions == L.assoc a g.regions);
  sub_layout_assoc sigma lay k;
  known_keys_sub sigma (RegionKey (RFree a)) r;
  T_WriteCell #sg #ln #g' #(sub_jctx sigma d) #a #k #(sub_ty_exp sigma e1)
    #(sub_layout sigma lay) #(sub_ty sigma t1) #(sub_ty sigma r) () () h1

let b_match (#sg: sig) (#ln: lctx) (sigma: tsub) (g': ctx) (d: jctx) (e: exp) (t r: typ)
  (th: list exp) (dt: dtree) (ts: list typ) (om: octx)
  (hes: exps_typing sg ln g' [] (sub_ty sigma r) (sub_ty_exps sigma th)
          (sub_tys sigma ts))
  (hm: match_typing sg ln g' [] (sub_ty sigma r) (sub_ty_exps sigma th)
         (sub_octx sigma om))
  (hdt: dt_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma om) (sub_ty_dt sigma dt)
          (sub_ty sigma t) (sub_ty sigma r))
  : Pure (tr sg ln g' sigma d e t r)
         (requires e == EMatch th dt /\ L.for_all (V.is_value sg) th)
         (ensures fun _ -> True) =
  values_sub_ty sg sigma th;
  T_Match (sub_octx sigma om) hes () hm hdt

let b_openeffc (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (r2: typ) (e1: exp) (r0: typ)
  (h1: typing sg ln g' [] (sub_ty_exp sigma e1) (sub_ty sigma t)
         (sub_ty sigma r0))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EOpenEffC r2 e1 /\ r == TRowUnion r0 r2 /\
                   entails (hyps g) (CDisj r0 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  sub_openeffc_eq sigma r2 e1;
  sub_union_eq sigma r0 r2;
  entails_into sg sigma g g' (CDisj r0 r2);
  check_sub sg sigma g g' r2 (KRow EEffect);
  T_OpenEffC #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma r2) h1 ()

let b_force (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (nu: atom)
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EForce nu /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  closed_sub sg sigma g g' t KType;
  check_sub sg sigma g g' r (KRow EEffect);
  T_Force #sg #ln #g' #(sub_jctx sigma d) #nu #t #(sub_ty sigma r) () ()

let b_fill (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (nu: atom) (e1: exp)
  (h1: typing sg ln g' (sub_jctx sigma []) (sub_ty_exp sigma e1) (sub_ty sigma t)
         (sub_ty sigma TRowEmpty))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EFill nu e1 /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  closed_sub sg sigma g g' t KType;
  check_sub sg sigma g g' r (KRow EEffect);
  let h1 : typing sg ln g' [] (sub_ty_exp sigma e1) t TRowEmpty = h1 in
  T_Fill #sg #ln #g' #(sub_jctx sigma d) #nu #(sub_ty_exp sigma e1) #t #(sub_ty sigma r) () () h1

let b_region_open (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (a: atom) (cells: list (key & exp)) (body: exp) (lay: layout)
  (hc: cells_typing sg ln g' (sub_ty_cells sigma cells) (sub_layout sigma lay))
  (hb: typing sg ln g' (sub_jctx sigma []) (sub_ty_exp sigma body) (sub_ty sigma t)
         (sub_ty sigma (TRowExt (EntRegion (RFree a)) r)))
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == ERegionOpen a cells body /\
                   L.assoc a g.regions == Some lay /\
                   check sg (closed_ctx g.regions) t KType /\
                   check sg (closed_ctx g.regions) r (KRow EEffect) /\
                   ~(L.mem a (frn_ty t @ frn_ty r)))
         (ensures fun _ -> True) =
  assert (L.assoc a g.regions == L.assoc a g.regions);
  closed_sub sg sigma g g' t KType;
  sub_region_open_eq sigma a cells body;
  sub_ext_eq sigma (EntRegion (RFree a)) r;
  closed_sub sg sigma g g' r (KRow EEffect);
  let hb : typing sg ln g' [] (sub_ty_exp sigma body) t (TRowExt (EntRegion (RFree a)) r) = hb in
  T_RegionOpen #sg #ln #g' #(sub_jctx sigma d) #a #(sub_ty_cells sigma cells)
    #(sub_ty_exp sigma body) #(sub_layout sigma lay) #t #r () () () hc hb

let b_opaque (#sg: sig) (#ln: lctx) (sigma: tsub) (g g': ctx) (d: jctx) (e: exp)
  (t r: typ) (w: nat)
  : Pure (tr sg ln g' sigma d e t r)
         (requires ty_sub_ok sg sigma g g' /\ e == EOpaque w t /\ opaque_type sg t /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  ty_head_sub sigma t;
  check_sub sg sigma g g' t KType;
  check_sub sg sigma g g' r (KRow EEffect);
  T_Opaque #sg #ln #g' #(sub_jctx sigma d) #w #(sub_ty sigma t) #(sub_ty sigma r) () ()

(* The mutual induction. *)

let pre (sg: sig) (sigma: tsub) (g g': ctx) : prop =
  sig_ok sg /\ tvars_wf g' /\ ty_sub_ok sg sigma g g'

let rec typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (sigma: tsub) (g': ctx)
  : Pure (typing sg ln g' (sub_jctx sigma d) (sub_ty_exp sigma e) (sub_ty sigma t)
            (sub_ty sigma r))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | T_Var #_ #_ #_ #_ #i _ _ -> b_var sigma g g' d e t r i
  | T_Global #_ #_ #_ #_ #q #ks #nk #t0 _ _ _ -> b_global sigma g g' d e t r q ks nk t0
  | T_Lit #_ #_ #_ #_ #c _ -> b_lit sigma g g' d e t r c
  | T_Lam #_ #_ #_ #_ #t1 #r1 #body #t2 _ _ hb ->
    ty_sub_ok_push_var sg sigma g g' t1;
    b_lam sigma g g' d e t r t1 r1 body t2
      (typing_sub_ty' hb sigma (push_var g' (sub_ty sigma t1)))
  | T_App #_ #_ #_ #_ #e1 #e2 #t1 #t2 h1 h2 ->
    b_app sigma g' d e t r e1 e2 t1 t2 (typing_sub_ty' h1 sigma g') (typing_sub_ty' h2 sigma g')
  | T_Chain #_ #_ #_ #_ #_ #t0 #th hc _ ->
    b_chain sigma g' d e t r t0 th (chain_typing_sub_ty' hc sigma g')
  | T_TyLam #_ #_ #_ #_ #k #body #t0 _ _ _ hb ->
    ty_sub_ok_up sg sigma g g' k;
    tvars_wf_push_tvar g' k;
    b_tylam sigma g g' d e t r k body t0
      (typing_sub_ty' hb (up_tsub sigma) (push_tvar g' k))
  | T_TyApp #_ #_ #_ #_ #e1 #s #k #t0 h1 _ ->
    b_tyapp sigma g g' d e t r e1 s k t0 (typing_sub_ty' h1 sigma g')
  | T_CLam #_ #_ #_ #_ #c #body #t0 _ _ _ hb ->
    ty_sub_ok_assump sg sigma g g' c;
    b_clam sigma g g' d e t r c body t0
      (typing_sub_ty' hb sigma (add_assump g' (sub_constr sigma c)))
  | T_CApp #_ #_ #_ #_ #e1 #c h1 _ ->
    b_capp sigma g g' d e t r e1 c (typing_sub_ty' h1 sigma g')
  | T_Let #_ #_ #_ #_ #t1 #e1 #e2 _ h1 h2 ->
    ty_sub_ok_push_var sg sigma g g' t1;
    b_let sigma g g' d e t r t1 e1 e2 (typing_sub_ty' h1 sigma g')
      (typing_sub_ty' h2 sigma (push_var g' (sub_ty sigma t1)))
  | T_LetRec #_ #_ #_ #_ #bs #body _ hbs hb ->
    ty_sub_ok_push_vars sg sigma g g' (L.map fst bs);
    let gb' = push_vars g' (sub_tys sigma (L.map fst bs)) in
    same_kinding_push_vars g' (sub_tys sigma (L.map fst bs));
    b_letrec sigma g' d e t r bs body (binds_typing_sub_ty' hbs sigma gb')
      (typing_sub_ty' hb sigma gb')
  | T_Conv #_ #_ #_ #_ #_ #t1 #r1 h1 _ _ ->
    b_conv sigma g g' d e t r t1 r1 (typing_sub_ty' h1 sigma g')
  | T_Case #_ #_ #_ #_ #es #dt #ts hes hdt ->
    b_case sigma g' d e t r es dt ts (exps_typing_sub_ty' hes sigma g')
      (dt_typing_sub_ty' hdt sigma g')
  | T_LetJoin #_ #_ #_ #_ #ts #_ #e1 #e2 _ h1 h2 ->
    ty_sub_ok_push_vars sg sigma g g' ts;
    same_kinding_push_vars g' (sub_tys sigma ts);
    b_letjoin sigma g g' d e t r ts e1 e2
      (typing_sub_ty' h1 sigma (push_vars g' (sub_tys sigma ts)))
      (typing_sub_ty' h2 sigma g')
  | T_Jump #_ #_ #_ #_ #j #es #ts _ _ hes ->
    b_jump sigma g g' d e t r j es ts (exps_typing_sub_ty' hes sigma g')
  | T_RecEmpty _ -> b_recempty sigma g g' d e t r
  | T_Extend #_ #_ #_ #_ #k #e1 #e2 #t1 #r0 h1 h2 _ ->
    b_extend sigma g g' d e t r k e1 e2 t1 r0 (typing_sub_ty' h1 sigma g')
      (typing_sub_ty' h2 sigma g')
  | T_Select #_ #_ #_ #_ #k #e1 #_ #r0 h1 _ ->
    b_select sigma g g' d e t r k e1 r0 (typing_sub_ty' h1 sigma g')
  | T_Restrict #_ #_ #_ #_ #k #e1 #t1 #r0 h1 _ ->
    b_restrict sigma g g' d e t r k e1 t1 r0 (typing_sub_ty' h1 sigma g')
  | T_Update #_ #_ #_ #_ #k #e1 #e2 #t1 #t2 #r0 h1 h2 _ ->
    b_update sigma g g' d e t r k e1 e2 t1 t2 r0 (typing_sub_ty' h1 sigma g')
      (typing_sub_ty' h2 sigma g')
  | T_Merge #_ #_ #_ #_ #e1 #e2 #r1 #r2 h1 h2 _ ->
    b_merge sigma g g' d e t r e1 e2 r1 r2 (typing_sub_ty' h1 sigma g')
      (typing_sub_ty' h2 sigma g')
  | T_Inject #_ #_ #_ #_ #k #r0 #e1 #t1 h1 _ _ ->
    b_inject sigma g g' d e t r k r0 e1 t1 (typing_sub_ty' h1 sigma g')
  | T_Weaken #_ #_ #_ #_ #k #t1 #e1 #r0 h1 _ _ ->
    b_weaken sigma g g' d e t r k t1 e1 r0 (typing_sub_ty' h1 sigma g')
  | T_VariantValue #_ #_ #_ #_ #_ #k #v #pt vr0 vr h1 _ h2 _ ->
    b_variant_value sigma g g' d e t r k v pt vr0 vr (typing_sub_ty' h1 sigma g')
      (typing_sub_ty' h2 sigma g')
  | T_Absurd #_ #_ #_ #_ #_ #e1 h1 _ ->
    b_absurd sigma g g' d e t r e1 (typing_sub_ty' h1 sigma g')
  | T_Perform #_ #_ #_ #_ #k #op #ss #e1 #_ #q #ei #os ts _ _ _ h1 ->
    b_perform sigma g g' d e t r k op ss e1 q ei os ts (typing_sub_ty' h1 sigma g')
  | T_Handle #_ #_ #_ #_ #e1 #hd #_ #_ #lbl #q #ts #ei _ _ _ _ h1 h2 hcl ->
    eff_params_length sg g lbl q ts r ei;
    ty_sub_ok_push_var sg sigma g g' hd.h_ret_ty;
    same_kinding_push_var g' (sub_ty sigma hd.h_ret_ty);
    b_handle sigma g g' d e t r e1 hd lbl q ts ei (typing_sub_ty' h1 sigma g')
      (typing_sub_ty' h2 sigma (push_var g' (sub_ty sigma hd.h_ret_ty)))
      (clauses_typing_sub_ty' hcl q sigma g')
  | T_OpenEff #_ #_ #_ #_ #r2 #e1 #t1 #r1 #t2 h1 _ ->
    b_openeff sigma g g' d e t r r2 e1 t1 r1 t2 (typing_sub_ty' h1 sigma g')
  | T_Region #_ #_ #_ #_ #lay #es #body _ _ hes hbody ->
    let lay' = sub_layout sigma lay in
    let hb' (a: atom{~(L.mem a (rdom g')) /\ ~(L.mem a (frn_exp (sub_ty_exp sigma body)))})
      : typing sg ln (enter_region g' a lay') (sub_jctx sigma [])
          (sub_ty_exp sigma (open_region a body)) (sub_ty sigma t)
          (sub_ty sigma (TRowExt (EntRegion (RFree a)) r)) =
      ty_sub_ok_fresh sg sigma g g' a body;
      ty_sub_ok_enter_region sg sigma g g' a lay;
      typing_sub_ty' (hbody a) sigma (enter_region g' a lay')
    in
    b_region sigma g g' d e t r lay es body (exps_typing_sub_ty' hes sigma g') hb'
  | T_ReadCell #_ #_ #_ #_ #a #k #lay _ _ _ -> b_readcell sigma g g' d e t r a k lay
  | T_WriteCell #_ #_ #_ #_ #a #k #e1 #lay #t1 _ _ h1 ->
    b_writecell sigma g g' d e t r a k e1 lay t1 (typing_sub_ty' h1 sigma g')
  | T_Match #_ #_ #_ #_ #th #dt #ts om hes _ hm hdt ->
    b_match sigma g' d e t r th dt ts om (exps_typing_sub_ty' hes sigma g')
      (match_typing_sub_ty' hm sigma g') (dt_typing_sub_ty' hdt sigma g')
  | T_OpenEffC #_ #_ #_ #_ #r2 #e1 #_ #r0 h1 _ ->
    b_openeffc sigma g g' d e t r r2 e1 r0 (typing_sub_ty' h1 sigma g')
  | T_Force #_ #_ #_ #_ #nu _ _ -> b_force sigma g g' d e t r nu
  | T_Fill #_ #_ #_ #_ #nu #e1 _ _ h1 ->
    b_fill sigma g g' d e t r nu e1 (typing_sub_ty' h1 sigma g')
  | T_RegionOpen #_ #_ #_ #_ #a #cells #body #lay _ _ _ hc hb ->
    b_region_open sigma g g' d e t r a cells body lay (cells_typing_sub_ty' hc sigma g')
      (typing_sub_ty' hb sigma g')
  | T_Opaque #_ #_ #_ #_ #w _ _ -> b_opaque sigma g g' d e t r w

and exps_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (sigma: tsub) (g': ctx)
  : Pure (exps_typing sg ln g' (sub_jctx sigma d) (sub_ty sigma r) (sub_ty_exps sigma es)
            (sub_tys sigma ts))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TE_Nil _ -> check_sub sg sigma g g' r (KRow EEffect); TE_Nil ()
  | TE_Cons h1 h2 -> TE_Cons (typing_sub_ty' h1 sigma g') (exps_typing_sub_ty' h2 sigma g')

and chain_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (sigma: tsub) (g': ctx)
  : Pure (chain_typing sg ln g' (sub_jctx sigma d) (sub_ty sigma r) (sub_ty_exp sigma e))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TS_Head #_ #_ #_ #_ #_ #q #ks #c #nk #t0 _ _ _ ->
    check_sub sg sigma g g' r (KRow EEffect);
    TS_Head #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma r) #q #ks #c #nk #t0 () () ()
  | TS_Ty #_ #_ #_ #_ #_ #e0 #s #k #t0 #th h0 _ _ ->
    chain_cursor_sub_ty sg sigma e0 (TForall k t0) th;
    sub_tyapp_eq sigma e0 s;
    let Some (_, th') = chain_cursor sg (sub_ty_exp sigma e0) in
    check_sub sg sigma g g' s k;
    TS_Ty #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma r) #(sub_ty_exp sigma e0) #(sub_ty sigma s)
      #k #t0 #th' (chain_typing_sub_ty' h0 sigma g') () ()
  | TS_Constr #_ #_ #_ #_ #_ #e0 #c #t0 #th h0 _ _ ->
    chain_cursor_sub_ty sg sigma e0 (TConstr c t0) th;
    sub_capp_eq sigma e0;
    let Some (_, th') = chain_cursor sg (sub_ty_exp sigma e0) in
    entails_into sg sigma g g' (sub_constr th c);
    TS_Constr #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma r) #(sub_ty_exp sigma e0) #c #t0 #th'
      (chain_typing_sub_ty' h0 sigma g') () ()
  | TS_Val #_ #_ #_ #_ #_ #e0 #v #t0 #th #t1 #r1 #t2 h0 _ hv ->
    chain_cursor_sub_ty sg sigma e0 t0 th;
    sub_app_eq sigma e0 v;
    let Some (_, th') = chain_cursor sg (sub_ty_exp sigma e0) in
    let hv' = cast (typing_sub_ty' hv sigma g') (sub_jctx sigma d) (sub_ty_exp sigma v)
      (sub_ty th' t1) (sub_ty sigma r) in
    TS_Val #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma r) #(sub_ty_exp sigma e0)
      #(sub_ty_exp sigma v) #t0 #th' #t1 #r1 #t2 (chain_typing_sub_ty' h0 sigma g') () hv'

and binds_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (sigma: tsub) (g': ctx)
  : Pure (binds_typing sg ln g' (sub_ty_binds sigma bs))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TB_Nil -> TB_Nil
  | TB_Cons #_ #_ #_ #t0 #e0 #_ _ h1 h2 ->
    check_sub sg sigma g g' t0 KType;
    let h1' = cast (typing_sub_ty' h1 sigma g') [] (sub_ty_exp sigma e0) (sub_ty sigma t0)
      TRowEmpty in
    TB_Cons () h1' (binds_typing_sub_ty' h2 sigma g')

and cells_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp))
  (#lay: layout) (h: cells_typing sg ln g cells lay) (sigma: tsub) (g': ctx)
  : Pure (cells_typing sg ln g' (sub_ty_cells sigma cells) (sub_layout sigma lay))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TC_Nil -> TC_Nil
  | TC_Cons #_ #_ #_ #k #v #t0 #cs0 #lay0 _ h1 h2 ->
    is_value_sub_ty sg sigma v;
    let h1' = cast (typing_sub_ty' h1 sigma g') [] (sub_ty_exp sigma v) (sub_ty sigma t0)
      TRowEmpty in
    TC_Cons #sg #ln #g' #k #(sub_ty_exp sigma v) #(sub_ty sigma t0) #(sub_ty_cells sigma cs0)
      #(sub_layout sigma lay0) () h1' (cells_typing_sub_ty' h2 sigma g')

and match_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (h: match_typing sg ln g d r th om) (sigma: tsub) (g': ctx)
  : Pure (match_typing sg ln g' (sub_jctx sigma d) (sub_ty sigma r) (sub_ty_exps sigma th)
            (sub_octx sigma om))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TM_Nil _ -> check_sub sg sigma g g' r (KRow EEffect); TM_Nil ()
  | TM_Cons #_ #_ #_ #_ #_ #_ #o #t0 #_ #v _ h1 h2 ->
    proj_sub_ty sg sigma th o;
    TM_Cons #sg #ln #g' #(sub_jctx sigma d) #(sub_ty sigma r) #(sub_ty_exps sigma th) #o
      #(sub_ty sigma t0) #(sub_octx sigma _) #(sub_ty_exp sigma v) () (typing_sub_ty' h1 sigma g')
      (match_typing_sub_ty' h2 sigma g')

and dt_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (sigma: tsub) (g': ctx)
  : Pure (dt_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma om) (sub_ty_dt sigma dt)
            (sub_ty sigma t) (sub_ty sigma r))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TD_Leaf h1 -> TD_Leaf (typing_sub_ty' h1 sigma g')
  | TD_Bind #_ #_ #_ #_ #_ #o #dt0 #t_o #_ #_ ho hdt ->
    ty_sub_ok_push_var sg sigma g g' t_o;
    same_kinding_push_var g' (sub_ty sigma t_o);
    TD_Bind (occ_typing_sub_ty' ho sigma g')
      (dt_typing_sub_ty' hdt sigma (push_var g' (sub_ty sigma t_o)))
  | TD_SwitchCtor #_ #_ #_ #_ #_ #o #bs #t_o #_ #_ tq ks ss cs ho _ _ _ hbr ->
    sub_tapps sigma (TCon tq ks) ss;
    ty_eq_sub sigma t_o (tapps (TCon tq ks) ss);
    check_sub sg sigma g g' (tapps (TCon tq ks) ss) KType;
    sub_ty_brs_labels sigma bs;
    TD_SwitchCtor tq ks (sub_tys sigma ss) cs (occ_typing_sub_ty' ho sigma g') () () ()
      (ctor_brs_typing_sub_ty' hbr sigma g')
  | TD_SwitchCtorDef #_ #_ #_ #_ #_ #o #bs #df #t_o #_ #_ tq ks ss cs ho _ _ _ hbr hdf ->
    sub_tapps sigma (TCon tq ks) ss;
    ty_eq_sub sigma t_o (tapps (TCon tq ks) ss);
    check_sub sg sigma g g' (tapps (TCon tq ks) ss) KType;
    sub_ty_brs_labels sigma bs;
    TD_SwitchCtorDef tq ks (sub_tys sigma ss) cs (occ_typing_sub_ty' ho sigma g') () () ()
      (ctor_brs_typing_sub_ty' hbr sigma g') (dt_typing_sub_ty' hdf sigma g')
  | TD_SwitchLit #_ #_ #_ #_ #_ #o #bs #df #t_o #_ #_ lq ho _ _ hbr hdf ->
    ty_eq_sub sigma t_o (TCon lq []);
    sub_ty_brs_labels sigma bs;
    let hbr' = lit_brs_typing_sub_ty' hbr sigma g' in
    TD_SwitchLit lq (occ_typing_sub_ty' ho sigma g') () () hbr' (dt_typing_sub_ty' hdf sigma g')
  | TD_SwitchKey #_ #_ #_ #_ #_ #o #bs #t_o #_ #_ vr kts ho _ _ _ hbr ->
    sub_t_variant sigma vr;
    ty_eq_sub sigma t_o (t_variant vr);
    check_sub sg sigma g g' vr (KRow EType);
    sub_ty_brs_labels sigma bs;
    key_split_sub sigma vr kts TRowEmpty;
    TD_SwitchKey (sub_ty sigma vr) (sub_layout sigma kts) (occ_typing_sub_ty' ho sigma g') () () ()
      (key_brs_typing_sub_ty' hbr sigma g')
  | TD_SwitchKeyDef #_ #_ #_ #_ #_ #o #bs #df #t_o #_ #_ vr vr' kts ho _ _ _ hbr hdf ->
    sub_t_variant sigma vr;
    sub_t_variant sigma vr';
    ty_eq_sub sigma t_o (t_variant vr);
    check_sub sg sigma g g' vr (KRow EType);
    check_sub sg sigma g g' vr' (KRow EType);
    sub_ty_brs_labels sigma bs;
    key_split_sub sigma vr kts vr';
    let hdf' = cast_dt (dt_typing_sub_ty' hdf sigma g')
      ((o, t_variant (sub_ty sigma vr')) :: sub_octx sigma om) (sub_ty sigma t) (sub_ty sigma r) in
    TD_SwitchKeyDef (sub_ty sigma vr) (sub_ty sigma vr') (sub_layout sigma kts)
      (occ_typing_sub_ty' ho sigma g') () () () (key_brs_typing_sub_ty' hbr sigma g') hdf'
  | TD_Guard h1 h2 h3 ->
    TD_Guard (typing_sub_ty' h1 sigma g') (dt_typing_sub_ty' h2 sigma g')
      (dt_typing_sub_ty' h3 sigma g')

and ctor_brs_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#ks: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ) (h: ctor_brs_typing sg ln g d om o ks ss cs bs t r) (sigma: tsub) (g': ctx)
  : Pure (ctor_brs_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma om) o ks
            (sub_tys sigma ss) cs (sub_ty_brs sigma bs) (sub_ty sigma t) (sub_ty sigma r))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCB_Nil _ ->
    check_sub sg sigma g g' t KType; check_sub sg sigma g g' r (KRow EEffect);
    TCB_Nil ()
  | TCB_Cons #_ #_ #_ #_ #_ #_ #_ #_ #_ #c #dt0 #bs0 #_ #_ #fs _ hdt h2 ->
    ctor_fields_sub sg c ks ss fs sigma;
    field_occs_sub sigma o c 0 fs;
    sub_octx_append sigma (field_occs o c 0 fs) om;
    let hdt' = cast_dt (dt_typing_sub_ty' hdt sigma g')
                 (L.append (field_occs o c 0 (sub_tys sigma fs)) (sub_octx sigma om))
                 (sub_ty sigma t) (sub_ty sigma r) in
    TCB_Cons #sg #ln #g' #(sub_jctx sigma d) #(sub_octx sigma om) #o #ks #(sub_tys sigma ss) #cs
      #c #(sub_ty_dt sigma dt0) #(sub_ty_brs sigma bs0) #(sub_ty sigma t) #(sub_ty sigma r)
      #(sub_tys sigma fs) () hdt' (ctor_brs_typing_sub_ty' h2 sigma g')

and lit_brs_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (sigma: tsub) (g': ctx)
  : Pure (lit_brs_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma om) (sub_ty sigma lt)
            (sub_ty_brs sigma bs) (sub_ty sigma t) (sub_ty sigma r))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TLB_Nil _ ->
    check_sub sg sigma g g' t KType; check_sub sg sigma g g' r (KRow EEffect);
    TLB_Nil ()
  | TLB_Cons #_ #_ #_ #_ #_ #_ #c #_ #_ #_ #_ _ hdt h2 ->
    sub_lit_type sigma c;
    ty_eq_sub sigma (lit_type c) lt;
    TLB_Cons #sg #ln #g' #(sub_jctx sigma d) #(sub_octx sigma om) #(sub_ty sigma lt) #c ()
      (dt_typing_sub_ty' hdt sigma g') (lit_brs_typing_sub_ty' h2 sigma g')

and key_brs_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (sigma: tsub) (g': ctx)
  : Pure (key_brs_typing sg ln g' (sub_jctx sigma d) (sub_octx sigma om) o
            (sub_layout sigma kts) (sub_ty_brs sigma bs) (sub_ty sigma t) (sub_ty sigma r))
         (requires pre sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TKB_Nil _ ->
    check_sub sg sigma g g' t KType; check_sub sg sigma g g' r (KRow EEffect);
    TKB_Nil ()
  | TKB_Cons #_ #_ #_ #_ #_ #_ #k #pt #_ #_ #_ #_ #_ _ hdt h2 ->
    check_sub sg sigma g g' pt KType;
    TKB_Cons () (dt_typing_sub_ty' hdt sigma g') (key_brs_typing_sub_ty' h2 sigma g')

and clauses_typing_sub_ty' (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause) (h: clauses_typing sg ln g ei ts r b cs) (q: qname)
  (sigma: tsub) (g': ctx)
  : Pure (clauses_typing sg ln g' ei (sub_tys sigma ts) (sub_ty sigma r) (sub_ty sigma b)
            (sub_ty_cls sigma cs))
         (requires pre sg sigma g g' /\ sg.effects q == Some ei /\
                   L.length ts == L.length ei.eff_params)
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCL_Nil _ ->
    check_sub sg sigma g g' b KType; check_sub sg sigma g g' r (KRow EEffect);
    TCL_Nil ()
  | TCL_Full #_ #_ #_ #_ #_ #_ #_ #op #nb #s #kt #body #cs0 #os _ _ _ hb hcs ->
    let su = upn_tsub nb sigma in
    let gb = push_tvars g os.binders in
    let gb' = push_tvars g' os.binders in
    ty_sub_ok_upn sg sigma g g' os.binders;
    binders_closed sg q ei op os;
    tvars_wf_push_tvars g' os.binders;
    eff_inst_sub_sig sg q ei op os ts sigma;
    check_sub sg su gb gb' s KType;
    ty_eq_sub su s (eff_inst nb ts os.arg);
    check_sub sg su gb gb' kt KType;
    ty_eq_sub su kt (t_fun (eff_inst nb ts os.res) (ren_ty (shift nb) r) (ren_ty (shift nb) b));
    sub_t_fun su (eff_inst nb ts os.res) (ren_ty (shift nb) r) (ren_ty (shift nb) b);
    sub_shift_up nb sigma r;
    sub_shift_up nb sigma b;
    ty_sub_ok_push_var sg su gb gb' s;
    ty_sub_ok_push_var sg su (push_var gb s) (push_var gb' (sub_ty su s)) kt;
    same_kinding_push_var gb' (sub_ty su s);
    same_kinding_push_var (push_var gb' (sub_ty su s)) (sub_ty su kt);
    let hb' = cast (typing_sub_ty' hb su (push_var (push_var gb' (sub_ty su s)) (sub_ty su kt))) []
                (sub_ty_exp su body) (ren_ty (shift nb) (sub_ty sigma b))
                (ren_ty (shift nb) (sub_ty sigma r)) in
    TCL_Full #sg #ln #g' #ei #(sub_tys sigma ts) #(sub_ty sigma r) #(sub_ty sigma b) #op #nb
      #(sub_ty su s) #(sub_ty su kt) #(sub_ty_exp su body) #(sub_ty_cls sigma cs0) #os () () () hb'
      (clauses_typing_sub_ty' hcs q sigma g')
  | TCL_Fast #_ #_ #_ #_ #_ #_ #_ #op #nb #s #body #cs0 #os _ _ hb hcs ->
    let su = upn_tsub nb sigma in
    let gb = push_tvars g os.binders in
    let gb' = push_tvars g' os.binders in
    ty_sub_ok_upn sg sigma g g' os.binders;
    binders_closed sg q ei op os;
    tvars_wf_push_tvars g' os.binders;
    eff_inst_sub_sig sg q ei op os ts sigma;
    check_sub sg su gb gb' s KType;
    ty_eq_sub su s (eff_inst nb ts os.arg);
    sub_shift_up nb sigma r;
    ty_sub_ok_push_var sg su gb gb' s;
    same_kinding_push_var gb' (sub_ty su s);
    let hb' = cast (typing_sub_ty' hb su (push_var gb' (sub_ty su s))) [] (sub_ty_exp su body)
                (eff_inst nb (sub_tys sigma ts) os.res) (ren_ty (shift nb) (sub_ty sigma r)) in
    TCL_Fast #sg #ln #g' #ei #(sub_tys sigma ts) #(sub_ty sigma r) #(sub_ty sigma b) #op #nb
      #(sub_ty su s) #(sub_ty_exp su body) #(sub_ty_cls sigma cs0) #os () () hb'
      (clauses_typing_sub_ty' hcs q sigma g')

and occ_typing_sub_ty' (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t) (sigma: tsub) (g': ctx)
  : Pure (occ_typing sg g' (sub_octx sigma om) o (sub_ty sigma t))
         (requires ty_sub_ok sg sigma g g')
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TO_Lookup _ -> assoc_sub_octx sigma om o; TO_Lookup ()
  | TO_Field #_ #_ #_ #o0 #k #t_o #_ r0 ho _ _ ->
    sub_t_record sigma r0;
    ty_eq_sub sigma t_o (t_record r0);
    check_sub sg sigma g g' r0 (KRow EType);
    check_sub sg sigma g g' t KType;
    entries_sub_ty sigma r0 k t;
    TO_Field #sg #g' #(sub_octx sigma om) #o0 #k #(sub_ty sigma t_o) #(sub_ty sigma t)
      (sub_ty sigma r0) (occ_typing_sub_ty' ho sigma g') () ()

(* The stated theorems. *)

let occ_typing_sub_ty #sg #g #om #o #t h sigma g' = occ_typing_sub_ty' h sigma g'

let typing_sub_ty #sg #ln #g #d #e #t #r h sigma g' = typing_sub_ty' h sigma g'

let exps_typing_sub_ty #sg #ln #g #d #r #es #ts h sigma g' = exps_typing_sub_ty' h sigma g'

let chain_typing_sub_ty #sg #ln #g #d #r #e h sigma g' = chain_typing_sub_ty' h sigma g'

let binds_typing_sub_ty #sg #ln #g #bs h sigma g' = binds_typing_sub_ty' h sigma g'

let cells_typing_sub_ty #sg #ln #g #cells #lay h sigma g' = cells_typing_sub_ty' h sigma g'

let match_typing_sub_ty #sg #ln #g #d #r #th #om h sigma g' = match_typing_sub_ty' h sigma g'

let dt_typing_sub_ty #sg #ln #g #d #om #dt #t #r h sigma g' = dt_typing_sub_ty' h sigma g'

let ctor_brs_typing_sub_ty #sg #ln #g #d #om #o #ks #ss #cs #bs #t #r h sigma g' =
  ctor_brs_typing_sub_ty' h sigma g'

let lit_brs_typing_sub_ty #sg #ln #g #d #om #lt #bs #t #r h sigma g' =
  lit_brs_typing_sub_ty' h sigma g'

let key_brs_typing_sub_ty #sg #ln #g #d #om #o #kts #bs #t #r h sigma g' =
  key_brs_typing_sub_ty' h sigma g'

let clauses_typing_sub_ty #sg #ln #g #ei #ts #r #b #cs h q sigma g' =
  clauses_typing_sub_ty' h q sigma g'

(* Instantiating one type variable. *)

let typing_subst1 #sg #ln #g #k #d #e #t #r h s =
  ty_sub_ok_subst1 sg g k s;
  typing_sub_ty' h (scons s tvar) g

let typing_subst1_assump #sg #ln #g #k #c #d #e #t #r h s =
  ty_sub_ok_subst1 sg g k s;
  ty_sub_ok_assump sg (scons s tvar) (push_tvar g k) g c;
  typing_sub_ty' h (scons s tvar) (add_assump g (sub_constr (scons s tvar) c))
