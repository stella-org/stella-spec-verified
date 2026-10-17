(* Proof structure.

   Each preservation theorem is one mutual induction following the
   definitions of `synth_kind`, `check`, `entry_ok`, `check_tys` and
   `constr_ok`, with the same measures. The context changes at `TForall`
   and `TConstr`; there the condition is re-established by `*_ok_up` and
   `*_ok_assumps` (for kind instantiation, the instantiated context
   commutes with `push_tvar` and `add_assumps`, `Stella.Core.Context`).

   The sharpness premises of row extension and union go through
   preservation of entailment (`entails_ren`, `entails_sub`,
   `entails_kinst`), which gives entailment by the images of the
   hypotheses of `g`; each image is entailed by the hypotheses of `g'`, so
   cut of a list (`entails_cut_all`, through `entails_img`) concludes.

   Substitution is proved after renaming, since `sub_ok_up` kinds the
   shifted substitutes with `check_shift`. In the substitution theorem, a
   function position is checked at an arrow kind, which only a synthesized
   kind can be (`check_nonrow_kind`).

   Weakening, cut and the single-variable instantiation are instances:
   `ctx_ext g g'` is `ren_ok id_ren g g'`, and instantiating index 0 is
   `sub_ok (scons s tvar) (push_tvar g k) g`. *)
module Stella.Core.Kinding.Subst
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Rows
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Lemmas
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

(* Lists. *)

let rec mem_map (#a #b: eqtype) (f: a -> b) (l: list a) (x: a)
  : Lemma (requires L.mem x l) (ensures L.mem (f x) (L.map f l)) (decreases l) =
  match l with
  | y :: tl -> if x = y then () else mem_map f tl x

let rec map_wit (#a #b: eqtype) (f: a -> b) (l: list a) (y: b)
  : Pure a (requires L.mem y (L.map f l)) (ensures fun x -> L.mem x l /\ f x == y) (decreases l) =
  match l with
  | x :: tl -> if f x = y then x else map_wit f tl y

let rec nth_length (#a: Type) (l: list a) (i: nat)
  : Lemma (requires Some? (L.nth l i)) (ensures i < L.length l) (decreases l) =
  match l with
  | _ :: tl -> if i = 0 then () else nth_length tl (i - 1)

(* The images of the hypotheses of `g` are entailed by those of `g'`, so
   whatever their list entails is entailed by `g'`. *)

let entails_img (f: constr -> constr) (hs hyps': list constr) (c: constr)
  : Lemma (requires (forall (h: constr). L.mem h hs ==> entails hyps' (f h)) /\
                    entails (L.map f hs) c)
          (ensures entails hyps' c) =
  introduce forall (h': constr). L.mem h' (L.map f hs) ==> entails hyps' h'
  with introduce _ ==> _
  with (let _ = map_wit f hs h' in ());
  entails_cut_all (L.map f hs) hyps' c

let entails_ren_into (xi: ren) (g g': ctx) (c: constr)
  : Lemma (requires ren_ok xi g g' /\ entails (hyps g) c)
          (ensures entails (hyps g') (ren_constr xi c)) =
  entails_ren xi (hyps g) c;
  entails_img (ren_constr xi) (hyps g) (hyps g') (ren_constr xi c)

let entails_sub_into (sg: sig) (sigma: tsub) (g g': ctx) (c: constr)
  : Lemma (requires sub_ok sg sigma g g' /\ entails (hyps g) c)
          (ensures entails (hyps g') (sub_constr sigma c)) =
  entails_sub sigma (hyps g) c;
  entails_img (sub_constr sigma) (hyps g) (hyps g') (sub_constr sigma c)

(* Keys of entries hold no types and no kinds. *)

let ent_key_ren (xi: ren) (en: entry) : Lemma (ent_key (ren_ent xi en) == ent_key en) =
  match en with
  | EntTy _ _ | EntEff _ _ _ | EntRegion _ -> ()

let ent_key_sub (sigma: tsub) (en: entry) : Lemma (ent_key (sub_ent sigma en) == ent_key en) =
  match en with
  | EntTy _ _ | EntEff _ _ _ | EntRegion _ -> ()

let ent_key_kinst (ks: list kind) (en: entry) : Lemma (ent_key (kinst_ent ks en) == ent_key en) =
  match en with
  | EntTy _ _ | EntEff _ _ _ | EntRegion _ -> ()

(* The conditions. *)

let rec constrs_ok_mem sg g cs =
  match cs with
  | [] -> ()
  | _ :: tl -> constrs_ok_mem sg g tl

let key_ok_rdom sg g g' k e = ()

let rdom_incl_push_tvar g g' k k' = rdom_push_tvar g k; rdom_push_tvar g' k'

let rdom_incl_add_assumps g g' cs cs' = rdom_add_assumps g cs; rdom_add_assumps g' cs'

let hyps_incl_add_assumps (g: ctx) (cs: list constr)
  : Lemma (forall (h: constr). L.mem h (hyps g) ==> L.mem h (hyps (add_assumps g cs))) =
  FStar.Classical.forall_intro (mem_hyps_add_assumps g cs)

(* Renaming. *)

let ren_ok_up xi g g' k =
  hyps_push_tvar g k;
  hyps_push_tvar g' k;
  rdom_push_tvar g k;
  rdom_push_tvar g' k;
  introduce forall (h: constr).
    L.mem h (hyps (push_tvar g k)) ==> entails (hyps (push_tvar g' k)) (ren_constr (up_ren xi) h)
  with introduce _ ==> _
  with begin
    let h0 = map_wit (ren_constr (shift 1)) (hyps g) h in
    entails_ren (shift 1) (hyps g') (ren_constr xi h0);
    ren_ren_constr (up_ren xi) (shift 1) (ren_shift 1 xi) h0;
    ren_ren_constr (shift 1) xi (ren_shift 1 xi) h0
  end;
  introduce forall (i: nat).
    i < L.length (push_tvar g k).tvars ==>
    L.nth (push_tvar g' k).tvars (up_ren xi i) == L.nth (push_tvar g k).tvars i
  with introduce _ ==> _
  with (if i = 0 then ()
        (* mentions `L.nth g.tvars (i - 1)`, the trigger of the hypothesis *)
        else assert (L.nth g.tvars (i - 1) == L.nth g.tvars (i - 1)))

let ren_ok_assumps xi g g' cs =
  let cs' = L.map (ren_constr xi) cs in
  let g1 = add_assumps g cs in
  let g1' = add_assumps g' cs' in
  hyps_incl_add_assumps g' cs';
  rdom_add_assumps g cs;
  rdom_add_assumps g' cs';
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g1') (ren_constr xi h)
  with introduce _ ==> _
  with begin
    mem_hyps_add_assumps g cs h;
    if L.mem h cs then begin
      mem_map (ren_constr xi) cs h;
      mem_hyps_add_assumps g' cs' (ren_constr xi h);
      entails_hyp (hyps g1') (ren_constr xi h)
    end
    else entails_weaken (hyps g') (hyps g1') (ren_constr xi h)
  end

let rec synth_kind_ren (sg: sig) (xi: ren) (g g': ctx) (t: typ)
  : Lemma (requires ren_ok xi g g' /\ Some? (synth_kind sg g t))
          (ensures synth_kind sg g' (ren_ty xi t) == synth_kind sg g t)
          (decreases %[t; 0]) =
  match t with
  | TVar i -> nth_length g.tvars i
  | TCon _ _ -> ()
  | TApp t1 t2 ->
    synth_kind_ren sg xi g g' t1;
    (match synth_kind sg g t1 with
     | Some (KArrow k1 _) -> check_ren sg xi g g' t2 k1
     | _ -> ())
  | TForall k t1 ->
    ren_ok_up xi g g' k;
    check_ren sg (up_ren xi) (push_tvar g k) (push_tvar g' k) t1 KType
  | TConstr c t1 ->
    let c' = ren_constr xi c in
    constr_ok_ren sg xi g g' c;
    ren_ok_assumps xi g g' [c];
    add_assump_assumps g c;
    add_assump_assumps g' c';
    check_ren sg xi (add_assump g c) (add_assump g' c') t1 KType

and check_ren (sg: sig) (xi: ren) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires ren_ok xi g g' /\ check sg g t k) (ensures check sg g' (ren_ty xi t) k)
          (decreases %[t; 1]) =
  match t with
  | TRowEmpty -> ()
  | TRowExt en r ->
    let KRow e = k in
    entry_ok_ren sg xi g g' en e;
    check_ren sg xi g g' r k;
    ent_key_ren xi en;
    entails_ren_into xi g g' (CLacks (ent_key en) r)
  | TRowUnion r1 r2 ->
    check_ren sg xi g g' r1 k;
    check_ren sg xi g g' r2 k;
    entails_ren_into xi g g' (CDisj r1 r2)
  | _ -> synth_kind_ren sg xi g g' t

and entry_ok_ren (sg: sig) (xi: ren) (g g': ctx) (en: entry) (e: elt_kind)
  : Lemma (requires ren_ok xi g g' /\ entry_ok sg g en e)
          (ensures entry_ok sg g' (ren_ent xi en) e)
          (decreases en) =
  match en with
  | EntTy _ t -> check_ren sg xi g g' t KType
  | EntEff _ q ts ->
    (match sg.effects q with
     | Some ei -> check_tys_ren sg xi g g' ts ei.eff_params
     | None -> ())
  | EntRegion _ -> ()

and check_tys_ren (sg: sig) (xi: ren) (g g': ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires ren_ok xi g g' /\ check_tys sg g ts ks)
          (ensures check_tys sg g' (ren_tys xi ts) ks)
          (decreases ts) =
  match ts, ks with
  | [], [] -> ()
  | t :: ts', k :: ks' -> check_ren sg xi g g' t k; check_tys_ren sg xi g g' ts' ks'

and constr_ok_ren (sg: sig) (xi: ren) (g g': ctx) (c: constr)
  : Lemma (requires ren_ok xi g g' /\ constr_ok sg g c) (ensures constr_ok sg g' (ren_constr xi c))
          (decreases c) =
  match c with
  | CLacks k r ->
    if check sg g r (KRow EType) && key_ok sg g k EType then begin
      check_ren sg xi g g' r (KRow EType);
      key_ok_rdom sg g g' k EType
    end else begin
      check_ren sg xi g g' r (KRow EEffect);
      key_ok_rdom sg g g' k EEffect
    end
  | CDisj r1 r2 ->
    if check sg g r1 (KRow EType) && check sg g r2 (KRow EType) then begin
      check_ren sg xi g g' r1 (KRow EType);
      check_ren sg xi g g' r2 (KRow EType)
    end else begin
      check_ren sg xi g g' r1 (KRow EEffect);
      check_ren sg xi g g' r2 (KRow EEffect)
    end

let rec constrs_ok_ren (sg: sig) (xi: ren) (g g': ctx) (cs: list constr)
  : Lemma (requires ren_ok xi g g' /\ constrs_ok sg g cs)
          (ensures constrs_ok sg g' (L.map (ren_constr xi) cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | c :: tl -> constr_ok_ren sg xi g g' c; constrs_ok_ren sg xi g g' tl

(* Weakening. *)

let ren_ok_shift g k =
  hyps_push_tvar g k;
  rdom_push_tvar g k;
  introduce forall (h: constr).
    L.mem h (hyps g) ==> entails (hyps (push_tvar g k)) (ren_constr (shift 1) h)
  with introduce _ ==> _
  with begin
    mem_map (ren_constr (shift 1)) (hyps g) h;
    entails_hyp (hyps (push_tvar g k)) (ren_constr (shift 1) h)
  end

let check_shift sg g k' t k = ren_ok_shift g k'; check_ren sg (shift 1) g (push_tvar g k') t k

let constr_ok_shift sg g k' c =
  ren_ok_shift g k'; constr_ok_ren sg (shift 1) g (push_tvar g k') c

let ren_ok_ext g g' =
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps g') (ren_constr id_ren h)
  with introduce _ ==> _
  with ren_id_constr id_ren h

let ctx_ext_add_assumps g cs =
  let g1 = add_assumps g cs in
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps g1) h
  with introduce _ ==> _
  with (mem_hyps_add_assumps g cs h; entails_hyp (hyps g1) h)

let ctx_ext_add_assump g c = add_assump_assumps g c; ctx_ext_add_assumps g [c]

let ctx_ext_enter_region g a l =
  let g1 = enter_region g a l in
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps g1) h
  with introduce _ ==> _
  with begin
    LP.append_mem g.facts g.assumps h;
    LP.append_mem (region_facts a 0 g.tvars) g.facts h;
    LP.append_mem g1.facts g1.assumps h;
    entails_hyp (hyps g1) h
  end

let ctx_ext_push_var g t =
  introduce forall (h: constr). L.mem h (hyps g) ==> entails (hyps (push_var g t)) h
  with introduce _ ==> _
  with entails_hyp (hyps g) h

let check_weaken sg g g' t k = ren_ok_ext g g'; check_ren sg id_ren g g' t k; ren_ty_id t

let entry_ok_weaken sg g g' en e =
  ren_ok_ext g g'; entry_ok_ren sg id_ren g g' en e; ren_id_ent id_ren en

let constr_ok_weaken sg g g' c =
  ren_ok_ext g g'; constr_ok_ren sg id_ren g g' c; ren_id_constr id_ren c

let rec constrs_ok_weaken sg g g' cs =
  match cs with
  | [] -> ()
  | c :: tl -> constr_ok_weaken sg g g' c; constrs_ok_weaken sg g g' tl

let check_decl sg g t k =
  assert (ren_ok id_ren (decl_ctx g.nk) g);
  check_ren sg id_ren (decl_ctx g.nk) g t k;
  ren_ty_id t

let check_cut sg g cs t k =
  let g1 = add_assumps g cs in
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g) h
  with introduce _ ==> _
  with begin
    mem_hyps_add_assumps g cs h;
    if L.mem h (hyps g) then entails_hyp (hyps g) h
  end;
  check_weaken sg g1 g t k

(* Well-formed parts of a context. *)

let tvars_wf_push_tvar g k = ()

let wf_hyps_push_tvar sg g k =
  ren_ok_shift g k;
  constrs_ok_ren sg (shift 1) g (push_tvar g k) (hyps g);
  hyps_push_tvar g k

let wf_hyps_add_assumps sg g cs =
  let g1 = add_assumps g cs in
  ctx_ext_add_assumps g cs;
  constrs_ok_mem sg g (hyps g);
  constrs_ok_mem sg g cs;
  constrs_ok_mem sg g1 (hyps g1);
  introduce forall (c: constr). L.mem c (hyps g1) ==> constr_ok sg g1 c
  with introduce _ ==> _
  with (mem_hyps_add_assumps g cs c; constr_ok_weaken sg g g1 c)

let wf_hyps_add_assump sg g c = add_assump_assumps g c; wf_hyps_add_assumps sg g [c]

(* The position in `ks` of the variable a region fact is about. *)
let rec region_facts_wit (a: atom) (d: nat) (ks: list kind) (c: constr)
  : Pure nat (requires L.mem c (region_facts a d ks))
             (ensures fun j -> L.nth ks j == Some (KRow EEffect) /\
                            c == CLacks (RegionKey (RFree a)) (TVar (d + j)))
             (decreases ks) =
  match ks with
  | k :: ks' ->
    if k = KRow EEffect && c = CLacks (RegionKey (RFree a)) (TVar d) then 0
    else 1 + region_facts_wit a (d + 1) ks' c

let wf_hyps_enter_region sg g a l =
  let g1 = enter_region g a l in
  ctx_ext_enter_region g a l;
  constrs_ok_mem sg g (hyps g);
  constrs_ok_mem sg g1 (hyps g1);
  introduce forall (c: constr). L.mem c (hyps g1) ==> constr_ok sg g1 c
  with introduce _ ==> _
  with begin
    LP.append_mem g1.facts g1.assumps c;
    LP.append_mem (region_facts a 0 g.tvars) g.facts c;
    LP.append_mem g.facts g.assumps c;
    if L.mem c (region_facts a 0 g.tvars) then begin
      let _ = region_facts_wit a 0 g.tvars c in
      rdom_enter_region g a l
    end
    else constr_ok_weaken sg g g1 c
  end

(* Substitution. *)

(* A type checked at a kind that is not a row kind synthesizes it. *)
let check_nonrow_kind (sg: sig) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg g t k /\ not (KRow? k)) (ensures synth_kind sg g t == Some k) =
  match t with
  | TRowEmpty | TRowExt _ _ | TRowUnion _ _ -> ()
  | _ -> ()

let sub_ok_up sg sigma g g' k =
  hyps_push_tvar g k;
  hyps_push_tvar g' k;
  rdom_push_tvar g k;
  rdom_push_tvar g' k;
  let th = tsub_shift 1 sigma in
  introduce forall (h: constr).
    L.mem h (hyps (push_tvar g k)) ==>
    entails (hyps (push_tvar g' k)) (sub_constr (up_tsub sigma) h)
  with introduce _ ==> _
  with begin
    let h0 = map_wit (ren_constr (shift 1)) (hyps g) h in
    entails_ren (shift 1) (hyps g') (sub_constr sigma h0);
    sub_ren_constr (up_tsub sigma) (shift 1) th h0;
    ren_sub_constr (shift 1) sigma th h0
  end;
  introduce forall (i: nat).
    (match L.nth (push_tvar g k).tvars i with
     | Some ki -> check sg (push_tvar g' k) (up_tsub sigma i) ki
     | None -> True)
  with begin
    if i = 0 then ()
    else
      match L.nth g.tvars (i - 1) with
      | Some ki -> check_shift sg g' k (sigma (i - 1)) ki
      | None -> ()
  end

let sub_ok_assumps sg sigma g g' cs =
  let cs' = L.map (sub_constr sigma) cs in
  let g1 = add_assumps g cs in
  let g1' = add_assumps g' cs' in
  hyps_incl_add_assumps g' cs';
  rdom_add_assumps g cs;
  rdom_add_assumps g' cs';
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g1') (sub_constr sigma h)
  with introduce _ ==> _
  with begin
    mem_hyps_add_assumps g cs h;
    if L.mem h cs then begin
      mem_map (sub_constr sigma) cs h;
      mem_hyps_add_assumps g' cs' (sub_constr sigma h);
      entails_hyp (hyps g1') (sub_constr sigma h)
    end
    else entails_weaken (hyps g') (hyps g1') (sub_constr sigma h)
  end;
  ctx_ext_add_assumps g' cs';
  introduce forall (i: nat).
    (match L.nth g1.tvars i with
     | Some ki -> check sg g1' (sigma i) ki
     | None -> True)
  with begin
    match L.nth g.tvars i with
    | Some ki -> check_weaken sg g' g1' (sigma i) ki
    | None -> ()
  end

let rec synth_kind_sub (sg: sig) (sigma: tsub) (g g': ctx) (t: typ)
  : Lemma (requires sub_ok sg sigma g g' /\ Some? (synth_kind sg g t))
          (ensures check sg g' (sub_ty sigma t) (Some?.v (synth_kind sg g t)))
          (decreases %[t; 0]) =
  match t with
  | TVar _ | TCon _ _ -> ()
  | TApp t1 t2 ->
    synth_kind_sub sg sigma g g' t1;
    (match synth_kind sg g t1 with
     | Some (KArrow k1 k2) ->
       check_nonrow_kind sg g' (sub_ty sigma t1) (KArrow k1 k2);
       check_sub sg sigma g g' t2 k1
     | _ -> ())
  | TForall k t1 ->
    sub_ok_up sg sigma g g' k;
    check_sub sg (up_tsub sigma) (push_tvar g k) (push_tvar g' k) t1 KType
  | TConstr c t1 ->
    let c' = sub_constr sigma c in
    constr_ok_sub sg sigma g g' c;
    sub_ok_assumps sg sigma g g' [c];
    add_assump_assumps g c;
    add_assump_assumps g' c';
    check_sub sg sigma (add_assump g c) (add_assump g' c') t1 KType

and check_sub (sg: sig) (sigma: tsub) (g g': ctx) (t: typ) (k: kind)
  : Lemma (requires sub_ok sg sigma g g' /\ check sg g t k)
          (ensures check sg g' (sub_ty sigma t) k)
          (decreases %[t; 1]) =
  match t with
  | TRowEmpty -> ()
  | TRowExt en r ->
    let KRow e = k in
    entry_ok_sub sg sigma g g' en e;
    check_sub sg sigma g g' r k;
    ent_key_sub sigma en;
    entails_sub_into sg sigma g g' (CLacks (ent_key en) r)
  | TRowUnion r1 r2 ->
    check_sub sg sigma g g' r1 k;
    check_sub sg sigma g g' r2 k;
    entails_sub_into sg sigma g g' (CDisj r1 r2)
  | _ -> synth_kind_sub sg sigma g g' t

and entry_ok_sub (sg: sig) (sigma: tsub) (g g': ctx) (en: entry) (e: elt_kind)
  : Lemma (requires sub_ok sg sigma g g' /\ entry_ok sg g en e)
          (ensures entry_ok sg g' (sub_ent sigma en) e)
          (decreases en) =
  match en with
  | EntTy _ t -> check_sub sg sigma g g' t KType
  | EntEff _ q ts ->
    (match sg.effects q with
     | Some ei -> check_tys_sub sg sigma g g' ts ei.eff_params
     | None -> ())
  | EntRegion _ -> ()

and check_tys_sub (sg: sig) (sigma: tsub) (g g': ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires sub_ok sg sigma g g' /\ check_tys sg g ts ks)
          (ensures check_tys sg g' (sub_tys sigma ts) ks)
          (decreases ts) =
  match ts, ks with
  | [], [] -> ()
  | t :: ts', k :: ks' -> check_sub sg sigma g g' t k; check_tys_sub sg sigma g g' ts' ks'

and constr_ok_sub (sg: sig) (sigma: tsub) (g g': ctx) (c: constr)
  : Lemma (requires sub_ok sg sigma g g' /\ constr_ok sg g c)
          (ensures constr_ok sg g' (sub_constr sigma c))
          (decreases c) =
  match c with
  | CLacks k r ->
    if check sg g r (KRow EType) && key_ok sg g k EType then begin
      check_sub sg sigma g g' r (KRow EType);
      key_ok_rdom sg g g' k EType
    end else begin
      check_sub sg sigma g g' r (KRow EEffect);
      key_ok_rdom sg g g' k EEffect
    end
  | CDisj r1 r2 ->
    if check sg g r1 (KRow EType) && check sg g r2 (KRow EType) then begin
      check_sub sg sigma g g' r1 (KRow EType);
      check_sub sg sigma g g' r2 (KRow EType)
    end else begin
      check_sub sg sigma g g' r1 (KRow EEffect);
      check_sub sg sigma g g' r2 (KRow EEffect)
    end

let rec constrs_ok_sub (sg: sig) (sigma: tsub) (g g': ctx) (cs: list constr)
  : Lemma (requires sub_ok sg sigma g g' /\ constrs_ok sg g cs)
          (ensures constrs_ok sg g' (L.map (sub_constr sigma) cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | c :: tl -> constr_ok_sub sg sigma g g' c; constrs_ok_sub sg sigma g g' tl

(* Instantiating one type variable. *)

let sub_ok_subst1 sg g k s =
  let sigma = scons s tvar in
  hyps_push_tvar g k;
  rdom_push_tvar g k;
  introduce forall (h: constr).
    L.mem h (hyps (push_tvar g k)) ==> entails (hyps g) (sub_constr sigma h)
  with introduce _ ==> _
  with begin
    let h0 = map_wit (ren_constr (shift 1)) (hyps g) h in
    sub_ren_constr sigma (shift 1) tvar h0;
    sub_id_constr tvar h0;
    entails_hyp (hyps g) h0
  end

let check_subst1 sg g k s t kt =
  sub_ok_subst1 sg g k s;
  check_sub sg (scons s tvar) (push_tvar g k) g t kt

let check_subst1_assumps sg g k cs s t kt =
  let sigma = scons s tvar in
  sub_ok_subst1 sg g k s;
  sub_ok_assumps sg sigma (push_tvar g k) g cs;
  check_sub sg sigma (add_assumps (push_tvar g k) cs) (add_assumps g (L.map (sub_constr sigma) cs))
    t kt

let check_subst1_entailed sg g k cs s t kt =
  let sigma = scons s tvar in
  let cs' = L.map (sub_constr sigma) cs in
  check_subst1_assumps sg g k cs s t kt;
  introduce forall (c': constr). L.mem c' cs' ==> entails (hyps g) c'
  with introduce _ ==> _
  with (let _ = map_wit (sub_constr sigma) cs c' in ());
  check_cut sg g cs' (subst1_ty s t) kt

(* Kind instantiation of kinds. *)

let rec qkinds_wf_index (nk: nat) (ks: list kind) (i: nat)
  : Lemma (requires qkinds_wf nk ks /\ i < L.length ks)
          (ensures kind_wf nk (L.index ks i) /\ qkind nk (L.index ks i))
          (decreases ks) =
  match ks with
  | _ :: tl -> if i = 0 then () else qkinds_wf_index nk tl (i - 1)

let rec kinst_kinds_length (ks kl: list kind)
  : Lemma (ensures L.length (kinst_kinds ks kl) == L.length kl) (decreases kl) =
  match kl with
  | [] -> ()
  | _ :: tl -> kinst_kinds_length ks tl

let rec index_kinst_kinds (ks kl: list kind) (i: nat)
  : Lemma (requires i < L.length kl /\ i < L.length (kinst_kinds ks kl))
          (ensures L.index (kinst_kinds ks kl) i == kinst_kind ks (L.index kl i))
          (decreases kl) =
  match kl with
  | _ :: tl -> if i = 0 then () else index_kinst_kinds ks tl (i - 1)

let rec nth_kinst_kinds (ks kl: list kind) (i: nat)
  : Lemma (ensures L.nth (kinst_kinds ks kl) i ==
                   (match L.nth kl i with Some k -> Some (kinst_kind ks k) | None -> None))
          (decreases kl) =
  match kl with
  | [] -> ()
  | _ :: tl -> if i = 0 then () else nth_kinst_kinds ks tl (i - 1)

let rec kinst_kind_wf (ks: list kind) (nk: nat) (k: kind)
  : Lemma (requires kind_wf (L.length ks) k /\ qkinds_wf nk ks)
          (ensures kind_wf nk (kinst_kind ks k))
          (decreases k) =
  match k with
  | KVar i -> qkinds_wf_index nk ks i
  | KArrow k1 k2 -> kinst_kind_wf ks nk k1; kinst_kind_wf ks nk k2
  | _ -> ()

let rec kinst_qkind (ks: list kind) (nk: nat) (k: kind)
  : Lemma (requires qkind (L.length ks) k /\ qkinds_wf nk ks)
          (ensures qkind nk (kinst_kind ks k))
          (decreases k) =
  match k with
  | KVar i -> qkinds_wf_index nk ks i
  | KArrow k1 k2 -> kinst_qkind ks nk k1; kinst_qkind ks nk k2; kinst_result ks k2
  | _ -> ()

let rec kinst_qkinds_wf (ks: list kind) (nk: nat) (kl: list kind)
  : Lemma (requires qkinds_wf (L.length ks) kl /\ qkinds_wf nk ks)
          (ensures qkinds_wf nk (kinst_kinds ks kl))
          (decreases kl) =
  match kl with
  | [] -> ()
  | k :: tl -> kinst_kind_wf ks nk k; kinst_qkind ks nk k; kinst_qkinds_wf ks nk tl

let rec kinst_kind_closed (ks: list kind) (k: kind)
  : Lemma (requires kind_wf 0 k) (ensures kinst_kind ks k == k) (decreases k) =
  match k with
  | KArrow k1 k2 -> kinst_kind_closed ks k1; kinst_kind_closed ks k2
  | _ -> ()

let rec kinst_kinds_closed (ks: list kind) (kl: list kind)
  : Lemma (requires qkinds_wf 0 kl) (ensures kinst_kinds ks kl == kl) (decreases kl) =
  match kl with
  | [] -> ()
  | k :: tl -> kinst_kind_closed ks k; kinst_kinds_closed ks tl

let rec kinst_kind_comp (ks ks0: list kind) (k: kind)
  : Lemma (requires kind_wf (L.length ks0) k)
          (ensures kinst_kind ks (kinst_kind ks0 k) == kinst_kind (kinst_kinds ks ks0) k)
          (decreases k) =
  match k with
  | KVar i -> kinst_kinds_length ks ks0; index_kinst_kinds ks ks0 i
  | KArrow k1 k2 -> kinst_kind_comp ks ks0 k1; kinst_kind_comp ks ks0 k2
  | _ -> ()

(* Kind instantiation of types. *)

let tycons_wf_at (sg: sig) (q: qname)
  : Lemma (requires tycons_wf sg /\ Some? (sg.tycons q))
          (ensures tycon_ok (Some?.v (sg.tycons q))) = ()

let effects_wf_at (sg: sig) (q: qname)
  : Lemma (requires effects_wf sg /\ Some? (sg.effects q))
          (ensures qkinds_wf 0 (Some?.v (sg.effects q)).eff_params) = ()

let rec synth_kind_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (t: typ)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ Some? (synth_kind sg g t))
          (ensures synth_kind sg (kinst_ctx ks nk g) (kinst_ty ks t) ==
                   Some (kinst_kind ks (Some?.v (synth_kind sg g t))))
          (decreases %[t; 0]) =
  match t with
  | TVar i -> nth_kinst_kinds ks g.tvars i
  | TCon q kl ->
    tycons_wf_at sg q;
    let ti = Some?.v (sg.tycons q) in
    kinst_kinds_length ks kl;
    kinst_qkinds_wf ks nk kl;
    kinst_kind_comp ks kl ti.tc_kind
  | TApp t1 t2 ->
    synth_kind_kinst sg ks nk g t1;
    (match synth_kind sg g t1 with
     | Some (KArrow k1 _) -> check_kinst sg ks nk g t2 k1
     | _ -> ())
  | TForall k t1 ->
    kinst_kind_wf ks nk k;
    kinst_qkind ks nk k;
    check_kinst sg ks nk (push_tvar g k) t1 KType;
    kinst_ctx_push_tvar ks nk g k
  | TConstr c t1 ->
    constr_ok_kinst sg ks nk g c;
    check_kinst sg ks nk (add_assump g c) t1 KType;
    add_assump_assumps g c;
    kinst_ctx_add_assumps ks nk g [c];
    add_assump_assumps (kinst_ctx ks nk g) (kinst_constr ks c)

and check_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ check sg g t k)
          (ensures check sg (kinst_ctx ks nk g) (kinst_ty ks t) (kinst_kind ks k))
          (decreases %[t; 1]) =
  match t with
  | TRowEmpty -> ()
  | TRowExt en r ->
    let KRow e = k in
    entry_ok_kinst sg ks nk g en e;
    check_kinst sg ks nk g r k;
    ent_key_kinst ks en;
    hyps_kinst_ctx ks nk g;
    entails_kinst ks (hyps g) (CLacks (ent_key en) r)
  | TRowUnion r1 r2 ->
    check_kinst sg ks nk g r1 k;
    check_kinst sg ks nk g r2 k;
    hyps_kinst_ctx ks nk g;
    entails_kinst ks (hyps g) (CDisj r1 r2)
  | _ -> synth_kind_kinst sg ks nk g t

and entry_ok_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (en: entry) (e: elt_kind)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ entry_ok sg g en e)
          (ensures entry_ok sg (kinst_ctx ks nk g) (kinst_ent ks en) e)
          (decreases en) =
  match en with
  | EntTy _ t -> check_kinst sg ks nk g t KType
  | EntEff _ q ts ->
    (match sg.effects q with
     | Some ei ->
       effects_wf_at sg q;
       kinst_kinds_closed ks ei.eff_params;
       check_tys_kinst sg ks nk g ts ei.eff_params
     | None -> ())
  | EntRegion _ -> rdom_kinst_ctx ks nk g

and check_tys_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (ts: list typ) (kl: list kind)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ check_tys sg g ts kl)
          (ensures check_tys sg (kinst_ctx ks nk g) (kinst_tys ks ts) (kinst_kinds ks kl))
          (decreases ts) =
  match ts, kl with
  | [], [] -> ()
  | t :: ts', k :: kl' -> check_kinst sg ks nk g t k; check_tys_kinst sg ks nk g ts' kl'

and constr_ok_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (c: constr)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ constr_ok sg g c)
          (ensures constr_ok sg (kinst_ctx ks nk g) (kinst_constr ks c))
          (decreases c) =
  let g' = kinst_ctx ks nk g in
  rdom_kinst_ctx ks nk g;
  match c with
  | CLacks k r ->
    if check sg g r (KRow EType) && key_ok sg g k EType then begin
      check_kinst sg ks nk g r (KRow EType);
      key_ok_rdom sg g g' k EType
    end else begin
      check_kinst sg ks nk g r (KRow EEffect);
      key_ok_rdom sg g g' k EEffect
    end
  | CDisj r1 r2 ->
    if check sg g r1 (KRow EType) && check sg g r2 (KRow EType) then begin
      check_kinst sg ks nk g r1 (KRow EType);
      check_kinst sg ks nk g r2 (KRow EType)
    end else begin
      check_kinst sg ks nk g r1 (KRow EEffect);
      check_kinst sg ks nk g r2 (KRow EEffect)
    end

let rec constrs_ok_kinst (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (cs: list constr)
  : Lemma (requires tycons_wf sg /\ effects_wf sg /\ kinst_ok ks nk g /\ constrs_ok sg g cs)
          (ensures constrs_ok sg (kinst_ctx ks nk g) (L.map (kinst_constr ks) cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | c :: tl -> constr_ok_kinst sg ks nk g c; constrs_ok_kinst sg ks nk g tl

let tvars_wf_kinst ks nk g = kinst_qkinds_wf ks nk g.tvars

let wf_hyps_kinst sg ks nk g =
  constrs_ok_kinst sg ks nk g (hyps g);
  hyps_kinst_ctx ks nk g

let kinst_decl_ctx ks nk n = ()

let scheme_inst sg g n t ks =
  check_kinst sg ks g.nk (decl_ctx n) t KType;
  kinst_decl_ctx ks g.nk n;
  check_decl sg g (kinst_ty ks t) KType
