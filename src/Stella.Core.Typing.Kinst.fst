(* Proof structure.

   The instantiated context is computed, so the binders of the rules need
   only equations: entering a term binder, a type binder, a telescope of
   them, or an assumption commutes with `kinst_ctx`, and the kinds of a
   clause's binders have no kind variable. Entering a region does not
   commute: its facts name the variables of kind `Row Effect`, and a
   variable of kind `KVar i` has that kind once instantiated. Every fact
   of the instantiated context is a fact of the region entered in the
   instantiated context, and the region and its layout are the same, so the
   body is weakened into the latter (`typing_weaken_ext`).

   The judgements are one mutual induction on the derivation, as for type
   renaming (`Stella.Core.Typing.Rename.Ty`). Side conditions go through
   `check_kinst`, `entails_kinst`, `ty_eq_kinst` and the facts of
   `Stella.Core.Typing.Kinst.Facts`; the closed types of the run-time forms
   and the operation signatures are fixed. The branches of a `switchCtor`
   carry the number of kinds of their data type, which the kinding premise
   of the switch gives (`ctor_nk_of_data`), so that the fields compose.

   Unfolding a global: `decl_ctx` instantiates to `decl_ctx`
   (`kinst_decl_ctx`), and the identity type renaming takes a declaration
   context to any context with the same kind variables. *)
module Stella.Core.Typing.Kinst
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Region
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
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing
open Stella.Core.Typing.Keys
open Stella.Core.Typing.Ops
open Stella.Core.Typing.Rename.Facts
open Stella.Core.Typing.Rename.Ty
open Stella.Core.Typing.Rename.Tm
open Stella.Core.Typing.Weaken
open Stella.Core.Typing.Kinst.Facts
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value
module KI = Stella.Core.Typing.Kinst.Init

(* Lists. *)

let rec nth_map (#a #b: Type) (f: a -> b) (l: list a) (i: nat)
  : Lemma (ensures L.nth (L.map f l) i == map_opt f (L.nth l i)) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> if i = 0 then () else nth_map f l (i - 1)

let rec nth_kinst_kinds (ks: list kind) (kl: list kind) (i: nat)
  : Lemma (ensures L.nth (kinst_kinds ks kl) i == map_opt (kinst_kind ks) (L.nth kl i))
          (decreases kl) =
  match kl with
  | [] -> ()
  | _ :: kl -> if i = 0 then () else nth_kinst_kinds ks kl (i - 1)

let rec assoc_kinst_regions (ks: list kind) (rs: list (atom & layout)) (a: atom)
  : Lemma (ensures L.assoc a (L.map (kinst_region ks) rs) == map_opt (kinst_layout ks) (L.assoc a rs))
          (decreases rs) =
  match rs with
  | [] -> ()
  | _ :: rs -> assoc_kinst_regions ks rs a

let rec map_wit (#a #b: eqtype) (f: a -> b) (l: list a) (y: b)
  : Pure a (requires L.mem y (L.map f l)) (ensures fun x -> L.mem x l /\ f x == y) (decreases l) =
  match l with
  | x :: tl -> if f x = y then x else map_wit f tl y

(* The instantiated context. *)

let kinst_ctx_push_var (ks: list kind) (nk: nat) (g: ctx) (t: typ)
  : Lemma (kinst_ctx ks nk (push_var g t) == push_var (kinst_ctx ks nk g) (kinst_ty ks t)) = ()

let rec kinst_ctx_push_vars (ks: list kind) (nk: nat) (g: ctx) (ts: list typ)
  : Lemma (ensures kinst_ctx ks nk (push_vars g ts) == push_vars (kinst_ctx ks nk g) (kinst_tys ks ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> kinst_ctx_push_var ks nk g t; kinst_ctx_push_vars ks nk (push_var g t) ts'

let kinst_ctx_add_assump (ks: list kind) (nk: nat) (g: ctx) (c: constr)
  : Lemma (kinst_ctx ks nk (add_assump g c) == add_assump (kinst_ctx ks nk g) (kinst_constr ks c)) =
  add_assump_assumps g c;
  add_assump_assumps (kinst_ctx ks nk g) (kinst_constr ks c);
  kinst_ctx_add_assumps ks nk g [c]

let rec kinst_ctx_push_tvars (ks: list kind) (nk: nat) (g: ctx) (kl: list kind)
  : Lemma (ensures kinst_ctx ks nk (push_tvars g kl) == push_tvars (kinst_ctx ks nk g) (kinst_kinds ks kl) /\
                   (push_tvars g kl).nk == g.nk)
          (decreases kl) =
  match kl with
  | [] -> ()
  | k :: kl' -> kinst_ctx_push_tvar ks nk g k; kinst_ctx_push_tvars ks nk (push_tvar g k) kl'

let rec ops_ok_assoc (sg: sig) (params: list kind) (ops: list (opname & op_sig)) (op: opname)
  (os: op_sig)
  : Lemma (requires ops_ok sg params ops /\ L.assoc op ops == Some os) (ensures op_ok sg params os)
          (decreases ops) =
  match ops with
  | (op', _) :: ops' -> if op = op' then () else ops_ok_assoc sg params ops' op os

(* The parameters of an effect and the binders of its operations have no
   kind variable. *)
let effect_kinds_closed (sg: sig) (q: qname) (ei: effect_info) (op: opname) (os: op_sig)
  : Lemma (requires effects_wf sg /\ sg.effects q == Some ei /\ op_of ei op == Some os)
          (ensures qkinds_wf 0 os.binders /\ qkinds_wf 0 ei.eff_params) =
  assert (match sg.effects q with Some ei -> effect_ok sg ei | None -> True);
  ops_ok_assoc sg ei.eff_params ei.eff_ops op os

(* Side conditions. *)

let check_k (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires sig_ok sg /\ kinst_ok ks nk g /\ check sg g t k)
          (ensures check sg (kinst_ctx ks nk g) (kinst_ty ks t) (kinst_kind ks k)) =
  check_kinst sg ks nk g t k

let entails_k (ks: list kind) (nk: nat) (g: ctx) (c: constr)
  : Lemma (requires entails (hyps g) c)
          (ensures entails (hyps (kinst_ctx ks nk g)) (kinst_constr ks c)) =
  entails_kinst ks (hyps g) c;
  hyps_kinst_ctx ks nk g

let key_ok_k (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (k: key) (e: elt_kind)
  : Lemma (requires key_ok sg g k e) (ensures key_ok sg (kinst_ctx ks nk g) k e) =
  rdom_kinst_ctx ks nk g;
  key_ok_rdom sg g (kinst_ctx ks nk g) k e

let rec tys_ok_k (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (ts: list typ)
  : Lemma (requires sig_ok sg /\ kinst_ok ks nk g /\ tys_ok sg g ts)
          (ensures tys_ok sg (kinst_ctx ks nk g) (kinst_tys ks ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> check_k sg ks nk g t KType; tys_ok_k sg ks nk g ts

(* A closed type of a run-time form stays kinded, and is fixed. *)
let closed_k (sg: sig) (ks: list kind) (nk: nat) (g: ctx) (t: typ) (k: kind)
  : Lemma (requires check sg (closed_ctx g.regions) t k)
          (ensures check sg (closed_ctx (kinst_ctx ks nk g).regions) t k /\ kinst_ty ks t == t) =
  rdom_kinst_ctx ks nk g;
  assert (L.map fst (kinst_ctx ks nk g).regions == L.map fst g.regions);
  check_closed_mono sg g.regions (kinst_ctx ks nk g).regions t k;
  check_closed_kinst sg g.regions t k ks

let rec scrut_occs_k (ks: list kind) (i: nat) (ts: list typ)
  : Lemma (ensures kinst_octx ks (scrut_occs i ts) == scrut_occs i (kinst_tys ks ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts -> scrut_occs_k ks (i + 1) ts

let rec field_occs_k (ks: list kind) (o: occ) (c: qname) (j: nat) (fs: list typ)
  : Lemma (ensures kinst_octx ks (field_occs o c j fs) == field_occs o c j (kinst_tys ks fs))
          (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs -> field_occs_k ks o c (j + 1) fs

let rec kinst_octx_append (ks: list kind) (om1 om2: octx)
  : Lemma (ensures kinst_octx ks (L.append om1 om2) == L.append (kinst_octx ks om1) (kinst_octx ks om2))
          (decreases om1) =
  match om1 with
  | [] -> ()
  | _ :: om1 -> kinst_octx_append ks om1 om2

let rec assoc_kinst_octx (ks: list kind) (om: octx) (o: occ)
  : Lemma (ensures L.assoc o (kinst_octx ks om) == map_opt (kinst_ty ks) (L.assoc o om))
          (decreases om) =
  match om with
  | [] -> ()
  | _ :: om -> assoc_kinst_octx ks om o

let rec nth_kinst_jctx (ks: list kind) (d: jctx) (j: nat)
  : Lemma (ensures L.nth (kinst_jctx ks d) j == map_opt (kinst_jt ks) (L.nth d j)) (decreases d) =
  match d with
  | [] -> ()
  | _ :: d -> if j = 0 then () else nth_kinst_jctx ks d (j - 1)

let rec clause_ops_k (ks: list kind) (cs: list clause)
  : Lemma (ensures clause_ops (kinst_cls ks cs) == clause_ops cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ _ :: cs | CFast _ _ _ _ :: cs -> clause_ops_k ks cs

(* The facts a region adds. *)

let rec region_facts_wit (a: atom) (d: nat) (kl: list kind) (h: constr)
  : Pure nat (requires L.mem h (region_facts a d kl))
         (ensures fun j -> h == CLacks (RegionKey (RFree a)) (TVar (d + j)) /\
                           L.nth kl j == Some (KRow EEffect))
         (decreases kl) =
  match kl with
  | k :: kl' ->
    if k = KRow EEffect && h = CLacks (RegionKey (RFree a)) (TVar d) then 0
    else 1 + region_facts_wit a (d + 1) kl' h

let rec region_facts_intro (a: atom) (d: nat) (kl: list kind) (j: nat)
  : Lemma (requires L.nth kl j == Some (KRow EEffect))
          (ensures L.mem (CLacks (RegionKey (RFree a)) (TVar (d + j))) (region_facts a d kl))
          (decreases kl) =
  match kl with
  | _ :: kl' -> if j = 0 then () else region_facts_intro a (d + 1) kl' (j - 1)

(* The instance of the context of a region body is weaker than the region
   entered in the instantiated context. *)
let kinst_enter_region (ks: list kind) (nk: nat) (g: ctx) (a: atom) (l: layout)
  : Lemma (ctx_weaker (kinst_ctx ks nk (enter_region g a l))
                      (enter_region (kinst_ctx ks nk g) a (kinst_layout ks l))) =
  let g1 = kinst_ctx ks nk (enter_region g a l) in
  let gk = kinst_ctx ks nk g in
  let g2 = enter_region gk a (kinst_layout ks l) in
  let rf = region_facts a 0 g.tvars in
  assert (g1.regions == g2.regions /\ g1.tvars == g2.tvars /\ g1.vars == g2.vars /\ g1.nk == g2.nk);
  LP.map_append (kinst_constr ks) rf g.facts;
  introduce forall (h: constr). L.mem h (hyps g1) ==> entails (hyps g2) h
  with introduce _ ==> _
  with begin
    LP.append_mem g1.facts g1.assumps h;
    LP.append_mem (L.map (kinst_constr ks) rf) (L.map (kinst_constr ks) g.facts) h;
    LP.append_mem g2.facts g2.assumps h;
    LP.append_mem (region_facts a 0 gk.tvars) gk.facts h;
    if L.mem h (L.map (kinst_constr ks) rf) then begin
      let f = map_wit (kinst_constr ks) rf h in
      let j = region_facts_wit a 0 g.tvars f in
      nth_kinst_kinds ks g.tvars j;
      region_facts_intro a 0 gk.tvars j
    end;
    entails_hyp (hyps g2) h
  end;
  assert (rdom g1 == rdom g2)

(* Casts along equalities of indices. *)

let cast (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp) (#t #r: typ)
  (h: typing sg ln g d e t r) (g': ctx{g' == g}) (d': jctx{d' == d}) (e': exp{e' == e})
  (t': typ{t' == t}) (r': typ{r' == r})
  : typing sg ln g' d' e' t' r' = h

let cast_dt (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx) (#dt: dtree)
  (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (om': octx{om' == om}) (t': typ{t' == t})
  (r': typ{r' == r})
  : dt_typing sg ln g d om' dt t' r' = h

(* The rules, one builder each, as for type renaming. *)

let tk (sg: sig) (ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) : Type =
  typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_exp ks e) (kinst_ty ks t) (kinst_ty ks r)

let pre (sg: sig) (ks: list kind) (nk: nat) (g: ctx) : prop = sig_ok sg /\ kinst_ok ks nk g

let kinst_rec_ext (ks: list kind) (k: key) (t r0: typ)
  : Lemma (kinst_ty ks (t_record (TRowExt (EntTy k t) r0)) ==
           t_record (TRowExt (EntTy k (kinst_ty ks t)) (kinst_ty ks r0))) =
  kinst_t_record ks (TRowExt (EntTy k t) r0)

let kinst_var_ext (ks: list kind) (k: key) (t r0: typ)
  : Lemma (kinst_ty ks (t_variant (TRowExt (EntTy k t) r0)) ==
           t_variant (TRowExt (EntTy k (kinst_ty ks t)) (kinst_ty ks r0))) =
  kinst_t_variant ks (TRowExt (EntTy k t) r0)

let kinst_app_eq (ks: list kind) (e0 v: exp)
  : Lemma (kinst_exp ks (EApp e0 v) == EApp (kinst_exp ks e0) (kinst_exp ks v)) = ()

let kinst_tyapp_eq (ks: list kind) (e0: exp) (s: typ)
  : Lemma (kinst_exp ks (ETyApp e0 s) == ETyApp (kinst_exp ks e0) (kinst_ty ks s)) = ()

let kinst_capp_eq (ks: list kind) (e0: exp) : Lemma (kinst_exp ks (ECApp e0) == ECApp (kinst_exp ks e0)) =
  ()

let kinst_let_eq (ks: list kind) (t1: typ) (e1 e2: exp)
  : Lemma (kinst_exp ks (ELet t1 e1 e2) == ELet (kinst_ty ks t1) (kinst_exp ks e1) (kinst_exp ks e2)) =
  ()

let kinst_letjoin_eq (ks: list kind) (ts: list typ) (t: typ) (e1 e2: exp)
  : Lemma (kinst_exp ks (ELetJoin ts t e1 e2) ==
           ELetJoin (kinst_tys ks ts) (kinst_ty ks t) (kinst_exp ks e1) (kinst_exp ks e2)) = ()

let kinst_extend_eq (ks: list kind) (k: key) (e1 e2: exp)
  : Lemma (kinst_exp ks (EExtend k e1 e2) == EExtend k (kinst_exp ks e1) (kinst_exp ks e2)) = ()

let kinst_update_eq (ks: list kind) (k: key) (e1 e2: exp)
  : Lemma (kinst_exp ks (EUpdate k e1 e2) == EUpdate k (kinst_exp ks e1) (kinst_exp ks e2)) = ()

let kinst_merge_eq (ks: list kind) (e1 e2: exp)
  : Lemma (kinst_exp ks (EMerge e1 e2) == EMerge (kinst_exp ks e1) (kinst_exp ks e2)) = ()

let kinst_inject_eq (ks: list kind) (k: key) (r0: typ) (e1: exp)
  : Lemma (kinst_exp ks (EInject k r0 e1) == EInject k (kinst_ty ks r0) (kinst_exp ks e1)) = ()

let kinst_weaken_eq (ks: list kind) (k: key) (t1: typ) (e1: exp)
  : Lemma (kinst_exp ks (EWeaken k t1 e1) == EWeaken k (kinst_ty ks t1) (kinst_exp ks e1)) = ()

let kinst_openeff_eq (ks: list kind) (r2: typ) (e1: exp)
  : Lemma (kinst_exp ks (EOpenEff r2 e1) == EOpenEff (kinst_ty ks r2) (kinst_exp ks e1)) = ()

let kinst_openeffc_eq (ks: list kind) (r2: typ) (e1: exp)
  : Lemma (kinst_exp ks (EOpenEffC r2 e1) == EOpenEffC (kinst_ty ks r2) (kinst_exp ks e1)) = ()

let kinst_writecell_eq (ks: list kind) (a: region_ref) (k: key) (e1: exp)
  : Lemma (kinst_exp ks (EWriteCell a k e1) == EWriteCell a k (kinst_exp ks e1)) = ()

let kinst_perform_eq (ks: list kind) (k: key) (op: opname) (ss: list typ) (e1: exp)
  : Lemma (kinst_exp ks (EPerform k op ss e1) == EPerform k op (kinst_tys ks ss) (kinst_exp ks e1)) =
  ()

let kinst_forall_eq (ks: list kind) (k: kind) (t0: typ)
  : Lemma (kinst_ty ks (TForall k t0) == TForall (kinst_kind ks k) (kinst_ty ks t0)) = ()

let kinst_constr_ty_eq (ks: list kind) (c: constr) (t0: typ)
  : Lemma (kinst_ty ks (TConstr c t0) == TConstr (kinst_constr ks c) (kinst_ty ks t0)) = ()

let kinst_union_eq (ks: list kind) (r1 r2: typ)
  : Lemma (kinst_ty ks (TRowUnion r1 r2) == TRowUnion (kinst_ty ks r1) (kinst_ty ks r2)) = ()

let kinst_ext_eq (ks: list kind) (en: entry) (r: typ)
  : Lemma (kinst_ty ks (TRowExt en r) == TRowExt (kinst_ent ks en) (kinst_ty ks r)) = ()

let kinst_lam_eq (ks: list kind) (t1 r1: typ) (body: exp)
  : Lemma (kinst_exp ks (ELam t1 r1 body) == ELam (kinst_ty ks t1) (kinst_ty ks r1) (kinst_exp ks body)) =
  ()

let kinst_tylam_eq (ks: list kind) (k: kind) (body: exp)
  : Lemma (kinst_exp ks (ETyLam k body) == ETyLam (kinst_kind ks k) (kinst_exp ks body)) = ()

let kinst_clam_eq (ks: list kind) (c: constr) (body: exp)
  : Lemma (kinst_exp ks (ECLam c body) == ECLam (kinst_constr ks c) (kinst_exp ks body)) = ()

let kinst_letrec_eq (ks: list kind) (bs: list (typ & exp)) (body: exp)
  : Lemma (kinst_exp ks (ELetRec bs body) == ELetRec (kinst_binds ks bs) (kinst_exp ks body)) = ()

let kinst_case_eq (ks: list kind) (es: list exp) (dt: dtree)
  : Lemma (kinst_exp ks (ECase es dt) == ECase (kinst_exps ks es) (kinst_dt ks dt)) = ()

let kinst_jump_eq (ks: list kind) (j: nat) (es: list exp)
  : Lemma (kinst_exp ks (EJump j es) == EJump j (kinst_exps ks es)) = ()

let kinst_select_eq (ks: list kind) (k: key) (e1: exp)
  : Lemma (kinst_exp ks (ESelect k e1) == ESelect k (kinst_exp ks e1)) = ()

let kinst_restrict_eq (ks: list kind) (k: key) (e1: exp)
  : Lemma (kinst_exp ks (ERestrict k e1) == ERestrict k (kinst_exp ks e1)) = ()

let kinst_absurd_eq (ks: list kind) (t: typ) (e1: exp)
  : Lemma (kinst_exp ks (EAbsurd t e1) == EAbsurd (kinst_ty ks t) (kinst_exp ks e1)) = ()

let kinst_handle_eq (ks: list kind) (e1: exp) (hd: handler)
  : Lemma (kinst_exp ks (EHandle e1 hd) ==
           EHandle (kinst_exp ks e1)
             { h_ent = kinst_ent ks hd.h_ent; h_ret_ty = kinst_ty ks hd.h_ret_ty;
               h_ret = kinst_exp ks hd.h_ret; h_clauses = kinst_cls ks hd.h_clauses }) = ()

let kinst_region_eq (ks: list kind) (l: layout) (es: list exp) (body: exp)
  : Lemma (kinst_exp ks (ERegion l es body)
           == ERegion (kinst_layout ks l) (kinst_exps ks es) (kinst_exp ks body)) = ()

let kinst_match_eq (ks: list kind) (th: list exp) (dt: dtree)
  : Lemma (kinst_exp ks (EMatch th dt) == EMatch (kinst_exps ks th) (kinst_dt ks dt)) = ()

let kinst_fill_eq (ks: list kind) (nu: atom) (e1: exp)
  : Lemma (kinst_exp ks (EFill nu e1) == EFill nu (kinst_exp ks e1)) = ()

let kinst_region_open_eq (ks: list kind) (a: atom) (cells: list (key & exp)) (body: exp)
  : Lemma (kinst_exp ks (ERegionOpen a cells body)
           == ERegionOpen a (kinst_cells ks cells) (kinst_exp ks body)) = ()

let kinst_opaque_eq (ks: list kind) (w: nat) (t: typ)
  : Lemma (kinst_exp ks (EOpaque w t) == EOpaque w (kinst_ty ks t)) = ()

let kinst_global_eq (ks: list kind) (q: qname) (kl: list kind)
  : Lemma (kinst_exp ks (EGlobal q kl) == EGlobal q (kinst_kinds ks kl)) = ()

let b_var (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (i: nat)
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EVar i /\ L.nth g.vars i == Some t /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_k sg ks nk g r (KRow EEffect);
  nth_map (kinst_ty ks) g.vars i;
  T_Var #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #i #(kinst_ty ks t) #(kinst_ty ks r) () ()

let b_global (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (q: qname) (kl: list kind) (n: nat) (t0: typ)
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EGlobal q kl /\ t == kinst_ty kl t0 /\
                   global_type sg q == Some (n, t0) /\ L.length kl == n /\ qkinds_wf g.nk kl /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_k sg ks nk g r (KRow EEffect);
  kinst_global_eq ks q kl;
  global_type_kinst sg q n t0 kl ks;
  kinst_kinds_length ks kl;
  kinst_qkinds_wf ks nk kl;
  T_Global #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #q #(kinst_kinds ks kl) #n #t0
    #(kinst_ty ks r) () () ()

let b_lit (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (c: lit)
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ELit c /\ t == lit_type c /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_k sg ks nk g r (KRow EEffect);
  kinst_lit_type ks c;
  T_Lit #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #c #(kinst_ty ks r) ()

let b_lam (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (t1 r1: typ) (body: exp) (t2: typ)
  (hb: typing sg ln (kinst_ctx ks nk (push_var g t1)) (kinst_jctx ks []) (kinst_exp ks body)
         (kinst_ty ks t2) (kinst_ty ks r1))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ELam t1 r1 body /\ t == t_fun t1 r1 t2 /\
                   check sg g t1 KType /\ check sg g r1 (KRow EEffect) /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  check_k sg ks nk g t1 KType;
  check_k sg ks nk g r1 (KRow EEffect);
  check_k sg ks nk g r (KRow EEffect);
  kinst_lam_eq ks t1 r1 body;
  kinst_t_fun ks t1 r1 t2;
  kinst_ctx_push_var ks nk g t1;
  T_Lam #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks t1) #(kinst_ty ks r1)
    #(kinst_exp ks body) #(kinst_ty ks t2) #(kinst_ty ks r) () () hb

let b_app (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (e1 e2: exp) (t1 t2: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (t_fun t1 r t2)) (kinst_ty ks r))
  (h2: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e2) (kinst_ty ks t1)
         (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r) (requires e == EApp e1 e2 /\ t == t2) (ensures fun _ -> True) =
  kinst_app_eq ks e1 e2;
  kinst_t_fun ks t1 r t2;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (t_fun (kinst_ty ks t1) (kinst_ty ks r) (kinst_ty ks t2)) (kinst_ty ks r) = h1 in
  T_App h1 h2

let b_chain (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (t0: typ) (th: tsub)
  (hc: chain_typing sg ln (kinst_ctx ks nk g) [] (kinst_ty ks r) (kinst_exp ks e))
  : Pure (tk sg ln ks nk g d e t r)
         (requires sig_ok sg /\ chain_cursor sg e == Some (t0, th) /\ t == sub_ty th t0)
         (ensures fun _ -> True) =
  chain_cursor_kinst sg ks e t0 th;
  let Some (t', th') = chain_cursor sg (kinst_exp ks e) in
  T_Chain #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_exp ks e) #t' #th'
    #(kinst_ty ks r) hc ()

let b_tylam (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (k: kind) (body: exp) (t0: typ)
  (hb: typing sg ln (kinst_ctx ks nk (push_tvar g k)) (kinst_jctx ks []) (kinst_exp ks body)
         (kinst_ty ks t0) (kinst_ty ks TRowEmpty))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ETyLam k body /\ t == TForall k t0 /\
                   kind_wf g.nk k /\ qkind g.nk k /\ value_form sg body /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  kinst_tylam_eq ks k body;
  kinst_forall_eq ks k t0;
  value_form_kinst sg ks body;
  check_k sg ks nk g r (KRow EEffect);
  kinst_kind_wf ks nk k;
  kinst_qkind ks nk k;
  kinst_ctx_push_tvar ks nk g k;
  let hb : typing sg ln (push_tvar (kinst_ctx ks nk g) (kinst_kind ks k)) [] (kinst_exp ks body)
             (kinst_ty ks t0) TRowEmpty = hb in
  T_TyLam #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_kind ks k) #(kinst_exp ks body)
    #(kinst_ty ks t0) #(kinst_ty ks r) () () () hb

let b_tyapp (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (e1: exp) (s: typ) (k: kind) (t0: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (TForall k t0)) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ETyApp e1 s /\ t == subst1_ty s t0 /\ check sg g s k)
         (ensures fun _ -> True) =
  check_k sg ks nk g s k;
  kinst_subst1 ks s t0;
  kinst_tyapp_eq ks e1 s;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (TForall (kinst_kind ks k) (kinst_ty ks t0)) (kinst_ty ks r) = h1 in
  T_TyApp #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_exp ks e1) #(kinst_ty ks s) h1 ()

let b_clam (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (c: constr) (body: exp) (t0: typ)
  (hb: typing sg ln (kinst_ctx ks nk (add_assump g c)) (kinst_jctx ks []) (kinst_exp ks body)
         (kinst_ty ks t0) (kinst_ty ks TRowEmpty))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ECLam c body /\ t == TConstr c t0 /\ constr_ok sg g c /\
                   value_form sg body /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  kinst_clam_eq ks c body;
  kinst_constr_ty_eq ks c t0;
  constr_ok_kinst sg ks nk g c;
  value_form_kinst sg ks body;
  check_k sg ks nk g r (KRow EEffect);
  kinst_ctx_add_assump ks nk g c;
  let hb : typing sg ln (add_assump (kinst_ctx ks nk g) (kinst_constr ks c)) []
             (kinst_exp ks body) (kinst_ty ks t0) TRowEmpty = hb in
  T_CLam #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_constr ks c) #(kinst_exp ks body)
    #(kinst_ty ks t0) #(kinst_ty ks r) () () () hb

let b_capp (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (e1: exp) (c: constr)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (TConstr c t)) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ECApp e1 /\ entails (hyps g) c)
         (ensures fun _ -> True) =
  entails_k ks nk g c;
  kinst_capp_eq ks e1;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (TConstr (kinst_constr ks c) (kinst_ty ks t)) (kinst_ty ks r) = h1 in
  T_CApp h1 ()

let b_let (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (t1: typ) (e1 e2: exp)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1) (kinst_ty ks t1)
         (kinst_ty ks r))
  (h2: typing sg ln (kinst_ctx ks nk (push_var g t1)) (kinst_jctx ks d) (kinst_exp ks e2)
         (kinst_ty ks t) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ELet t1 e1 e2 /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  kinst_let_eq ks t1 e1 e2;
  check_k sg ks nk g t1 KType;
  kinst_ctx_push_var ks nk g t1;
  T_Let () h1 h2

let b_letrec (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (bs: list (typ & exp)) (body: exp)
  (hbs: binds_typing sg ln (kinst_ctx ks nk (push_vars g (L.map fst bs))) (kinst_binds ks bs))
  (hb: typing sg ln (kinst_ctx ks nk (push_vars g (L.map fst bs))) (kinst_jctx ks d)
         (kinst_exp ks body) (kinst_ty ks t) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires e == ELetRec bs body /\ Stella.Core.Init.init_safe_letrec sg bs)
         (ensures fun _ -> True) =
  kinst_letrec_eq ks bs body;
  KI.init_safe_kinst sg ks bs;
  kinst_binds_fst ks bs;
  kinst_ctx_push_vars ks nk g (L.map fst bs);
  T_LetRec #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_binds ks bs)
    #(kinst_exp ks body) #(kinst_ty ks t) #(kinst_ty ks r) () hbs hb

let b_conv (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (t1 r1: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_exp ks e) (kinst_ty ks t1)
         (kinst_ty ks r1))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ ty_eq t1 t /\ ty_eq r1 r /\ check sg g t KType /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  ty_eq_kinst ks t1 t; ty_eq_kinst ks r1 r;
  check_k sg ks nk g t KType; check_k sg ks nk g r (KRow EEffect);
  T_Conv h1 () ()

let b_case (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (es: list exp) (dt: dtree) (ts: list typ)
  (hes: exps_typing sg ln (kinst_ctx ks nk g) [] (kinst_ty ks r)
          (kinst_exps ks es) (kinst_tys ks ts))
  (hdt: dt_typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_octx ks (scrut_occs 0 ts))
          (kinst_dt ks dt) (kinst_ty ks t) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r) (requires e == ECase es dt) (ensures fun _ -> True) =
  kinst_case_eq ks es dt;
  scrut_occs_k ks 0 ts;
  T_Case hes (cast_dt hdt (scrut_occs 0 (kinst_tys ks ts)) (kinst_ty ks t) (kinst_ty ks r))

let b_letjoin (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (ts: list typ) (e1 e2: exp)
  (h1: typing sg ln (kinst_ctx ks nk (push_vars g ts)) (kinst_jctx ks ((ts, t, r) :: d))
         (kinst_exp ks e1) (kinst_ty ks t) (kinst_ty ks r))
  (h2: typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks ((ts, t, r) :: d)) (kinst_exp ks e2)
         (kinst_ty ks t) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ELetJoin ts t e1 e2 /\ tys_ok sg g ts /\
                   check sg g t KType)
         (ensures fun _ -> True) =
  kinst_letjoin_eq ks ts t e1 e2;
  tys_ok_k sg ks nk g ts;
  check_k sg ks nk g t KType;
  kinst_ctx_push_vars ks nk g ts;
  T_LetJoin #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_tys ks ts) #(kinst_ty ks t)
    #(kinst_exp ks e1) #(kinst_exp ks e2) #(kinst_ty ks r) () h1 h2

let b_jump (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx) (e: exp)
  (t r: typ) (j: nat) (es: list exp) (ts: list typ)
  (hes: exps_typing sg ln (kinst_ctx ks nk g) [] (kinst_ty ks r)
          (kinst_exps ks es) (kinst_tys ks ts))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EJump j es /\ L.nth d j == Some (ts, t, r) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  kinst_jump_eq ks j es;
  nth_kinst_jctx ks d j;
  check_k sg ks nk g t KType; check_k sg ks nk g r (KRow EEffect);
  T_Jump #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #j #(kinst_exps ks es) #(kinst_tys ks ts)
    #(kinst_ty ks t) #(kinst_ty ks r) () () hes

let b_recempty (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ)
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ERecEmpty /\ t == t_record TRowEmpty /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  kinst_t_record ks TRowEmpty;
  check_k sg ks nk g r (KRow EEffect);
  T_RecEmpty #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks r) ()

let b_extend (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (e1 e2: exp) (t1 r0: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1) (kinst_ty ks t1)
         (kinst_ty ks r))
  (h2: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e2)
         (kinst_ty ks (t_record r0)) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EExtend k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t1) r0) /\ key_ok sg g k EType /\
                   entails (hyps g) (CLacks k r0))
         (ensures fun _ -> True) =
  kinst_extend_eq ks k e1 e2;
  kinst_rec_ext ks k t1 r0;
  key_ok_k sg ks nk g k EType;
  entails_k ks nk g (CLacks k r0);
  let h2 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e2)
             (t_record (kinst_ty ks r0)) (kinst_ty ks r) = h2 in
  T_Extend #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #k h1 h2 ()

let b_select (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (e1: exp) (r0: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (t_record (TRowExt (EntTy k t) r0))) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ESelect k e1 /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  kinst_select_eq ks k e1;
  kinst_rec_ext ks k t r0;
  key_ok_k sg ks nk g k EType;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (t_record (TRowExt (EntTy k (kinst_ty ks t)) (kinst_ty ks r0))) (kinst_ty ks r) = h1 in
  T_Select h1 ()

let b_restrict (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (e1: exp) (t1 r0: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (t_record (TRowExt (EntTy k t1) r0))) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ERestrict k e1 /\ t == t_record r0 /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  kinst_restrict_eq ks k e1;
  kinst_t_record ks r0;
  kinst_rec_ext ks k t1 r0;
  key_ok_k sg ks nk g k EType;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (t_record (TRowExt (EntTy k (kinst_ty ks t1)) (kinst_ty ks r0))) (kinst_ty ks r) = h1 in
  T_Restrict h1 ()

let b_update (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (e1 e2: exp) (t1 t2 r0: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (t_record (TRowExt (EntTy k t1) r0))) (kinst_ty ks r))
  (h2: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e2) (kinst_ty ks t2)
         (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EUpdate k e1 e2 /\
                   t == t_record (TRowExt (EntTy k t2) r0) /\ key_ok sg g k EType)
         (ensures fun _ -> True) =
  kinst_update_eq ks k e1 e2;
  kinst_rec_ext ks k t1 r0; kinst_rec_ext ks k t2 r0;
  key_ok_k sg ks nk g k EType;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (t_record (TRowExt (EntTy k (kinst_ty ks t1)) (kinst_ty ks r0))) (kinst_ty ks r) = h1 in
  T_Update h1 h2 ()

let b_merge (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (e1 e2: exp) (r1 r2: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (t_record r1)) (kinst_ty ks r))
  (h2: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e2)
         (kinst_ty ks (t_record r2)) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EMerge e1 e2 /\ t == t_record (TRowUnion r1 r2) /\
                   entails (hyps g) (CDisj r1 r2))
         (ensures fun _ -> True) =
  kinst_merge_eq ks e1 e2;
  kinst_union_eq ks r1 r2;
  kinst_t_record ks (TRowUnion r1 r2); kinst_t_record ks r1; kinst_t_record ks r2;
  entails_k ks nk g (CDisj r1 r2);
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (t_record (kinst_ty ks r1)) (kinst_ty ks r) = h1 in
  let h2 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e2)
             (t_record (kinst_ty ks r2)) (kinst_ty ks r) = h2 in
  T_Merge h1 h2 ()

let b_inject (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (r0: typ) (e1: exp) (t1: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1) (kinst_ty ks t1)
         (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EInject k r0 e1 /\ t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\
                   check sg g r0 (KRow EType))
         (ensures fun _ -> True) =
  kinst_inject_eq ks k r0 e1;
  kinst_var_ext ks k t1 r0;
  key_ok_k sg ks nk g k EType;
  entails_k ks nk g (CLacks k r0);
  check_k sg ks nk g r0 (KRow EType);
  T_Inject #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #k #(kinst_ty ks r0) h1 () ()

let b_weaken (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (t1: typ) (e1: exp) (r0: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (t_variant r0)) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EWeaken k t1 e1 /\ t == t_variant (TRowExt (EntTy k t1) r0) /\
                   key_ok sg g k EType /\ entails (hyps g) (CLacks k r0) /\ check sg g t1 KType)
         (ensures fun _ -> True) =
  kinst_weaken_eq ks k t1 e1;
  kinst_var_ext ks k t1 r0;
  key_ok_k sg ks nk g k EType;
  entails_k ks nk g (CLacks k r0);
  check_k sg ks nk g t1 KType;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (t_variant (kinst_ty ks r0)) (kinst_ty ks r) = h1 in
  T_Weaken #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #k #(kinst_ty ks t1) h1 () ()

let b_variant_value (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (v: exp) (pt vr0 vr: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e)
         (kinst_ty ks (t_variant vr0)) (kinst_ty ks r))
  (h2: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks v) (kinst_ty ks pt)
         (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ t == t_variant vr /\ V.is_value sg e /\
                   variant_view e == Some (k, v) /\ check sg g (t_variant vr) KType /\
                   check sg g pt KType /\ L.mem (k, PTy (canon pt)) (row_entries (canon vr)))
         (ensures fun _ -> True) =
  kinst_t_variant ks vr; kinst_t_variant ks vr0;
  is_value_kinst sg ks e;
  variant_view_kinst ks e;
  check_k sg ks nk g (t_variant vr) KType;
  check_k sg ks nk g pt KType;
  entries_kinst_ty ks vr k pt;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e)
             (t_variant (kinst_ty ks vr0)) (kinst_ty ks r) = h1 in
  T_VariantValue #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_exp ks e) #k
    #(kinst_exp ks v) #(kinst_ty ks pt) #(kinst_ty ks r) (kinst_ty ks vr0) (kinst_ty ks vr) h1 () h2 ()

let b_absurd (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (e1: exp)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (t_variant TRowEmpty)) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EAbsurd t e1 /\ check sg g t KType)
         (ensures fun _ -> True) =
  kinst_absurd_eq ks t e1;
  kinst_t_variant ks TRowEmpty;
  check_k sg ks nk g t KType;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (t_variant TRowEmpty) (kinst_ty ks r) = h1 in
  T_Absurd #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks t) h1 ()

let b_perform (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (k: key) (op: opname) (ss: list typ) (e1: exp) (q: qname) (ei: effect_info)
  (os: op_sig) (ts: list typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (op_inst ts ss os.arg)) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EPerform k op ss e1 /\ t == op_inst ts ss os.res /\
                   L.mem (k, PEff q (canon_tys ts)) (row_entries (canon r)) /\
                   sg.effects q == Some ei /\ op_of ei op == Some os /\
                   check_tys sg g ts ei.eff_params /\ check_tys sg g ss os.binders)
         (ensures fun _ -> True) =
  kinst_perform_eq ks k op ss e1;
  entries_kinst_eff ks r k q ts;
  effect_kinds_closed sg q ei op os;
  check_tys_kinst sg ks nk g ts ei.eff_params;
  check_tys_kinst sg ks nk g ss os.binders;
  kinst_kinds_closed ks ei.eff_params;
  kinst_kinds_closed ks os.binders;
  op_types_closed sg q ei op os;
  op_inst_kinst ks ts ss os.arg;
  op_inst_kinst ks ts ss os.res;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (op_inst (kinst_tys ks ts) (kinst_tys ks ss) os.arg) (kinst_ty ks r) = h1 in
  T_Perform #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #k #op #(kinst_tys ks ss)
    #(kinst_exp ks e1) #(kinst_ty ks r) #q #ei #os (kinst_tys ks ts) () () () h1

let kinst_handler (ks: list kind) (hd: handler) : handler =
  { h_ent = kinst_ent ks hd.h_ent; h_ret_ty = kinst_ty ks hd.h_ret_ty;
    h_ret = kinst_exp ks hd.h_ret; h_clauses = kinst_cls ks hd.h_clauses }

let b_handle (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (e1: exp) (hd: handler) (lbl: option string) (q: qname) (ts: list typ)
  (ei: effect_info)
  (h1: typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks []) (kinst_exp ks e1)
         (kinst_ty ks hd.h_ret_ty) (kinst_ty ks (TRowExt hd.h_ent r)))
  (h2: typing sg ln (kinst_ctx ks nk (push_var g hd.h_ret_ty)) (kinst_jctx ks [])
         (kinst_exp ks hd.h_ret) (kinst_ty ks t) (kinst_ty ks r))
  (hcl: clauses_typing sg ln (kinst_ctx ks nk g) ei (kinst_tys ks ts) (kinst_ty ks r)
          (kinst_ty ks t) (kinst_cls ks hd.h_clauses))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EHandle e1 hd /\ hd.h_ent == EntEff lbl q ts /\
                   sg.effects q == Some ei /\
                   check sg g (TRowExt hd.h_ent r) (KRow EEffect) /\
                   check sg g hd.h_ret_ty KType /\
                   check sg g t KType /\ check sg g r (KRow EEffect) /\
                   clauses_cover ei hd.h_clauses)
         (ensures fun _ -> True) =
  kinst_handle_eq ks e1 hd;
  kinst_ext_eq ks hd.h_ent r;
  let hd' = kinst_handler ks hd in
  let gk = kinst_ctx ks nk g in
  check_k sg ks nk g (TRowExt hd.h_ent r) (KRow EEffect);
  check_k sg ks nk g hd.h_ret_ty KType;
  check_k sg ks nk g t KType;
  check_k sg ks nk g r (KRow EEffect);
  clause_ops_k ks hd.h_clauses;
  kinst_ctx_push_var ks nk g hd.h_ret_ty;
  let h1 : typing sg ln gk [] (kinst_exp ks e1) hd'.h_ret_ty
             (TRowExt hd'.h_ent (kinst_ty ks r)) = h1 in
  let h2 : typing sg ln (push_var gk hd'.h_ret_ty) [] hd'.h_ret (kinst_ty ks t)
             (kinst_ty ks r) = h2 in
  let hcl : clauses_typing sg ln gk ei (kinst_tys ks ts) (kinst_ty ks r) (kinst_ty ks t)
              hd'.h_clauses = hcl in
  T_Handle #sg #ln #gk #(kinst_jctx ks d) #(kinst_exp ks e1) #hd' #(kinst_ty ks t)
    #(kinst_ty ks r) #lbl #q #(kinst_tys ks ts) #ei () () () () h1 h2 hcl

let b_openeff (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (r2: typ) (e1: exp) (t1 r1 t2: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
         (kinst_ty ks (t_fun t1 r1 t2)) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EOpenEff r2 e1 /\ t == t_fun t1 (TRowUnion r1 r2) t2 /\
                   entails (hyps g) (CDisj r1 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  kinst_openeff_eq ks r2 e1;
  kinst_union_eq ks r1 r2;
  entails_k ks nk g (CDisj r1 r2);
  check_k sg ks nk g r2 (KRow EEffect);
  kinst_t_fun ks t1 r1 t2;
  kinst_t_fun ks t1 (TRowUnion r1 r2) t2;
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1)
             (t_fun (kinst_ty ks t1) (kinst_ty ks r1) (kinst_ty ks t2)) (kinst_ty ks r) = h1 in
  T_OpenEff #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks r2) h1 ()

let b_region (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (lay: layout) (es: list exp) (body: exp)
  (hes: exps_typing sg ln (kinst_ctx ks nk g) [] (kinst_ty ks r)
          (kinst_exps ks es) (kinst_tys ks (L.map snd lay)))
  (hb: (a: atom{~(L.mem a (rdom (kinst_ctx ks nk g))) /\
               ~(L.mem a (frn_exp (kinst_exp ks body)))} ->
        typing sg ln (enter_region (kinst_ctx ks nk g) a (kinst_layout ks lay)) []
          (kinst_exp ks (open_region a body)) (kinst_ty ks t)
          (TRowExt (EntRegion (RFree a)) (kinst_ty ks r))))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ERegion lay es body /\
                   check sg g (layout_row lay) (KRow EType) /\ L.noRepeats (L.map fst lay) /\
                   check sg g t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  let gk = kinst_ctx ks nk g in
  let lay' = kinst_layout ks lay in
  let body' = kinst_exp ks body in
  kinst_region_eq ks lay es body;
  kinst_layout_row ks lay;
  kinst_layout_keys ks lay;
  kinst_layout_snd ks lay;
  check_k sg ks nk g (layout_row lay) (KRow EType);
  check_k sg ks nk g t KType;
  check_k sg ks nk g r (KRow EEffect);
  let hes : exps_typing sg ln gk [] (kinst_ty ks r) (kinst_exps ks es)
              (L.map snd lay') = hes in
  let hb' (a: atom{~(L.mem a (rdom gk)) /\ ~(L.mem a (frn_exp body'))})
    : typing sg ln (enter_region gk a lay') [] (open_region a body') (kinst_ty ks t)
        (TRowExt (EntRegion (RFree a)) (kinst_ty ks r)) =
    open_region_kinst a ks body;
    hb a
  in
  T_Region #sg #ln #gk #(kinst_jctx ks d) #lay' #(kinst_exps ks es) #body' #(kinst_ty ks t)
    #(kinst_ty ks r) () () hes hb'

let b_readcell (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (a: atom) (k: key) (lay: layout)
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EReadCell (RFree a) k /\ L.assoc a g.regions == Some lay /\
                   L.assoc k lay == Some t /\ L.mem (RegionKey (RFree a)) (known_keys r) /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  assoc_kinst_regions ks g.regions a;
  kinst_layout_assoc ks lay k;
  known_keys_kinst ks r (RegionKey (RFree a));
  check_k sg ks nk g r (KRow EEffect);
  T_ReadCell #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #a #k #(kinst_layout ks lay)
    #(kinst_ty ks t) #(kinst_ty ks r) () () ()

let b_writecell (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (a: atom) (k: key) (e1: exp) (lay: layout) (t1: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1) (kinst_ty ks t1)
         (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EWriteCell (RFree a) k e1 /\ t == t_unit /\
                   L.assoc a g.regions == Some lay /\ L.assoc k lay == Some t1 /\
                   L.mem (RegionKey (RFree a)) (known_keys r))
         (ensures fun _ -> True) =
  kinst_writecell_eq ks (RFree a) k e1;
  assoc_kinst_regions ks g.regions a;
  kinst_layout_assoc ks lay k;
  known_keys_kinst ks r (RegionKey (RFree a));
  kinst_t_unit ks;
  T_WriteCell #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #a #k #(kinst_exp ks e1)
    #(kinst_layout ks lay) #(kinst_ty ks t1) #(kinst_ty ks r) () () h1

let b_match (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (th: list exp) (dt: dtree) (ts: list typ) (om: octx)
  (hes: exps_typing sg ln (kinst_ctx ks nk g) [] (kinst_ty ks r)
          (kinst_exps ks th) (kinst_tys ks ts))
  (hm: match_typing sg ln (kinst_ctx ks nk g) [] (kinst_ty ks r) (kinst_exps ks th)
         (kinst_octx ks om))
  (hdt: dt_typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_octx ks om) (kinst_dt ks dt)
          (kinst_ty ks t) (kinst_ty ks r))
  : Pure (tk sg ln ks nk g d e t r)
         (requires e == EMatch th dt /\ L.for_all (V.is_value sg) th)
         (ensures fun _ -> True) =
  kinst_match_eq ks th dt;
  values_kinst sg ks th;
  T_Match (kinst_octx ks om) hes () hm hdt

let b_openeffc (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (r2: typ) (e1: exp) (r0: typ)
  (h1: typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1) (kinst_ty ks t)
         (kinst_ty ks r0))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EOpenEffC r2 e1 /\ r == TRowUnion r0 r2 /\
                   entails (hyps g) (CDisj r0 r2) /\ check sg g r2 (KRow EEffect))
         (ensures fun _ -> True) =
  kinst_openeffc_eq ks r2 e1;
  kinst_union_eq ks r0 r2;
  entails_k ks nk g (CDisj r0 r2);
  check_k sg ks nk g r2 (KRow EEffect);
  T_OpenEffC #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks r2) h1 ()

let b_force (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (nu: atom)
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EForce nu /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  closed_k sg ks nk g t KType;
  check_k sg ks nk g r (KRow EEffect);
  T_Force #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #nu #t #(kinst_ty ks r) () ()

let b_fill (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (nu: atom) (e1: exp)
  (h1: typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks []) (kinst_exp ks e1) (kinst_ty ks t)
         (kinst_ty ks TRowEmpty))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EFill nu e1 /\ L.nth ln nu == Some t /\
                   check sg (closed_ctx g.regions) t KType /\ check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  kinst_fill_eq ks nu e1;
  closed_k sg ks nk g t KType;
  check_k sg ks nk g r (KRow EEffect);
  let h1 : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks e1) t TRowEmpty = h1 in
  T_Fill #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #nu #(kinst_exp ks e1) #t
    #(kinst_ty ks r) () () h1

let b_region_open (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (a: atom) (cells: list (key & exp)) (body: exp) (lay: layout)
  (hc: cells_typing sg ln (kinst_ctx ks nk g) (kinst_cells ks cells) (kinst_layout ks lay))
  (hb: typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks []) (kinst_exp ks body) (kinst_ty ks t)
         (kinst_ty ks (TRowExt (EntRegion (RFree a)) r)))
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == ERegionOpen a cells body /\
                   L.assoc a g.regions == Some lay /\
                   check sg (closed_ctx g.regions) t KType /\
                   check sg (closed_ctx g.regions) r (KRow EEffect) /\
                   ~(L.mem a (frn_ty t @ frn_ty r)))
         (ensures fun _ -> True) =
  kinst_region_open_eq ks a cells body;
  kinst_ext_eq ks (EntRegion (RFree a)) r;
  assoc_kinst_regions ks g.regions a;
  closed_k sg ks nk g t KType;
  closed_k sg ks nk g r (KRow EEffect);
  let hb : typing sg ln (kinst_ctx ks nk g) [] (kinst_exp ks body) t
             (TRowExt (EntRegion (RFree a)) r) = hb in
  T_RegionOpen #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #a #(kinst_cells ks cells)
    #(kinst_exp ks body) #(kinst_layout ks lay) #t #r () () () hc hb

let b_opaque (#sg: sig) (#ln: lctx) (ks: list kind) (nk: nat) (g: ctx) (d: jctx)
  (e: exp) (t r: typ) (w: nat)
  : Pure (tk sg ln ks nk g d e t r)
         (requires pre sg ks nk g /\ e == EOpaque w t /\ opaque_type sg t /\ check sg g t KType /\
                   check sg g r (KRow EEffect))
         (ensures fun _ -> True) =
  kinst_opaque_eq ks w t;
  ty_head_kinst ks t;
  check_k sg ks nk g t KType;
  check_k sg ks nk g r (KRow EEffect);
  T_Opaque #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #w #(kinst_ty ks t) #(kinst_ty ks r)
    () ()

(* The cursor of an instantiated chain at a value argument. *)
let chain_val_kinst (sg: sig) (ks: list kind) (e0: exp) (t0: typ) (th: tsub) (t1 r1 t2: typ)
  : Lemma (requires sig_wf sg /\ chain_cursor sg e0 == Some (t0, th) /\
                    as_function sg t0 == Some (t1, r1, t2))
          (ensures (match chain_cursor sg (kinst_exp ks e0) with
                    | Some (t', th') ->
                      as_function sg t' == Some (kinst_ty ks t1, kinst_ty ks r1, kinst_ty ks t2) /\
                      sub_ty th' (kinst_ty ks t1) == kinst_ty ks (sub_ty th t1)
                    | None -> False)) =
  chain_cursor_kinst sg ks e0 t0 th

(* The mutual induction. *)

let rec typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#e: exp)
  (#t #r: typ) (h: typing sg ln g d e t r) (ks: list kind) (nk: nat)
  : Pure (tk sg ln ks nk g d e t r) (requires pre sg ks nk g) (ensures fun _ -> True)
         (decreases h) =
  match h with
  | T_Var #_ #_ #_ #_ #i _ _ -> b_var ks nk g d e t r i
  | T_Global #_ #_ #_ #_ #q #kl #n #t0 _ _ _ -> b_global ks nk g d e t r q kl n t0
  | T_Lit #_ #_ #_ #_ #c _ -> b_lit ks nk g d e t r c
  | T_Lam #_ #_ #_ #_ #t1 #r1 #body #t2 _ _ hb ->
    b_lam ks nk g d e t r t1 r1 body t2 (typing_kinst' hb ks nk)
  | T_App #_ #_ #_ #_ #e1 #e2 #t1 #t2 h1 h2 ->
    b_app ks nk g d e t r e1 e2 t1 t2 (typing_kinst' h1 ks nk) (typing_kinst' h2 ks nk)
  | T_Chain #_ #_ #_ #_ #_ #t0 #th hc _ ->
    b_chain ks nk g d e t r t0 th (chain_typing_kinst' hc ks nk)
  | T_TyLam #_ #_ #_ #_ #k #body #t0 _ _ _ hb ->
    b_tylam ks nk g d e t r k body t0 (typing_kinst' hb ks nk)
  | T_TyApp #_ #_ #_ #_ #e1 #s #k #t0 h1 _ ->
    b_tyapp ks nk g d e t r e1 s k t0 (typing_kinst' h1 ks nk)
  | T_CLam #_ #_ #_ #_ #c #body #t0 _ _ _ hb ->
    b_clam ks nk g d e t r c body t0 (typing_kinst' hb ks nk)
  | T_CApp #_ #_ #_ #_ #e1 #c h1 _ ->
    b_capp ks nk g d e t r e1 c (typing_kinst' h1 ks nk)
  | T_Let #_ #_ #_ #_ #t1 #e1 #e2 _ h1 h2 ->
    b_let ks nk g d e t r t1 e1 e2 (typing_kinst' h1 ks nk) (typing_kinst' h2 ks nk)
  | T_LetRec #_ #_ #_ #_ #bs #body _ hbs hb ->
    same_kinding_push_vars g (L.map fst bs);
    b_letrec ks nk g d e t r bs body (binds_typing_kinst' hbs ks nk) (typing_kinst' hb ks nk)
  | T_Conv #_ #_ #_ #_ #_ #t1 #r1 h1 _ _ ->
    b_conv ks nk g d e t r t1 r1 (typing_kinst' h1 ks nk)
  | T_Case #_ #_ #_ #_ #es #dt #ts hes hdt ->
    b_case ks nk g d e t r es dt ts (exps_typing_kinst' hes ks nk) (dt_typing_kinst' hdt ks nk)
  | T_LetJoin #_ #_ #_ #_ #ts #_ #e1 #e2 _ h1 h2 ->
    same_kinding_push_vars g ts;
    b_letjoin ks nk g d e t r ts e1 e2 (typing_kinst' h1 ks nk) (typing_kinst' h2 ks nk)
  | T_Jump #_ #_ #_ #_ #j #es #ts _ _ hes ->
    b_jump ks nk g d e t r j es ts (exps_typing_kinst' hes ks nk)
  | T_RecEmpty _ -> b_recempty ks nk g d e t r
  | T_Extend #_ #_ #_ #_ #k #e1 #e2 #t1 #r0 h1 h2 _ ->
    b_extend ks nk g d e t r k e1 e2 t1 r0 (typing_kinst' h1 ks nk) (typing_kinst' h2 ks nk)
  | T_Select #_ #_ #_ #_ #k #e1 #_ #r0 h1 _ ->
    b_select ks nk g d e t r k e1 r0 (typing_kinst' h1 ks nk)
  | T_Restrict #_ #_ #_ #_ #k #e1 #t1 #r0 h1 _ ->
    b_restrict ks nk g d e t r k e1 t1 r0 (typing_kinst' h1 ks nk)
  | T_Update #_ #_ #_ #_ #k #e1 #e2 #t1 #t2 #r0 h1 h2 _ ->
    b_update ks nk g d e t r k e1 e2 t1 t2 r0 (typing_kinst' h1 ks nk) (typing_kinst' h2 ks nk)
  | T_Merge #_ #_ #_ #_ #e1 #e2 #r1 #r2 h1 h2 _ ->
    b_merge ks nk g d e t r e1 e2 r1 r2 (typing_kinst' h1 ks nk) (typing_kinst' h2 ks nk)
  | T_Inject #_ #_ #_ #_ #k #r0 #e1 #t1 h1 _ _ ->
    b_inject ks nk g d e t r k r0 e1 t1 (typing_kinst' h1 ks nk)
  | T_Weaken #_ #_ #_ #_ #k #t1 #e1 #r0 h1 _ _ ->
    b_weaken ks nk g d e t r k t1 e1 r0 (typing_kinst' h1 ks nk)
  | T_VariantValue #_ #_ #_ #_ #_ #k #v #pt vr0 vr h1 _ h2 _ ->
    b_variant_value ks nk g d e t r k v pt vr0 vr (typing_kinst' h1 ks nk)
      (typing_kinst' h2 ks nk)
  | T_Absurd #_ #_ #_ #_ #_ #e1 h1 _ ->
    b_absurd ks nk g d e t r e1 (typing_kinst' h1 ks nk)
  | T_Perform #_ #_ #_ #_ #k #op #ss #e1 #_ #q #ei #os ts _ _ _ h1 ->
    b_perform ks nk g d e t r k op ss e1 q ei os ts (typing_kinst' h1 ks nk)
  | T_Handle #_ #_ #_ #_ #e1 #hd #_ #_ #lbl #q #ts #ei _ _ _ _ h1 h2 hcl ->
    b_handle ks nk g d e t r e1 hd lbl q ts ei (typing_kinst' h1 ks nk) (typing_kinst' h2 ks nk)
      (clauses_typing_kinst' hcl q ks nk)
  | T_OpenEff #_ #_ #_ #_ #r2 #e1 #t1 #r1 #t2 h1 _ ->
    b_openeff ks nk g d e t r r2 e1 t1 r1 t2 (typing_kinst' h1 ks nk)
  | T_Region #_ #_ #_ #_ #lay #es #body _ _ hes hbody ->
    let gk = kinst_ctx ks nk g in
    let lay' = kinst_layout ks lay in
    let hb' (a: atom{~(L.mem a (rdom gk)) /\ ~(L.mem a (frn_exp (kinst_exp ks body)))})
      : typing sg ln (enter_region gk a lay') [] (kinst_exp ks (open_region a body))
          (kinst_ty ks t) (TRowExt (EntRegion (RFree a)) (kinst_ty ks r)) =
      rdom_kinst_ctx ks nk g;
      kinst_ext_eq ks (EntRegion (RFree a)) r;
      frn_kinst_exp ks body;
      let h1 = typing_kinst' (hbody a) ks nk in
      kinst_enter_region ks nk g a lay;
      typing_weaken_ext h1 (enter_region gk a lay')
    in
    b_region ks nk g d e t r lay es body (exps_typing_kinst' hes ks nk) hb'
  | T_ReadCell #_ #_ #_ #_ #a #k #lay _ _ _ -> b_readcell ks nk g d e t r a k lay
  | T_WriteCell #_ #_ #_ #_ #a #k #e1 #lay #t1 _ _ h1 ->
    b_writecell ks nk g d e t r a k e1 lay t1 (typing_kinst' h1 ks nk)
  | T_Match #_ #_ #_ #_ #th #dt #ts om hes _ hm hdt ->
    b_match ks nk g d e t r th dt ts om (exps_typing_kinst' hes ks nk)
      (match_typing_kinst' hm ks nk) (dt_typing_kinst' hdt ks nk)
  | T_OpenEffC #_ #_ #_ #_ #r2 #e1 #_ #r0 h1 _ ->
    b_openeffc ks nk g d e t r r2 e1 r0 (typing_kinst' h1 ks nk)
  | T_Force #_ #_ #_ #_ #nu _ _ -> b_force ks nk g d e t r nu
  | T_Fill #_ #_ #_ #_ #nu #e1 _ _ h1 ->
    b_fill ks nk g d e t r nu e1 (typing_kinst' h1 ks nk)
  | T_RegionOpen #_ #_ #_ #_ #a #cells #body #lay _ _ _ hc hb ->
    b_region_open ks nk g d e t r a cells body lay (cells_typing_kinst' hc ks nk)
      (typing_kinst' hb ks nk)
  | T_Opaque #_ #_ #_ #_ #w _ _ -> b_opaque ks nk g d e t r w

and exps_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ)
  (#es: list exp) (#ts: list typ) (h: exps_typing sg ln g d r es ts) (ks: list kind) (nk: nat)
  : Pure (exps_typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_ty ks r)
            (kinst_exps ks es) (kinst_tys ks ts))
         (requires pre sg ks nk g) (ensures fun _ -> True) (decreases h) =
  match h with
  | TE_Nil _ -> check_k sg ks nk g r (KRow EEffect); TE_Nil ()
  | TE_Cons h1 h2 -> TE_Cons (typing_kinst' h1 ks nk) (exps_typing_kinst' h2 ks nk)

and chain_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#e: exp)
  (h: chain_typing sg ln g d r e) (ks: list kind) (nk: nat)
  : Pure (chain_typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_ty ks r) (kinst_exp ks e))
         (requires pre sg ks nk g) (ensures fun _ -> True) (decreases h) =
  match h with
  | TS_Head #_ #_ #_ #_ #_ #q #kl #c #n #t0 _ _ _ ->
    check_k sg ks nk g r (KRow EEffect);
    kinst_kinds_length ks kl;
    kinst_qkinds_wf ks nk kl;
    TS_Head #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks r) #q #(kinst_kinds ks kl)
      #c #n #t0 () () ()
  | TS_Ty #_ #_ #_ #_ #_ #e0 #s #k #t0 #th h0 _ _ ->
    chain_cursor_kinst sg ks e0 (TForall k t0) th;
    kinst_forall_eq ks k t0;
    kinst_tyapp_eq ks e0 s;
    let Some (_, th') = chain_cursor sg (kinst_exp ks e0) in
    check_k sg ks nk g s k;
    TS_Ty #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks r) #(kinst_exp ks e0)
      #(kinst_ty ks s) #(kinst_kind ks k) #(kinst_ty ks t0) #th' (chain_typing_kinst' h0 ks nk) () ()
  | TS_Constr #_ #_ #_ #_ #_ #e0 #c #t0 #th h0 _ _ ->
    chain_cursor_kinst sg ks e0 (TConstr c t0) th;
    kinst_constr_ty_eq ks c t0;
    kinst_capp_eq ks e0;
    let Some (_, th') = chain_cursor sg (kinst_exp ks e0) in
    entails_k ks nk g (sub_constr th c);
    TS_Constr #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks r) #(kinst_exp ks e0)
      #(kinst_constr ks c) #(kinst_ty ks t0) #th' (chain_typing_kinst' h0 ks nk) () ()
  | TS_Val #_ #_ #_ #_ #_ #e0 #v #t0 #th #t1 #r1 #t2 h0 _ hv ->
    chain_cursor_kinst sg ks e0 t0 th;
    chain_val_kinst sg ks e0 t0 th t1 r1 t2;
    kinst_app_eq ks e0 v;
    let Some (t', th') = chain_cursor sg (kinst_exp ks e0) in
    let hv' = cast (typing_kinst' hv ks nk) (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_exp ks v)
      (sub_ty th' (kinst_ty ks t1)) (kinst_ty ks r) in
    TS_Val #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks r) #(kinst_exp ks e0)
      #(kinst_exp ks v) #t' #th' #(kinst_ty ks t1) #(kinst_ty ks r1) #(kinst_ty ks t2)
      (chain_typing_kinst' h0 ks nk) () hv'

and binds_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#bs: list (typ & exp))
  (h: binds_typing sg ln g bs) (ks: list kind) (nk: nat)
  : Pure (binds_typing sg ln (kinst_ctx ks nk g) (kinst_binds ks bs))
         (requires pre sg ks nk g) (ensures fun _ -> True) (decreases h) =
  match h with
  | TB_Nil -> TB_Nil
  | TB_Cons #_ #_ #_ #t0 #e0 #_ _ h1 h2 ->
    check_k sg ks nk g t0 KType;
    let h1' = cast (typing_kinst' h1 ks nk) (kinst_ctx ks nk g) [] (kinst_exp ks e0) (kinst_ty ks t0)
      TRowEmpty in
    TB_Cons () h1' (binds_typing_kinst' h2 ks nk)

and cells_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#cells: list (key & exp)) (#lay: layout)
  (h: cells_typing sg ln g cells lay) (ks: list kind) (nk: nat)
  : Pure (cells_typing sg ln (kinst_ctx ks nk g) (kinst_cells ks cells) (kinst_layout ks lay))
         (requires pre sg ks nk g) (ensures fun _ -> True) (decreases h) =
  match h with
  | TC_Nil -> TC_Nil
  | TC_Cons #_ #_ #_ #k #v #t0 #cs0 #lay0 _ h1 h2 ->
    is_value_kinst sg ks v;
    let h1' = cast (typing_kinst' h1 ks nk) (kinst_ctx ks nk g) [] (kinst_exp ks v) (kinst_ty ks t0)
      TRowEmpty in
    TC_Cons #sg #ln #(kinst_ctx ks nk g) #k #(kinst_exp ks v) #(kinst_ty ks t0) #(kinst_cells ks cs0)
      #(kinst_layout ks lay0) () h1' (cells_typing_kinst' h2 ks nk)

and match_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#r: typ) (#th: list exp)
  (#om: octx) (h: match_typing sg ln g d r th om) (ks: list kind) (nk: nat)
  : Pure (match_typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_ty ks r) (kinst_exps ks th)
            (kinst_octx ks om))
         (requires pre sg ks nk g) (ensures fun _ -> True) (decreases h) =
  match h with
  | TM_Nil _ -> check_k sg ks nk g r (KRow EEffect); TM_Nil ()
  | TM_Cons #_ #_ #_ #_ #_ #_ #o #t0 #_ #v _ h1 h2 ->
    proj_kinst sg ks th o;
    TM_Cons #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_ty ks r) #(kinst_exps ks th) #o
      #(kinst_ty ks t0) #(kinst_octx ks _) #(kinst_exp ks v) () (typing_kinst' h1 ks nk)
      (match_typing_kinst' h2 ks nk)

and dt_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#dt: dtree) (#t #r: typ) (h: dt_typing sg ln g d om dt t r) (ks: list kind) (nk: nat)
  : Pure (dt_typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_octx ks om) (kinst_dt ks dt)
            (kinst_ty ks t) (kinst_ty ks r))
         (requires pre sg ks nk g) (ensures fun _ -> True) (decreases h) =
  match h with
  | TD_Leaf h1 -> TD_Leaf (typing_kinst' h1 ks nk)
  | TD_Bind #_ #_ #_ #_ #_ #o #dt0 #t_o #_ #_ ho hdt ->
    kinst_ctx_push_var ks nk g t_o;
    TD_Bind (occ_typing_kinst' ho ks nk) (dt_typing_kinst' hdt ks nk)
  | TD_SwitchCtor #_ #_ #_ #_ #_ #o #bs #t_o #_ #_ tq kl ss cs ho _ _ _ hbr ->
    kinst_tapps ks (TCon tq kl) ss;
    ty_eq_kinst ks t_o (tapps (TCon tq kl) ss);
    check_k sg ks nk g (tapps (TCon tq kl) ss) KType;
    kinst_brs_labels ks bs;
    introduce forall (c: qname). L.mem c cs ==>
      (match sg.ctors c with Some ci -> L.length kl == ci.ct_nk | None -> False)
    with introduce _ ==> _
    with ctor_nk_of_data sg g tq kl ss cs c;
    TD_SwitchCtor tq (kinst_kinds ks kl) (kinst_tys ks ss) cs (occ_typing_kinst' ho ks nk) () () ()
      (ctor_brs_typing_kinst' hbr ks nk)
  | TD_SwitchCtorDef #_ #_ #_ #_ #_ #o #bs #df #t_o #_ #_ tq kl ss cs ho _ _ _ hbr hdf ->
    kinst_tapps ks (TCon tq kl) ss;
    ty_eq_kinst ks t_o (tapps (TCon tq kl) ss);
    check_k sg ks nk g (tapps (TCon tq kl) ss) KType;
    kinst_brs_labels ks bs;
    introduce forall (c: qname). L.mem c cs ==>
      (match sg.ctors c with Some ci -> L.length kl == ci.ct_nk | None -> False)
    with introduce _ ==> _
    with ctor_nk_of_data sg g tq kl ss cs c;
    TD_SwitchCtorDef tq (kinst_kinds ks kl) (kinst_tys ks ss) cs (occ_typing_kinst' ho ks nk) () () ()
      (ctor_brs_typing_kinst' hbr ks nk) (dt_typing_kinst' hdf ks nk)
  | TD_SwitchLit #_ #_ #_ #_ #_ #o #bs #df #t_o #_ #_ lq ho _ _ hbr hdf ->
    ty_eq_kinst ks t_o (TCon lq []);
    kinst_brs_labels ks bs;
    let hbr' = lit_brs_typing_kinst' hbr ks nk in
    TD_SwitchLit lq (occ_typing_kinst' ho ks nk) () () hbr' (dt_typing_kinst' hdf ks nk)
  | TD_SwitchKey #_ #_ #_ #_ #_ #o #bs #t_o #_ #_ vr kts ho _ _ _ hbr ->
    kinst_t_variant ks vr;
    ty_eq_kinst ks t_o (t_variant vr);
    check_k sg ks nk g vr (KRow EType);
    kinst_brs_labels ks bs;
    key_split_kinst ks vr kts TRowEmpty;
    TD_SwitchKey (kinst_ty ks vr) (kinst_layout ks kts) (occ_typing_kinst' ho ks nk) () () ()
      (key_brs_typing_kinst' hbr ks nk)
  | TD_SwitchKeyDef #_ #_ #_ #_ #_ #o #bs #df #t_o #_ #_ vr vr' kts ho _ _ _ hbr hdf ->
    kinst_t_variant ks vr;
    kinst_t_variant ks vr';
    ty_eq_kinst ks t_o (t_variant vr);
    check_k sg ks nk g vr (KRow EType);
    check_k sg ks nk g vr' (KRow EType);
    kinst_brs_labels ks bs;
    key_split_kinst ks vr kts vr';
    let hdf' = cast_dt (dt_typing_kinst' hdf ks nk)
      ((o, t_variant (kinst_ty ks vr')) :: kinst_octx ks om) (kinst_ty ks t) (kinst_ty ks r) in
    TD_SwitchKeyDef (kinst_ty ks vr) (kinst_ty ks vr') (kinst_layout ks kts)
      (occ_typing_kinst' ho ks nk) () () () (key_brs_typing_kinst' hbr ks nk) hdf'
  | TD_Guard h1 h2 h3 ->
    TD_Guard (typing_kinst' h1 ks nk) (dt_typing_kinst' h2 ks nk) (dt_typing_kinst' h3 ks nk)

and ctor_brs_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kl: list kind) (#ss: list typ) (#cs: list qname) (#bs: list (qname & dtree))
  (#t #r: typ) (h: ctor_brs_typing sg ln g d om o kl ss cs bs t r) (ks: list kind) (nk: nat)
  : Pure (ctor_brs_typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_octx ks om) o
            (kinst_kinds ks kl) (kinst_tys ks ss) cs (kinst_brs ks bs) (kinst_ty ks t)
            (kinst_ty ks r))
         (requires pre sg ks nk g /\
                   (forall (c: qname). L.mem c cs ==>
                      (match sg.ctors c with Some ci -> L.length kl == ci.ct_nk | None -> False)))
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCB_Nil _ ->
    check_k sg ks nk g t KType; check_k sg ks nk g r (KRow EEffect);
    TCB_Nil ()
  | TCB_Cons #_ #_ #_ #_ #_ #_ #_ #_ #_ #c #dt0 #bs0 #_ #_ #fs _ hdt h2 ->
    ctor_fields_kinst sg c kl ss fs ks;
    field_occs_k ks o c 0 fs;
    kinst_octx_append ks (field_occs o c 0 fs) om;
    let hdt' = cast_dt (dt_typing_kinst' hdt ks nk)
                 (L.append (field_occs o c 0 (kinst_tys ks fs)) (kinst_octx ks om))
                 (kinst_ty ks t) (kinst_ty ks r) in
    TCB_Cons #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_octx ks om) #o
      #(kinst_kinds ks kl) #(kinst_tys ks ss) #cs #c #(kinst_dt ks dt0) #(kinst_brs ks bs0)
      #(kinst_ty ks t) #(kinst_ty ks r) #(kinst_tys ks fs) () hdt' (ctor_brs_typing_kinst' h2 ks nk)

and lit_brs_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#lt: typ) (#bs: list (lit & dtree)) (#t #r: typ)
  (h: lit_brs_typing sg ln g d om lt bs t r) (ks: list kind) (nk: nat)
  : Pure (lit_brs_typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_octx ks om)
            (kinst_ty ks lt) (kinst_brs ks bs) (kinst_ty ks t) (kinst_ty ks r))
         (requires pre sg ks nk g) (ensures fun _ -> True) (decreases h) =
  match h with
  | TLB_Nil _ ->
    check_k sg ks nk g t KType; check_k sg ks nk g r (KRow EEffect);
    TLB_Nil ()
  | TLB_Cons #_ #_ #_ #_ #_ #_ #c #_ #_ #_ #_ _ hdt h2 ->
    kinst_lit_type ks c;
    ty_eq_kinst ks (lit_type c) lt;
    TLB_Cons #sg #ln #(kinst_ctx ks nk g) #(kinst_jctx ks d) #(kinst_octx ks om) #(kinst_ty ks lt)
      #c () (dt_typing_kinst' hdt ks nk) (lit_brs_typing_kinst' h2 ks nk)

and key_brs_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#d: jctx) (#om: octx)
  (#o: occ) (#kts: list (key & typ)) (#bs: list (key & dtree)) (#t #r: typ)
  (h: key_brs_typing sg ln g d om o kts bs t r) (ks: list kind) (nk: nat)
  : Pure (key_brs_typing sg ln (kinst_ctx ks nk g) (kinst_jctx ks d) (kinst_octx ks om) o
            (kinst_layout ks kts) (kinst_brs ks bs) (kinst_ty ks t) (kinst_ty ks r))
         (requires pre sg ks nk g) (ensures fun _ -> True) (decreases h) =
  match h with
  | TKB_Nil _ ->
    check_k sg ks nk g t KType; check_k sg ks nk g r (KRow EEffect);
    TKB_Nil ()
  | TKB_Cons #_ #_ #_ #_ #_ #_ #k #pt #_ #_ #_ #_ #_ _ hdt h2 ->
    check_k sg ks nk g pt KType;
    TKB_Cons () (dt_typing_kinst' hdt ks nk) (key_brs_typing_kinst' h2 ks nk)

and clauses_typing_kinst' (#sg: sig) (#ln: lctx) (#g: ctx) (#ei: effect_info) (#ts: list typ)
  (#r #b: typ) (#cs: list clause) (h: clauses_typing sg ln g ei ts r b cs) (q: qname)
  (ks: list kind) (nk: nat)
  : Pure (clauses_typing sg ln (kinst_ctx ks nk g) ei (kinst_tys ks ts) (kinst_ty ks r)
            (kinst_ty ks b) (kinst_cls ks cs))
         (requires pre sg ks nk g /\ sg.effects q == Some ei)
         (ensures fun _ -> True) (decreases h) =
  match h with
  | TCL_Nil _ ->
    check_k sg ks nk g b KType; check_k sg ks nk g r (KRow EEffect);
    TCL_Nil ()
  | TCL_Full #_ #_ #_ #_ #_ #_ #_ #op #nb #s #kt #body #cs0 #os _ _ _ hb hcs ->
    let gb = push_tvars g os.binders in
    let gk = kinst_ctx ks nk g in
    effect_kinds_closed sg q ei op os;
    kinst_kinds_closed ks os.binders;
    kinst_ctx_push_tvars ks nk g os.binders;
    op_types_closed sg q ei op os;
    eff_inst_kinst ks nb ts os.arg;
    eff_inst_kinst ks nb ts os.res;
    check_k sg ks nk gb s KType;
    ty_eq_kinst ks s (eff_inst nb ts os.arg);
    check_k sg ks nk gb kt KType;
    ty_eq_kinst ks kt (t_fun (eff_inst nb ts os.res) (ren_ty (shift nb) r) (ren_ty (shift nb) b));
    kinst_t_fun ks (eff_inst nb ts os.res) (ren_ty (shift nb) r) (ren_ty (shift nb) b);
    kinst_ren_ty ks (shift nb) r;
    kinst_ren_ty ks (shift nb) b;
    kinst_ctx_push_var ks nk gb s;
    kinst_ctx_push_var ks nk (push_var gb s) kt;
    let hb' = cast (typing_kinst' hb ks nk)
                (push_var (push_var (push_tvars gk os.binders) (kinst_ty ks s)) (kinst_ty ks kt)) []
                (kinst_exp ks body) (ren_ty (shift nb) (kinst_ty ks b))
                (ren_ty (shift nb) (kinst_ty ks r)) in
    TCL_Full #sg #ln #gk #ei #(kinst_tys ks ts) #(kinst_ty ks r) #(kinst_ty ks b) #op #nb
      #(kinst_ty ks s) #(kinst_ty ks kt) #(kinst_exp ks body) #(kinst_cls ks cs0) #os () () () hb'
      (clauses_typing_kinst' hcs q ks nk)
  | TCL_Fast #_ #_ #_ #_ #_ #_ #_ #op #nb #s #body #cs0 #os _ _ hb hcs ->
    let gb = push_tvars g os.binders in
    let gk = kinst_ctx ks nk g in
    effect_kinds_closed sg q ei op os;
    kinst_kinds_closed ks os.binders;
    kinst_ctx_push_tvars ks nk g os.binders;
    op_types_closed sg q ei op os;
    eff_inst_kinst ks nb ts os.arg;
    eff_inst_kinst ks nb ts os.res;
    check_k sg ks nk gb s KType;
    ty_eq_kinst ks s (eff_inst nb ts os.arg);
    kinst_ren_ty ks (shift nb) r;
    kinst_ctx_push_var ks nk gb s;
    let hb' = cast (typing_kinst' hb ks nk) (push_var (push_tvars gk os.binders) (kinst_ty ks s)) []
                (kinst_exp ks body) (eff_inst nb (kinst_tys ks ts) os.res)
                (ren_ty (shift nb) (kinst_ty ks r)) in
    TCL_Fast #sg #ln #gk #ei #(kinst_tys ks ts) #(kinst_ty ks r) #(kinst_ty ks b) #op #nb
      #(kinst_ty ks s) #(kinst_exp ks body) #(kinst_cls ks cs0) #os () () hb'
      (clauses_typing_kinst' hcs q ks nk)

and occ_typing_kinst' (#sg: sig) (#g: ctx) (#om: octx) (#o: occ) (#t: typ)
  (h: occ_typing sg g om o t) (ks: list kind) (nk: nat)
  : Pure (occ_typing sg (kinst_ctx ks nk g) (kinst_octx ks om) o (kinst_ty ks t))
         (requires pre sg ks nk g) (ensures fun _ -> True) (decreases h) =
  match h with
  | TO_Lookup _ -> assoc_kinst_octx ks om o; TO_Lookup ()
  | TO_Field #_ #_ #_ #o0 #k #t_o #_ r0 ho _ _ ->
    kinst_t_record ks r0;
    ty_eq_kinst ks t_o (t_record r0);
    check_k sg ks nk g r0 (KRow EType);
    check_k sg ks nk g t KType;
    entries_kinst_ty ks r0 k t;
    TO_Field #sg #(kinst_ctx ks nk g) #(kinst_octx ks om) #o0 #k #(kinst_ty ks t_o) #(kinst_ty ks t)
      (kinst_ty ks r0) (occ_typing_kinst' ho ks nk) () ()

(* The stated theorems. *)

let occ_typing_kinst #sg #g #om #o #t h ks nk' = occ_typing_kinst' h ks nk'

let typing_kinst #sg #ln #g #d #e #t #r h ks nk' = typing_kinst' h ks nk'

let exps_typing_kinst #sg #ln #g #d #r #es #ts h ks nk' = exps_typing_kinst' h ks nk'

let chain_typing_kinst #sg #ln #g #d #r #e h ks nk' = chain_typing_kinst' h ks nk'

let binds_typing_kinst #sg #ln #g #bs h ks nk' = binds_typing_kinst' h ks nk'

let cells_typing_kinst #sg #ln #g #cells #lay h ks nk' = cells_typing_kinst' h ks nk'

let match_typing_kinst #sg #ln #g #d #r #th #om h ks nk' = match_typing_kinst' h ks nk'

let dt_typing_kinst #sg #ln #g #d #om #dt #t #r h ks nk' = dt_typing_kinst' h ks nk'

let ctor_brs_typing_kinst #sg #ln #g #d #om #o #kl #ss #cs #bs #t #r h ks nk' =
  ctor_brs_typing_kinst' h ks nk'

let lit_brs_typing_kinst #sg #ln #g #d #om #lt #bs #t #r h ks nk' =
  lit_brs_typing_kinst' h ks nk'

let key_brs_typing_kinst #sg #ln #g #d #om #o #kts #bs #t #r h ks nk' =
  key_brs_typing_kinst' h ks nk'

let clauses_typing_kinst #sg #ln #g #ei #ts #r #b #cs h q ks nk' = clauses_typing_kinst' h q ks nk'

(* Unfolding a global. *)

let typing_decl_kinst #sg #ln #nk #v #t h ks nk' =
  kinst_decl_ctx ks nk' nk;
  typing_kinst' h ks nk'

let decl_ren_ok (n: nat) (g: ctx) : Lemma (requires g.nk == n) (ensures ty_ren_ok id_ren (decl_ctx n) g) =
  ()

let typing_global_unfold #sg #ln #nk #v #t h ks g =
  let h1 = typing_decl_kinst h ks g.nk in
  decl_ren_ok g.nk g;
  let h2 = typing_ren_ty h1 id_ren g in
  ren_ty_exp_id (kinst_exp ks v);
  ren_ty_id (kinst_ty ks t);
  h2
