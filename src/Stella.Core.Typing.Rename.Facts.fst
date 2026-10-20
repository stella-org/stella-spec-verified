(* Proof structure.

   Lists and layouts: induction on the list. Binders: the σ-calculus laws of
   `Stella.Core.Subst.Lemmas.Typ`. Rows: canonicalization commutes with
   renaming (`canon_ren`), and the view of a renamed row holds the images of
   the entries (`cren_view`); known keys go through the substitution case.
   Declared types are kinded with no type variable in scope, so every
   substitution fixes them and their instances at kinds (`sub_tvs_below`).

   Region names: a mutual induction over the term classes, as the maps
   themselves are defined. Values: by induction on the value; a chain is
   read through its view, which a type substitution and a term renaming
   map argument by argument, and whose cursor reaches the same remainder,
   since the cursor reads the declared type and the shape of the
   arguments. *)
module Stella.Core.Typing.Rename.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Subst.Lemmas.TyExp
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.OrdSet
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Facts
open Stella.Core.Spine
open Stella.Core.Spine.Lemmas
open Stella.Core.Spine.Wf
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing.Ops
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

(* Lists and layouts. *)

let rec ren_layout_snd xi l =
  match l with
  | [] -> ()
  | _ :: l -> ren_layout_snd xi l

let rec ren_layout_assoc (xi: ren) (l: layout) (k: key)
  : Lemma (ensures L.assoc k (ren_layout xi l) == map_opt (ren_ty xi) (L.assoc k l)) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> ren_layout_assoc xi l k

let ren_layout_row xi l =
  brs_row_empty l;
  brs_row_empty (ren_layout xi l);
  ren_brs_row xi l TRowEmpty

let rec ren_ty_binds_fst xi bs =
  match bs with
  | [] -> ()
  | _ :: bs -> ren_ty_binds_fst xi bs

let rec ren_tm_binds_fst xi bs =
  match bs with
  | [] -> ()
  | _ :: bs -> ren_tm_binds_fst xi bs

let rec ren_tapps (xi: ren) (h: typ) (ts: list typ)
  : Lemma (ensures ren_ty xi (tapps h ts) == tapps (ren_ty xi h) (ren_tys xi ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> ren_tapps xi (TApp h t) ts

(* Types of `Prim`. *)

let ren_app3 (xi: ren) (h a b c: typ)
  : Lemma (ren_ty xi (TApp (TApp (TApp h a) b) c) ==
           TApp (TApp (TApp (ren_ty xi h) (ren_ty xi a)) (ren_ty xi b)) (ren_ty xi c)) =
  assert (ren_ty xi (TApp h a) == TApp (ren_ty xi h) (ren_ty xi a));
  assert (ren_ty xi (TApp (TApp h a) b) == TApp (ren_ty xi (TApp h a)) (ren_ty xi b))

let ren_t_fun xi t1 r t2 = ren_app3 xi (TCon prim_function []) t1 r t2

let ren_t_record xi r = ()

let ren_t_variant xi r = ()

let ren_lit_type xi c = ()

(* Binders. *)

let ren_subst1 xi s t =
  let th1 (i: nat) : typ = ren_ty xi (scons s tvar i) in
  ren_sub_ty xi (scons s tvar) th1 t;
  let th2 (i: nat) : typ = scons (ren_ty xi s) tvar (up_ren xi i) in
  sub_ren_ty (scons (ren_ty xi s) tvar) (up_ren xi) th2 t;
  sub_ty_ext th1 th2 t

let ren_shift_up n xi t =
  let th = ren_shift n xi in
  ren_ren_ty (upn_ren n xi) (shift n) th t;
  ren_ren_ty (shift n) xi th t

let ren_layout_shift_up n xi l =
  let th = ren_shift n xi in
  ren_ren_layout (upn_ren n xi) (shift n) th l;
  ren_ren_layout (shift n) xi th l

(* Rows. *)

let rec ty_head_ren xi t =
  match t with
  | TApp f _ -> ty_head_ren xi f
  | _ -> ()

let known_keys_ren xi t k =
  ren_ty_as_sub xi t;
  known_keys_sub (ren_tsub xi) k t

let entries_ren xi t e =
  canon_ren xi t;
  cren_view xi (canon t);
  LP.mem_memP e (row_entries (canon t));
  LP.memP_map_intro (cren_ent xi) e (row_entries (canon t));
  LP.mem_memP (cren_ent xi e) (L.map (cren_ent xi) (row_entries (canon t)));
  let v = rop (cren_ent xi) (cren_vf xi) (view_row (canon t)) in
  LP.append_mem (L.map (cren_ent xi) (row_entries (canon t)))
    (flat_es (L.map (cren_vf xi) (snd (view_row (canon t))))) (cren_ent xi e);
  assert (L.mem (cren_ent xi e) (fst v))

let entries_ren_ty xi r k t =
  entries_ren xi r (k, PTy (canon t));
  canon_ren xi t

let entries_ren_eff xi r k q ts =
  entries_ren xi r (k, PEff q (canon_tys ts));
  canon_ren_tys xi ts

(* Declared types. *)

let global_scheme_closed (sg: sig) (q: qname) (nk: nat) (t: typ)
  : Lemma (requires sig_wf sg /\ global_type sg q == Some (nk, t)) (ensures tvs_below 0 t) =
  (match sg.ctors q, sg.foreigns q, sg.values q with
   | Some ci, None, None -> assert (scheme_ok sg ci.ct_nk ci.ct_ty)
   | None, Some fi, None -> assert (scheme_ok sg fi.fr_nk fi.fr_ty)
   | None, None, Some vi -> assert (scheme_ok sg vi.vl_nk vi.vl_ty));
  check_tvs_below sg (decl_ctx nk) t KType

let closed_ren (xi: ren) (t: typ) : Lemma (requires tvs_below 0 t) (ensures ren_ty xi t == t) =
  ren_ty_as_sub xi t;
  sub_tvs_below 0 (ren_tsub xi) t

let global_inst_ren sg q nk t ks xi =
  global_scheme_closed sg q nk t;
  kinst_tvs_below ks 0 t;
  closed_ren xi (kinst_ty ks t)

let rec inst_foralls_ren (xi: ren) (t: typ) (ss: list typ)
  : Lemma (ensures inst_foralls (ren_ty xi t) (ren_tys xi ss)
      == map_opt (ren_ty xi) (inst_foralls t ss))
          (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' ->
    (match t with
     | TForall _ b -> ren_subst1 xi s b; inst_foralls_ren xi (subst1_ty s b) ss'
     | _ -> ())

let rec fun_args_ren (sg: sig) (xi: ren) (t: typ)
  : Lemma (ensures fun_args sg (ren_ty xi t) == ren_tys xi (fun_args sg t)) (decreases t) =
  match t with
  | TApp (TApp (TApp h t1) r) t2 ->
    ren_app3 xi h t1 r t2;
    (match h with
     | TCon q [] -> fun_args_ren sg xi t2
     | _ -> ())
  | TApp (TApp h a) b ->
    assert (ren_ty xi (TApp h a) == TApp (ren_ty xi h) (ren_ty xi a))
  | _ -> ()

let ctor_fields_ren sg c ks ss xi =
  match sg.ctors c with
  | Some ci ->
    assert (scheme_ok sg ci.ct_nk ci.ct_ty);
    check_tvs_below sg (decl_ctx ci.ct_nk) ci.ct_ty KType;
    kinst_tvs_below ks 0 ci.ct_ty;
    closed_ren xi (kinst_ty ks ci.ct_ty);
    inst_foralls_ren xi (kinst_ty ks ci.ct_ty) ss;
    (match inst_foralls (kinst_ty ks ci.ct_ty) ss with
     | Some t -> fun_args_ren sg xi t
     | None -> ())
  | None -> ()

let rec check_tys_length (sg: sig) (g: ctx) (ts: list typ) (ks: list kind)
  : Lemma (requires check_tys sg g ts ks) (ensures L.length ts == L.length ks) (decreases ts) =
  match ts, ks with
  | [], [] -> ()
  | _ :: ts, _ :: ks -> check_tys_length sg g ts ks

let op_inst_ren_sig sg q ei op os ts ss xi =
  op_types_closed sg q ei op os;
  op_inst_ren xi ts ss os.arg;
  op_inst_ren xi ts ss os.res

let eff_inst_ren_sig sg q ei op os ts xi =
  op_types_closed sg q ei op os;
  let m = L.length os.binders in
  eff_inst_ren xi m ts os.arg;
  eff_inst_ren xi m ts os.res

(* Region names. *)

let rec frn_ren_ty xi t =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 | TRowUnion t1 t2 -> frn_ren_ty xi t1; frn_ren_ty xi t2
  | TForall _ b -> frn_ren_ty (up_ren xi) b
  | TConstr c b -> frn_ren_constr xi c; frn_ren_ty xi b
  | TRowExt en r -> frn_ren_ent xi en; frn_ren_ty xi r

and frn_ren_ent (xi: ren) (en: entry) : Lemma (ensures frn_ent (ren_ent xi en) == frn_ent en)
  (decreases en) =
  match en with
  | EntTy _ t -> frn_ren_ty xi t
  | EntEff _ _ ts -> frn_ren_tys xi ts
  | EntRegion _ -> ()

and frn_ren_constr (xi: ren) (c: constr) : Lemma
  (ensures frn_constr (ren_constr xi c) == frn_constr c)
  (decreases c) =
  match c with
  | CLacks _ t -> frn_ren_ty xi t
  | CDisj t1 t2 -> frn_ren_ty xi t1; frn_ren_ty xi t2

and frn_ren_tys (xi: ren) (ts: list typ) : Lemma (ensures frn_tys (ren_tys xi ts) == frn_tys ts)
  (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> frn_ren_ty xi t; frn_ren_tys xi ts

let rec frn_ren_layout (xi: ren) (l: layout)
  : Lemma (ensures frn_layout (ren_layout xi l) == frn_layout l) (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> frn_ren_ty xi t; frn_ren_layout xi l

let rec frn_ren_ty_exp xi e =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> frn_ren_ty xi t; frn_ren_ty xi r; frn_ren_ty_exp xi b
  | EApp e1 e2 | EMerge e1 e2 -> frn_ren_ty_exp xi e1; frn_ren_ty_exp xi e2
  | ETyLam _ b -> frn_ren_ty_exp (up_ren xi) b
  | ETyApp b t -> frn_ren_ty_exp xi b; frn_ren_ty xi t
  | ECLam c b -> frn_ren_constr xi c; frn_ren_ty_exp xi b
  | ECApp b | ESelect _ b | ERestrict _ b | EWriteCell _ _ b | EFill _ b -> frn_ren_ty_exp xi b
  | ELet t e1 e2 -> frn_ren_ty xi t; frn_ren_ty_exp xi e1; frn_ren_ty_exp xi e2
  | ELetRec bs b -> frn_ren_ty_binds xi bs; frn_ren_ty_exp xi b
  | ECase es dt | EMatch es dt -> frn_ren_ty_exps xi es; frn_ren_ty_dt xi dt
  | ELetJoin ts t e1 e2 ->
    frn_ren_tys xi ts; frn_ren_ty xi t; frn_ren_ty_exp xi e1; frn_ren_ty_exp xi e2
  | EJump _ es -> frn_ren_ty_exps xi es
  | EExtend _ e1 e2 | EUpdate _ e1 e2 -> frn_ren_ty_exp xi e1; frn_ren_ty_exp xi e2
  | EInject _ t b | EWeaken _ t b | EAbsurd t b | EOpenEff t b | EOpenEffC t b ->
    frn_ren_ty xi t; frn_ren_ty_exp xi b
  | EPerform _ _ ts b -> frn_ren_tys xi ts; frn_ren_ty_exp xi b
  | EHandle b h ->
    frn_ren_ty_exp xi b; frn_ren_ent xi h.h_ent; frn_ren_ty xi h.h_ret_ty;
    frn_ren_ty_exp xi h.h_ret; frn_ren_ty_cls xi h.h_clauses
  | ERegion l es b -> frn_ren_layout xi l; frn_ren_ty_exps xi es; frn_ren_ty_exp xi b
  | ERegionOpen _ th b -> frn_ren_ty_cells xi th; frn_ren_ty_exp xi b
  | EOpaque _ t -> frn_ren_ty xi t

and frn_ren_ty_exps (xi: ren) (es: list exp)
  : Lemma (ensures frn_exps (ren_ty_exps xi es) == frn_exps es) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> frn_ren_ty_exp xi e; frn_ren_ty_exps xi es

and frn_ren_ty_binds (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures frn_binds (ren_ty_binds xi bs) == frn_binds bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> frn_ren_ty xi t; frn_ren_ty_exp xi e; frn_ren_ty_binds xi bs

and frn_ren_ty_cells (xi: ren) (th: list (key & exp))
  : Lemma (ensures frn_cells (ren_ty_cells xi th) == frn_cells th) (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> frn_ren_ty_exp xi e; frn_ren_ty_cells xi th

and frn_ren_ty_dt (xi: ren) (dt: dtree)
  : Lemma (ensures frn_dt (ren_ty_dt xi dt) == frn_dt dt) (decreases dt) =
  match dt with
  | DLeaf e -> frn_ren_ty_exp xi e
  | DBind _ dt -> frn_ren_ty_dt xi dt
  | DSwitchCtor _ bs df -> frn_ren_ty_brs xi bs; frn_ren_ty_odt xi df
  | DSwitchLit _ bs df -> frn_ren_ty_brs xi bs; frn_ren_ty_dt xi df
  | DSwitchKey _ bs df -> frn_ren_ty_kbrs xi bs; frn_ren_ty_odt xi df
  | DGuard e dt1 dt2 -> frn_ren_ty_exp xi e; frn_ren_ty_dt xi dt1; frn_ren_ty_dt xi dt2

and frn_ren_ty_odt (xi: ren) (df: option dtree)
  : Lemma (ensures frn_odt (ren_ty_odt xi df) == frn_odt df) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> frn_ren_ty_dt xi dt

and frn_ren_ty_brs (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Lemma (ensures frn_brs (ren_ty_brs xi bs) == frn_brs bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> frn_ren_ty_dt xi dt; frn_ren_ty_brs xi bs

and frn_ren_ty_kbrs (xi: ren) (bs: list (key & dtree))
  : Lemma (ensures frn_kbrs (ren_ty_brs xi bs) == frn_kbrs bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> frn_ren_ty_dt xi dt; frn_ren_ty_kbrs xi bs

and frn_ren_ty_cls (xi: ren) (cs: list clause)
  : Lemma (ensures frn_cls (ren_ty_cls xi cs) == frn_cls cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ nb s kt b :: cs ->
    frn_ren_ty (upn_ren nb xi) s; frn_ren_ty (upn_ren nb xi) kt;
    frn_ren_ty_exp (upn_ren nb xi) b; frn_ren_ty_cls xi cs
  | CFast _ nb s b :: cs ->
    frn_ren_ty (upn_ren nb xi) s; frn_ren_ty_exp (upn_ren nb xi) b; frn_ren_ty_cls xi cs

let rec frn_ren_tm xi e =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ | EOpaque _ _ -> ()
  | ELam _ _ b -> frn_ren_tm (up_ren xi) b
  | EApp e1 e2 | EMerge e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 ->
    frn_ren_tm xi e1; frn_ren_tm xi e2
  | ETyLam _ b | ETyApp b _ | ECLam _ b | ECApp b | ESelect _ b | ERestrict _ b
  | EInject _ _ b | EWeaken _ _ b | EAbsurd _ b | EPerform _ _ _ b | EOpenEff _ b
  | EWriteCell _ _ b | EOpenEffC _ b | EFill _ b -> frn_ren_tm xi b
  | ELet _ e1 e2 -> frn_ren_tm xi e1; frn_ren_tm (up_ren xi) e2
  | ELetRec bs b ->
    frn_ren_tm_binds (upn_ren (L.length bs) xi) bs; frn_ren_tm (upn_ren (L.length bs) xi) b
  | ECase es dt | EMatch es dt -> frn_ren_tm_exps xi es; frn_ren_tm_dt xi dt
  | ELetJoin ts _ e1 e2 -> frn_ren_tm (upn_ren (L.length ts) xi) e1; frn_ren_tm xi e2
  | EJump _ es -> frn_ren_tm_exps xi es
  | EHandle b h ->
    frn_ren_tm xi b; frn_ren_tm (up_ren xi) h.h_ret; frn_ren_tm_cls xi h.h_clauses
  | ERegion _ es b -> frn_ren_tm_exps xi es; frn_ren_tm xi b
  | ERegionOpen _ th b -> frn_ren_tm_cells xi th; frn_ren_tm xi b

and frn_ren_tm_exps (xi: ren) (es: list exp)
  : Lemma (ensures frn_exps (ren_tm_exps xi es) == frn_exps es) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> frn_ren_tm xi e; frn_ren_tm_exps xi es

and frn_ren_tm_binds (xi: ren) (bs: list (typ & exp))
  : Lemma (ensures frn_binds (ren_tm_binds xi bs) == frn_binds bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, e) :: bs -> frn_ren_tm xi e; frn_ren_tm_binds xi bs

and frn_ren_tm_cells (xi: ren) (th: list (key & exp))
  : Lemma (ensures frn_cells (ren_tm_cells xi th) == frn_cells th) (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> frn_ren_tm xi e; frn_ren_tm_cells xi th

and frn_ren_tm_dt (xi: ren) (dt: dtree)
  : Lemma (ensures frn_dt (ren_tm_dt xi dt) == frn_dt dt) (decreases dt) =
  match dt with
  | DLeaf e -> frn_ren_tm xi e
  | DBind _ dt -> frn_ren_tm_dt (up_ren xi) dt
  | DSwitchCtor _ bs df -> frn_ren_tm_brs xi bs; frn_ren_tm_odt xi df
  | DSwitchLit _ bs df -> frn_ren_tm_brs xi bs; frn_ren_tm_dt xi df
  | DSwitchKey _ bs df -> frn_ren_tm_kbrs xi bs; frn_ren_tm_odt xi df
  | DGuard e dt1 dt2 -> frn_ren_tm xi e; frn_ren_tm_dt xi dt1; frn_ren_tm_dt xi dt2

and frn_ren_tm_odt (xi: ren) (df: option dtree)
  : Lemma (ensures frn_odt (ren_tm_odt xi df) == frn_odt df) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> frn_ren_tm_dt xi dt

and frn_ren_tm_brs (#lb: eqtype) (xi: ren) (bs: list (lb & dtree))
  : Lemma (ensures frn_brs (ren_tm_brs xi bs) == frn_brs bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> frn_ren_tm_dt xi dt; frn_ren_tm_brs xi bs

and frn_ren_tm_kbrs (xi: ren) (bs: list (key & dtree))
  : Lemma (ensures frn_kbrs (ren_tm_brs xi bs) == frn_kbrs bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> frn_ren_tm_dt xi dt; frn_ren_tm_kbrs xi bs

and frn_ren_tm_cls (xi: ren) (cs: list clause)
  : Lemma (ensures frn_cls (ren_tm_cls xi cs) == frn_cls cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ _ _ b :: cs -> frn_ren_tm (upn_ren 2 xi) b; frn_ren_tm_cls xi cs
  | CFast _ _ _ b :: cs -> frn_ren_tm (up_ren xi) b; frn_ren_tm_cls xi cs

(* Values under a type substitution. *)

let rec ren_ty_exps_as_sub (xi: ren) (es: list exp)
  : Lemma (ensures ren_ty_exps xi es == sub_ty_exps (ren_tsub xi) es) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> ren_ty_exp_as_sub xi e; ren_ty_exps_as_sub xi es

let rec value_form_sub_ty sg sigma e : Lemma
  (ensures value_form sg (sub_ty_exp sigma e) == value_form sg e)
  (decreases %[e; 1]) =
  match e with
  | ETyLam _ v -> value_form_sub_ty sg (up_tsub sigma) v
  | ECLam _ v | EInject _ _ v -> value_form_sub_ty sg sigma v
  | EExtend _ v1 v2 -> value_form_sub_ty sg sigma v1; value_form_sub_ty sg sigma v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ctor_chain_form_sub_ty sg sigma e
  | _ -> ()

and ctor_chain_form_sub_ty (sg: sig) (sigma: tsub) (e: exp)
  : Lemma (ensures ctor_chain_form sg (sub_ty_exp sigma e) == ctor_chain_form sg e)
          (decreases %[e; 0]) =
  match e with
  | EApp f v -> ctor_chain_form_sub_ty sg sigma f; value_form_sub_ty sg sigma v
  | ETyApp f _ | ECApp f -> ctor_chain_form_sub_ty sg sigma f
  | _ -> ()

(* The cursor reaches the same remainder whatever the type arguments and
   the accumulated substitution are. *)
let same_rem (o1 o2: option (typ & tsub)) : prop =
  match o1, o2 with
  | Some (t1, _), Some (t2, _) -> t1 == t2
  | None, None -> True
  | _ -> False

let rec cursor_sub_rem (sg: sig) (sigma: tsub) (t: typ) (th th': tsub) (args: list spine_arg)
  : Lemma (ensures same_rem (cursor sg t th (L.map (sub_arg sigma) args)) (cursor sg t th' args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: args' ->
    match cursor_step sg t th (sub_arg sigma a), cursor_step sg t th' a with
    | Some (t1, th1), Some (_, th1') -> cursor_sub_rem sg sigma t1 th1 th1' args'
    | _ -> ()

let spine_unsaturated_sub (sg: sig) (sigma: tsub) (q: qname) (ks: list kind) (args: list spine_arg)
  : Lemma (spine_unsaturated sg q ks (L.map (sub_arg sigma) args)
      == spine_unsaturated sg q ks args) =
  match global_scheme sg q with
  | Some (_, nk, t)
    -> if L.length ks = nk then cursor_sub_rem sg sigma (kinst_ty ks t) tvar tvar args
  | None -> ()

let value_head_sub_ty (sg: sig) (sigma: tsub) (e: exp)
  : Lemma (V.value_head sg (sub_ty_exp sigma e) == V.value_head sg e) =
  decompose_sub_ty_exp sigma e;
  match decompose_global_app e with
  | Some (q, ks, args) -> spine_unsaturated_sub sg sigma q ks args
  | None -> ()

let rec is_value_sub_ty sg sigma e : Lemma
  (ensures V.is_value sg (sub_ty_exp sigma e) == V.is_value sg e)
  (decreases %[e; 1]) =
  match e with
  | ETyLam _ v -> is_value_sub_ty sg (up_tsub sigma) v
  | ECLam _ v | EInject _ _ v | EWeaken _ _ v | EOpenEff _ v -> is_value_sub_ty sg sigma v
  | EExtend _ v1 v2 -> is_value_sub_ty sg sigma v1; is_value_sub_ty sg sigma v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ ->
    value_head_sub_ty sg sigma e; chain_values_sub_ty sg sigma e
  | _ -> ()

and chain_values_sub_ty (sg: sig) (sigma: tsub) (e: exp)
  : Lemma (ensures V.chain_values sg (sub_ty_exp sigma e) == V.chain_values sg e)
          (decreases %[e; 0]) =
  match e with
  | EApp f v -> chain_values_sub_ty sg sigma f; is_value_sub_ty sg sigma v
  | ETyApp f _ | ECApp f -> chain_values_sub_ty sg sigma f
  | _ -> ()

let rec values_sub_ty (sg: sig) (sigma: tsub) (es: list exp)
  : Lemma (ensures L.for_all (V.is_value sg) (sub_ty_exps sigma es) == L.for_all (V.is_value sg) es)
    (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> is_value_sub_ty sg sigma e; values_sub_ty sg sigma es

let rec nth_sub_ty_exps (sigma: tsub) (es: list exp) (i: nat)
  : Lemma (ensures L.nth (sub_ty_exps sigma es) i == map_opt (sub_ty_exp sigma) (L.nth es i))
          (decreases es) =
  match es with
  | [] -> ()
  | _ :: es -> if i = 0 then () else nth_sub_ty_exps sigma es (i - 1)

let rec value_args_sub (sigma: tsub) (args: list spine_arg)
  : Lemma (ensures value_args (L.map (sub_arg sigma) args) == sub_ty_exps sigma (value_args args))
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: args -> value_args_sub sigma args

let rec record_field_sub (sigma: tsub) (k: key) (v: exp)
  : Lemma (ensures record_field k (sub_ty_exp sigma v)
      == map_opt (sub_ty_exp sigma) (record_field k v))
          (decreases v) =
  match v with
  | EExtend _ _ v2 -> record_field_sub sigma k v2
  | _ -> ()

let rec variant_payload_sub (sigma: tsub) (k: key) (v: exp)
  : Lemma (ensures variant_payload k (sub_ty_exp sigma v) ==
                   map_opt (sub_ty_exp sigma) (variant_payload k v))
          (decreases v) =
  match v with
  | EWeaken _ _ v1 -> variant_payload_sub sigma k v1
  | _ -> ()

let ctor_field_sub (sg: sig) (sigma: tsub) (q: qname) (j: nat) (v: exp)
  : Lemma (ctor_field sg q j (sub_ty_exp sigma v)
      == map_opt (sub_ty_exp sigma) (ctor_field sg q j v)) =
  decompose_sub_ty_exp sigma v;
  match decompose_global_app v with
  | Some (_, _, args) -> value_args_sub sigma args; nth_sub_ty_exps sigma (value_args args) j
  | None -> ()

let rec proj_sub_ty (sg: sig) (sigma: tsub) (th: list exp) (o: occ)
  : Lemma (ensures proj sg (sub_ty_exps sigma th) o == map_opt (sub_ty_exp sigma) (proj sg th o))
    (decreases o) =
  match o with
  | OScrut i -> nth_sub_ty_exps sigma th i
  | OCtor o' q j ->
    proj_sub_ty sg sigma th o';
    (match proj sg th o' with Some v -> ctor_field_sub sg sigma q j v | None -> ())
  | ORecord o' k ->
    proj_sub_ty sg sigma th o';
    (match proj sg th o' with Some v -> record_field_sub sigma k v | None -> ())
  | OVariant o' k ->
    proj_sub_ty sg sigma th o';
    (match proj sg th o' with Some v -> variant_payload_sub sigma k v | None -> ())

let value_form_ren_ty sg xi e = ren_ty_exp_as_sub xi e; value_form_sub_ty sg (ren_tsub xi) e

let is_value_ren_ty sg xi e = ren_ty_exp_as_sub xi e; is_value_sub_ty sg (ren_tsub xi) e

let values_ren_ty sg xi es = ren_ty_exps_as_sub xi es; values_sub_ty sg (ren_tsub xi) es

let proj_ren_ty sg xi th o =
  ren_ty_exps_as_sub xi th;
  proj_sub_ty sg (ren_tsub xi) th o;
  match proj sg th o with
  | Some v -> ren_ty_exp_as_sub xi v
  | None -> ()

let chain_cursor_ren_ty sg xi e t th =
  ren_ty_exp_as_sub xi e;
  chain_cursor_sub_ty sg (ren_tsub xi) e t th;
  ren_ty_as_sub xi (sub_ty th t);
  introduce forall (t1 r t2: typ). as_function sg t == Some (t1, r, t2) ==>
    ren_ty xi (sub_ty th t1) == sub_ty (ren_tsub xi) (sub_ty th t1)
  with ren_ty_as_sub xi (sub_ty th t1);
  introduce forall (c: constr) (b: typ). t == TConstr c b ==>
    ren_constr xi (sub_constr th c) == sub_constr (ren_tsub xi) (sub_constr th c)
  with rinst_constr xi (ren_tsub xi) (sub_constr th c)

(* Values under a term renaming. *)

let rec value_form_ren_tm sg xi e : Lemma (ensures value_form sg (ren_tm xi e) == value_form sg e)
  (decreases %[e; 1]) =
  match e with
  | ETyLam _ v | ECLam _ v | EInject _ _ v -> value_form_ren_tm sg xi v
  | EExtend _ v1 v2 -> value_form_ren_tm sg xi v1; value_form_ren_tm sg xi v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ctor_chain_form_ren_tm sg xi e
  | _ -> ()

and ctor_chain_form_ren_tm (sg: sig) (xi: ren) (e: exp)
  : Lemma (ensures ctor_chain_form sg (ren_tm xi e) == ctor_chain_form sg e) (decreases %[e; 0]) =
  match e with
  | EApp f v -> ctor_chain_form_ren_tm sg xi f; value_form_ren_tm sg xi v
  | ETyApp f _ | ECApp f -> ctor_chain_form_ren_tm sg xi f
  | _ -> ()

let value_head_ren_tm (sg: sig) (xi: ren) (e: exp)
  : Lemma (V.value_head sg (ren_tm xi e) == V.value_head sg e) =
  decompose_ren_tm xi e;
  match decompose_global_app e with
  | Some (q, ks, args) ->
    (match global_scheme sg q with
     | Some (_, nk, t) ->
       if L.length ks = nk then cursor_val_args sg (ren_tm xi) (kinst_ty ks t) tvar args
     | None -> ())
  | None -> ()

let rec is_value_ren_tm sg xi e : Lemma (ensures V.is_value sg (ren_tm xi e) == V.is_value sg e)
  (decreases %[e; 1]) =
  match e with
  | ETyLam _ v | ECLam _ v | EInject _ _ v | EWeaken _ _ v | EOpenEff _ v -> is_value_ren_tm sg xi v
  | EExtend _ v1 v2 -> is_value_ren_tm sg xi v1; is_value_ren_tm sg xi v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ ->
    value_head_ren_tm sg xi e; chain_values_ren_tm sg xi e
  | _ -> ()

and chain_values_ren_tm (sg: sig) (xi: ren) (e: exp)
  : Lemma (ensures V.chain_values sg (ren_tm xi e) == V.chain_values sg e) (decreases %[e; 0]) =
  match e with
  | EApp f v -> chain_values_ren_tm sg xi f; is_value_ren_tm sg xi v
  | ETyApp f _ | ECApp f -> chain_values_ren_tm sg xi f
  | _ -> ()

let rec values_ren_tm (sg: sig) (xi: ren) (es: list exp)
  : Lemma (ensures L.for_all (V.is_value sg) (ren_tm_exps xi es) == L.for_all (V.is_value sg) es)
    (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> is_value_ren_tm sg xi e; values_ren_tm sg xi es

let rec nth_ren_tm_exps (xi: ren) (es: list exp) (i: nat)
  : Lemma (ensures L.nth (ren_tm_exps xi es) i == map_opt (ren_tm xi) (L.nth es i)) (decreases es) =
  match es with
  | [] -> ()
  | _ :: es -> if i = 0 then () else nth_ren_tm_exps xi es (i - 1)

let rec value_args_ren_tm (xi: ren) (args: list spine_arg)
  : Lemma (ensures value_args (L.map (val_arg (ren_tm xi)) args)
      == ren_tm_exps xi (value_args args))
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: args -> value_args_ren_tm xi args

let rec record_field_ren_tm (xi: ren) (k: key) (v: exp)
  : Lemma (ensures record_field k (ren_tm xi v) == map_opt (ren_tm xi) (record_field k v))
          (decreases v) =
  match v with
  | EExtend _ _ v2 -> record_field_ren_tm xi k v2
  | _ -> ()

let rec variant_payload_ren_tm (xi: ren) (k: key) (v: exp)
  : Lemma (ensures variant_payload k (ren_tm xi v) == map_opt (ren_tm xi) (variant_payload k v))
          (decreases v) =
  match v with
  | EWeaken _ _ v1 -> variant_payload_ren_tm xi k v1
  | _ -> ()

let ctor_field_ren_tm (sg: sig) (xi: ren) (q: qname) (j: nat) (v: exp)
  : Lemma (ctor_field sg q j (ren_tm xi v) == map_opt (ren_tm xi) (ctor_field sg q j v)) =
  decompose_ren_tm xi v;
  match decompose_global_app v with
  | Some (_, _, args) -> value_args_ren_tm xi args; nth_ren_tm_exps xi (value_args args) j
  | None -> ()

let rec proj_ren_tm (sg: sig) (xi: ren) (th: list exp) (o: occ)
  : Lemma (ensures proj sg (ren_tm_exps xi th) o == map_opt (ren_tm xi) (proj sg th o))
    (decreases o) =
  match o with
  | OScrut i -> nth_ren_tm_exps xi th i
  | OCtor o' q j ->
    proj_ren_tm sg xi th o';
    (match proj sg th o' with Some v -> ctor_field_ren_tm sg xi q j v | None -> ())
  | ORecord o' k ->
    proj_ren_tm sg xi th o';
    (match proj sg th o' with Some v -> record_field_ren_tm xi k v | None -> ())
  | OVariant o' k ->
    proj_ren_tm sg xi th o';
    (match proj sg th o' with Some v -> variant_payload_ren_tm xi k v | None -> ())
