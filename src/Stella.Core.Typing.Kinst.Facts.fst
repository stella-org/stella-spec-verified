(* Proof structure.

   Lists, layouts and the types of `Prim`: induction on the list, and
   computation. Binders: `kinst_sub_ty` at the instantiated substitution.
   Rows: canonicalization commutes with kind instantiation (`canon_kinst`),
   and the view of an instantiated row holds the images of the entries
   (`ckinst_view`); an image keeps its key.

   Declared types are kinded under their kind variables, so their kind
   variables are below their number (`check_kvs_below`) and instantiations
   compose (`kinst_ty_comp`). Instantiating `forall`s and reading the
   arrows of a type commute with every kind instantiation, which keeps the
   former at the head of every type. A constructor has the kind variables
   of its data type, and a kinded instance of the data type has as many
   kinds.

   Region names and region maps: mutual inductions over the term classes,
   as the maps are defined.

   Values: by induction on the value. A chain is read through its view,
   which a kind instantiation maps argument by argument; the cursor of the
   instantiated chain walks the instantiated remainder in step with the
   original one, and saturation reads only the shape. *)
module Stella.Core.Typing.Kinst.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.OrdSet
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Spine
open Stella.Core.Spine.Lemmas
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing.Rename.Facts
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module V = Stella.Core.Value

(* Lists and layouts. *)

let rec kinst_kinds_length ks kl =
  match kl with
  | [] -> ()
  | _ :: kl -> kinst_kinds_length ks kl

let rec kinst_tys_length ks ts =
  match ts with
  | [] -> ()
  | _ :: ts -> kinst_tys_length ks ts

let rec kinst_layout_snd ks l =
  match l with
  | [] -> ()
  | _ :: l -> kinst_layout_snd ks l

let rec kinst_layout_assoc (ks: list kind) (l: layout) (k: key)
  : Lemma (ensures L.assoc k (kinst_layout ks l) == map_opt (kinst_ty ks) (L.assoc k l))
          (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> kinst_layout_assoc ks l k

let kinst_layout_row ks l =
  brs_row_empty l;
  brs_row_empty (kinst_layout ks l);
  kinst_brs_row ks l TRowEmpty

let rec kinst_binds_fst ks bs =
  match bs with
  | [] -> ()
  | _ :: bs -> kinst_binds_fst ks bs

let rec kinst_tapps (ks: list kind) (h: typ) (ts: list typ)
  : Lemma (ensures kinst_ty ks (tapps h ts) == tapps (kinst_ty ks h) (kinst_tys ks ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> kinst_tapps ks (TApp h t) ts

(* Types of `Prim`. *)

let kinst_app3 (ks: list kind) (h a b c: typ)
  : Lemma (kinst_ty ks (TApp (TApp (TApp h a) b) c) ==
           TApp (TApp (TApp (kinst_ty ks h) (kinst_ty ks a)) (kinst_ty ks b)) (kinst_ty ks c)) =
  assert (kinst_ty ks (TApp h a) == TApp (kinst_ty ks h) (kinst_ty ks a));
  assert (kinst_ty ks (TApp (TApp h a) b) == TApp (kinst_ty ks (TApp h a)) (kinst_ty ks b))

let kinst_t_fun ks t1 r t2 = kinst_app3 ks (TCon prim_function []) t1 r t2

let kinst_t_record ks r = ()

let kinst_t_variant ks r = ()

let kinst_lit_type ks c = ()

let kinst_t_unit ks = ()

(* Binders. *)

let kinst_subst1 ks s t =
  let th (i: nat) : typ = kinst_ty ks (scons s tvar i) in
  introduce forall (i: nat). th i == kinst_ty ks (scons s tvar i) with ();
  kinst_sub_ty ks (scons s tvar) th t;
  introduce forall (i: nat). th i == scons (kinst_ty ks s) tvar i
  with (if i = 0 then () else ());
  Stella.Core.Subst.Lemmas.Typ.sub_ty_ext th (scons (kinst_ty ks s) tvar) (kinst_ty ks t)

(* Rows. *)

let rec ty_head_kinst ks t =
  match t with
  | TApp f _ -> ty_head_kinst ks f
  | _ -> ()

let entries_kinst (ks: list kind) (t: typ) (e: centry)
  : Lemma (requires L.mem e (row_entries (canon t)))
          (ensures L.mem (ckinst_ent ks e) (row_entries (canon (kinst_ty ks t)))) =
  canon_kinst ks t;
  ckinst_view ks (canon t);
  LP.mem_memP e (row_entries (canon t));
  LP.memP_map_intro (ckinst_ent ks) e (row_entries (canon t));
  LP.mem_memP (ckinst_ent ks e) (L.map (ckinst_ent ks) (row_entries (canon t)));
  let v = rop (ckinst_ent ks) (ckinst_vf ks) (view_row (canon t)) in
  LP.append_mem (L.map (ckinst_ent ks) (row_entries (canon t)))
    (flat_es (L.map (ckinst_vf ks) (snd (view_row (canon t))))) (ckinst_ent ks e);
  assert (L.mem (ckinst_ent ks e) (fst v))

let known_keys_kinst ks t k =
  mem_ckeys k (canon t);
  mem_ckeys k (canon (kinst_ty ks t));
  introduce forall (p: cpayload). L.mem (k, p) (row_entries (canon t)) ==>
    L.mem (k, ckinst_pay ks p) (row_entries (canon (kinst_ty ks t)))
  with introduce _ ==> _
  with entries_kinst ks t (k, p)

let entries_kinst_ty ks r k t =
  entries_kinst ks r (k, PTy (canon t));
  canon_kinst ks t

let entries_kinst_eff ks r k q ts =
  entries_kinst ks r (k, PEff q (canon_tys ts));
  canon_kinst_tys ks ts

(* Declared types. *)

let global_type_kinst sg q nk t ks0 ks =
  (match sg.ctors q, sg.foreigns q, sg.values q with
   | Some ci, None, None -> assert (scheme_ok sg ci.ct_nk ci.ct_ty)
   | None, Some fi, None -> assert (scheme_ok sg fi.fr_nk fi.fr_ty)
   | None, None, Some vi -> assert (scheme_ok sg vi.vl_nk vi.vl_ty));
  check_kvs_below sg (decl_ctx nk) t KType;
  kinst_ty_comp ks ks0 t

let rec inst_foralls_kinst (ks: list kind) (t: typ) (ss: list typ)
  : Lemma (ensures inst_foralls (kinst_ty ks t) (kinst_tys ks ss)
                   == map_opt (kinst_ty ks) (inst_foralls t ss))
          (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' ->
    match t with
    | TForall _ b -> kinst_subst1 ks s b; inst_foralls_kinst ks (subst1_ty s b) ss'
    | _ -> ()

let rec fun_args_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (ensures fun_args sg (kinst_ty ks t) == kinst_tys ks (fun_args sg t)) (decreases t) =
  match t with
  | TApp (TApp (TApp h t1) r) t2 ->
    kinst_app3 ks h t1 r t2;
    (match h with
     | TCon q [] -> fun_args_kinst sg ks t2
     | _ -> ())
  | TApp (TApp h a) b -> assert (kinst_ty ks (TApp h a) == TApp (kinst_ty ks h) (kinst_ty ks a))
  | _ -> ()

let ctor_fields_kinst sg c ks0 ss fs ks =
  let Some ci = sg.ctors c in
  assert (scheme_ok sg ci.ct_nk ci.ct_ty);
  check_kvs_below sg (decl_ctx ci.ct_nk) ci.ct_ty KType;
  kinst_ty_comp ks ks0 ci.ct_ty;
  inst_foralls_kinst ks (kinst_ty ks0 ci.ct_ty) ss;
  let Some u = inst_foralls (kinst_ty ks0 ci.ct_ty) ss in
  fun_args_kinst sg ks u

let rec tapps_synth (sg: sig) (g: ctx) (h: typ) (ss: list typ) (k: kind)
  : Lemma (requires (TCon? h \/ TApp? h) /\ check sg g (tapps h ss) k)
          (ensures Some? (synth_kind sg g h)) (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' -> tapps_synth sg g (TApp h s) ss' k

let ctor_nk_of_data sg g tq ks0 ss cs c =
  tapps_synth sg g (TCon tq ks0) ss KType;
  let Some ti = sg.tycons tq in
  ctor_of_data sg tq ti cs c;
  let Some ci = sg.ctors c in
  assert (ctor_ok sg c ci)

(* Region names. *)

let rec frn_kinst_ty (ks: list kind) (t: typ)
  : Lemma (ensures frn_ty (kinst_ty ks t) == frn_ty t) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 | TRowUnion t1 t2 -> frn_kinst_ty ks t1; frn_kinst_ty ks t2
  | TForall _ b -> frn_kinst_ty ks b
  | TConstr c b -> frn_kinst_constr ks c; frn_kinst_ty ks b
  | TRowExt en r -> frn_kinst_ent ks en; frn_kinst_ty ks r

and frn_kinst_ent (ks: list kind) (en: entry)
  : Lemma (ensures frn_ent (kinst_ent ks en) == frn_ent en) (decreases en) =
  match en with
  | EntTy _ t -> frn_kinst_ty ks t
  | EntEff _ _ ts -> frn_kinst_tys ks ts
  | EntRegion _ -> ()

and frn_kinst_constr (ks: list kind) (c: constr)
  : Lemma (ensures frn_constr (kinst_constr ks c) == frn_constr c) (decreases c) =
  match c with
  | CLacks _ t -> frn_kinst_ty ks t
  | CDisj t1 t2 -> frn_kinst_ty ks t1; frn_kinst_ty ks t2

and frn_kinst_tys (ks: list kind) (ts: list typ)
  : Lemma (ensures frn_tys (kinst_tys ks ts) == frn_tys ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> frn_kinst_ty ks t; frn_kinst_tys ks ts

let rec frn_kinst_layout (ks: list kind) (l: layout)
  : Lemma (ensures frn_layout (kinst_layout ks l) == frn_layout l) (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> frn_kinst_ty ks t; frn_kinst_layout ks l

let rec frn_kinst_exp (ks: list kind) (e: exp)
  : Lemma (ensures frn_exp (kinst_exp ks e) == frn_exp e) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> frn_kinst_ty ks t; frn_kinst_ty ks r; frn_kinst_exp ks b
  | EApp e1 e2 | EMerge e1 e2 -> frn_kinst_exp ks e1; frn_kinst_exp ks e2
  | ETyLam _ b -> frn_kinst_exp ks b
  | ETyApp b t -> frn_kinst_exp ks b; frn_kinst_ty ks t
  | ECLam c b -> frn_kinst_constr ks c; frn_kinst_exp ks b
  | ECApp b | ESelect _ b | ERestrict _ b | EWriteCell _ _ b | EFill _ b -> frn_kinst_exp ks b
  | ELet t e1 e2 -> frn_kinst_ty ks t; frn_kinst_exp ks e1; frn_kinst_exp ks e2
  | ELetRec bs b -> frn_kinst_binds ks bs; frn_kinst_exp ks b
  | ECase es dt | EMatch es dt -> frn_kinst_exps ks es; frn_kinst_dt ks dt
  | ELetJoin ts t e1 e2 ->
    frn_kinst_tys ks ts; frn_kinst_ty ks t; frn_kinst_exp ks e1; frn_kinst_exp ks e2
  | EJump _ es -> frn_kinst_exps ks es
  | EExtend _ e1 e2 | EUpdate _ e1 e2 -> frn_kinst_exp ks e1; frn_kinst_exp ks e2
  | EInject _ t b | EWeaken _ t b | EAbsurd t b | EOpenEff t b | EOpenEffC t b ->
    frn_kinst_ty ks t; frn_kinst_exp ks b
  | EPerform _ _ ts b -> frn_kinst_tys ks ts; frn_kinst_exp ks b
  | EHandle b h ->
    frn_kinst_exp ks b; frn_kinst_ent ks h.h_ent; frn_kinst_ty ks h.h_ret_ty;
    frn_kinst_exp ks h.h_ret; frn_kinst_cls ks h.h_clauses
  | ERegion l es b -> frn_kinst_layout ks l; frn_kinst_exps ks es; frn_kinst_exp ks b
  | ERegionOpen _ th b -> frn_kinst_cells ks th; frn_kinst_exp ks b
  | EOpaque _ t -> frn_kinst_ty ks t

and frn_kinst_exps (ks: list kind) (es: list exp)
  : Lemma (ensures frn_exps (kinst_exps ks es) == frn_exps es) (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> frn_kinst_exp ks e; frn_kinst_exps ks es

and frn_kinst_binds (ks: list kind) (bs: list (typ & exp))
  : Lemma (ensures frn_binds (kinst_binds ks bs) == frn_binds bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> frn_kinst_ty ks t; frn_kinst_exp ks e; frn_kinst_binds ks bs

and frn_kinst_cells (ks: list kind) (th: list (key & exp))
  : Lemma (ensures frn_cells (kinst_cells ks th) == frn_cells th) (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> frn_kinst_exp ks e; frn_kinst_cells ks th

and frn_kinst_dt (ks: list kind) (dt: dtree)
  : Lemma (ensures frn_dt (kinst_dt ks dt) == frn_dt dt) (decreases dt) =
  match dt with
  | DLeaf e -> frn_kinst_exp ks e
  | DBind _ dt -> frn_kinst_dt ks dt
  | DSwitchCtor _ bs df -> frn_kinst_brs ks bs; frn_kinst_odt ks df
  | DSwitchLit _ bs df -> frn_kinst_brs ks bs; frn_kinst_dt ks df
  | DSwitchKey _ bs df -> frn_kinst_kbrs ks bs; frn_kinst_odt ks df
  | DGuard e dt1 dt2 -> frn_kinst_exp ks e; frn_kinst_dt ks dt1; frn_kinst_dt ks dt2

and frn_kinst_odt (ks: list kind) (df: option dtree)
  : Lemma (ensures frn_odt (kinst_odt ks df) == frn_odt df) (decreases df) =
  match df with
  | None -> ()
  | Some dt -> frn_kinst_dt ks dt

and frn_kinst_brs (#lb: eqtype) (ks: list kind) (bs: list (lb & dtree))
  : Lemma (ensures frn_brs (kinst_brs ks bs) == frn_brs bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> frn_kinst_dt ks dt; frn_kinst_brs ks bs

and frn_kinst_kbrs (ks: list kind) (bs: list (key & dtree))
  : Lemma (ensures frn_kbrs (kinst_brs ks bs) == frn_kbrs bs) (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> frn_kinst_dt ks dt; frn_kinst_kbrs ks bs

and frn_kinst_cls (ks: list kind) (cs: list clause)
  : Lemma (ensures frn_cls (kinst_cls ks cs) == frn_cls cs) (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt b :: cs ->
    frn_kinst_ty ks s; frn_kinst_ty ks kt; frn_kinst_exp ks b; frn_kinst_cls ks cs
  | CFast _ _ s b :: cs -> frn_kinst_ty ks s; frn_kinst_exp ks b; frn_kinst_cls ks cs

(* Region maps. *)

let rec rmap_kinst_ty (f: region_ref -> region_ref) (ks: list kind) (t: typ)
  : Lemma (ensures rmap_ty f (kinst_ty ks t) == kinst_ty ks (rmap_ty f t)) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 | TRowUnion t1 t2 -> rmap_kinst_ty f ks t1; rmap_kinst_ty f ks t2
  | TForall _ b -> rmap_kinst_ty f ks b
  | TConstr c b -> rmap_kinst_constr f ks c; rmap_kinst_ty f ks b
  | TRowExt en r -> rmap_kinst_ent f ks en; rmap_kinst_ty f ks r

and rmap_kinst_ent (f: region_ref -> region_ref) (ks: list kind) (en: entry)
  : Lemma (ensures rmap_ent f (kinst_ent ks en) == kinst_ent ks (rmap_ent f en)) (decreases en) =
  match en with
  | EntTy _ t -> rmap_kinst_ty f ks t
  | EntEff _ _ ts -> rmap_kinst_tys f ks ts
  | EntRegion _ -> ()

and rmap_kinst_constr (f: region_ref -> region_ref) (ks: list kind) (c: constr)
  : Lemma (ensures rmap_constr f (kinst_constr ks c) == kinst_constr ks (rmap_constr f c))
          (decreases c) =
  match c with
  | CLacks _ t -> rmap_kinst_ty f ks t
  | CDisj t1 t2 -> rmap_kinst_ty f ks t1; rmap_kinst_ty f ks t2

and rmap_kinst_tys (f: region_ref -> region_ref) (ks: list kind) (ts: list typ)
  : Lemma (ensures rmap_tys f (kinst_tys ks ts) == kinst_tys ks (rmap_tys f ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> rmap_kinst_ty f ks t; rmap_kinst_tys f ks ts

let rec rmap_kinst_layout (f: region_ref -> region_ref) (ks: list kind) (l: layout)
  : Lemma (ensures rmap_layout f (kinst_layout ks l) == kinst_layout ks (rmap_layout f l))
          (decreases l) =
  match l with
  | [] -> ()
  | (_, t) :: l -> rmap_kinst_ty f ks t; rmap_kinst_layout f ks l

let rec rmap_kinst_exp (f: nat -> region_ref -> region_ref) (d: nat) (ks: list kind) (e: exp)
  : Lemma (ensures rmap_exp f d (kinst_exp ks e) == kinst_exp ks (rmap_exp f d e)) (decreases e) =
  match e with
  | EVar _ | EGlobal _ _ | ELit _ | ERecEmpty | EReadCell _ _ | EForce _ -> ()
  | ELam t r b -> rmap_kinst_ty (f d) ks t; rmap_kinst_ty (f d) ks r; rmap_kinst_exp f d ks b
  | EApp e1 e2 | EMerge e1 e2 | EExtend _ e1 e2 | EUpdate _ e1 e2 ->
    rmap_kinst_exp f d ks e1; rmap_kinst_exp f d ks e2
  | ETyLam _ b | ECApp b | ESelect _ b | ERestrict _ b | EWriteCell _ _ b | EFill _ b ->
    rmap_kinst_exp f d ks b
  | ETyApp b t -> rmap_kinst_exp f d ks b; rmap_kinst_ty (f d) ks t
  | ECLam c b -> rmap_kinst_constr (f d) ks c; rmap_kinst_exp f d ks b
  | ELet t e1 e2 -> rmap_kinst_ty (f d) ks t; rmap_kinst_exp f d ks e1; rmap_kinst_exp f d ks e2
  | ELetRec bs b -> rmap_kinst_binds f d ks bs; rmap_kinst_exp f d ks b
  | ECase es dt | EMatch es dt -> rmap_kinst_exps f d ks es; rmap_kinst_dt f d ks dt
  | ELetJoin ts t e1 e2 ->
    rmap_kinst_tys (f d) ks ts; rmap_kinst_ty (f d) ks t; rmap_kinst_exp f d ks e1;
    rmap_kinst_exp f d ks e2
  | EJump _ es -> rmap_kinst_exps f d ks es
  | EInject _ t b | EWeaken _ t b | EAbsurd t b | EOpenEff t b | EOpenEffC t b ->
    rmap_kinst_ty (f d) ks t; rmap_kinst_exp f d ks b
  | EPerform _ _ ts b -> rmap_kinst_tys (f d) ks ts; rmap_kinst_exp f d ks b
  | EHandle b h ->
    rmap_kinst_exp f d ks b; rmap_kinst_ent (f d) ks h.h_ent; rmap_kinst_ty (f d) ks h.h_ret_ty;
    rmap_kinst_exp f d ks h.h_ret; rmap_kinst_cls f d ks h.h_clauses
  | ERegion l es b ->
    rmap_kinst_layout (f d) ks l; rmap_kinst_exps f d ks es; rmap_kinst_exp f (d + 1) ks b
  | ERegionOpen _ th b -> rmap_kinst_cells f d ks th; rmap_kinst_exp f d ks b
  | EOpaque _ t -> rmap_kinst_ty (f d) ks t

and rmap_kinst_exps (f: nat -> region_ref -> region_ref) (d: nat) (ks: list kind) (es: list exp)
  : Lemma (ensures rmap_exps f d (kinst_exps ks es) == kinst_exps ks (rmap_exps f d es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> rmap_kinst_exp f d ks e; rmap_kinst_exps f d ks es

and rmap_kinst_binds (f: nat -> region_ref -> region_ref) (d: nat) (ks: list kind)
  (bs: list (typ & exp))
  : Lemma (ensures rmap_binds f d (kinst_binds ks bs) == kinst_binds ks (rmap_binds f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (t, e) :: bs -> rmap_kinst_ty (f d) ks t; rmap_kinst_exp f d ks e; rmap_kinst_binds f d ks bs

and rmap_kinst_cells (f: nat -> region_ref -> region_ref) (d: nat) (ks: list kind)
  (th: list (key & exp))
  : Lemma (ensures rmap_cells f d (kinst_cells ks th) == kinst_cells ks (rmap_cells f d th))
          (decreases th) =
  match th with
  | [] -> ()
  | (_, e) :: th -> rmap_kinst_exp f d ks e; rmap_kinst_cells f d ks th

and rmap_kinst_dt (f: nat -> region_ref -> region_ref) (d: nat) (ks: list kind) (dt: dtree)
  : Lemma (ensures rmap_dt f d (kinst_dt ks dt) == kinst_dt ks (rmap_dt f d dt)) (decreases dt) =
  match dt with
  | DLeaf e -> rmap_kinst_exp f d ks e
  | DBind _ dt -> rmap_kinst_dt f d ks dt
  | DSwitchCtor _ bs df -> rmap_kinst_brs f d ks bs; rmap_kinst_odt f d ks df
  | DSwitchLit _ bs df -> rmap_kinst_brs f d ks bs; rmap_kinst_dt f d ks df
  | DSwitchKey _ bs df -> rmap_kinst_kbrs f d ks bs; rmap_kinst_odt f d ks df
  | DGuard e dt1 dt2 ->
    rmap_kinst_exp f d ks e; rmap_kinst_dt f d ks dt1; rmap_kinst_dt f d ks dt2

and rmap_kinst_odt (f: nat -> region_ref -> region_ref) (d: nat) (ks: list kind)
  (df: option dtree)
  : Lemma (ensures rmap_odt f d (kinst_odt ks df) == kinst_odt ks (rmap_odt f d df))
          (decreases df) =
  match df with
  | None -> ()
  | Some dt -> rmap_kinst_dt f d ks dt

and rmap_kinst_brs (#lb: eqtype) (f: nat -> region_ref -> region_ref) (d: nat) (ks: list kind)
  (bs: list (lb & dtree))
  : Lemma (ensures rmap_brs f d (kinst_brs ks bs) == kinst_brs ks (rmap_brs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_kinst_dt f d ks dt; rmap_kinst_brs f d ks bs

and rmap_kinst_kbrs (f: nat -> region_ref -> region_ref) (d: nat) (ks: list kind)
  (bs: list (key & dtree))
  : Lemma (ensures rmap_kbrs f d (kinst_brs ks bs) == kinst_brs ks (rmap_kbrs f d bs))
          (decreases bs) =
  match bs with
  | [] -> ()
  | (_, dt) :: bs -> rmap_kinst_dt f d ks dt; rmap_kinst_kbrs f d ks bs

and rmap_kinst_cls (f: nat -> region_ref -> region_ref) (d: nat) (ks: list kind) (cs: list clause)
  : Lemma (ensures rmap_cls f d (kinst_cls ks cs) == kinst_cls ks (rmap_cls f d cs))
          (decreases cs) =
  match cs with
  | [] -> ()
  | CFull _ _ s kt b :: cs ->
    rmap_kinst_ty (f d) ks s; rmap_kinst_ty (f d) ks kt; rmap_kinst_exp f d ks b;
    rmap_kinst_cls f d ks cs
  | CFast _ _ s b :: cs ->
    rmap_kinst_ty (f d) ks s; rmap_kinst_exp f d ks b; rmap_kinst_cls f d ks cs

let open_region_kinst a ks e = rmap_kinst_exp (open_rr a) 0 ks e

(* Values. *)

let rec value_form_kinst sg ks e : Lemma
  (ensures value_form sg (kinst_exp ks e) == value_form sg e)
  (decreases %[e; 1]) =
  match e with
  | ETyLam _ v | ECLam _ v | EInject _ _ v -> value_form_kinst sg ks v
  | EExtend _ v1 v2 -> value_form_kinst sg ks v1; value_form_kinst sg ks v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ -> ctor_chain_form_kinst sg ks e
  | _ -> ()

and ctor_chain_form_kinst (sg: sig) (ks: list kind) (e: exp)
  : Lemma (ensures ctor_chain_form sg (kinst_exp ks e) == ctor_chain_form sg e)
          (decreases %[e; 0]) =
  match e with
  | EApp f v -> ctor_chain_form_kinst sg ks f; value_form_kinst sg ks v
  | ETyApp f _ | ECApp f -> ctor_chain_form_kinst sg ks f
  | _ -> ()

let as_function_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (as_function sg (kinst_ty ks t) ==
           (match as_function sg t with
            | Some (t1, r, t2) -> Some (kinst_ty ks t1, kinst_ty ks r, kinst_ty ks t2)
            | None -> None)) =
  match t with
  | TApp (TApp (TApp h t1) r) t2 -> kinst_app3 ks h t1 r t2
  | TApp (TApp h a) b -> assert (kinst_ty ks (TApp h a) == TApp (kinst_ty ks h) (kinst_ty ks a))
  | _ -> ()

(* The cursors of a chain and of its instance walk the remainder in step:
   both are defined or neither, and their remainders are instances of one
   type, so both are saturated or neither. *)
let rec cursor_kinst_shape (sg: sig) (ks1 ks2 ks: list kind) (x: typ) (th1 th2: tsub)
  (args: list spine_arg)
  : Lemma (ensures (match cursor sg (kinst_ty ks1 x) th1 (L.map (kinst_arg ks) args),
                          cursor sg (kinst_ty ks2 x) th2 args with
                    | Some (t1, _), Some (t2, _) -> saturated sg t1 == saturated sg t2
                    | None, None -> True
                    | _ -> False))
          (decreases args) =
  match args with
  | [] -> saturated_kinst sg ks1 x; saturated_kinst sg ks2 x
  | a :: args' ->
    match a with
    | STy s ->
      (match x with
       | TForall _ b -> cursor_kinst_shape sg ks1 ks2 ks b (scons (kinst_ty ks s) th1) (scons s th2) args'
       | _ -> ())
    | SConstr ->
      (match x with
       | TConstr _ b -> cursor_kinst_shape sg ks1 ks2 ks b th1 th2 args'
       | _ -> ())
    | SVal _ ->
      as_function_kinst sg ks1 x;
      as_function_kinst sg ks2 x;
      (match as_function sg x with
       | Some (_, _, b) -> cursor_kinst_shape sg ks1 ks2 ks b th1 th2 args'
       | None -> ())

let spine_unsaturated_kinst (sg: sig) (ks: list kind) (q: qname) (kl: list kind)
  (args: list spine_arg)
  : Lemma (spine_unsaturated sg q (kinst_kinds ks kl) (L.map (kinst_arg ks) args)
           == spine_unsaturated sg q kl args) =
  kinst_kinds_length ks kl;
  match global_scheme sg q with
  | Some (_, nk, t) ->
    if L.length kl = nk then cursor_kinst_shape sg (kinst_kinds ks kl) kl ks t tvar tvar args
  | None -> ()

let value_head_kinst (sg: sig) (ks: list kind) (e: exp)
  : Lemma (V.value_head sg (kinst_exp ks e) == V.value_head sg e) =
  decompose_kinst ks e;
  match decompose_global_app e with
  | Some (q, kl, args) -> spine_unsaturated_kinst sg ks q kl args
  | None -> ()

let rec is_value_kinst sg ks e : Lemma
  (ensures V.is_value sg (kinst_exp ks e) == V.is_value sg e)
  (decreases %[e; 1]) =
  match e with
  | ETyLam _ v | ECLam _ v | EInject _ _ v | EWeaken _ _ v | EOpenEff _ v -> is_value_kinst sg ks v
  | EExtend _ v1 v2 -> is_value_kinst sg ks v1; is_value_kinst sg ks v2
  | EGlobal _ _ | EApp _ _ | ETyApp _ _ | ECApp _ ->
    value_head_kinst sg ks e; chain_values_kinst sg ks e
  | _ -> ()

and chain_values_kinst (sg: sig) (ks: list kind) (e: exp)
  : Lemma (ensures V.chain_values sg (kinst_exp ks e) == V.chain_values sg e)
          (decreases %[e; 0]) =
  match e with
  | EApp f v -> chain_values_kinst sg ks f; is_value_kinst sg ks v
  | ETyApp f _ | ECApp f -> chain_values_kinst sg ks f
  | _ -> ()

let rec values_kinst (sg: sig) (ks: list kind) (es: list exp)
  : Lemma (ensures L.for_all (V.is_value sg) (kinst_exps ks es) == L.for_all (V.is_value sg) es)
          (decreases es) =
  match es with
  | [] -> ()
  | e :: es -> is_value_kinst sg ks e; values_kinst sg ks es

let rec nth_kinst_exps (ks: list kind) (es: list exp) (i: nat)
  : Lemma (ensures L.nth (kinst_exps ks es) i == map_opt (kinst_exp ks) (L.nth es i))
          (decreases es) =
  match es with
  | [] -> ()
  | _ :: es -> if i = 0 then () else nth_kinst_exps ks es (i - 1)

let rec value_args_kinst (ks: list kind) (args: list spine_arg)
  : Lemma (ensures value_args (L.map (kinst_arg ks) args) == kinst_exps ks (value_args args))
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: args -> value_args_kinst ks args

let rec record_field_kinst (ks: list kind) (k: key) (v: exp)
  : Lemma (ensures record_field k (kinst_exp ks v) == map_opt (kinst_exp ks) (record_field k v))
          (decreases v) =
  match v with
  | EExtend _ _ v2 -> record_field_kinst ks k v2
  | _ -> ()

let rec variant_payload_kinst (ks: list kind) (k: key) (v: exp)
  : Lemma (ensures variant_payload k (kinst_exp ks v)
                   == map_opt (kinst_exp ks) (variant_payload k v))
          (decreases v) =
  match v with
  | EWeaken _ _ v1 -> variant_payload_kinst ks k v1
  | _ -> ()

let ctor_field_kinst (sg: sig) (ks: list kind) (q: qname) (j: nat) (v: exp)
  : Lemma (ctor_field sg q j (kinst_exp ks v) == map_opt (kinst_exp ks) (ctor_field sg q j v)) =
  decompose_kinst ks v;
  match decompose_global_app v with
  | Some (_, _, args) -> value_args_kinst ks args; nth_kinst_exps ks (value_args args) j
  | None -> ()

let rec proj_kinst (sg: sig) (ks: list kind) (th: list exp) (o: occ)
  : Lemma (ensures proj sg (kinst_exps ks th) o == map_opt (kinst_exp ks) (proj sg th o))
          (decreases o) =
  match o with
  | OScrut i -> nth_kinst_exps ks th i
  | OCtor o' q j ->
    proj_kinst sg ks th o';
    (match proj sg th o' with Some v -> ctor_field_kinst sg ks q j v | None -> ())
  | ORecord o' k ->
    proj_kinst sg ks th o';
    (match proj sg th o' with Some v -> record_field_kinst ks k v | None -> ())
  | OVariant o' k ->
    proj_kinst sg ks th o';
    (match proj sg th o' with Some v -> variant_payload_kinst ks k v | None -> ())
