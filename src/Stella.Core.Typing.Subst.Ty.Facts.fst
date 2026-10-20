(* Proof structure.

   Lists and layouts: induction on the list. Binders: the σ-calculus laws of
   `Stella.Core.Subst.Lemmas.Typ`, the substitutions compared pointwise.
   Rows: canonicalization commutes with substitution (`canon_sub`), and the
   view of a substituted row holds the images of the entries (`csub_view`).

   Declared types are kinded with no type variable in scope, so every
   substitution fixes them (`sub_tvs_below`). For the fields of a
   constructor, `fshape` says that a type is `forall`s over arrows over an
   application of a type constructor that is no function type. Every
   substitution and kind instantiation keeps the shape, instantiating a
   `forall` keeps it, and on such a type `fun_args` commutes with every
   substitution. A constructor's scheme has the shape, and an instance
   `inst_foralls` reaches commutes with the substitution.

   Region names: a mutual induction over the term classes, as the maps
   are defined; a variable has no atom.

   Region facts: the decomposition of `k ∉ ρ` is consistent, since no
   entry of a kinded `ρ` names the atom out of scope (`row_entry_key`),
   and its atomic facts are `k ∉ a` for the tails `a` of `ρ`, each a
   `Row Effect` variable (`check_row_tails`), whose fact the region
   adds. *)
module Stella.Core.Typing.Subst.Ty.Facts
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.OrdSet
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Prim
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Facts
open Stella.Core.Kinding.Lemmas
open Stella.Core.Kinding.Keys
open Stella.Core.Spine
open Stella.Core.Typing.Aux
open Stella.Core.Typing.Aux.Lemmas
open Stella.Core.Typing.Ops
open Stella.Core.Typing.Rename.Facts
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

(* Lists and layouts. *)

let rec sub_layout_snd sigma l =
  match l with
  | [] -> ()
  | _ :: l -> sub_layout_snd sigma l

let rec sub_layout_assoc (sigma: tsub) (l: layout) (k: key)
  : Lemma (ensures L.assoc k (sub_layout sigma l) == map_opt (sub_ty sigma) (L.assoc k l))
          (decreases l) =
  match l with
  | [] -> ()
  | _ :: l -> sub_layout_assoc sigma l k

let sub_layout_row sigma l =
  brs_row_empty l;
  brs_row_empty (sub_layout sigma l);
  sub_brs_row sigma l TRowEmpty

let rec sub_ty_binds_fst sigma bs =
  match bs with
  | [] -> ()
  | _ :: bs -> sub_ty_binds_fst sigma bs

let rec sub_tapps (sigma: tsub) (h: typ) (ts: list typ)
  : Lemma (ensures sub_ty sigma (tapps h ts) == tapps (sub_ty sigma h) (sub_tys sigma ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> sub_tapps sigma (TApp h t) ts

(* Types of `Prim`. *)

let sub_app3 (sigma: tsub) (h a b c: typ)
  : Lemma (sub_ty sigma (TApp (TApp (TApp h a) b) c) ==
           TApp (TApp (TApp (sub_ty sigma h) (sub_ty sigma a)) (sub_ty sigma b)) (sub_ty sigma c)) =
  assert (sub_ty sigma (TApp h a) == TApp (sub_ty sigma h) (sub_ty sigma a));
  assert (sub_ty sigma (TApp (TApp h a) b) == TApp (sub_ty sigma (TApp h a)) (sub_ty sigma b))

let sub_t_fun sigma t1 r t2 = sub_app3 sigma (TCon prim_function []) t1 r t2

let sub_t_record sigma r = ()

let sub_t_variant sigma r = ()

let sub_lit_type sigma c = ()

(* Binders. *)

let subst1_shift_back (x u: typ) : Lemma (sub_ty (scons x tvar) (ren_ty (shift 1) u) == u) =
  sub_ren_ty (scons x tvar) (shift 1) tvar u;
  sub_ty_tvar u

let sub_subst1 sigma s t =
  let th1 (i: nat) : typ = sub_ty sigma (scons s tvar i) in
  sub_sub_ty sigma (scons s tvar) th1 t;
  let th2 (i: nat) : typ = sub_ty (scons (sub_ty sigma s) tvar) (up_tsub sigma i) in
  sub_sub_ty (scons (sub_ty sigma s) tvar) (up_tsub sigma) th2 t;
  introduce forall (i: nat). th1 i == th2 i
  with (if i = 0 then () else subst1_shift_back (sub_ty sigma s) (sigma (i - 1)));
  sub_ty_ext th1 th2 t

let sub_shift_up n sigma t =
  let th = tsub_shift n sigma in
  sub_ren_ty (upn_tsub n sigma) (shift n) th t;
  ren_sub_ty (shift n) sigma th t

let sub_layout_shift_up n sigma l =
  let th = tsub_shift n sigma in
  sub_ren_layout (upn_tsub n sigma) (shift n) th l;
  ren_sub_layout (shift n) sigma th l

let upn_tsub_succ n sigma i =
  if i < n then ()
  else if i = n then ()
  else ren_ren_ty (shift n) (shift 1) (shift (n + 1)) (sigma (i - n - 1))

(* Rows. *)

let rec ty_head_sub (sigma: tsub) (t: typ)
  : Lemma (requires Some? (ty_head t)) (ensures ty_head (sub_ty sigma t) == ty_head t)
          (decreases t) =
  match t with
  | TApp f _ -> ty_head_sub sigma f
  | _ -> ()

let csub_of (sigma: tsub) (i: nat) : ctyp = canon (sigma i)

let entries_sub (sigma: tsub) (t: typ) (e: centry)
  : Lemma (requires L.mem e (row_entries (canon t)))
          (ensures L.mem (csub_ent (csub_of sigma) e) (row_entries (canon (sub_ty sigma t)))) =
  let s = csub_of sigma in
  canon_sub sigma s t;
  csub_view s (canon t);
  LP.mem_memP e (row_entries (canon t));
  LP.memP_map_intro (csub_ent s) e (row_entries (canon t));
  LP.mem_memP (csub_ent s e) (L.map (csub_ent s) (row_entries (canon t)));
  let v = rop (csub_ent s) (csub_vf s) (view_row (canon t)) in
  LP.append_mem (L.map (csub_ent s) (row_entries (canon t)))
    (flat_es (L.map (csub_vf s) (snd (view_row (canon t))))) (csub_ent s e);
  assert (L.mem (csub_ent s e) (fst v))

let entries_sub_ty sigma r k t =
  entries_sub sigma r (k, PTy (canon t));
  canon_sub sigma (csub_of sigma) t

let entries_sub_eff sigma r k q ts =
  entries_sub sigma r (k, PEff q (canon_tys ts));
  canon_sub_tys sigma (csub_of sigma) ts

(* Declared types. *)

let global_scheme_closed (sg: sig) (q: qname) (nk: nat) (t: typ)
  : Lemma (requires sig_wf sg /\ global_type sg q == Some (nk, t)) (ensures tvs_below 0 t) =
  (match sg.ctors q, sg.foreigns q, sg.values q with
   | Some ci, None, None -> assert (scheme_ok sg ci.ct_nk ci.ct_ty)
   | None, Some fi, None -> assert (scheme_ok sg fi.fr_nk fi.fr_ty)
   | None, None, Some vi -> assert (scheme_ok sg vi.vl_nk vi.vl_ty));
  check_tvs_below sg (decl_ctx nk) t KType

let closed_sub (sigma: tsub) (t: typ)
  : Lemma (requires tvs_below 0 t) (ensures sub_ty sigma t == t) =
  sub_tvs_below 0 sigma t

let global_inst_sub sg q nk t ks sigma =
  global_scheme_closed sg q nk t;
  kinst_tvs_below ks 0 t;
  closed_sub sigma (kinst_ty ks t)

(* The shape of a constructor's scheme. *)

let rec ashape (sg: sig) (t: typ) : Tot bool (decreases t) =
  match t with
  | TApp (TApp (TApp (TCon q []) _) _) t2 -> if is_function_tycon sg q then ashape sg t2 else true
  | _ ->
    (TCon? t || TApp? t) &&
    (match ty_head t with
     | Some q -> not (is_function_tycon sg q)
     | None -> false)

let rec fshape (sg: sig) (t: typ) : Tot bool (decreases t) =
  match t with
  | TForall _ b -> fshape sg b
  | _ -> ashape sg t

let ty_head_app3 (h a b c: typ)
  : Lemma (ty_head (TApp (TApp (TApp h a) b) c) == ty_head h) =
  assert (ty_head (TApp (TApp (TApp h a) b) c) == ty_head (TApp (TApp h a) b));
  assert (ty_head (TApp (TApp h a) b) == ty_head (TApp h a));
  assert (ty_head (TApp h a) == ty_head h)

let headed_no_args (sg: sig) (t: typ) (q: qname)
  : Lemma (requires (TCon? t \/ TApp? t) /\ ty_head t == Some q /\ not (is_function_tycon sg q))
          (ensures fun_args sg t == []) =
  match t with
  | TApp (TApp (TApp h a) b) c -> ty_head_app3 h a b c
  | _ -> ()

(* An application of a head that is no function type has the shape. *)
let ashape_headed (sg: sig) (t: typ) (q: qname)
  : Lemma (requires (TCon? t \/ TApp? t) /\ ty_head t == Some q /\ not (is_function_tycon sg q))
          (ensures ashape sg t) =
  match t with
  | TApp (TApp (TApp (TCon q' []) a) b) c -> ty_head_app3 (TCon q' []) a b c
  | _ -> ()

(* A terminal of the shape: an application of a non-function head. *)
let terminal_sub (sg: sig) (sigma: tsub) (t: typ) (q: qname)
  : Lemma (requires (TCon? t \/ TApp? t) /\ ty_head t == Some q /\ not (is_function_tycon sg q))
          (ensures ashape sg (sub_ty sigma t) /\ fun_args sg (sub_ty sigma t) == [] /\
                   fun_args sg t == []) =
  ty_head_sub sigma t;
  headed_no_args sg t q;
  headed_no_args sg (sub_ty sigma t) q;
  ashape_headed sg (sub_ty sigma t) q

let rec ashape_sub (sg: sig) (sigma: tsub) (t: typ)
  : Lemma (requires ashape sg t)
          (ensures ashape sg (sub_ty sigma t) /\
                   fun_args sg (sub_ty sigma t) == sub_tys sigma (fun_args sg t))
          (decreases t) =
  match t with
  | TApp (TApp (TApp (TCon q []) t1) r) t2 ->
    sub_app3 sigma (TCon q []) t1 r t2;
    if is_function_tycon sg q then ashape_sub sg sigma t2
    else begin
      ty_head_app3 (TCon q []) t1 r t2;
      terminal_sub sg sigma t q
    end
  | _ -> let Some q = ty_head t in terminal_sub sg sigma t q

let rec fshape_sub (sg: sig) (sigma: tsub) (t: typ)
  : Lemma (requires fshape sg t)
          (ensures fshape sg (sub_ty sigma t) /\
                   fun_args sg (sub_ty sigma t) == sub_tys sigma (fun_args sg t))
          (decreases t) =
  match t with
  | TForall _ b -> fshape_sub sg (up_tsub sigma) b
  | _ -> ashape_sub sg sigma t

let rec head_kinst (ks: list kind) (u: typ)
  : Lemma (ensures ty_head (kinst_ty ks u) == ty_head u /\
                   (TCon? u ==> TCon? (kinst_ty ks u)) /\ (TApp? u ==> TApp? (kinst_ty ks u)))
          (decreases u) =
  match u with
  | TApp f _ -> head_kinst ks f
  | _ -> ()

let kinst_app3 (ks: list kind) (h a b c: typ)
  : Lemma (kinst_ty ks (TApp (TApp (TApp h a) b) c) ==
           TApp (TApp (TApp (kinst_ty ks h) (kinst_ty ks a)) (kinst_ty ks b)) (kinst_ty ks c)) =
  assert (kinst_ty ks (TApp h a) == TApp (kinst_ty ks h) (kinst_ty ks a));
  assert (kinst_ty ks (TApp (TApp h a) b) == TApp (kinst_ty ks (TApp h a)) (kinst_ty ks b))

let rec ashape_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (requires ashape sg t) (ensures ashape sg (kinst_ty ks t)) (decreases t) =
  match t with
  | TApp (TApp (TApp (TCon q []) t1) r) t2 ->
    kinst_app3 ks (TCon q []) t1 r t2;
    if is_function_tycon sg q then ashape_kinst sg ks t2
    else begin
      ty_head_app3 (TCon q []) t1 r t2;
      head_kinst ks t;
      ashape_headed sg (kinst_ty ks t) q
    end
  | _ -> let Some q = ty_head t in head_kinst ks t; ashape_headed sg (kinst_ty ks t) q

let rec fshape_kinst (sg: sig) (ks: list kind) (t: typ)
  : Lemma (requires fshape sg t) (ensures fshape sg (kinst_ty ks t)) (decreases t) =
  match t with
  | TForall _ b -> fshape_kinst sg ks b
  | _ -> ashape_kinst sg ks t

let rec head_tapps (h: typ) (ts: list typ)
  : Lemma (requires TCon? h \/ TApp? h)
          (ensures (TCon? (tapps h ts) \/ TApp? (tapps h ts)) /\ ty_head (tapps h ts) == ty_head h)
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> head_tapps (TApp h t) ts'

(* The arrows of a constructor scheme over its result, which is no
   `forall`. *)
let rec fshape_pure_arrows (sg: sig) (fs: list typ) (res: typ)
  : Lemma (requires prim_wf sg /\ ashape sg res /\ (TCon? res \/ TApp? res))
          (ensures fshape sg (pure_arrows fs res)) (decreases fs) =
  match fs with
  | [] -> ()
  | _ :: fs' -> fshape_pure_arrows sg fs' res

let rec fshape_foralls (sg: sig) (ps: list kind) (b: typ)
  : Lemma (requires fshape sg b) (ensures fshape sg (foralls ps b)) (decreases ps) =
  match ps with
  | [] -> ()
  | _ :: ps' -> fshape_foralls sg ps' b

let ctor_fshape (sg: sig) (c: qname) (ci: ctor_info) (ks: list kind)
  : Lemma (requires sig_ok sg /\ sg.ctors c == Some ci) (ensures fshape sg (kinst_ty ks ci.ct_ty)) =
  assert (ctor_ok sg c ci);
  let Some ti = sg.tycons ci.ct_owner in
  let fs = ctor_decl_fields ti ci.ct_ty in
  let ps = arg_kinds ti.tc_kind in
  let owner = ci.ct_owner in
  let res = tapps (TCon owner (kind_vars ti.tc_nk)) (type_vars (L.length ps)) in
  assert (not (is_function_tycon sg owner));
  head_tapps (TCon owner (kind_vars ti.tc_nk)) (type_vars (L.length ps));
  ashape_headed sg res owner;
  fshape_pure_arrows sg fs res;
  fshape_foralls sg ps (pure_arrows fs res);
  fshape_kinst sg ks ci.ct_ty

(* Instances of `forall`s. *)

let rec inst_some_sub (sigma: tsub) (t: typ) (ss: list typ) (u: typ)
  : Lemma (requires inst_foralls t ss == Some u)
          (ensures inst_foralls (sub_ty sigma t) (sub_tys sigma ss) == Some (sub_ty sigma u))
          (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' ->
    let TForall _ b = t in
    sub_subst1 sigma s b;
    inst_some_sub sigma (subst1_ty s b) ss' u

let rec fshape_inst (sg: sig) (t: typ) (ss: list typ) (u: typ)
  : Lemma (requires fshape sg t /\ inst_foralls t ss == Some u) (ensures fshape sg u)
          (decreases ss) =
  match ss with
  | [] -> ()
  | s :: ss' ->
    let TForall _ b = t in
    fshape_sub sg (scons s tvar) b;
    fshape_inst sg (subst1_ty s b) ss' u

let ctor_fields_sub sg c ks ss fs sigma =
  let Some ci = sg.ctors c in
  let t0 = kinst_ty ks ci.ct_ty in
  assert (scheme_ok sg ci.ct_nk ci.ct_ty);
  check_tvs_below sg (decl_ctx ci.ct_nk) ci.ct_ty KType;
  kinst_tvs_below ks 0 ci.ct_ty;
  closed_sub sigma t0;
  let Some u = inst_foralls t0 ss in
  inst_some_sub sigma t0 ss u;
  ctor_fshape sg c ci ks;
  fshape_inst sg t0 ss u;
  fshape_sub sg sigma u

let op_inst_sub_sig sg q ei op os ts ss sigma =
  op_types_closed sg q ei op os;
  op_inst_sub sigma ts ss os.arg;
  op_inst_sub sigma ts ss os.res

let eff_inst_sub_sig sg q ei op os ts sigma =
  op_types_closed sg q ei op os;
  let m = L.length os.binders in
  eff_inst_sub sigma m ts os.arg;
  eff_inst_sub sigma m ts os.res

(* Region names. *)

let rec frn_sub_ty (sigma: tsub) (t: typ) (a: atom)
  : Lemma (requires L.mem a (frn_ty t)) (ensures L.mem a (frn_ty (sub_ty sigma t))) (decreases t) =
  match t with
  | TApp t1 t2 | TRowUnion t1 t2 ->
    if L.mem a (frn_ty t1) then frn_sub_ty sigma t1 a else frn_sub_ty sigma t2 a
  | TForall _ b -> frn_sub_ty (up_tsub sigma) b a
  | TConstr c b -> if L.mem a (frn_constr c) then frn_sub_constr sigma c a else frn_sub_ty sigma b a
  | TRowExt en r -> if L.mem a (frn_ent en) then frn_sub_ent sigma en a else frn_sub_ty sigma r a

and frn_sub_ent (sigma: tsub) (en: entry) (a: atom)
  : Lemma (requires L.mem a (frn_ent en)) (ensures L.mem a (frn_ent (sub_ent sigma en)))
          (decreases en) =
  match en with
  | EntTy k t -> if L.mem a (frn_key k) then () else frn_sub_ty sigma t a
  | EntEff _ _ ts -> frn_sub_tys sigma ts a
  | EntRegion _ -> ()

and frn_sub_constr (sigma: tsub) (c: constr) (a: atom)
  : Lemma (requires L.mem a (frn_constr c)) (ensures L.mem a (frn_constr (sub_constr sigma c)))
          (decreases c) =
  match c with
  | CLacks k t -> if L.mem a (frn_key k) then () else frn_sub_ty sigma t a
  | CDisj t1 t2 -> if L.mem a (frn_ty t1) then frn_sub_ty sigma t1 a else frn_sub_ty sigma t2 a

and frn_sub_tys (sigma: tsub) (ts: list typ) (a: atom)
  : Lemma (requires L.mem a (frn_tys ts)) (ensures L.mem a (frn_tys (sub_tys sigma ts)))
          (decreases ts) =
  match ts with
  | t :: ts -> if L.mem a (frn_ty t) then frn_sub_ty sigma t a else frn_sub_tys sigma ts a

let rec frn_sub_layout (sigma: tsub) (l: layout) (a: atom)
  : Lemma (requires L.mem a (frn_layout l)) (ensures L.mem a (frn_layout (sub_layout sigma l)))
          (decreases l) =
  match l with
  | (k, t) :: l ->
    if L.mem a (frn_key k) then ()
    else if L.mem a (frn_ty t) then frn_sub_ty sigma t a
    else frn_sub_layout sigma l a

let rec frn_sub_ty_exp sigma e a =
  match e with
  | ELam t r b ->
    if L.mem a (frn_ty t) then frn_sub_ty sigma t a
    else if L.mem a (frn_ty r) then frn_sub_ty sigma r a
    else frn_sub_ty_exp sigma b a
  | EApp e1 e2 | EMerge e1 e2 ->
    if L.mem a (frn_exp e1) then frn_sub_ty_exp sigma e1 a else frn_sub_ty_exp sigma e2 a
  | ETyLam _ b -> frn_sub_ty_exp (up_tsub sigma) b a
  | ETyApp b t -> if L.mem a (frn_exp b) then frn_sub_ty_exp sigma b a else frn_sub_ty sigma t a
  | ECLam c b -> if L.mem a (frn_constr c) then frn_sub_constr sigma c a else frn_sub_ty_exp sigma b a
  | ECApp b | EFill _ b -> frn_sub_ty_exp sigma b a
  | ESelect k b | ERestrict k b -> if L.mem a (frn_key k) then () else frn_sub_ty_exp sigma b a
  | EWriteCell r k b ->
    if L.mem a (frn_rr r) || L.mem a (frn_key k) then () else frn_sub_ty_exp sigma b a
  | ELet t e1 e2 ->
    if L.mem a (frn_ty t) then frn_sub_ty sigma t a
    else if L.mem a (frn_exp e1) then frn_sub_ty_exp sigma e1 a
    else frn_sub_ty_exp sigma e2 a
  | ELetRec bs b -> if L.mem a (frn_binds bs) then frn_sub_binds sigma bs a else frn_sub_ty_exp sigma b a
  | ECase es dt | EMatch es dt ->
    if L.mem a (frn_exps es) then frn_sub_exps sigma es a else frn_sub_dt sigma dt a
  | ELetJoin ts t e1 e2 ->
    if L.mem a (frn_tys ts) then frn_sub_tys sigma ts a
    else if L.mem a (frn_ty t) then frn_sub_ty sigma t a
    else if L.mem a (frn_exp e1) then frn_sub_ty_exp sigma e1 a
    else frn_sub_ty_exp sigma e2 a
  | EJump _ es -> frn_sub_exps sigma es a
  | EExtend k e1 e2 | EUpdate k e1 e2 ->
    if L.mem a (frn_key k) then ()
    else if L.mem a (frn_exp e1) then frn_sub_ty_exp sigma e1 a
    else frn_sub_ty_exp sigma e2 a
  | EInject k t b | EWeaken k t b ->
    if L.mem a (frn_key k) then ()
    else if L.mem a (frn_ty t) then frn_sub_ty sigma t a
    else frn_sub_ty_exp sigma b a
  | EAbsurd t b | EOpenEff t b | EOpenEffC t b ->
    if L.mem a (frn_ty t) then frn_sub_ty sigma t a else frn_sub_ty_exp sigma b a
  | EPerform k _ ts b ->
    if L.mem a (frn_key k) then ()
    else if L.mem a (frn_tys ts) then frn_sub_tys sigma ts a
    else frn_sub_ty_exp sigma b a
  | EHandle b h ->
    if L.mem a (frn_exp b) then frn_sub_ty_exp sigma b a
    else if L.mem a (frn_ent h.h_ent) then frn_sub_ent sigma h.h_ent a
    else if L.mem a (frn_ty h.h_ret_ty) then frn_sub_ty sigma h.h_ret_ty a
    else if L.mem a (frn_exp h.h_ret) then frn_sub_ty_exp sigma h.h_ret a
    else frn_sub_cls sigma h.h_clauses a
  | ERegion l es b ->
    if L.mem a (frn_layout l) then frn_sub_layout sigma l a
    else if L.mem a (frn_exps es) then frn_sub_exps sigma es a
    else frn_sub_ty_exp sigma b a
  | ERegionOpen ell th b ->
    if a = ell then ()
    else if L.mem a (frn_cells th) then frn_sub_cells sigma th a
    else frn_sub_ty_exp sigma b a
  | EOpaque _ t -> frn_sub_ty sigma t a
  | _ -> ()

and frn_sub_exps (sigma: tsub) (es: list exp) (a: atom)
  : Lemma (requires L.mem a (frn_exps es)) (ensures L.mem a (frn_exps (sub_ty_exps sigma es)))
          (decreases es) =
  match es with
  | e :: es -> if L.mem a (frn_exp e) then frn_sub_ty_exp sigma e a else frn_sub_exps sigma es a

and frn_sub_binds (sigma: tsub) (bs: list (typ & exp)) (a: atom)
  : Lemma (requires L.mem a (frn_binds bs)) (ensures L.mem a (frn_binds (sub_ty_binds sigma bs)))
          (decreases bs) =
  match bs with
  | (t, e) :: bs ->
    if L.mem a (frn_ty t) then frn_sub_ty sigma t a
    else if L.mem a (frn_exp e) then frn_sub_ty_exp sigma e a
    else frn_sub_binds sigma bs a

and frn_sub_cells (sigma: tsub) (th: list (key & exp)) (a: atom)
  : Lemma (requires L.mem a (frn_cells th)) (ensures L.mem a (frn_cells (sub_ty_cells sigma th)))
          (decreases th) =
  match th with
  | (k, e) :: th ->
    if L.mem a (frn_key k) then ()
    else if L.mem a (frn_exp e) then frn_sub_ty_exp sigma e a
    else frn_sub_cells sigma th a

and frn_sub_dt (sigma: tsub) (dt: dtree) (a: atom)
  : Lemma (requires L.mem a (frn_dt dt)) (ensures L.mem a (frn_dt (sub_ty_dt sigma dt)))
          (decreases dt) =
  match dt with
  | DLeaf e -> frn_sub_ty_exp sigma e a
  | DBind o dt -> if L.mem a (frn_occ o) then () else frn_sub_dt sigma dt a
  | DSwitchCtor o bs df ->
    if L.mem a (frn_occ o) then ()
    else if L.mem a (frn_brs bs) then frn_sub_brs sigma bs a
    else frn_sub_odt sigma df a
  | DSwitchLit o bs df ->
    if L.mem a (frn_occ o) then ()
    else if L.mem a (frn_brs bs) then frn_sub_brs sigma bs a
    else frn_sub_dt sigma df a
  | DSwitchKey o bs df ->
    if L.mem a (frn_occ o) then ()
    else if L.mem a (frn_kbrs bs) then frn_sub_kbrs sigma bs a
    else frn_sub_odt sigma df a
  | DGuard e dt1 dt2 ->
    if L.mem a (frn_exp e) then frn_sub_ty_exp sigma e a
    else if L.mem a (frn_dt dt1) then frn_sub_dt sigma dt1 a
    else frn_sub_dt sigma dt2 a

and frn_sub_odt (sigma: tsub) (df: option dtree) (a: atom)
  : Lemma (requires L.mem a (frn_odt df)) (ensures L.mem a (frn_odt (sub_ty_odt sigma df)))
          (decreases df) =
  match df with
  | Some dt -> frn_sub_dt sigma dt a

and frn_sub_brs (#lb: eqtype) (sigma: tsub) (bs: list (lb & dtree)) (a: atom)
  : Lemma (requires L.mem a (frn_brs bs)) (ensures L.mem a (frn_brs (sub_ty_brs sigma bs)))
          (decreases bs) =
  match bs with
  | (_, dt) :: bs -> if L.mem a (frn_dt dt) then frn_sub_dt sigma dt a else frn_sub_brs sigma bs a

and frn_sub_kbrs (sigma: tsub) (bs: list (key & dtree)) (a: atom)
  : Lemma (requires L.mem a (frn_kbrs bs)) (ensures L.mem a (frn_kbrs (sub_ty_brs sigma bs)))
          (decreases bs) =
  match bs with
  | (k, dt) :: bs ->
    if L.mem a (frn_key k) then ()
    else if L.mem a (frn_dt dt) then frn_sub_dt sigma dt a
    else frn_sub_kbrs sigma bs a

and frn_sub_cls (sigma: tsub) (cs: list clause) (a: atom)
  : Lemma (requires L.mem a (frn_cls cs)) (ensures L.mem a (frn_cls (sub_ty_cls sigma cs)))
          (decreases cs) =
  match cs with
  | CFull _ nb s kt b :: cs ->
    if L.mem a (frn_ty s) then frn_sub_ty (upn_tsub nb sigma) s a
    else if L.mem a (frn_ty kt) then frn_sub_ty (upn_tsub nb sigma) kt a
    else if L.mem a (frn_exp b) then frn_sub_ty_exp (upn_tsub nb sigma) b a
    else frn_sub_cls sigma cs a
  | CFast _ nb s b :: cs ->
    if L.mem a (frn_ty s) then frn_sub_ty (upn_tsub nb sigma) s a
    else if L.mem a (frn_exp b) then frn_sub_ty_exp (upn_tsub nb sigma) b a
    else frn_sub_cls sigma cs a

(* Region facts. *)

let rec region_facts_intro (a: atom) (d: nat) (ks: list kind) (j: nat)
  : Lemma (requires L.nth ks j == Some (KRow EEffect))
          (ensures L.mem (CLacks (RegionKey (RFree a)) (TVar (d + j))) (region_facts a d ks))
          (decreases ks) =
  match ks with
  | _ :: ks' -> if j = 0 then () else region_facts_intro a (d + 1) ks' (j - 1)

let rec mem_lacks_each (k: key) (ts: list ctyp) (f: afact)
  : Lemma (requires L.mem f (lacks_each k ts))
          (ensures (match f with ALacks k' c -> k' == k /\ L.mem c ts | ADisj _ _ -> False))
          (decreases ts) =
  match ts with
  | c :: ts' -> if f = ALacks k c then () else mem_lacks_each k ts' f

let region_lacks_row sg g a l r =
  let g1 = enter_region g a l in
  let k = RegionKey (RFree a) in
  if inconsistent (hyps g1) then ()
  else begin
    mem_ckeys k (canon r);
    introduce forall (p: cpayload). ~(L.mem (k, p) (row_entries (canon r)))
    with introduce L.mem (k, p) (row_entries (canon r)) ==> False
    with row_entry_key sg g r EEffect k p;
    assert (cconsistent (CCLacks k (canon r)));
    check_row_tails sg g r EEffect;
    let ts = row_tails (canon r) in
    introduce forall (f: afact). L.mem f (lacks_each k ts) ==> derivable_in (gamma_star (hyps g1)) f
    with introduce _ ==> _
    with begin
      mem_lacks_each k ts f;
      let ALacks _ c = f in
      let CVar i = c in
      let h = CLacks k (TVar i) in
      region_facts_intro a 0 g.tvars i;
      LP.append_mem (region_facts a 0 g.tvars) g.facts h;
      LP.append_mem g1.facts g1.assumps h;
      assert (decompose h == Some [ALacks k (CVar i)]);
      mem_gamma_star (hyps g1) f
    end;
    all_derivable_mem (gamma_star (hyps g1)) (lacks_each k ts)
  end
