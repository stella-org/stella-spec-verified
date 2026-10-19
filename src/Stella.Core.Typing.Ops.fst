(* Proof structure.

   `op_inst τ̄ σ̄` is one substitution by the list `rev σ̄ @ rev τ̄`
   (`op_inst_list`), and `eff_inst m τ̄` is the substitution by `rev τ̄`
   lifted past `m` binders. A map of the types composes with either
   substitution into the substitution by the mapped list, pointwise on the
   variables below the length of the list (`list_tsub_map`); a
   substitution agrees with it there only, so the signature's type has its
   variables below that length (`sub_tvs_ext`). A kind instantiation and a
   region map fix every variable, so they agree everywhere.

   The signature's types are kinded in a context with no kind variable and
   no region, which `check_kinst_fixed` and `check_lc` read. *)
module Stella.Core.Typing.Ops
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Region
open Stella.Core.Region.Lemmas
open Stella.Core.Sig
open Stella.Core.Sig.Wf
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Facts
open Stella.Core.Typing.Aux
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

(* The types of an operation. *)

let rec ops_ok_assoc (sg: sig) (params: list kind) (ops: list (opname & op_sig)) (op: opname)
  (os: op_sig)
  : Lemma (requires ops_ok sg params ops /\ L.assoc op ops == Some os) (ensures op_ok sg params os)
          (decreases ops) =
  match ops with
  | p_ :: ops' -> if op = fst p_ then () else ops_ok_assoc sg params ops' op os

let rec push_tvars_closed (g: ctx) (ks: list kind)
  : Lemma (ensures (let g' = push_tvars g ks in
                    L.length g'.tvars == L.length g.tvars + L.length ks /\ g'.nk == g.nk /\
                    (g.regions == [] ==> g'.regions == [])))
          (decreases ks) =
  match ks with
  | [] -> ()
  | k :: ks' -> push_tvars_closed (push_tvar g k) ks'

let rmap_key_noregion (f: region_ref -> region_ref) (k: key)
  : Lemma (requires lc_key 0 k /\ (forall (a: atom). ~(L.mem a (frn_key k)))) (ensures rmap_key f k == k) =
  match k with
  | RegionKey (RFree a) -> assert (L.mem a (frn_key k))
  | _ -> ()

let rec rmap_noregion_ty (f: region_ref -> region_ref) (t: typ)
  : Lemma (requires lc_ty_at 0 t /\ (forall (a: atom). ~(L.mem a (frn_ty t))))
          (ensures rmap_ty f t == t) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp t1 t2 | TRowUnion t1 t2 -> rmap_noregion_ty f t1; rmap_noregion_ty f t2
  | TForall _ b -> rmap_noregion_ty f b
  | TConstr c b -> rmap_noregion_constr f c; rmap_noregion_ty f b
  | TRowExt en r -> rmap_noregion_ent f en; rmap_noregion_ty f r

and rmap_noregion_ent (f: region_ref -> region_ref) (en: entry)
  : Lemma (requires lc_ent_at 0 en /\ (forall (a: atom). ~(L.mem a (frn_ent en))))
          (ensures rmap_ent f en == en) (decreases en) =
  match en with
  | EntTy k t -> rmap_key_noregion f k; rmap_noregion_ty f t
  | EntEff _ _ ts -> rmap_noregion_tys f ts
  | EntRegion (RFree a) -> assert (L.mem a (frn_ent en))
  | EntRegion _ -> ()

and rmap_noregion_constr (f: region_ref -> region_ref) (c: constr)
  : Lemma (requires lc_constr_at 0 c /\ (forall (a: atom). ~(L.mem a (frn_constr c))))
          (ensures rmap_constr f c == c) (decreases c) =
  match c with
  | CLacks k t -> rmap_key_noregion f k; rmap_noregion_ty f t
  | CDisj t1 t2 -> rmap_noregion_ty f t1; rmap_noregion_ty f t2

and rmap_noregion_tys (f: region_ref -> region_ref) (ts: list typ)
  : Lemma (requires lc_tys_at 0 ts /\ (forall (a: atom). ~(L.mem a (frn_tys ts))))
          (ensures rmap_tys f ts == ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> rmap_noregion_ty f t; rmap_noregion_tys f ts'

let op_type_closed (sg: sig) (params binders: list kind) (t: typ)
  : Lemma (requires check sg (push_tvars (push_tvars (decl_ctx 0) params) binders) t KType)
          (ensures sig_closed (L.length binders + L.length params) t) =
  let g0 = push_tvars (push_tvars (decl_ctx 0) params) binders in
  push_tvars_closed (decl_ctx 0) params;
  push_tvars_closed (push_tvars (decl_ctx 0) params) binders;
  check_tvs_below sg g0 t KType;
  introduce forall (ks: list kind). kinst_ty ks t == t
  with check_kinst_fixed sg g0 t KType ks;
  check_lc sg g0 t KType;
  introduce forall (f: region_ref -> region_ref). rmap_ty f t == t
  with rmap_noregion_ty f t

let op_types_closed sg q ei op os =
  assert (match sg.effects q with Some ei -> effect_ok sg ei | None -> True);
  ops_ok_assoc sg ei.eff_params ei.eff_ops op os;
  op_type_closed sg ei.eff_params os.binders os.arg;
  op_type_closed sg ei.eff_params os.binders os.res

(* Lists. *)

let rec sub_tys_map (sigma: tsub) (l: list typ)
  : Lemma (ensures sub_tys sigma l == L.map (sub_ty sigma) l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l' -> sub_tys_map sigma l'

let rec kinst_tys_map (ks: list kind) (l: list typ)
  : Lemma (ensures kinst_tys ks l == L.map (kinst_ty ks) l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l' -> kinst_tys_map ks l'

let rec rmap_tys_map (f: region_ref -> region_ref) (l: list typ)
  : Lemma (ensures rmap_tys f l == L.map (rmap_ty f) l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: l' -> rmap_tys_map f l'

let rec map_rev' (f: typ -> typ) (l: list typ)
  : Lemma (ensures L.map f (LP.rev' l) == LP.rev' (L.map f l)) (decreases l) =
  match l with
  | [] -> ()
  | x :: l' -> map_rev' f l'; LP.map_append f (LP.rev' l') [x]

let map_rev (f: typ -> typ) (l: list typ) : Lemma (L.map f (L.rev l) == L.rev (L.map f l)) =
  LP.rev_rev' l;
  LP.rev_rev' (L.map f l);
  map_rev' f l

let list_tsub_cons (x: typ) (l: list typ) (i: nat)
  : Lemma (list_tsub (x :: l) i == (if i = 0 then x else list_tsub l (i - 1))) = ()

let rec list_tsub_map (f: typ -> typ) (l: list typ) (i: nat)
  : Lemma (ensures list_tsub (L.map f l) i ==
                   (if i < L.length l then f (list_tsub l i) else list_tsub l i))
          (decreases l) =
  match l with
  | [] -> ()
  | x :: l' ->
    list_tsub_cons x l' i;
    list_tsub_cons (f x) (L.map f l') i;
    if i = 0 then () else list_tsub_map f l' (i - 1)

let rec list_tsub_append (a b: list typ) (i: nat)
  : Lemma (ensures list_tsub (L.append a b) i ==
                   (if i < L.length a then list_tsub a i else list_tsub b (i - L.length a)))
          (decreases a) =
  match a with
  | [] -> ()
  | x :: a' ->
    list_tsub_cons x (L.append a' b) i;
    list_tsub_cons x a' i;
    if i = 0 then () else list_tsub_append a' b (i - 1)

(* `op_inst` as one substitution. *)

let op_inst_at (a b: list typ) (i: nat)
  : Lemma (sub_ty (upn_tsub 0 (list_tsub a)) (upn_tsub (L.length a) (list_tsub b) i) ==
           list_tsub (L.append a b) i) =
  let m = L.length a in
  let tau = upn_tsub 0 (list_tsub a) in
  list_tsub_append a b i;
  introduce forall (j: nat). tau j == list_tsub a j
  with ren_ty_shift0 (list_tsub a j);
  if i < m then ()
  else begin
    let x = list_tsub b (i - m) in
    introduce forall (j: nat). tvar j == tau (shift m j)
    with ren_ty_shift0 (list_tsub a (shift m j));
    sub_ren_ty tau (shift m) tvar x;
    sub_ty_tvar x
  end

let op_inst_list (ts ss: list typ) (t: typ)
  : Lemma (op_inst ts ss t == sub_ty (list_tsub (L.append (L.rev ss) (L.rev ts))) t) =
  let a = L.rev ss in
  let b = L.rev ts in
  LP.rev_length ss;
  introduce forall (i: nat).
    list_tsub (L.append a b) i ==
    sub_ty (upn_tsub 0 (list_tsub a)) (upn_tsub (L.length a) (list_tsub b) i)
  with op_inst_at a b i;
  sub_sub_ty (upn_tsub 0 (list_tsub a)) (upn_tsub (L.length a) (list_tsub b))
    (list_tsub (L.append a b)) t

(* The instantiating list of the mapped types is the mapped list. *)
let inst_list_map (f: typ -> typ) (ts ss: list typ)
  : Lemma (L.append (L.rev (L.map f ss)) (L.rev (L.map f ts)) ==
           L.map f (L.append (L.rev ss) (L.rev ts)) /\
           L.length (L.append (L.rev ss) (L.rev ts)) == L.length ss + L.length ts) =
  map_rev f ss;
  map_rev f ts;
  LP.map_append f (L.rev ss) (L.rev ts);
  LP.append_length (L.rev ss) (L.rev ts);
  LP.rev_length ss;
  LP.rev_length ts

(* `perform`. *)

let op_inst_sub sigma ts ss t =
  let l = L.append (L.rev ss) (L.rev ts) in
  let f = sub_ty sigma in
  sub_tys_map sigma ts;
  sub_tys_map sigma ss;
  inst_list_map f ts ss;
  op_inst_list ts ss t;
  op_inst_list (L.map f ts) (L.map f ss) t;
  let comp (i: nat) : typ = sub_ty sigma (list_tsub l i) in
  sub_sub_ty sigma (list_tsub l) comp t;
  FStar.Classical.forall_intro (list_tsub_map f l);
  sub_tvs_ext (L.length l) comp (list_tsub (L.map f l)) t

let op_inst_ren xi ts ss t =
  ren_ty_as_sub xi (op_inst ts ss t);
  op_inst_sub (ren_tsub xi) ts ss t;
  rinst_tys xi (ren_tsub xi) ts;
  rinst_tys xi (ren_tsub xi) ss

let op_inst_kinst ks ts ss t =
  let l = L.append (L.rev ss) (L.rev ts) in
  let f = kinst_ty ks in
  kinst_tys_map ks ts;
  kinst_tys_map ks ss;
  inst_list_map f ts ss;
  op_inst_list ts ss t;
  op_inst_list (L.map f ts) (L.map f ss) t;
  FStar.Classical.forall_intro (list_tsub_map f l);
  kinst_sub_ty ks (list_tsub l) (list_tsub (L.map f l)) t

let op_inst_rmap f ts ss t =
  let l = L.append (L.rev ss) (L.rev ts) in
  let g = rmap_ty f in
  rmap_tys_map f ts;
  rmap_tys_map f ss;
  inst_list_map g ts ss;
  op_inst_list ts ss t;
  op_inst_list (L.map g ts) (L.map g ss) t;
  FStar.Classical.forall_intro (list_tsub_map g l);
  rmap_sub_ty f (list_tsub l) (list_tsub (L.map g l)) t

(* Clauses. *)

let rev_map_tsub (f: typ -> typ) (ts: list typ) (i: nat)
  : Lemma (list_tsub (L.rev (L.map f ts)) i ==
           (if i < L.length ts then f (list_tsub (L.rev ts) i) else list_tsub (L.rev ts) i)) =
  map_rev f ts;
  LP.rev_length ts;
  list_tsub_map f (L.rev ts) i

let eff_inst_sub sigma m ts t =
  let lt = list_tsub (L.rev ts) in
  let f = sub_ty sigma in
  sub_tys_map sigma ts;
  let lt' = list_tsub (L.rev (L.map f ts)) in
  let comp (i: nat) : typ = sub_ty sigma (lt i) in
  upn_sub_sub_ty m sigma lt comp;
  sub_sub_ty (upn_tsub m sigma) (upn_tsub m lt) (upn_tsub m comp) t;
  introduce forall (i: nat). i < m + L.length ts ==> upn_tsub m comp i == upn_tsub m lt' i
  with introduce _ ==> _
  with (if i < m then () else rev_map_tsub f ts (i - m));
  sub_tvs_ext (m + L.length ts) (upn_tsub m comp) (upn_tsub m lt') t

let eff_inst_ren xi m ts t =
  upn_rinst_ty m xi (ren_tsub xi);
  rinst_ty (upn_ren m xi) (upn_tsub m (ren_tsub xi)) (eff_inst m ts t);
  eff_inst_sub (ren_tsub xi) m ts t;
  rinst_tys xi (ren_tsub xi) ts

let eff_inst_kinst ks m ts t =
  let lt = list_tsub (L.rev ts) in
  let f = kinst_ty ks in
  kinst_tys_map ks ts;
  let lt' = list_tsub (L.rev (L.map f ts)) in
  introduce forall (i: nat). upn_tsub m lt' i == kinst_ty ks (upn_tsub m lt i)
  with (if i < m then ()
        else begin
          let i' = i - m in
          rev_map_tsub f ts i';
          kinst_ren_ty ks (shift m) (lt i');
          LP.rev_length ts;
          if i' < L.length ts then () else assert (lt i' == TVar (i' - L.length ts))
        end);
  kinst_sub_ty ks (upn_tsub m lt) (upn_tsub m lt') t

let eff_inst_rmap f m ts t =
  let lt = list_tsub (L.rev ts) in
  let g = rmap_ty f in
  rmap_tys_map f ts;
  let lt' = list_tsub (L.rev (L.map g ts)) in
  introduce forall (i: nat). upn_tsub m lt' i == rmap_ty f (upn_tsub m lt i)
  with (if i < m then ()
        else begin
          let i' = i - m in
          rev_map_tsub g ts i';
          rmap_ren_ty f (shift m) (lt i');
          LP.rev_length ts;
          if i' < L.length ts then () else assert (lt i' == TVar (i' - L.length ts))
        end);
  rmap_sub_ty f (upn_tsub m lt) (upn_tsub m lt') t
