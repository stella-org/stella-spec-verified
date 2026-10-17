(* Proof structure.

   Every fact about rows reduces to membership: `seteq` facts about `norm`,
   `L.append`, `L.map` and `flat_*` come first, and `veq` lifts `seteq` to
   row views.

   The four operations `cren`, `csub`, `cmap` and `ckinst` share one row
   argument. For each of them, the view of the image of any form has the
   members of `rop fe fv` applied to the form's view (`op_view`,
   established by `cren_op_view`, `csub_op_view`, `cmap_op_view` and
   `ckinst_op_view`), and every image is `row_canonical`. From these two
   facts alone, `ext_case` and `union_case` close the row cases of all
   four commutation theorems: both sides are row-canonical and their views
   have the same members.

   The substitution theorem lifts `s` under a binder with `cren`, so it
   uses the renaming theorem at the substitutes; renaming is therefore
   proved first. *)
module Stella.Core.Rows.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.OrdSet
open Stella.Core.Rows
module L = FStar.List.Tot

(* Membership facts about lists. *)

let mem_app (#a: eqtype) (z: a) (l1 l2: list a)
  : Lemma (L.mem z (L.append l1 l2) = (L.mem z l1 || L.mem z l2))
          [SMTPat (L.mem z (L.append l1 l2))] =
  FStar.List.Tot.Properties.append_mem l1 l2 z

let rec mem_map (#a #b: eqtype) (f: a -> b) (l: list a) (x: a)
  : Lemma (requires L.mem x l) (ensures L.mem (f x) (L.map f l)) (decreases l) =
  match l with
  | y :: tl -> if x = y then () else mem_map f tl x

let rec map_incl (#a #b: eqtype) (f: a -> b) (l l': list a)
  : Lemma (requires incl l l') (ensures incl (L.map f l) (L.map f l')) (decreases l) =
  match l with
  | [] -> ()
  | x :: tl -> mem_map f l' x; map_incl f tl l'

let map_seteq (#a #b: eqtype) (f: a -> b) (l l': list a)
  : Lemma (requires seteq l l') (ensures seteq (L.map f l) (L.map f l')) =
  map_incl f l l'; map_incl f l' l

let rec mem_flat_es (v: rview) (vs: list rview)
  : Lemma (requires L.mem v vs) (ensures incl (fst v) (flat_es vs)) (decreases vs) =
  match vs with
  | w :: tl -> if v = w then () else mem_flat_es v tl

let rec mem_flat_ts (v: rview) (vs: list rview)
  : Lemma (requires L.mem v vs) (ensures incl (snd v) (flat_ts vs)) (decreases vs) =
  match vs with
  | w :: tl -> if v = w then () else mem_flat_ts v tl

let rec flat_incl (vs vs': list rview)
  : Lemma (requires incl vs vs')
          (ensures incl (flat_es vs) (flat_es vs') /\ incl (flat_ts vs) (flat_ts vs'))
          (decreases vs) =
  match vs with
  | [] -> ()
  | v :: tl -> mem_flat_es v vs'; mem_flat_ts v vs'; flat_incl tl vs'

let flat_seteq (vs vs': list rview)
  : Lemma (requires seteq vs vs')
          (ensures seteq (flat_es vs) (flat_es vs') /\ seteq (flat_ts vs) (flat_ts vs')) =
  flat_incl vs vs'; flat_incl vs' vs

let rec flat_append (vs1 vs2: list rview)
  : Lemma (flat_es (L.append vs1 vs2) == L.append (flat_es vs1) (flat_es vs2) /\
           flat_ts (L.append vs1 vs2) == L.append (flat_ts vs1) (flat_ts vs2))
          (decreases vs1) =
  match vs1 with
  | [] -> ()
  | v :: tl ->
    flat_append tl vs2;
    FStar.List.Tot.Properties.append_assoc (fst v) (flat_es tl) (flat_es vs2);
    FStar.List.Tot.Properties.append_assoc (snd v) (flat_ts tl) (flat_ts vs2)

let norm_seteq (#a: eqtype) (o: ord a) (l: list a) : Lemma (seteq (norm o l) l) = ()

let seteq_cons (#a: eqtype) (x: a) (l l': list a)
  : Lemma (requires seteq l l') (ensures seteq (x :: l) (x :: l')) = ()

let seteq_trans (#a: eqtype) (l1 l2 l3: list a)
  : Lemma (requires seteq l1 l2 /\ seteq l2 l3) (ensures seteq l1 l3) = ()

let veq (v1 v2: rview) : prop = seteq (fst v1) (fst v2) /\ seteq (snd v1) (snd v2)

let view_mkrow es ts =
  match es, ts with
  | [], [t] -> ()
  | _ -> ()

let view_nrow es ts = view_mkrow (norm ord_centry es) (norm ord_ctyp ts)

let nrow_ext es es' ts ts' =
  norm_ext ord_centry es es';
  norm_ext ord_ctyp ts ts'

let row_canonical_nrow es ts =
  view_nrow es ts;
  norm_idem ord_centry es;
  norm_idem ord_ctyp ts

let row_canonical_nonrow c = assert_norm (norm ord_ctyp [c] == [c])

let row_canonical_sorted c =
  view_nrow (row_entries c) (row_tails c);
  sorted_norm ord_centry (row_entries c);
  sorted_norm ord_ctyp (row_tails c)

let row_canonical_ext c1 c2 =
  nrow_ext (row_entries c1) (row_entries c2) (row_tails c1) (row_tails c2)

(* The row argument shared by the three operations. *)

let op_view (fe: centry -> centry) (fv: ctyp -> rview) (c fc: ctyp) : prop =
  veq (view_row fc) (rop fe fv (view_row c))

let rop_veq (fe: centry -> centry) (fv: ctyp -> rview) (v v': rview)
  : Lemma (requires veq v v') (ensures veq (rop fe fv v) (rop fe fv v')) =
  map_seteq fe (fst v) (fst v');
  map_seteq fv (snd v) (snd v');
  flat_seteq (L.map fv (snd v)) (L.map fv (snd v'))

let rop_append (fe: centry -> centry) (fv: ctyp -> rview) (v1 v2: rview)
  : Lemma (let r1 = rop fe fv v1 in
           let r2 = rop fe fv v2 in
           veq (rop fe fv (L.append (fst v1) (fst v2), L.append (snd v1) (snd v2)))
               (L.append (fst r1) (fst r2), L.append (snd r1) (snd r2))) =
  FStar.List.Tot.Properties.map_append fe (fst v1) (fst v2);
  FStar.List.Tot.Properties.map_append fv (snd v1) (snd v2);
  flat_append (L.map fv (snd v1)) (L.map fv (snd v2))

(* The view of an `nrow` has the members of its arguments. *)
let view_nrow_veq (es: list centry) (ts: list ctyp)
  : Lemma (veq (view_row (nrow es ts)) (es, ts)) =
  view_nrow es ts

let veq_trans (v1 v2 v3: rview)
  : Lemma (requires veq v1 v2 /\ veq v2 v3) (ensures veq v1 v3) = ()

let veq_append (v1 v1' v2 v2': rview)
  : Lemma (requires veq v1 v1' /\ veq v2 v2')
          (ensures veq (L.append (fst v1) (fst v2), L.append (snd v1) (snd v2))
                       (L.append (fst v1') (fst v2'), L.append (snd v1') (snd v2'))) = ()

let ext_case (fe: centry -> centry) (fv: ctyp -> rview) (ce: centry) (c fc fN: ctyp)
  : Lemma (requires op_view fe fv c fc /\
                    op_view fe fv (nrow (ce :: row_entries c) (row_tails c)) fN /\
                    row_canonical fN)
          (ensures nrow (fe ce :: row_entries fc) (row_tails fc) == fN) =
  let n = nrow (ce :: row_entries c) (row_tails c) in
  view_nrow_veq (ce :: row_entries c) (row_tails c);
  rop_veq fe fv (view_row n) (ce :: row_entries c, row_tails c);
  let lhs = nrow (fe ce :: row_entries fc) (row_tails fc) in
  view_nrow_veq (fe ce :: row_entries fc) (row_tails fc);
  row_canonical_nrow (fe ce :: row_entries fc) (row_tails fc);
  row_canonical_ext lhs fN

let union_case (fe: centry -> centry) (fv: ctyp -> rview) (c1 c2 fc1 fc2 fN: ctyp)
  : Lemma (requires op_view fe fv c1 fc1 /\ op_view fe fv c2 fc2 /\
                    op_view fe fv
                      (nrow (L.append (row_entries c1) (row_entries c2))
                            (L.append (row_tails c1) (row_tails c2))) fN /\
                    row_canonical fN)
          (ensures nrow (L.append (row_entries fc1) (row_entries fc2))
                        (L.append (row_tails fc1) (row_tails fc2)) == fN) =
  let v = (L.append (row_entries c1) (row_entries c2), L.append (row_tails c1) (row_tails c2)) in
  let n = nrow (fst v) (snd v) in
  view_nrow_veq (fst v) (snd v);
  rop_veq fe fv (view_row n) v;
  rop_append fe fv (view_row c1) (view_row c2);
  let r1 = rop fe fv (view_row c1) in
  let r2 = rop fe fv (view_row c2) in
  let es = L.append (row_entries fc1) (row_entries fc2) in
  let ts = L.append (row_tails fc1) (row_tails fc2) in
  veq_append (view_row fc1) r1 (view_row fc2) r2;
  let r12 = (L.append (fst r1) (fst r2), L.append (snd r1) (snd r2)) in
  veq_trans (view_row fN) (rop fe fv (view_row n)) (rop fe fv v);
  veq_trans (view_row fN) (rop fe fv v) r12;
  view_nrow_veq es ts;
  veq_trans (view_row (nrow es ts)) (es, ts) r12;
  row_canonical_nrow es ts;
  row_canonical_ext (nrow es ts) fN

(* On a form `c` that is not a row, `rop` has the members of `fv c`. *)
let rop_single (fe: centry -> centry) (fv: ctyp -> rview) (c: ctyp)
  : Lemma (veq (rop fe fv ([], [c])) (fv c)) =
  let v = fv c in
  assert (L.map fv [c] == [v]);
  assert (flat_es [v] == L.append (fst v) [] /\ flat_ts [v] == L.append (snd v) []);
  FStar.List.Tot.Properties.append_l_nil (fst v);
  FStar.List.Tot.Properties.append_l_nil (snd v)

(* Each operation as an instance of the shared argument. *)

let rec cren_maps (xi: ren) (es: list centry) (ts: list ctyp)
  : Lemma (ensures cren_ents xi es == L.map (cren_ent xi) es /\
                   cren_views xi ts == L.map (cren_vf xi) ts)
          (decreases %[es; ts]) =
  match es, ts with
  | [], [] -> ()
  | _ :: es', _ -> cren_maps xi es' ts
  | [], _ :: ts' -> cren_maps xi [] ts'

let cren_op_view (xi: ren) (c: ctyp)
  : Lemma (op_view (cren_ent xi) (cren_vf xi) c (cren xi c)) =
  match c with
  | CRow es ts ->
    cren_maps xi es ts;
    let v = rop (cren_ent xi) (cren_vf xi) (es, ts) in
    view_nrow_veq (fst v) (snd v)
  | _ -> rop_single (cren_ent xi) (cren_vf xi) c

let cren_view xi c = cren_op_view xi c

let row_canonical_cren xi c =
  match c with
  | CRow es ts -> row_canonical_nrow (L.append (cren_ents xi es) (flat_es (cren_views xi ts)))
                   (flat_ts (cren_views xi ts))
  | _ -> row_canonical_nonrow (cren xi c)

let rec csub_maps (s: csubst) (es: list centry) (ts: list ctyp)
  : Lemma (ensures csub_ents s es == L.map (csub_ent s) es /\
                   csub_views s ts == L.map (csub_vf s) ts)
          (decreases %[es; ts]) =
  match es, ts with
  | [], [] -> ()
  | _ :: es', _ -> csub_maps s es' ts
  | [], _ :: ts' -> csub_maps s [] ts'

let csub_op_view (s: csubst) (c: ctyp)
  : Lemma (op_view (csub_ent s) (csub_vf s) c (csub s c)) =
  match c with
  | CRow es ts ->
    csub_maps s es ts;
    let v = rop (csub_ent s) (csub_vf s) (es, ts) in
    view_nrow_veq (fst v) (snd v)
  | _ -> rop_single (csub_ent s) (csub_vf s) c

let csub_view s c = csub_op_view s c

let row_canonical_csub s c =
  match c with
  | CVar _ -> ()
  | CRow es ts -> row_canonical_nrow (L.append (csub_ents s es) (flat_es (csub_views s ts)))
                   (flat_ts (csub_views s ts))
  | _ -> row_canonical_nonrow (csub s c)

let rec cmap_maps (f: region_ref -> region_ref) (es: list centry) (ts: list ctyp)
  : Lemma (ensures cmap_ents f es == L.map (cmap_ent f) es /\
                   cmap_views f ts == L.map (cmap_vf f) ts)
          (decreases %[es; ts]) =
  match es, ts with
  | [], [] -> ()
  | _ :: es', _ -> cmap_maps f es' ts
  | [], _ :: ts' -> cmap_maps f [] ts'

let cmap_op_view (f: region_ref -> region_ref) (c: ctyp)
  : Lemma (op_view (cmap_ent f) (cmap_vf f) c (cmap f c)) =
  match c with
  | CRow es ts ->
    cmap_maps f es ts;
    let v = rop (cmap_ent f) (cmap_vf f) (es, ts) in
    view_nrow_veq (fst v) (snd v)
  | _ -> rop_single (cmap_ent f) (cmap_vf f) c

let cmap_view f c = cmap_op_view f c

let row_canonical_cmap f c =
  match c with
  | CRow es ts -> row_canonical_nrow (L.append (cmap_ents f es) (flat_es (cmap_views f ts)))
                   (flat_ts (cmap_views f ts))
  | _ -> row_canonical_nonrow (cmap f c)

let rec ckinst_maps (ks: list kind) (es: list centry) (ts: list ctyp)
  : Lemma (ensures ckinst_ents ks es == L.map (ckinst_ent ks) es /\
                   ckinst_views ks ts == L.map (ckinst_vf ks) ts)
          (decreases %[es; ts]) =
  match es, ts with
  | [], [] -> ()
  | _ :: es', _ -> ckinst_maps ks es' ts
  | [], _ :: ts' -> ckinst_maps ks [] ts'

let ckinst_op_view (ks: list kind) (c: ctyp)
  : Lemma (op_view (ckinst_ent ks) (ckinst_vf ks) c (ckinst ks c)) =
  match c with
  | CRow es ts ->
    ckinst_maps ks es ts;
    let v = rop (ckinst_ent ks) (ckinst_vf ks) (es, ts) in
    view_nrow_veq (fst v) (snd v)
  | _ -> rop_single (ckinst_ent ks) (ckinst_vf ks) c

let ckinst_view ks c = ckinst_op_view ks c

let row_canonical_ckinst ks c =
  match c with
  | CRow es ts -> row_canonical_nrow (L.append (ckinst_ents ks es) (flat_es (ckinst_views ks ts)))
                   (flat_ts (ckinst_views ks ts))
  | _ -> row_canonical_nonrow (ckinst ks c)

let canon_row_canonical t =
  match t with
  | TRowEmpty -> assert_norm (row_canonical (CRow [] []))
  | TRowExt en r ->
    let v = view_row (canon r) in
    row_canonical_nrow (canon_ent en :: fst v) (snd v)
  | TRowUnion a b ->
    let v1 = view_row (canon a) in
    let v2 = view_row (canon b) in
    row_canonical_nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2))
  | _ -> row_canonical_nonrow (canon t)

let canon_sorted t = canon_row_canonical t; row_canonical_sorted (canon t)

let rec canon_tails_nonrow t c =
  match t with
  | TRowExt en r ->
    let v = view_row (canon r) in
    view_nrow (canon_ent en :: fst v) (snd v);
    canon_tails_nonrow r c
  | TRowUnion a b ->
    let v1 = view_row (canon a) in
    let v2 = view_row (canon b) in
    view_nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2));
    if L.mem c (snd v1) then canon_tails_nonrow a c else canon_tails_nonrow b c
  | _ -> ()

let canon_not_single_tail t =
  match canon t with
  | CRow [] [x] ->
    canon_row_canonical t;
    canon_tails_nonrow t x;
    assert (norm ord_ctyp [x] == [x])
  | _ -> ()

let canon_ent_key en = ()

let ty_eq_refl t = ()

let ty_eq_sym t1 t2 = ()

let ty_eq_trans t1 t2 t3 = ()

let union_idem r =
  let v = view_row (canon r) in
  nrow_ext (L.append (fst v) (fst v)) (fst v) (L.append (snd v) (snd v)) (snd v);
  canon_row_canonical r

let union_empty_r r =
  let v = view_row (canon r) in
  FStar.List.Tot.Properties.append_l_nil (fst v);
  FStar.List.Tot.Properties.append_l_nil (snd v);
  canon_row_canonical r

let union_empty_l r = canon_row_canonical r

let union_comm a b =
  let v1 = view_row (canon a) in
  let v2 = view_row (canon b) in
  nrow_ext (L.append (fst v1) (fst v2)) (L.append (fst v2) (fst v1))
           (L.append (snd v1) (snd v2)) (L.append (snd v2) (snd v1))

let union_assoc a b c =
  let va = view_row (canon a) in
  let vb = view_row (canon b) in
  let vc = view_row (canon c) in
  view_nrow (L.append (fst va) (fst vb)) (L.append (snd va) (snd vb));
  view_nrow (L.append (fst vb) (fst vc)) (L.append (snd vb) (snd vc));
  nrow_ext (L.append (norm ord_centry (L.append (fst va) (fst vb))) (fst vc))
           (L.append (fst va) (norm ord_centry (L.append (fst vb) (fst vc))))
           (L.append (norm ord_ctyp (L.append (snd va) (snd vb))) (snd vc))
           (L.append (snd va) (norm ord_ctyp (L.append (snd vb) (snd vc))))

let ext_as_union en r =
  let ce = canon_ent en in
  assert (norm ord_centry [ce] == [ce]);
  assert (norm ord_ctyp [] == []);
  view_nrow [ce] [];
  assert (view_row (canon (TRowExt en TRowEmpty)) == ([ce], []))

let ext_comm e1 e2 r =
  let v = view_row (canon r) in
  let c1 = canon_ent e1 in
  let c2 = canon_ent e2 in
  view_nrow (c2 :: fst v) (snd v);
  view_nrow (c1 :: fst v) (snd v);
  let l1 = c1 :: norm ord_centry (c2 :: fst v) in
  let l2 = c2 :: norm ord_centry (c1 :: fst v) in
  norm_seteq ord_centry (c2 :: fst v);
  norm_seteq ord_centry (c1 :: fst v);
  seteq_cons c1 (norm ord_centry (c2 :: fst v)) (c2 :: fst v);
  seteq_cons c2 (norm ord_centry (c1 :: fst v)) (c1 :: fst v);
  assert (seteq (c1 :: c2 :: fst v) (c2 :: c1 :: fst v));
  seteq_trans l1 (c1 :: c2 :: fst v) (c2 :: c1 :: fst v);
  seteq_trans l1 (c2 :: c1 :: fst v) l2;
  nrow_ext l1 l2 (norm ord_ctyp (snd v)) (norm ord_ctyp (snd v))

let ext_idem en r =
  let v = view_row (canon r) in
  let c = canon_ent en in
  view_nrow (c :: fst v) (snd v);
  norm_seteq ord_centry (c :: fst v);
  seteq_cons c (norm ord_centry (c :: fst v)) (c :: fst v);
  assert (seteq (c :: c :: fst v) (c :: fst v));
  seteq_trans (c :: norm ord_centry (c :: fst v)) (c :: c :: fst v) (c :: fst v);
  nrow_ext (c :: norm ord_centry (c :: fst v)) (c :: fst v) (norm ord_ctyp (snd v)) (snd v)

let ty_eq_union_cong a a' b b' = ()

let ty_eq_ext_cong e e' r r' = ()

let canon_nonrow t = ()

let canon_ext_row en r =
  let v = view_row (canon r) in
  mem_norm ord_centry (canon_ent en :: fst v) (canon_ent en);
  view_nrow (canon_ent en :: fst v) (snd v)

let ty_eq_head t1 t2 = ()

let ty_eq_row_nonrow t1 t2 =
  match t1 with
  | TRowExt en r -> canon_ext_row en r
  | _ -> ()

let ty_eq_var_inv i j = ()

let ty_eq_con_inv q q' ks ks' = ()

let ty_eq_app_inv a b c d = ()

let ty_eq_forall_inv k k' a b = ()

let ty_eq_constr_inv c c' a b = ()

let constr_eq_lacks_inv k k' r r' = ()

let constr_eq_disj_inv a b a' b' = ()

let constr_eq_lacks_disj k r a b = ()

let rec mem_keys_of (k: key) (es: list centry)
  : Lemma (L.mem k (keys_of es) <==> (exists (p: cpayload). L.mem (k, p) es)) (decreases es) =
  match es with
  | [] -> ()
  | (k', p') :: tl -> mem_keys_of k tl

let rec keys_of_incl (es es': list centry)
  : Lemma (requires incl es es') (ensures incl (keys_of es) (keys_of es')) (decreases es) =
  match es with
  | [] -> ()
  | (k, p) :: tl -> mem_keys_of k es'; keys_of_incl tl es'

let rec keys_of_append (es es': list centry)
  : Lemma (keys_of (L.append es es') == L.append (keys_of es) (keys_of es')) (decreases es) =
  match es with
  | [] -> ()
  | _ :: tl -> keys_of_append tl es'

(* `keys_of` respects `seteq`, so the keys of a normalized list are those of
   the list. *)
let keys_of_norm (k: key) (es: list centry)
  : Lemma (L.mem k (keys_of (norm ord_centry es)) = L.mem k (keys_of es)) =
  keys_of_incl (norm ord_centry es) es;
  keys_of_incl es (norm ord_centry es)

let mem_ckeys k c = mem_keys_of k (row_entries c)

let known_keys_empty () = ()

let mem_known_keys_ext k en r =
  let v = view_row (canon r) in
  view_nrow (canon_ent en :: fst v) (snd v);
  keys_of_norm k (canon_ent en :: fst v)

let mem_known_keys_union k a b =
  let v1 = view_row (canon a) in
  let v2 = view_row (canon b) in
  view_nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2));
  keys_of_norm k (L.append (fst v1) (fst v2));
  keys_of_append (fst v1) (fst v2)

let rec canon_ren (xi: ren) (t: typ)
  : Lemma (ensures canon (ren_ty xi t) == cren xi (canon t)) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp a b -> canon_ren xi a; canon_ren xi b
  | TForall _ a -> canon_ren (up_ren xi) a
  | TConstr cn a -> canon_ren_constr xi cn; canon_ren xi a
  | TRowExt en r ->
    canon_ren_ent xi en;
    canon_ren xi r;
    cren_op_view xi (canon r);
    cren_op_view xi (canon t);
    row_canonical_cren xi (canon t);
    ext_case (cren_ent xi) (cren_vf xi) (canon_ent en) (canon r) (cren xi (canon r))
      (cren xi (canon t))
  | TRowUnion a b ->
    canon_ren xi a;
    canon_ren xi b;
    cren_op_view xi (canon a);
    cren_op_view xi (canon b);
    cren_op_view xi (canon t);
    row_canonical_cren xi (canon t);
    union_case (cren_ent xi) (cren_vf xi) (canon a) (canon b) (cren xi (canon a))
      (cren xi (canon b)) (cren xi (canon t))

and canon_ren_ent (xi: ren) (en: entry)
  : Lemma (ensures canon_ent (ren_ent xi en) == cren_ent xi (canon_ent en)) (decreases en) =
  match en with
  | EntTy _ t -> canon_ren xi t
  | EntEff _ _ ts -> canon_ren_tys xi ts
  | EntRegion _ -> ()

and canon_ren_constr (xi: ren) (cn: constr)
  : Lemma (ensures canon_constr (ren_constr xi cn) == cren_constr xi (canon_constr cn))
          (decreases cn) =
  match cn with
  | CLacks _ t -> canon_ren xi t
  | CDisj a b -> canon_ren xi a; canon_ren xi b

and canon_ren_tys (xi: ren) (ts: list typ)
  : Lemma (ensures canon_tys (ren_tys xi ts) == cren_list xi (canon_tys ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> canon_ren xi t; canon_ren_tys xi ts

let sub_row_canonical (sigma: tsub) (s: csubst)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures forall (i: nat). row_canonical (s i)) =
  introduce forall (i: nat). row_canonical (s i) with canon_row_canonical (sigma i)

(* Lifting preserves the agreement of `s` with `canon ∘ σ`: a shifted
   substitute is the canonical form of the shifted type. *)
let cup_canon (sigma: tsub) (s: csubst)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures forall (i: nat). cup s i == canon (up_tsub sigma i)) =
  introduce forall (i: nat). cup s i == canon (up_tsub sigma i)
  with (if i = 0 then () else canon_ren (shift 1) (sigma (i - 1)))

let rec canon_sub (sigma: tsub) (s: csubst) (t: typ)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures canon (sub_ty sigma t) == csub s (canon t))
          (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp a b -> canon_sub sigma s a; canon_sub sigma s b
  | TForall _ a -> cup_canon sigma s; canon_sub (up_tsub sigma) (cup s) a
  | TConstr cn a -> canon_sub_constr sigma s cn; canon_sub sigma s a
  | TRowExt en r ->
    canon_sub_ent sigma s en;
    canon_sub sigma s r;
    sub_row_canonical sigma s;
    csub_op_view s (canon r);
    csub_op_view s (canon t);
    row_canonical_csub s (canon t);
    ext_case (csub_ent s) (csub_vf s) (canon_ent en) (canon r) (csub s (canon r))
      (csub s (canon t))
  | TRowUnion a b ->
    canon_sub sigma s a;
    canon_sub sigma s b;
    sub_row_canonical sigma s;
    csub_op_view s (canon a);
    csub_op_view s (canon b);
    csub_op_view s (canon t);
    row_canonical_csub s (canon t);
    union_case (csub_ent s) (csub_vf s) (canon a) (canon b) (csub s (canon a))
      (csub s (canon b)) (csub s (canon t))

and canon_sub_ent (sigma: tsub) (s: csubst) (en: entry)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures canon_ent (sub_ent sigma en) == csub_ent s (canon_ent en))
          (decreases en) =
  match en with
  | EntTy _ t -> canon_sub sigma s t
  | EntEff _ _ ts -> canon_sub_tys sigma s ts
  | EntRegion _ -> ()

and canon_sub_constr (sigma: tsub) (s: csubst) (cn: constr)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures canon_constr (sub_constr sigma cn) == csub_constr s (canon_constr cn))
          (decreases cn) =
  match cn with
  | CLacks _ t -> canon_sub sigma s t
  | CDisj a b -> canon_sub sigma s a; canon_sub sigma s b

and canon_sub_tys (sigma: tsub) (s: csubst) (ts: list typ)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures canon_tys (sub_tys sigma ts) == csub_list s (canon_tys ts))
          (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> canon_sub sigma s t; canon_sub_tys sigma s ts

let rec canon_rmap (f: region_ref -> region_ref) (t: typ)
  : Lemma (ensures canon (rmap_ty f t) == cmap f (canon t)) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp a b -> canon_rmap f a; canon_rmap f b
  | TForall _ a -> canon_rmap f a
  | TConstr cn a -> canon_rmap_constr f cn; canon_rmap f a
  | TRowExt en r ->
    canon_rmap_ent f en;
    canon_rmap f r;
    cmap_op_view f (canon r);
    cmap_op_view f (canon t);
    row_canonical_cmap f (canon t);
    ext_case (cmap_ent f) (cmap_vf f) (canon_ent en) (canon r) (cmap f (canon r))
      (cmap f (canon t))
  | TRowUnion a b ->
    canon_rmap f a;
    canon_rmap f b;
    cmap_op_view f (canon a);
    cmap_op_view f (canon b);
    cmap_op_view f (canon t);
    row_canonical_cmap f (canon t);
    union_case (cmap_ent f) (cmap_vf f) (canon a) (canon b) (cmap f (canon a))
      (cmap f (canon b)) (cmap f (canon t))

and canon_rmap_ent (f: region_ref -> region_ref) (en: entry)
  : Lemma (ensures canon_ent (rmap_ent f en) == cmap_ent f (canon_ent en)) (decreases en) =
  match en with
  | EntTy _ t -> canon_rmap f t
  | EntEff _ _ ts -> canon_rmap_tys f ts
  | EntRegion _ -> ()

and canon_rmap_constr (f: region_ref -> region_ref) (cn: constr)
  : Lemma (ensures canon_constr (rmap_constr f cn) == cmap_constr f (canon_constr cn))
          (decreases cn) =
  match cn with
  | CLacks _ t -> canon_rmap f t
  | CDisj a b -> canon_rmap f a; canon_rmap f b

and canon_rmap_tys (f: region_ref -> region_ref) (ts: list typ)
  : Lemma (ensures canon_tys (rmap_tys f ts) == cmap_list f (canon_tys ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> canon_rmap f t; canon_rmap_tys f ts

let canon_open_region d a t = canon_rmap (open_rr a d) t

let canon_close_region d a t = canon_rmap (close_rr a d) t

let rec canon_kinst (ks: list kind) (t: typ)
  : Lemma (ensures canon (kinst_ty ks t) == ckinst ks (canon t)) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp a b -> canon_kinst ks a; canon_kinst ks b
  | TForall _ a -> canon_kinst ks a
  | TConstr cn a -> canon_kinst_constr ks cn; canon_kinst ks a
  | TRowExt en r ->
    canon_kinst_ent ks en;
    canon_kinst ks r;
    ckinst_op_view ks (canon r);
    ckinst_op_view ks (canon t);
    row_canonical_ckinst ks (canon t);
    ext_case (ckinst_ent ks) (ckinst_vf ks) (canon_ent en) (canon r) (ckinst ks (canon r))
      (ckinst ks (canon t))
  | TRowUnion a b ->
    canon_kinst ks a;
    canon_kinst ks b;
    ckinst_op_view ks (canon a);
    ckinst_op_view ks (canon b);
    ckinst_op_view ks (canon t);
    row_canonical_ckinst ks (canon t);
    union_case (ckinst_ent ks) (ckinst_vf ks) (canon a) (canon b) (ckinst ks (canon a))
      (ckinst ks (canon b)) (ckinst ks (canon t))

and canon_kinst_ent (ks: list kind) (en: entry)
  : Lemma (ensures canon_ent (kinst_ent ks en) == ckinst_ent ks (canon_ent en)) (decreases en) =
  match en with
  | EntTy _ t -> canon_kinst ks t
  | EntEff _ _ ts -> canon_kinst_tys ks ts
  | EntRegion _ -> ()

and canon_kinst_constr (ks: list kind) (cn: constr)
  : Lemma (ensures canon_constr (kinst_constr ks cn) == ckinst_constr ks (canon_constr cn))
          (decreases cn) =
  match cn with
  | CLacks _ t -> canon_kinst ks t
  | CDisj a b -> canon_kinst ks a; canon_kinst ks b

and canon_kinst_tys (ks: list kind) (ts: list typ)
  : Lemma (ensures canon_tys (kinst_tys ks ts) == ckinst_list ks (canon_tys ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> canon_kinst ks t; canon_kinst_tys ks ts

(* `canon ∘ σ`, named so that both sides of a corollary use one term. *)
let canon_tsub (sigma: tsub) (i: nat) : ctyp = canon (sigma i)

let ty_eq_ren xi t t' = canon_ren xi t; canon_ren xi t'

let ty_eq_sub sigma t t' =
  canon_sub sigma (canon_tsub sigma) t;
  canon_sub sigma (canon_tsub sigma) t'

let ty_eq_sub_pointwise sigma sigma' t =
  canon_sub sigma (canon_tsub sigma) t;
  canon_sub sigma' (canon_tsub sigma) t

let ty_eq_sub_cong sigma sigma' t t' =
  canon_sub sigma (canon_tsub sigma) t;
  canon_sub sigma' (canon_tsub sigma) t'

let constr_eq_ren xi c c' = canon_ren_constr xi c; canon_ren_constr xi c'

let constr_eq_sub_cong sigma sigma' c c' =
  canon_sub_constr sigma (canon_tsub sigma) c;
  canon_sub_constr sigma' (canon_tsub sigma) c'

let ty_eq_rmap f t t' = canon_rmap f t; canon_rmap f t'

let constr_eq_rmap f c c' = canon_rmap_constr f c; canon_rmap_constr f c'

let ty_eq_kinst ks t t' = canon_kinst ks t; canon_kinst ks t'

let constr_eq_kinst ks c c' = canon_kinst_constr ks c; canon_kinst_constr ks c'

let ty_eq_open_region d a t t' = ty_eq_rmap (open_rr a d) t t'

let ty_eq_close_region d a t t' = ty_eq_rmap (close_rr a d) t t'

let rec clc_ents_mem (n: nat) (e: centry) (es: list centry)
  : Lemma (requires L.mem e es /\ clc_ents_at n es) (ensures clc_ent_at n e) (decreases es) =
  match es with
  | e' :: tl -> if e = e' then () else clc_ents_mem n e tl

let rec clc_ents_incl (n: nat) (es es': list centry)
  : Lemma (requires incl es es' /\ clc_ents_at n es') (ensures clc_ents_at n es) (decreases es) =
  match es with
  | [] -> ()
  | e :: tl -> clc_ents_mem n e es'; clc_ents_incl n tl es'

let rec clc_list_mem (n: nat) (c: ctyp) (cs: list ctyp)
  : Lemma (requires L.mem c cs /\ clc_list_at n cs) (ensures clc_at n c) (decreases cs) =
  match cs with
  | c' :: tl -> if c = c' then () else clc_list_mem n c tl

let rec clc_list_incl (n: nat) (cs cs': list ctyp)
  : Lemma (requires incl cs cs' /\ clc_list_at n cs') (ensures clc_list_at n cs) (decreases cs) =
  match cs with
  | [] -> ()
  | c :: tl -> clc_list_mem n c cs'; clc_list_incl n tl cs'

let rec clc_ents_append (n: nat) (es es': list centry)
  : Lemma (clc_ents_at n (L.append es es') == (clc_ents_at n es && clc_ents_at n es'))
          (decreases es) =
  match es with
  | [] -> ()
  | _ :: tl -> clc_ents_append n tl es'

let rec clc_list_append (n: nat) (cs cs': list ctyp)
  : Lemma (clc_list_at n (L.append cs cs') == (clc_list_at n cs && clc_list_at n cs'))
          (decreases cs) =
  match cs with
  | [] -> ()
  | _ :: tl -> clc_list_append n tl cs'

let clc_view (n: nat) (c: ctyp)
  : Lemma (clc_at n c == (clc_ents_at n (row_entries c) && clc_list_at n (row_tails c))) = ()

let clc_nrow (n: nat) (es: list centry) (ts: list ctyp)
  : Lemma (clc_at n (nrow es ts) == (clc_ents_at n es && clc_list_at n ts)) =
  clc_view n (nrow es ts);
  view_nrow es ts;
  let es' = norm ord_centry es in
  let ts' = norm ord_ctyp ts in
  FStar.Classical.move_requires (clc_ents_incl n es) es';
  FStar.Classical.move_requires (clc_ents_incl n es') es;
  FStar.Classical.move_requires (clc_list_incl n ts) ts';
  FStar.Classical.move_requires (clc_list_incl n ts') ts

let rec lc_canon (n: nat) (t: typ)
  : Lemma (ensures clc_at n (canon t) == lc_ty_at n t) (decreases t) =
  match t with
  | TVar _ | TCon _ _ | TRowEmpty -> ()
  | TApp a b -> lc_canon n a; lc_canon n b
  | TForall _ a -> lc_canon n a
  | TConstr cn a -> lc_canon_constr n cn; lc_canon n a
  | TRowExt en r ->
    lc_canon_ent n en;
    lc_canon n r;
    let v = view_row (canon r) in
    clc_view n (canon r);
    clc_nrow n (canon_ent en :: fst v) (snd v)
  | TRowUnion a b ->
    lc_canon n a;
    lc_canon n b;
    let v1 = view_row (canon a) in
    let v2 = view_row (canon b) in
    clc_view n (canon a);
    clc_view n (canon b);
    clc_nrow n (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2));
    clc_ents_append n (fst v1) (fst v2);
    clc_list_append n (snd v1) (snd v2)

and lc_canon_ent (n: nat) (en: entry)
  : Lemma (ensures clc_ent_at n (canon_ent en) == lc_ent_at n en) (decreases en) =
  match en with
  | EntTy _ t -> lc_canon n t
  | EntEff _ _ ts -> lc_canon_tys n ts
  | EntRegion _ -> ()

and lc_canon_constr (n: nat) (cn: constr)
  : Lemma (ensures clc_constr_at n (canon_constr cn) == lc_constr_at n cn) (decreases cn) =
  match cn with
  | CLacks _ t -> lc_canon n t
  | CDisj a b -> lc_canon n a; lc_canon n b

and lc_canon_tys (n: nat) (ts: list typ)
  : Lemma (ensures clc_list_at n (canon_tys ts) == lc_tys_at n ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts -> lc_canon n t; lc_canon_tys n ts

let ty_eq_lc n t t' = lc_canon n t; lc_canon n t'
