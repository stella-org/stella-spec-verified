(**
 * Facts about canonical forms and type equality (design §2, §2.1).
 *
 *   - Row views: `view_row` inverts `mkrow`; a `row_canonical` form is
 *     determined by the members of its entry and tail lists.
 *   - `ty_eq` is an equivalence; row union is idempotent, commutative and
 *     associative with unit `()`; row extension is union with a one-entry
 *     row.
 *   - Inversion: type formers that are not rows are compared component by
 *     component.
 *   - `knownKeys` of an extension and of a union.
 *   - Commutation: `canon` commutes with renaming, substitution, maps
 *     over region references (covering region open and close) and kind
 *     instantiation. Hence `ty_eq` is preserved by every renaming, every
 *     substitution, every region map and every kind instantiation, with no
 *     kinding hypothesis.
 *   - Local closure: `canon` preserves and reflects `lc_ty_at`.
 *)
module Stella.Core.Rows.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Region
open Stella.Core.OrdSet
open Stella.Core.Rows
module L = FStar.List.Tot

(** * Row views *)

val view_mkrow (es: list centry) (ts: list ctyp) : Lemma (view_row (mkrow es ts) == (es, ts))

val view_nrow (es: list centry) (ts: list ctyp)
  : Lemma (view_row (nrow es ts) == (norm ord_centry es, norm ord_ctyp ts))

(** `nrow` depends only on the members of its arguments. *)
val nrow_ext (es es': list centry) (ts ts': list ctyp)
  : Lemma (requires seteq es es' /\ seteq ts ts') (ensures nrow es ts == nrow es' ts')

val row_canonical_nrow (es: list centry) (ts: list ctyp) : Lemma (row_canonical (nrow es ts))

val row_canonical_nonrow (c: ctyp) : Lemma (requires not (CRow? c)) (ensures row_canonical c)

val row_canonical_sorted (c: ctyp)
  : Lemma (requires row_canonical c)
          (ensures sorted ord_centry (row_entries c) /\ sorted ord_ctyp (row_tails c))

(** Row-canonical forms whose views have the same members are equal. *)
val row_canonical_ext (c1 c2: ctyp)
  : Lemma (requires row_canonical c1 /\ row_canonical c2 /\
                    seteq (row_entries c1) (row_entries c2) /\
                    seteq (row_tails c1) (row_tails c2))
          (ensures c1 == c2)

(** * Operations on canonical forms read as rows

    Each operation's view of a row has the members of `rop` applied to the
    row's view: its entries are the images of the entries together with the
    entries of the images of the tails, and its tails are the tails of the
    images of the tails. *)

val cren_view (xi: ren) (c: ctyp)
  : Lemma (let v = rop (cren_ent xi) (cren_vf xi) (view_row c) in
           seteq (row_entries (cren xi c)) (fst v) /\ seteq (row_tails (cren xi c)) (snd v))

val row_canonical_cren (xi: ren) (c: ctyp) : Lemma (row_canonical (cren xi c))

val csub_view (s: csubst) (c: ctyp)
  : Lemma (let v = rop (csub_ent s) (csub_vf s) (view_row c) in
           seteq (row_entries (csub s c)) (fst v) /\ seteq (row_tails (csub s c)) (snd v))

val row_canonical_csub (s: csubst) (c: ctyp)
  : Lemma (requires forall (i: nat). row_canonical (s i)) (ensures row_canonical (csub s c))

val cmap_view (f: region_ref -> region_ref) (c: ctyp)
  : Lemma (let v = rop (cmap_ent f) (cmap_vf f) (view_row c) in
           seteq (row_entries (cmap f c)) (fst v) /\ seteq (row_tails (cmap f c)) (snd v))

val row_canonical_cmap (f: region_ref -> region_ref) (c: ctyp) : Lemma (row_canonical (cmap f c))

val ckinst_view (ks: list kind) (c: ctyp)
  : Lemma (let v = rop (ckinst_ent ks) (ckinst_vf ks) (view_row c) in
           seteq (row_entries (ckinst ks c)) (fst v) /\ seteq (row_tails (ckinst ks c)) (snd v))

val row_canonical_ckinst (ks: list kind) (c: ctyp) : Lemma (row_canonical (ckinst ks c))

(** * Shape of canonical forms *)

val canon_row_canonical (t: typ) : Lemma (row_canonical (canon t))

val canon_sorted (t: typ)
  : Lemma (sorted ord_centry (row_entries (canon t)) /\ sorted ord_ctyp (row_tails (canon t)))

(** No tail of a canonical form is a row. *)
val canon_tails_nonrow (t: typ) (c: ctyp)
  : Lemma (requires L.mem c (row_tails (canon t))) (ensures not (CRow? c))

(** No canonical form is a `CRow` with no entries and a single tail. *)
val canon_not_single_tail (t: typ)
  : Lemma (not (CRow? (canon t) && Nil? (row_entries (canon t)) &&
                L.length (row_tails (canon t)) = 1))

(** The key of a canonical entry is `key(ent)`. *)
val canon_ent_key (en: entry) : Lemma (fst (canon_ent en) == ent_key en)

(** * Type equality is an equivalence *)

val ty_eq_refl (t: typ) : Lemma (ty_eq t t)

val ty_eq_sym (t1 t2: typ) : Lemma (requires ty_eq t1 t2) (ensures ty_eq t2 t1)

val ty_eq_trans (t1 t2 t3: typ)
  : Lemma (requires ty_eq t1 t2 /\ ty_eq t2 t3) (ensures ty_eq t1 t3)

(** * Union and extension *)

val union_idem (r: typ) : Lemma (ty_eq (TRowUnion r r) r)

val union_empty_r (r: typ) : Lemma (ty_eq (TRowUnion r TRowEmpty) r)

val union_empty_l (r: typ) : Lemma (ty_eq (TRowUnion TRowEmpty r) r)

val union_comm (a b: typ) : Lemma (ty_eq (TRowUnion a b) (TRowUnion b a))

val union_assoc (a b c: typ)
  : Lemma (ty_eq (TRowUnion (TRowUnion a b) c) (TRowUnion a (TRowUnion b c)))

(** `( ent | ρ ) ≡ ( ent | () ) ⊎ ρ` *)
val ext_as_union (en: entry) (r: typ)
  : Lemma (ty_eq (TRowExt en r) (TRowUnion (TRowExt en TRowEmpty) r))

val ext_comm (e1 e2: entry) (r: typ)
  : Lemma (ty_eq (TRowExt e1 (TRowExt e2 r)) (TRowExt e2 (TRowExt e1 r)))

val ext_idem (en: entry) (r: typ) : Lemma (ty_eq (TRowExt en (TRowExt en r)) (TRowExt en r))

val ty_eq_union_cong (a a' b b': typ)
  : Lemma (requires ty_eq a a' /\ ty_eq b b') (ensures ty_eq (TRowUnion a b) (TRowUnion a' b'))

val ty_eq_ext_cong (e e': entry) (r r': typ)
  : Lemma (requires ent_eq e e' /\ ty_eq r r') (ensures ty_eq (TRowExt e r) (TRowExt e' r'))

(** * Inversion *)

(** The row formers. Every other former canonicalizes to the corresponding
    non-row constructor of `ctyp`. A row former canonicalizes to a `CRow`,
    except a union, which collapses to its single tail when it has no
    entries and one tail. *)
let is_row_former (t: typ) : bool = TRowEmpty? t || TRowExt? t || TRowUnion? t

let head_index (t: typ) : nat =
  match t with
  | TVar _ -> 0
  | TCon _ _ -> 1
  | TApp _ _ -> 2
  | TForall _ _ -> 3
  | TConstr _ _ -> 4
  | _ -> 5

val canon_nonrow (t: typ) : Lemma (requires not (is_row_former t)) (ensures not (CRow? (canon t)))

val canon_ext_row (en: entry) (r: typ)
  : Lemma (CRow? (canon (TRowExt en r)) /\ Cons? (row_entries (canon (TRowExt en r))))

(** Equal non-row formers have the same head. *)
val ty_eq_head (t1 t2: typ)
  : Lemma (requires ty_eq t1 t2 /\ not (is_row_former t1) /\ not (is_row_former t2))
          (ensures head_index t1 == head_index t2)

(** `()` and an extension are never equal to a non-row former. *)
val ty_eq_row_nonrow (t1 t2: typ)
  : Lemma (requires (TRowEmpty? t1 || TRowExt? t1) /\ not (is_row_former t2))
          (ensures not (ty_eq t1 t2))

val ty_eq_var_inv (i j: nat) : Lemma (requires ty_eq (TVar i) (TVar j)) (ensures i == j)

val ty_eq_con_inv (q q': qname) (ks ks': list kind)
  : Lemma (requires ty_eq (TCon q ks) (TCon q' ks')) (ensures q == q' /\ ks == ks')

val ty_eq_app_inv (a b c d: typ)
  : Lemma (requires ty_eq (TApp a b) (TApp c d)) (ensures ty_eq a c /\ ty_eq b d)

val ty_eq_forall_inv (k k': kind) (a b: typ)
  : Lemma (requires ty_eq (TForall k a) (TForall k' b)) (ensures k == k' /\ ty_eq a b)

val ty_eq_constr_inv (c c': constr) (a b: typ)
  : Lemma (requires ty_eq (TConstr c a) (TConstr c' b)) (ensures constr_eq c c' /\ ty_eq a b)

val constr_eq_lacks_inv (k k': key) (r r': typ)
  : Lemma (requires constr_eq (CLacks k r) (CLacks k' r')) (ensures k == k' /\ ty_eq r r')

val constr_eq_disj_inv (a b a' b': typ)
  : Lemma (requires constr_eq (CDisj a b) (CDisj a' b')) (ensures ty_eq a a' /\ ty_eq b b')

val constr_eq_lacks_disj (k: key) (r a b: typ) : Lemma (not (constr_eq (CLacks k r) (CDisj a b)))

(** * Known keys *)

val mem_ckeys (k: key) (c: ctyp)
  : Lemma (L.mem k (ckeys c) <==> (exists (p: cpayload). L.mem (k, p) (row_entries c)))

val known_keys_empty (_: unit) : Lemma (known_keys TRowEmpty == [])

val mem_known_keys_ext (k: key) (en: entry) (r: typ)
  : Lemma (L.mem k (known_keys (TRowExt en r)) = (k = ent_key en || L.mem k (known_keys r)))

val mem_known_keys_union (k: key) (a b: typ)
  : Lemma (L.mem k (known_keys (TRowUnion a b)) = (L.mem k (known_keys a) || L.mem k (known_keys b)))

(** * Canonicalization commutes with renaming *)

val canon_ren (xi: ren) (t: typ) : Lemma (canon (ren_ty xi t) == cren xi (canon t))

val canon_ren_ent (xi: ren) (en: entry)
  : Lemma (canon_ent (ren_ent xi en) == cren_ent xi (canon_ent en))

val canon_ren_constr (xi: ren) (cn: constr)
  : Lemma (canon_constr (ren_constr xi cn) == cren_constr xi (canon_constr cn))

val canon_ren_tys (xi: ren) (ts: list typ)
  : Lemma (canon_tys (ren_tys xi ts) == cren_list xi (canon_tys ts))

(** * Canonicalization commutes with substitution

    `s` is any substitution agreeing pointwise with `canon ∘ σ`. *)

val canon_sub (sigma: tsub) (s: csubst) (t: typ)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures canon (sub_ty sigma t) == csub s (canon t))

val canon_sub_ent (sigma: tsub) (s: csubst) (en: entry)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures canon_ent (sub_ent sigma en) == csub_ent s (canon_ent en))

val canon_sub_constr (sigma: tsub) (s: csubst) (cn: constr)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures canon_constr (sub_constr sigma cn) == csub_constr s (canon_constr cn))

val canon_sub_tys (sigma: tsub) (s: csubst) (ts: list typ)
  : Lemma (requires forall (i: nat). s i == canon (sigma i))
          (ensures canon_tys (sub_tys sigma ts) == csub_list s (canon_tys ts))

(** * Canonicalization commutes with region maps *)

val canon_rmap (f: region_ref -> region_ref) (t: typ)
  : Lemma (canon (rmap_ty f t) == cmap f (canon t))

val canon_rmap_ent (f: region_ref -> region_ref) (en: entry)
  : Lemma (canon_ent (rmap_ent f en) == cmap_ent f (canon_ent en))

val canon_rmap_constr (f: region_ref -> region_ref) (cn: constr)
  : Lemma (canon_constr (rmap_constr f cn) == cmap_constr f (canon_constr cn))

val canon_rmap_tys (f: region_ref -> region_ref) (ts: list typ)
  : Lemma (canon_tys (rmap_tys f ts) == cmap_list f (canon_tys ts))

val canon_open_region (d: nat) (a: atom) (t: typ)
  : Lemma (canon (open_region_ty d a t) == cmap (open_rr a d) (canon t))

val canon_close_region (d: nat) (a: atom) (t: typ)
  : Lemma (canon (close_region_ty d a t) == cmap (close_rr a d) (canon t))

(** * Canonicalization commutes with kind instantiation *)

val canon_kinst (ks: list kind) (t: typ) : Lemma (canon (kinst_ty ks t) == ckinst ks (canon t))

val canon_kinst_ent (ks: list kind) (en: entry)
  : Lemma (canon_ent (kinst_ent ks en) == ckinst_ent ks (canon_ent en))

val canon_kinst_constr (ks: list kind) (cn: constr)
  : Lemma (canon_constr (kinst_constr ks cn) == ckinst_constr ks (canon_constr cn))

val canon_kinst_tys (ks: list kind) (ts: list typ)
  : Lemma (canon_tys (kinst_tys ks ts) == ckinst_list ks (canon_tys ts))

(** * Type equality is preserved by renaming, substitution, region maps and
      kind instantiation *)

val ty_eq_ren (xi: ren) (t t': typ)
  : Lemma (requires ty_eq t t') (ensures ty_eq (ren_ty xi t) (ren_ty xi t'))

val ty_eq_sub (sigma: tsub) (t t': typ)
  : Lemma (requires ty_eq t t') (ensures ty_eq (sub_ty sigma t) (sub_ty sigma t'))

(** Substitutions that agree up to `ty_eq` give equal results. *)
val ty_eq_sub_pointwise (sigma sigma': tsub) (t: typ)
  : Lemma (requires forall (i: nat). ty_eq (sigma i) (sigma' i))
          (ensures ty_eq (sub_ty sigma t) (sub_ty sigma' t))

val ty_eq_sub_cong (sigma sigma': tsub) (t t': typ)
  : Lemma (requires ty_eq t t' /\ (forall (i: nat). ty_eq (sigma i) (sigma' i)))
          (ensures ty_eq (sub_ty sigma t) (sub_ty sigma' t'))

val constr_eq_ren (xi: ren) (c c': constr)
  : Lemma (requires constr_eq c c') (ensures constr_eq (ren_constr xi c) (ren_constr xi c'))

val constr_eq_sub_cong (sigma sigma': tsub) (c c': constr)
  : Lemma (requires constr_eq c c' /\ (forall (i: nat). ty_eq (sigma i) (sigma' i)))
          (ensures constr_eq (sub_constr sigma c) (sub_constr sigma' c'))

val ty_eq_rmap (f: region_ref -> region_ref) (t t': typ)
  : Lemma (requires ty_eq t t') (ensures ty_eq (rmap_ty f t) (rmap_ty f t'))

val constr_eq_rmap (f: region_ref -> region_ref) (c c': constr)
  : Lemma (requires constr_eq c c') (ensures constr_eq (rmap_constr f c) (rmap_constr f c'))

val ty_eq_kinst (ks: list kind) (t t': typ)
  : Lemma (requires ty_eq t t') (ensures ty_eq (kinst_ty ks t) (kinst_ty ks t'))

val constr_eq_kinst (ks: list kind) (c c': constr)
  : Lemma (requires constr_eq c c') (ensures constr_eq (kinst_constr ks c) (kinst_constr ks c'))

val ty_eq_open_region (d: nat) (a: atom) (t t': typ)
  : Lemma (requires ty_eq t t') (ensures ty_eq (open_region_ty d a t) (open_region_ty d a t'))

val ty_eq_close_region (d: nat) (a: atom) (t t': typ)
  : Lemma (requires ty_eq t t') (ensures ty_eq (close_region_ty d a t) (close_region_ty d a t'))

(** * Local closure *)

val lc_canon (n: nat) (t: typ) : Lemma (clc_at n (canon t) == lc_ty_at n t)

val lc_canon_ent (n: nat) (en: entry) : Lemma (clc_ent_at n (canon_ent en) == lc_ent_at n en)

val lc_canon_constr (n: nat) (cn: constr)
  : Lemma (clc_constr_at n (canon_constr cn) == lc_constr_at n cn)

val lc_canon_tys (n: nat) (ts: list typ) : Lemma (clc_list_at n (canon_tys ts) == lc_tys_at n ts)

(** Type equality preserves local closure. *)
val ty_eq_lc (n: nat) (t t': typ)
  : Lemma (requires ty_eq t t') (ensures lc_ty_at n t == lc_ty_at n t')
