(* Proof structure.

   Every fact reduces to membership in the views of canonical forms.
   `view_nrow` and `mem_norm` give the members of the view of an extension
   and of a union; `row_drop_view` gives those of `row_drop k t` by
   induction on `t`. List equalities follow from membership through
   `sorted_ext`, the canonical lists being sorted (`canon_sorted`) and
   `ents_drop` keeping a list sorted. Equalities of canonical forms follow
   through `nrow_ext` and `row_canonical_ext`. *)
module Stella.Core.Rows.Split
open Stella.Core.Syntax
open Stella.Core.OrdSet
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
module L = FStar.List.Tot

let mem_app (#a: eqtype) (z: a) (l1 l2: list a)
  : Lemma (L.mem z (L.append l1 l2) = (L.mem z l1 || L.mem z l2))
          [SMTPat (L.mem z (L.append l1 l2))] =
  FStar.List.Tot.Properties.append_mem l1 l2 z

(* Entries and tails of extensions and unions. *)

let mem_entries_ext en r e =
  let v = view_row (canon r) in
  view_nrow (canon_ent en :: fst v) (snd v);
  mem_norm ord_centry (canon_ent en :: fst v) e

let tails_ext en r =
  let v = view_row (canon r) in
  view_nrow (canon_ent en :: fst v) (snd v);
  canon_sorted r;
  norm_sorted ord_ctyp (snd v)

let mem_entries_union a b e =
  let v1 = view_row (canon a) in
  let v2 = view_row (canon b) in
  view_nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2));
  mem_norm ord_centry (L.append (fst v1) (fst v2)) e

let mem_tails_union a b c =
  let v1 = view_row (canon a) in
  let v2 = view_row (canon b) in
  view_nrow (L.append (fst v1) (fst v2)) (L.append (snd v1) (snd v2));
  mem_norm ord_ctyp (L.append (snd v1) (snd v2)) c

let view_nonrow t = canon_nonrow t

(* Sub-rows. *)

let sub_row_refl r = ()

let sub_row_trans r1 r2 r3 = ()

let sub_row_ext en r =
  introduce forall (k: key). L.mem k (known_keys r) ==> L.mem k (known_keys (TRowExt en r))
  with mem_known_keys_ext k en r;
  tails_ext en r

let sub_row_union_l a b =
  introduce forall (k: key). L.mem k (known_keys a) ==> L.mem k (known_keys (TRowUnion a b))
  with mem_known_keys_union k a b;
  introduce forall (c: ctyp). L.mem c (row_tails (canon a)) ==> L.mem c (row_tails (canon (TRowUnion a b)))
  with mem_tails_union a b c

let sub_row_union_r a b =
  introduce forall (k: key). L.mem k (known_keys b) ==> L.mem k (known_keys (TRowUnion a b))
  with mem_known_keys_union k a b;
  introduce forall (c: ctyp). L.mem c (row_tails (canon b)) ==> L.mem c (row_tails (canon (TRowUnion a b)))
  with mem_tails_union a b c

(* Dropping a key. *)

let rec mem_ents_drop k es e =
  match es with
  | [] -> ()
  | _ :: tl -> mem_ents_drop k tl e

let rec sorted_lt_mem (#a: eqtype) (o: ord a) (x: a) (l: list a) (y: a)
  : Lemma (requires sorted o (x :: l) /\ L.mem y l) (ensures lt o x y) (decreases l) =
  match l with
  | z :: tl -> if y = z then () else (sorted_lt_mem o z tl y; lt_trans o x z y)

let sorted_cons_intro (#a: eqtype) (o: ord a) (x: a) (l: list a)
  : Lemma (requires sorted o l /\ (forall (y: a). L.mem y l ==> lt o x y))
          (ensures sorted o (x :: l)) =
  match l with
  | [] -> ()
  | _ :: _ -> ()

let sorted_tail (#a: eqtype) (o: ord a) (x: a) (l: list a)
  : Lemma (requires sorted o (x :: l)) (ensures sorted o l) =
  match l with
  | [] -> ()
  | _ :: _ -> ()

let rec sorted_ents_drop (k: key) (es: list centry)
  : Lemma (requires sorted ord_centry es) (ensures sorted ord_centry (ents_drop k es))
          (decreases es) =
  match es with
  | [] -> ()
  | e :: tl ->
    sorted_tail ord_centry e tl;
    sorted_ents_drop k tl;
    if fst e = k then ()
    else begin
      introduce forall (y: centry). L.mem y (ents_drop k tl) ==> lt ord_centry e y
      with introduce _ ==> _
      with (mem_ents_drop k tl y; sorted_lt_mem ord_centry e tl y);
      sorted_cons_intro ord_centry e (ents_drop k tl)
    end

let rec row_drop_view (k: key) (t: typ) (e: centry) (c: ctyp)
  : Lemma (ensures
            (L.mem e (row_entries (canon (row_drop k t))) =
             (fst e <> k && L.mem e (row_entries (canon t)))) /\
            (L.mem c (row_tails (canon (row_drop k t))) = L.mem c (row_tails (canon t))))
          (decreases t) =
  match t with
  | TRowEmpty -> ()
  | TRowExt en r ->
    mem_entries_ext en r e;
    tails_ext en r;
    canon_ent_key en;
    row_drop_view k r e c;
    if ent_key en = k then ()
    else begin
      mem_entries_ext en (row_drop k r) e;
      tails_ext en (row_drop k r)
    end
  | TRowUnion a b ->
    mem_entries_union a b e;
    mem_tails_union a b c;
    mem_entries_union (row_drop k a) (row_drop k b) e;
    mem_tails_union (row_drop k a) (row_drop k b) c;
    row_drop_view k a e c;
    row_drop_view k b e c
  | _ -> view_nonrow t

let row_drop_entries k t =
  let es = row_entries (canon t) in
  let aux (e: centry)
    : Lemma (L.mem e (row_entries (canon (row_drop k t))) = L.mem e (ents_drop k es)) =
    row_drop_view k t e (CRow [] []);
    mem_ents_drop k es e
  in
  FStar.Classical.forall_intro aux;
  canon_sorted (row_drop k t);
  canon_sorted t;
  sorted_ents_drop k es;
  sorted_ext ord_centry (row_entries (canon (row_drop k t))) (ents_drop k es)

let row_drop_tails k t =
  let aux (c: ctyp)
    : Lemma (L.mem c (row_tails (canon (row_drop k t))) = L.mem c (row_tails (canon t))) =
    row_drop_view k t (SymbolKey "", PRegion (RBound 0)) c
  in
  FStar.Classical.forall_intro aux;
  canon_sorted (row_drop k t);
  canon_sorted t;
  sorted_ext ord_ctyp (row_tails (canon (row_drop k t))) (row_tails (canon t))

let mem_known_keys_drop k k' t =
  mem_ckeys k' (canon (row_drop k t));
  mem_ckeys k' (canon t);
  introduce forall (p: cpayload).
    L.mem (k', p) (row_entries (canon (row_drop k t))) =
    (k' <> k && L.mem (k', p) (row_entries (canon t)))
  with row_drop_view k t (k', p) (CRow [] [])

let sub_row_drop k t =
  introduce forall (k': key). L.mem k' (known_keys (row_drop k t)) ==> L.mem k' (known_keys t)
  with mem_known_keys_drop k k' t;
  row_drop_tails k t

(* Splitting a row at a key. *)

let canon_split k p r =
  let es = row_entries (canon r) in
  row_drop_entries k r;
  row_drop_tails k r;
  FStar.Classical.forall_intro (mem_ents_drop k es);
  introduce forall (e: centry). L.mem e es ==> L.mem e ((k, p) :: ents_drop k es)
  with introduce _ ==> _
  with (match e with (k0, p0) -> if k0 = k then assert (L.mem (k, p0) es) else ());
  canon_row_canonical r;
  nrow_ext es ((k, p) :: ents_drop k es) (row_tails (canon r)) (row_tails (canon r))

let split_at en r =
  canon_ent_key en;
  let k = ent_key en in
  let p = snd (canon_ent en) in
  assert (canon_ent en == (k, p));
  canon_split k p r

let split_at_ty k t r = split_at (EntTy k t) r

let rec eff_entry_key_go (r: typ) (k: key) (q: qname) (cs: list ctyp)
  : Lemma (requires L.mem (k, PEff q cs) (row_entries (canon r)))
          (ensures eff_key (eff_label k) q == k) (decreases r) =
  match r with
  | TRowExt en r0 ->
    mem_entries_ext en r0 (k, PEff q cs);
    if (k, PEff q cs) = canon_ent en then () else eff_entry_key_go r0 k q cs
  | TRowUnion a b ->
    mem_entries_union a b (k, PEff q cs);
    if L.mem (k, PEff q cs) (row_entries (canon a)) then eff_entry_key_go a k q cs
    else eff_entry_key_go b k q cs
  | TRowEmpty -> ()
  | _ -> view_nonrow r

let eff_entry_key r k q cs = eff_entry_key_go r k q cs

let split_at_eff k q ts r =
  eff_entry_key r k q (canon_tys ts);
  split_at (EntEff (eff_label k) q ts) r

(* Cancellation. *)

let ext_cancel e e' r0 r1 =
  let k = ent_key e in
  canon_ent_key e;
  canon_ent_key e';
  mem_ckeys k (canon r0);
  mem_ckeys k (canon r1);
  let ce = canon_ent e in
  mem_entries_ext e r0 ce;
  mem_entries_ext e' r1 ce;
  (match ce with (k0, p0) -> assert (not (L.mem (k0, p0) (row_entries (canon r1)))));
  assert (ce == canon_ent e');
  introduce forall (x: centry).
    L.mem x (row_entries (canon r0)) <==> L.mem x (row_entries (canon r1))
  with begin
    mem_entries_ext e r0 x;
    mem_entries_ext e' r1 x;
    match x with
    | (kx, px) -> ()
  end;
  tails_ext e r0;
  tails_ext e' r1;
  canon_row_canonical r0;
  canon_row_canonical r1;
  row_canonical_ext (canon r0) (canon r1)

let ext_ty_cancel k t t' r0 r1 = ext_cancel (EntTy k t) (EntTy k t') r0 r1

let ext_other_entry k k' t0 t1 r0 r1 =
  mem_entries_ext (EntTy k t0) r0 (k, PTy (canon t0));
  mem_entries_ext (EntTy k' t1) r1 (k, PTy (canon t0))

(* Extension under union. *)

let union_ext_l en r r3 =
  let e1 = TRowExt en TRowEmpty in
  ext_as_union en r;
  ty_eq_union_cong (TRowExt en r) (TRowUnion e1 r) r3 r3;
  union_assoc e1 r r3;
  ext_as_union en (TRowUnion r r3)
