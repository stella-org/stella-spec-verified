(* Proof structure.

   Every lemma is by induction on the row, following `check`: an extension
   and a union are unfolded by `check_ext` and `check_union`, and a type
   that is not a row former has no canonical entries (`view_nonrow`).

   Sharpness reads the sharpness premises through the known-key facts of
   `Stella.Core.Entail.Split`, which need consistency. Kinding of
   `row_drop` and its Lacks constraint use only the sub-row facts there,
   which hold in every context. *)
module Stella.Core.Kinding.Sharp
open Stella.Core.Syntax
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Rows.Split
open Stella.Core.Entail
open Stella.Core.Entail.Split
open Stella.Core.Sig
open Stella.Core.Context
open Stella.Core.Kinding
open Stella.Core.Kinding.Facts
module L = FStar.List.Tot

let key_known (r: typ) (x: centry)
  : Lemma (requires L.mem x (row_entries (canon r))) (ensures L.mem (fst x) (known_keys r)) =
  match x with
  | (k, _) -> mem_ckeys k (canon r)

(* Sharpness. *)

let sharp_ext (sg: sig) (g: ctx) (en: entry) (r0: typ) (e: elt_kind) (e1 e2: centry)
  : Lemma (requires check sg g (TRowExt en r0) (KRow e) /\ not (inconsistent (hyps g)) /\
                    L.mem e1 (row_entries (canon (TRowExt en r0))) /\
                    L.mem e2 (row_entries (canon (TRowExt en r0))) /\ fst e1 == fst e2 /\
                    ~(L.mem e1 (row_entries (canon r0)) /\ L.mem e2 (row_entries (canon r0))))
          (ensures snd e1 == snd e2) =
  check_ext sg g en r0 e;
  entails_lacks_known (hyps g) (ent_key en) r0;
  canon_ent_key en;
  mem_entries_ext en r0 e1;
  mem_entries_ext en r0 e2;
  if e1 = canon_ent en then (if e2 = canon_ent en then () else key_known r0 e2)
  else key_known r0 e1

let sharp_union (sg: sig) (g: ctx) (a b: typ) (e: elt_kind) (e1 e2: centry)
  : Lemma (requires check sg g (TRowUnion a b) (KRow e) /\ not (inconsistent (hyps g)) /\
                    L.mem e1 (row_entries (canon a)) /\ L.mem e2 (row_entries (canon b)) /\
                    fst e1 == fst e2)
          (ensures False) =
  check_union sg g a b e;
  key_known a e1;
  key_known b e2;
  entails_disj_known (hyps g) a b (fst e1)

let rec check_sharp_go (sg: sig) (g: ctx) (r: typ) (e: elt_kind) (e1 e2: centry)
  : Lemma (requires check sg g r (KRow e) /\ not (inconsistent (hyps g)) /\
                    L.mem e1 (row_entries (canon r)) /\ L.mem e2 (row_entries (canon r)) /\
                    fst e1 == fst e2)
          (ensures snd e1 == snd e2) (decreases r) =
  match r with
  | TRowEmpty -> ()
  | TRowExt en r0 ->
    check_ext sg g en r0 e;
    if L.mem e1 (row_entries (canon r0)) && L.mem e2 (row_entries (canon r0))
    then check_sharp_go sg g r0 e e1 e2
    else sharp_ext sg g en r0 e e1 e2
  | TRowUnion a b ->
    check_union sg g a b e;
    mem_entries_union a b e1;
    mem_entries_union a b e2;
    let ea = row_entries (canon a) in
    let eb = row_entries (canon b) in
    if L.mem e1 ea && L.mem e2 ea then check_sharp_go sg g a e e1 e2
    else if L.mem e1 eb && L.mem e2 eb then check_sharp_go sg g b e e1 e2
    else if L.mem e1 ea then sharp_union sg g a b e e1 e2
    else sharp_union sg g a b e e2 e1
  | _ -> view_nonrow r

let check_sharp sg g r e =
  introduce forall (e1 e2: centry).
    L.mem e1 (row_entries (canon r)) /\ L.mem e2 (row_entries (canon r)) /\ fst e1 == fst e2 ==>
    snd e1 == snd e2
  with introduce _ ==> _
  with check_sharp_go sg g r e e1 e2

let ex_falso_unsharp sg g k t t' =
  let r1 = TRowExt (EntTy k t') TRowEmpty in
  mem_entries_ext (EntTy k t) r1 (k, PTy (canon t));
  mem_entries_ext (EntTy k t) r1 (k, PTy (canon t'));
  mem_entries_ext (EntTy k t') TRowEmpty (k, PTy (canon t'));
  check_ext_ty sg g k t r1;
  check_ext_ty sg g k t' TRowEmpty

(* Dropping a key from a kinded row. *)

let rec check_row_drop_go (sg: sig) (g: ctx) (k: key) (r: typ) (e: elt_kind)
  : Lemma (requires check sg g r (KRow e)) (ensures check sg g (row_drop k r) (KRow e))
          (decreases r) =
  match r with
  | TRowExt en r0 ->
    check_ext sg g en r0 e;
    check_row_drop_go sg g k r0 e;
    if ent_key en = k then ()
    else begin
      sub_row_drop k r0;
      entails_lacks_sub (hyps g) (ent_key en) r0 (row_drop k r0);
      check_ext sg g en (row_drop k r0) e
    end
  | TRowUnion a b ->
    check_union sg g a b e;
    check_row_drop_go sg g k a e;
    check_row_drop_go sg g k b e;
    sub_row_drop k a;
    sub_row_drop k b;
    entails_disj_sub (hyps g) a b (row_drop k a) (row_drop k b);
    check_union sg g (row_drop k a) (row_drop k b) e
  | _ -> ()

let check_row_drop sg g k r e = check_row_drop_go sg g k r e

(* `k ∉ row_drop k b`, for a side `b` of a union whose other side `a`
   knows `k`. *)
let drop_lacks_other (h: list constr) (k: key) (a b: typ)
  : Lemma (requires entails h (CDisj a b) /\ L.mem k (known_keys a))
          (ensures entails h (CLacks k (row_drop k b))) =
  entails_disj_lacks h a b k;
  sub_row_drop k b;
  entails_lacks_sub h k b (row_drop k b)

let rec check_drop_lacks_go (sg: sig) (g: ctx) (k: key) (r: typ) (e: elt_kind)
  : Lemma (requires check sg g r (KRow e) /\ L.mem k (known_keys r))
          (ensures entails (hyps g) (CLacks k (row_drop k r))) (decreases r) =
  let h = hyps g in
  match r with
  | TRowExt en r0 ->
    check_ext sg g en r0 e;
    mem_known_keys_ext k en r0;
    if ent_key en = k then begin
      sub_row_drop k r0;
      entails_lacks_sub h k r0 (row_drop k r0)
    end else begin
      check_drop_lacks_go sg g k r0 e;
      entails_lacks_ext h k en (row_drop k r0)
    end
  | TRowUnion a b ->
    check_union sg g a b e;
    mem_known_keys_union k a b;
    let ka = L.mem k (known_keys a) in
    let kb = L.mem k (known_keys b) in
    (if ka then check_drop_lacks_go sg g k a e
     else begin
       entails_disj_lacks_r h a b k;
       sub_row_drop k a;
       entails_lacks_sub h k a (row_drop k a)
     end);
    (if kb then check_drop_lacks_go sg g k b e else drop_lacks_other h k a b);
    entails_lacks_union h k (row_drop k a) (row_drop k b)
  | TRowEmpty -> ()
  | _ -> view_nonrow r

let check_drop_lacks sg g k r e = check_drop_lacks_go sg g k r e

(* Splitting a kinded row at a key. *)

let check_split sg g en r e =
  check_sharp sg g r e;
  canon_ent_key en;
  let k = ent_key en in
  let ce = canon_ent en in
  introduce forall (p: cpayload). L.mem (k, p) (row_entries (canon r)) ==> p == snd ce
  with introduce _ ==> _
  with assert (fst (k, p) == fst ce);
  split_at en r;
  check_row_drop sg g k r e;
  key_known r ce;
  check_drop_lacks sg g k r e

let check_split_eff sg g k q ts r =
  eff_entry_key r k q (canon_tys ts);
  check_split sg g (EntEff (eff_label k) q ts) r EEffect

let check_split_ty sg g k t r = check_split sg g (EntTy k t) r EType
