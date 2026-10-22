(* Proof structure.

   In consistent hypotheses, `entails hyps c` is consistency of
   `canon_constr c` together with the derivability of each of its atoms
   (`entails_iff`, from `mem_catoms` and `all_derivable_mem`). Each lemma
   with an entailed conclusion is ex falso when the hypotheses are
   inconsistent, and otherwise maps the known keys and the atoms of the
   conclusion into those of a premise (`lacks_mono`, `disj_mono`). *)
module Stella.Core.Entail.Split
open Stella.Core.Syntax
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Rows.Split
open Stella.Core.Entail
open Stella.Core.Entail.Lemmas
module L = FStar.List.Tot

(* Entailment in consistent hypotheses. *)

let atoms_derivable (hyps: list constr) (cc: cconstr) : prop =
  forall (a: afact). in_atoms cc a ==> derivable hyps a

let entails_iff (hyps: list constr) (c: constr)
  : Lemma (requires not (inconsistent hyps))
          (ensures entails hyps c <==>
                   cconsistent (canon_constr c) /\ atoms_derivable hyps (canon_constr c)) =
  let cc = canon_constr c in
  FStar.Classical.forall_intro (mem_catoms cc);
  all_derivable_mem (gamma_star hyps) (catoms cc)

(* `k ∉ r'` from `k ∉ r`, when the known keys and the tails of `r'` are
   among those of `r`. *)
let lacks_mono (hyps: list constr) (k: key) (r r': typ)
  : Lemma (requires entails hyps (CLacks k r) /\ not (L.mem k (known_keys r')) /\
                    (forall (c: ctyp). L.mem c (row_tails (canon r')) ==> L.mem c (row_tails (canon r))))
          (ensures entails hyps (CLacks k r')) =
  if inconsistent hyps then ()
  else begin
    entails_iff hyps (CLacks k r);
    entails_iff hyps (CLacks k r');
    introduce forall (a: afact). in_atoms (CCLacks k (canon r')) a ==> derivable hyps a
    with introduce _ ==> _
    with (match a with
          | ALacks k' t -> assert (in_atoms (CCLacks k (canon r)) (ALacks k' t))
          | _ -> ())
  end

let entails_lacks_known hyps k r = entails_iff hyps (CLacks k r)

let entails_disj_known hyps r1 r2 k =
  entails_iff hyps (CDisj r1 r2);
  disjoint_keys_mem (known_keys r1) (known_keys r2)

let entails_lacks_sub hyps k r r' =
  if inconsistent hyps then () else (entails_iff hyps (CLacks k r); lacks_mono hyps k r r')

let entails_disj_sub hyps r1 r2 r1' r2' =
  if inconsistent hyps then ()
  else begin
    let c1 = canon r1 in
    let c2 = canon r2 in
    let c1' = canon r1' in
    let c2' = canon r2' in
    entails_iff hyps (CDisj r1 r2);
    entails_iff hyps (CDisj r1' r2');
    disjoint_keys_mem (ckeys c1) (ckeys c2);
    disjoint_keys_mem (ckeys c1') (ckeys c2');
    introduce forall (a: afact). in_atoms (CCDisj c1' c2') a ==> derivable hyps a
    with introduce _ ==> _
    with (match a with
          | ALacks k t -> assert (in_atoms (CCDisj c1 c2) (ALacks k t))
          | ADisj t1 t2 -> assert (in_atoms (CCDisj c1 c2) (ADisj t1 t2)))
  end

let entails_disj_lacks hyps r1 r2 k =
  if inconsistent hyps then ()
  else begin
    let c1 = canon r1 in
    let c2 = canon r2 in
    entails_iff hyps (CDisj r1 r2);
    entails_iff hyps (CLacks k r2);
    disjoint_keys_mem (ckeys c1) (ckeys c2);
    introduce forall (a: afact). in_atoms (CCLacks k c2) a ==> derivable hyps a
    with introduce _ ==> _
    with (match a with
          | ALacks k' t -> assert (in_atoms (CCDisj c1 c2) (ALacks k' t))
          | _ -> ())
  end

let entails_disj_lacks_r hyps r1 r2 k =
  if inconsistent hyps then ()
  else begin
    let c1 = canon r1 in
    let c2 = canon r2 in
    entails_iff hyps (CDisj r1 r2);
    entails_iff hyps (CLacks k r1);
    disjoint_keys_mem (ckeys c1) (ckeys c2);
    introduce forall (a: afact). in_atoms (CCLacks k c1) a ==> derivable hyps a
    with introduce _ ==> _
    with (match a with
          | ALacks k' t -> assert (in_atoms (CCDisj c1 c2) (ALacks k' t))
          | _ -> ())
  end

let entails_lacks_ext hyps k en r =
  if inconsistent hyps then ()
  else begin
    entails_iff hyps (CLacks k r);
    mem_known_keys_ext k en r;
    tails_ext en r;
    lacks_mono hyps k r (TRowExt en r)
  end

let entails_lacks_union hyps k r r3 =
  if inconsistent hyps then ()
  else begin
    let u = TRowUnion r r3 in
    entails_iff hyps (CLacks k r);
    entails_iff hyps (CLacks k r3);
    entails_iff hyps (CLacks k u);
    mem_known_keys_union k r r3;
    introduce forall (a: afact). in_atoms (CCLacks k (canon u)) a ==> derivable hyps a
    with introduce _ ==> _
    with (match a with
          | ALacks k' t ->
            mem_tails_union r r3 t;
            if L.mem t (row_tails (canon r))
            then assert (in_atoms (CCLacks k (canon r)) (ALacks k' t))
            else assert (in_atoms (CCLacks k (canon r3)) (ALacks k' t))
          | _ -> ())
  end

let entails_disj_ext hyps en r r3 =
  sub_row_ext en r;
  sub_row_refl r3;
  entails_disj_sub hyps (TRowExt en r) r3 r r3;
  mem_known_keys_ext (ent_key en) en r;
  entails_disj_lacks hyps (TRowExt en r) r3 (ent_key en)

let ext_cancel_entails hyps e e' r0 r1 =
  entails_lacks_known hyps (ent_key e) r0;
  entails_lacks_known hyps (ent_key e) r1;
  ext_cancel e e' r0 r1

let ext_ty_cancel_entails hyps k t t' r0 r1 =
  entails_lacks_known hyps k r0;
  entails_lacks_known hyps k r1;
  ext_ty_cancel k t t' r0 r1
