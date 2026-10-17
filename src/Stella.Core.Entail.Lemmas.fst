(* Proof structure.

   Every fact is reduced to membership, and existential facts are produced
   by witness functions (`*_wit`, `cover`, `gs_source`) rather than stated.

   The row facts of an operation on canonical forms come from its `*_view`
   lemma: the keys of `csub s c` are those of `c` and of the images of its
   tails, and its tails are the tails of those images (`csub_keys`,
   `csub_tails`). The same holds for `cmap f` with keys mapped, and there,
   because the tails of a canonical form are not rows, every tail has
   exactly one image.

   Substitution. Write `aimg s a` for the canonical constraint an atomic
   fact becomes: `k ∉ csub s t` or `csub s t1 # csub s t2`. For a canonical
   constraint `cc`,
     - an inconsistent `cc` stays inconsistent (`csub_inconsistent`);
     - `csub_constr s cc` is consistent iff `cc` is and every `aimg s a`
       with `a` an atom of `cc` is (`img_consistent`, `sub_consistent`);
     - the atoms of `csub_constr s cc` are those of the `aimg s a`, for
       `a` ranging over the atoms of `cc` (`img_atoms`, `cover`).
   From these, an atomic fact derivable from the hypotheses has an image
   whose atoms are derivable from the substituted hypotheses
   (`derivable_img`), and `entails_sub` follows. The symmetric case of
   `derivable` uses that `aimg s (ADisj t2 t1)` is the mirror image of
   `aimg s (ADisj t1 t2)` (`disj_mirror`).

   Region maps. An atomic fact `a` has the single image `amap f a`. The
   image of a consistent hypothesis contains the images of its atoms
   (`cmap_atoms`), and every atom of the image of `c` is the image of an
   atom of `c` (`rcover`). Only consistency of the image of `c` needs
   injectivity (`cmap_consistent`): an inconsistent image of a hypothesis
   is ex falso.

   Kind instantiation is the same argument with the keys left unchanged,
   so consistency is preserved and reflected (`ckinst_consistent`).

   Cut of a list removes the hypotheses one at a time: each is entailed by
   the rest together with `hyps'`, by weakening. *)
module Stella.Core.Entail.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Region
open Stella.Core.OrdSet
open Stella.Core.Rows
open Stella.Core.Rows.Lemmas
open Stella.Core.Entail
module L = FStar.List.Tot

(* Lists. *)

let mem_app (#a: eqtype) (z: a) (l1 l2: list a)
  : Lemma (L.mem z (L.append l1 l2) = (L.mem z l1 || L.mem z l2))
          [SMTPat (L.mem z (L.append l1 l2))] =
  FStar.List.Tot.Properties.append_mem l1 l2 z

let rec mem_map (#a #b: eqtype) (f: a -> b) (l: list a) (x: a)
  : Lemma (requires L.mem x l) (ensures L.mem (f x) (L.map f l)) (decreases l) =
  match l with
  | y :: tl -> if x = y then () else mem_map f tl x

let rec map_wit (#a #b: eqtype) (f: a -> b) (l: list a) (y: b)
  : Pure a (requires L.mem y (L.map f l)) (ensures fun x -> L.mem x l /\ f x == y) (decreases l) =
  match l with
  | x :: tl -> if f x = y then x else map_wit f tl y

(* Membership in atom lists. *)

let rec mem_lacks_each (k: key) (ts: list ctyp) (a: afact)
  : Lemma (ensures L.mem a (lacks_each k ts) =
                   (match a with ALacks k' t -> k' = k && L.mem t ts | _ -> false))
          (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts -> mem_lacks_each k ts a

let rec mem_lacks_all (ks: list key) (ts: list ctyp) (a: afact)
  : Lemma (ensures L.mem a (lacks_all ks ts) =
                   (match a with ALacks k t -> L.mem k ks && L.mem t ts | _ -> false))
          (decreases ks) =
  match ks with
  | [] -> ()
  | k :: ks -> mem_lacks_each k ts a; mem_lacks_all ks ts a

let rec mem_disj_each (t1: ctyp) (ts: list ctyp) (a: afact)
  : Lemma (ensures L.mem a (disj_each t1 ts) =
                   (match a with ADisj x y -> x = t1 && L.mem y ts | _ -> false))
          (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts -> mem_disj_each t1 ts a

let rec mem_disj_all (ts1 ts2: list ctyp) (a: afact)
  : Lemma (ensures L.mem a (disj_all ts1 ts2) =
                   (match a with ADisj x y -> L.mem x ts1 && L.mem y ts2 | _ -> false))
          (decreases ts1) =
  match ts1 with
  | [] -> ()
  | t1 :: ts1 -> mem_disj_each t1 ts2 a; mem_disj_all ts1 ts2 a

let mem_catoms cc a =
  match cc with
  | CCLacks k c -> mem_lacks_each k (row_tails c) a
  | CCDisj c1 c2 ->
    mem_lacks_all (ckeys c1) (row_tails c2) a;
    mem_lacks_all (ckeys c2) (row_tails c1) a;
    mem_disj_all (row_tails c1) (row_tails c2) a

(* Disjointness of key lists. *)

let rec disjoint_keys_mem ks1 ks2 =
  match ks1 with
  | [] -> ()
  | _ :: ks1 -> disjoint_keys_mem ks1 ks2

let disjoint_keys_elim (ks1 ks2: list key) (k: key)
  : Lemma (requires disjoint_keys ks1 ks2 /\ L.mem k ks1 /\ L.mem k ks2) (ensures False) =
  disjoint_keys_mem ks1 ks2

let rec common_key (ks1 ks2: list key)
  : Pure key (requires not (disjoint_keys ks1 ks2)) (ensures fun k -> L.mem k ks1 /\ L.mem k ks2)
             (decreases ks1) =
  match ks1 with
  | k :: ks1 -> if L.mem k ks2 then k else common_key ks1 ks2

let disjoint_keys_sym (ks1 ks2: list key) : Lemma (disjoint_keys ks1 ks2 = disjoint_keys ks2 ks1) =
  disjoint_keys_mem ks1 ks2;
  disjoint_keys_mem ks2 ks1

(* Keys of entry lists. *)

let rec keys_of_intro (k: key) (p: cpayload) (es: list centry)
  : Lemma (requires L.mem (k, p) es) (ensures L.mem k (keys_of es)) (decreases es) =
  match es with
  | e :: tl -> if e = (k, p) then () else keys_of_intro k p tl

let rec keys_of_incl (k: key) (es es': list centry)
  : Lemma (requires incl es es' /\ L.mem k (keys_of es)) (ensures L.mem k (keys_of es'))
          (decreases es) =
  match es with
  | (k', p) :: tl -> if k = k' then keys_of_intro k p es' else keys_of_incl k tl es'

let keys_of_seteq (k: key) (es es': list centry)
  : Lemma (requires seteq es es') (ensures L.mem k (keys_of es) = L.mem k (keys_of es')) =
  FStar.Classical.move_requires (keys_of_incl k es) es';
  FStar.Classical.move_requires (keys_of_incl k es') es

let rec keys_of_append (es es': list centry)
  : Lemma (ensures keys_of (L.append es es') == L.append (keys_of es) (keys_of es'))
          (decreases es) =
  match es with
  | [] -> ()
  | _ :: tl -> keys_of_append tl es'

let rec keys_of_csub_ents (s: csubst) (es: list centry)
  : Lemma (ensures keys_of (L.map (csub_ent s) es) == keys_of es) (decreases es) =
  match es with
  | [] -> ()
  | _ :: tl -> keys_of_csub_ents s tl

let rec keys_of_cmap_ents (f: region_ref -> region_ref) (es: list centry)
  : Lemma (ensures keys_of (L.map (cmap_ent f) es) == L.map (rmap_key f) (keys_of es))
          (decreases es) =
  match es with
  | [] -> ()
  | _ :: tl -> keys_of_cmap_ents f tl

(* The entries and tails contributed by the images of the tails. *)

let rec vkeys (fv: ctyp -> rview) (k: key) (ts: list ctyp) : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | t :: ts -> L.mem k (keys_of (fst (fv t))) || vkeys fv k ts

let rec vtails (fv: ctyp -> rview) (t': ctyp) (ts: list ctyp) : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | t :: ts -> L.mem t' (snd (fv t)) || vtails fv t' ts

let rec mem_keys_flat (fv: ctyp -> rview) (k: key) (ts: list ctyp)
  : Lemma (ensures L.mem k (keys_of (flat_es (L.map fv ts))) = vkeys fv k ts) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: ts' -> keys_of_append (fst (fv t)) (flat_es (L.map fv ts')); mem_keys_flat fv k ts'

let rec mem_tails_flat (fv: ctyp -> rview) (t': ctyp) (ts: list ctyp)
  : Lemma (ensures L.mem t' (flat_ts (L.map fv ts)) = vtails fv t' ts) (decreases ts) =
  match ts with
  | [] -> ()
  | _ :: ts' -> mem_tails_flat fv t' ts'

let rec vkeys_intro (fv: ctyp -> rview) (k: key) (t: ctyp) (ts: list ctyp)
  : Lemma (requires L.mem t ts /\ L.mem k (keys_of (fst (fv t)))) (ensures vkeys fv k ts)
          (decreases ts) =
  match ts with
  | t0 :: ts -> if t0 = t then () else vkeys_intro fv k t ts

let rec vtails_intro (fv: ctyp -> rview) (t' t: ctyp) (ts: list ctyp)
  : Lemma (requires L.mem t ts /\ L.mem t' (snd (fv t))) (ensures vtails fv t' ts)
          (decreases ts) =
  match ts with
  | t0 :: ts -> if t0 = t then () else vtails_intro fv t' t ts

let rec vkeys_wit (fv: ctyp -> rview) (k: key) (ts: list ctyp)
  : Pure ctyp (requires vkeys fv k ts)
              (ensures fun t -> L.mem t ts /\ L.mem k (keys_of (fst (fv t))))
              (decreases ts) =
  match ts with
  | t :: ts -> if L.mem k (keys_of (fst (fv t))) then t else vkeys_wit fv k ts

let rec vtails_wit (fv: ctyp -> rview) (t': ctyp) (ts: list ctyp)
  : Pure ctyp (requires vtails fv t' ts) (ensures fun t -> L.mem t ts /\ L.mem t' (snd (fv t)))
              (decreases ts) =
  match ts with
  | t :: ts -> if L.mem t' (snd (fv t)) then t else vtails_wit fv t' ts

(* The row facts of substitution. *)

let csub_keys (s: csubst) (c: ctyp) (k: key)
  : Lemma (L.mem k (ckeys (csub s c)) =
           (L.mem k (ckeys c) || vkeys (csub_vf s) k (row_tails c))) =
  csub_view s c;
  let v = view_row c in
  let es = L.append (L.map (csub_ent s) (fst v)) (flat_es (L.map (csub_vf s) (snd v))) in
  keys_of_seteq k (row_entries (csub s c)) es;
  keys_of_append (L.map (csub_ent s) (fst v)) (flat_es (L.map (csub_vf s) (snd v)));
  keys_of_csub_ents s (fst v);
  mem_keys_flat (csub_vf s) k (snd v)

let csub_tails (s: csubst) (c: ctyp) (t': ctyp)
  : Lemma (L.mem t' (row_tails (csub s c)) = vtails (csub_vf s) t' (row_tails c)) =
  csub_view s c;
  mem_tails_flat (csub_vf s) t' (row_tails c)

(* A known key of `c`, or of the image of a tail of `c`, is a known key of
   `csub s c`; a tail of the image of a tail of `c` is a tail of
   `csub s c`. *)

let keys_up (s: csubst) (c: ctyp) (k: key)
  : Lemma (requires L.mem k (ckeys c)) (ensures L.mem k (ckeys (csub s c))) =
  csub_keys s c k

let keys_up_tail (s: csubst) (c t: ctyp) (k: key)
  : Lemma (requires L.mem t (row_tails c) /\ L.mem k (ckeys (csub s t)))
          (ensures L.mem k (ckeys (csub s c))) =
  vkeys_intro (csub_vf s) k t (row_tails c);
  csub_keys s c k

let tails_up (s: csubst) (c t t': ctyp)
  : Lemma (requires L.mem t (row_tails c) /\ L.mem t' (row_tails (csub s t)))
          (ensures L.mem t' (row_tails (csub s c))) =
  vtails_intro (csub_vf s) t' t (row_tails c);
  csub_tails s c t'

(* Atomic facts under substitution. *)

let aimg (s: csubst) (a: afact) : cconstr =
  match a with
  | ALacks k t -> CCLacks k (csub s t)
  | ADisj t1 t2 -> CCDisj (csub s t1) (csub s t2)

let csub_inconsistent (s: csubst) (cc: cconstr)
  : Lemma (requires not (cconsistent cc)) (ensures not (cconsistent (csub_constr s cc))) =
  match cc with
  | CCLacks k c -> keys_up s c k
  | CCDisj c1 c2 ->
    let k = common_key (ckeys c1) (ckeys c2) in
    keys_up s c1 k;
    keys_up s c2 k;
    FStar.Classical.move_requires (disjoint_keys_elim (ckeys (csub s c1)) (ckeys (csub s c2))) k

let img_consistent (s: csubst) (cc: cconstr) (a: afact)
  : Lemma (requires in_atoms cc a /\ cconsistent (csub_constr s cc))
          (ensures cconsistent (aimg s a)) =
  match cc, a with
  | CCLacks k c, ALacks _ t ->
    FStar.Classical.move_requires (keys_up_tail s c t) k
  | CCDisj c1 c2, ALacks k t ->
    let ks1 = ckeys (csub s c1) in
    let ks2 = ckeys (csub s c2) in
    if L.mem k (ckeys (csub s t)) then begin
      if L.mem k (ckeys c1) && L.mem t (row_tails c2) then begin
        keys_up s c1 k; keys_up_tail s c2 t k; disjoint_keys_elim ks1 ks2 k
      end else begin
        keys_up s c2 k; keys_up_tail s c1 t k; disjoint_keys_elim ks1 ks2 k
      end
    end
  | CCDisj c1 c2, ADisj t1 t2 ->
    if not (disjoint_keys (ckeys (csub s t1)) (ckeys (csub s t2))) then begin
      let k = common_key (ckeys (csub s t1)) (ckeys (csub s t2)) in
      keys_up_tail s c1 t1 k;
      keys_up_tail s c2 t2 k;
      disjoint_keys_elim (ckeys (csub s c1)) (ckeys (csub s c2)) k
    end

let img_atoms (s: csubst) (cc: cconstr) (a b: afact)
  : Lemma (requires in_atoms cc a /\ in_atoms (aimg s a) b)
          (ensures in_atoms (csub_constr s cc) b) =
  match cc, a, b with
  | CCLacks k c, ALacks _ t, ALacks _ t' -> tails_up s c t t'
  | CCDisj c1 c2, ALacks k t, ALacks _ t' ->
    if L.mem k (ckeys c1) && L.mem t (row_tails c2) then begin
      keys_up s c1 k; tails_up s c2 t t'
    end else begin
      keys_up s c2 k; tails_up s c1 t t'
    end
  | CCDisj c1 c2, ADisj t1 t2, ALacks k t' ->
    if L.mem k (ckeys (csub s t1)) && L.mem t' (row_tails (csub s t2)) then begin
      keys_up_tail s c1 t1 k; tails_up s c2 t2 t'
    end else begin
      keys_up_tail s c2 t2 k; tails_up s c1 t1 t'
    end
  | CCDisj c1 c2, ADisj t1 t2, ADisj x y -> tails_up s c1 t1 x; tails_up s c2 t2 y

let sub_consistent (s: csubst) (cc: cconstr)
  : Lemma (requires cconsistent cc /\ (forall (a: afact). in_atoms cc a ==> cconsistent (aimg s a)))
          (ensures cconsistent (csub_constr s cc)) =
  match cc with
  | CCLacks k c ->
    csub_keys s c k;
    if L.mem k (ckeys (csub s c)) then begin
      let t = vkeys_wit (csub_vf s) k (row_tails c) in
      assert (in_atoms cc (ALacks k t))
    end
  | CCDisj c1 c2 ->
    let ks1 = ckeys (csub s c1) in
    let ks2 = ckeys (csub s c2) in
    if not (disjoint_keys ks1 ks2) then begin
      let k = common_key ks1 ks2 in
      csub_keys s c1 k;
      csub_keys s c2 k;
      if L.mem k (ckeys c1) then begin
        if L.mem k (ckeys c2) then disjoint_keys_elim (ckeys c1) (ckeys c2) k
        else begin
          let t2 = vkeys_wit (csub_vf s) k (row_tails c2) in
          assert (in_atoms cc (ALacks k t2))
        end
      end else begin
        let t1 = vkeys_wit (csub_vf s) k (row_tails c1) in
        if L.mem k (ckeys c2) then assert (in_atoms cc (ALacks k t1))
        else begin
          let t2 = vkeys_wit (csub_vf s) k (row_tails c2) in
          assert (in_atoms cc (ADisj t1 t2));
          disjoint_keys_elim (ckeys (csub s t1)) (ckeys (csub s t2)) k
        end
      end
    end

(* The atom of `cc` whose image contains a given atom of `csub_constr s cc`. *)
let cover (s: csubst) (cc: cconstr) (b: afact)
  : Pure afact (requires in_atoms (csub_constr s cc) b)
               (ensures fun a -> in_atoms cc a /\ in_atoms (aimg s a) b) =
  match cc, b with
  | CCLacks k c, ALacks _ t' ->
    csub_tails s c t';
    ALacks k (vtails_wit (csub_vf s) t' (row_tails c))
  | CCDisj c1 c2, ALacks k t' ->
    if L.mem k (ckeys (csub s c1)) && L.mem t' (row_tails (csub s c2)) then begin
      csub_tails s c2 t';
      csub_keys s c1 k;
      let t2 = vtails_wit (csub_vf s) t' (row_tails c2) in
      if L.mem k (ckeys c1) then ALacks k t2
      else ADisj (vkeys_wit (csub_vf s) k (row_tails c1)) t2
    end else begin
      csub_tails s c1 t';
      csub_keys s c2 k;
      let t1 = vtails_wit (csub_vf s) t' (row_tails c1) in
      if L.mem k (ckeys c2) then ALacks k t1
      else ADisj t1 (vkeys_wit (csub_vf s) k (row_tails c2))
    end
  | CCDisj c1 c2, ADisj x y ->
    csub_tails s c1 x;
    csub_tails s c2 y;
    ADisj (vtails_wit (csub_vf s) x (row_tails c1)) (vtails_wit (csub_vf s) y (row_tails c2))

(* The mirror image of an atomic fact. *)
let flip (a: afact) : afact =
  match a with
  | ADisj x y -> ADisj y x
  | _ -> a

let derivable_flip (gs: list afact) (b: afact)
  : Lemma (requires L.mem (flip b) gs) (ensures derivable_in gs b) = ()

let disj_mirror (u1 u2: ctyp) (b: afact)
  : Lemma (cconsistent (CCDisj u1 u2) = cconsistent (CCDisj u2 u1) /\
           (in_atoms (CCDisj u1 u2) b ==> in_atoms (CCDisj u2 u1) (flip b))) =
  disjoint_keys_sym (ckeys u1) (ckeys u2)

(* Hypotheses: consistency and `Γ*`. *)

let rec consistent_mem (hyps: list constr) (h: constr)
  : Lemma (requires not (inconsistent hyps) /\ L.mem h hyps) (ensures cconsistent (canon_constr h))
          (decreases hyps) =
  match hyps with
  | h' :: tl -> if h = h' then () else consistent_mem tl h

let rec inconsistent_intro (hyps: list constr) (h: constr)
  : Lemma (requires L.mem h hyps /\ not (cconsistent (canon_constr h))) (ensures inconsistent hyps)
          (decreases hyps) =
  match hyps with
  | h' :: tl -> if h = h' then () else inconsistent_intro tl h

let rec inconsistent_wit (hyps: list constr)
  : Pure constr (requires inconsistent hyps)
                (ensures fun h -> L.mem h hyps /\ not (cconsistent (canon_constr h)))
                (decreases hyps) =
  match hyps with
  | h :: tl -> if None? (decompose h) then h else inconsistent_wit tl

let rec gs_intro (hyps: list constr) (h: constr) (a: afact)
  : Lemma (requires L.mem h hyps /\ cconsistent (canon_constr h) /\ in_atoms (canon_constr h) a)
          (ensures L.mem a (gamma_star hyps))
          (decreases hyps) =
  match hyps with
  | h' :: tl -> if h = h' then mem_catoms (canon_constr h) a else gs_intro tl h a

let rec gs_source (hyps: list constr) (a: afact)
  : Pure constr (requires L.mem a (gamma_star hyps))
                (ensures fun h -> L.mem h hyps /\ cconsistent (canon_constr h) /\
                               in_atoms (canon_constr h) a)
                (decreases hyps) =
  match hyps with
  | h :: tl ->
    mem_catoms (canon_constr h) a;
    if cconsistent (canon_constr h) && in_atoms (canon_constr h) a then h else gs_source tl a

let rec all_derivable_intro (gs l: list afact)
  : Lemma (requires forall (a: afact). L.mem a l ==> derivable_in gs a)
          (ensures all_derivable gs l) (decreases l) =
  match l with
  | [] -> ()
  | _ :: tl -> all_derivable_intro gs tl

let rec all_derivable_elim (gs l: list afact) (a: afact)
  : Lemma (requires all_derivable gs l /\ L.mem a l) (ensures derivable_in gs a) (decreases l) =
  match l with
  | a' :: tl -> if a = a' then () else all_derivable_elim gs tl a

let inconsistent_mem hyps =
  if inconsistent hyps then begin
    let h = inconsistent_wit hyps in
    assert (L.mem h hyps /\ None? (decompose h))
  end
  else FStar.Classical.forall_intro (FStar.Classical.move_requires (consistent_mem hyps))

let mem_gamma_star hyps a =
  if L.mem a (gamma_star hyps) then begin
    let h = gs_source hyps a in
    mem_catoms (canon_constr h) a
  end else begin
    let aux (h: constr)
      : Lemma (requires L.mem h hyps /\ Some? (decompose h) /\ L.mem a (Some?.v (decompose h)))
              (ensures False) =
      mem_catoms (canon_constr h) a;
      gs_intro hyps h a
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end

let all_derivable_mem gs l =
  FStar.Classical.move_requires (all_derivable_intro gs) l;
  FStar.Classical.forall_intro (FStar.Classical.move_requires (all_derivable_elim gs l))

(* Every atomic fact of `cc` is derivable from `gs`. `entails_intro` and
   `entails_elim` read a consistent hypothesis list's `entails` through it. *)
let atoms_derivable (gs: list afact) (cc: cconstr) : prop =
  forall (a: afact). in_atoms cc a ==> derivable_in gs a

let entails_intro (hyps: list constr) (c: constr)
  : Lemma (requires cconsistent (canon_constr c) /\
                    atoms_derivable (gamma_star hyps) (canon_constr c))
          (ensures entails hyps c) =
  let cc = canon_constr c in
  FStar.Classical.forall_intro (mem_catoms cc);
  all_derivable_intro (gamma_star hyps) (catoms cc)

let entails_elim (hyps: list constr) (c: constr)
  : Lemma (requires entails hyps c /\ not (inconsistent hyps))
          (ensures cconsistent (canon_constr c) /\
                   atoms_derivable (gamma_star hyps) (canon_constr c)) =
  let cc = canon_constr c in
  FStar.Classical.forall_intro (mem_catoms cc);
  FStar.Classical.forall_intro
    (FStar.Classical.move_requires (all_derivable_elim (gamma_star hyps) (catoms cc)))

let entails_hyp hyps c =
  if inconsistent hyps then ()
  else begin
    consistent_mem hyps c;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (gs_intro hyps c));
    entails_intro hyps c
  end

(* Type equality. *)

let entails_constr_eq hyps c c' = ()

let rec constrs_eq_same (hs hs': list constr)
  : Lemma (requires constrs_eq hs hs')
          (ensures inconsistent hs = inconsistent hs' /\ gamma_star hs == gamma_star hs')
          (decreases hs) =
  match hs, hs' with
  | [], [] -> ()
  | _ :: tl, _ :: tl' -> constrs_eq_same tl tl'

let entails_constrs_eq hs hs' c = constrs_eq_same hs hs'

(* Known keys under substitution. *)

(* `canon ∘ σ` *)
let cs (sigma: tsub) (i: nat) : ctyp = canon (sigma i)

let canon_sub_cs (sigma: tsub) (c: constr)
  : Lemma (canon_constr (sub_constr sigma c) == csub_constr (cs sigma) (canon_constr c)) =
  canon_sub_constr sigma (cs sigma) c

let known_keys_sub sigma k t =
  canon_sub sigma (cs sigma) t;
  keys_up (cs sigma) (canon t) k

let decompose_sub_none sigma c =
  canon_sub_cs sigma c;
  csub_inconsistent (cs sigma) (canon_constr c)

let inconsistent_sub sigma hyps =
  let h = inconsistent_wit hyps in
  decompose_sub_none sigma h;
  mem_map (sub_constr sigma) hyps h;
  inconsistent_intro (L.map (sub_constr sigma) hyps) (sub_constr sigma h)

let inconsistent_sound hyps sigma =
  let h = inconsistent_wit hyps in
  decompose_sub_none sigma h;
  assert (L.mem h hyps /\ not (entails [] (sub_constr sigma h)))

(* The inconsistency characterization: completeness. *)

let rec var_tails_mem (ts: list ctyp) (t: ctyp)
  : Lemma (requires var_tails ts /\ L.mem t ts) (ensures CVar? t) (decreases ts) =
  match ts with
  | t' :: tl -> if t = t' then () else var_tails_mem tl t

let consistent_complete c =
  let s = cs empty_rows in
  let cc = canon_constr c in
  let e = CRow [] [] in
  assert (forall (i: nat). s i == e);
  let img (a: afact)
    : Lemma (requires in_atoms cc a)
            (ensures cconsistent (aimg s a) /\ (forall (b: afact). not (in_atoms (aimg s a) b))) =
    match cc, a with
    | CCLacks _ r, ALacks _ t -> var_tails_mem (row_tails r) t
    | CCDisj r1 r2, ALacks k t ->
      FStar.Classical.move_requires (var_tails_mem (row_tails r1)) t;
      FStar.Classical.move_requires (var_tails_mem (row_tails r2)) t
    | CCDisj r1 r2, ADisj t1 t2 ->
      var_tails_mem (row_tails r1) t1;
      var_tails_mem (row_tails r2) t2
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires img);
  sub_consistent s cc;
  let none (b: afact) : Lemma (not (in_atoms (csub_constr s cc) b)) =
    if in_atoms (csub_constr s cc) b then img (cover s cc b)
  in
  FStar.Classical.forall_intro none;
  canon_sub_cs empty_rows c;
  entails_intro [] (sub_constr empty_rows c)

let inconsistent_complete hyps =
  let rec aux (hs: list constr) (h: constr)
    : Lemma (requires not (inconsistent hs) /\ var_tailed_all hs /\ L.mem h hs)
            (ensures entails [] (sub_constr empty_rows h)) (decreases hs) =
    match hs with
    | h' :: tl -> if h = h' then consistent_complete h else aux tl h
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires (aux hyps))

(* Preservation under substitution. *)

(* An atomic fact of `Γ*` has a consistent image, all of whose atoms are in
   the substituted `Γ*`, as long as the substituted hypotheses are
   consistent. *)
let gs_img (sigma: tsub) (hyps: list constr) (a: afact)
  : Lemma (requires not (inconsistent (L.map (sub_constr sigma) hyps)) /\ L.mem a (gamma_star hyps))
          (ensures cconsistent (aimg (cs sigma) a) /\
                   (forall (b: afact). in_atoms (aimg (cs sigma) a) b ==>
                                  L.mem b (gamma_star (L.map (sub_constr sigma) hyps)))) =
  let s = cs sigma in
  let hyps' = L.map (sub_constr sigma) hyps in
  let h = gs_source hyps a in
  let h' = sub_constr sigma h in
  mem_map (sub_constr sigma) hyps h;
  consistent_mem hyps' h';
  canon_sub_cs sigma h;
  img_consistent s (canon_constr h) a;
  let aux (b: afact)
    : Lemma (requires in_atoms (aimg s a) b) (ensures L.mem b (gamma_star hyps')) =
    img_atoms s (canon_constr h) a b;
    gs_intro hyps' h' b
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let derivable_img (sigma: tsub) (hyps: list constr) (a: afact)
  : Lemma (requires not (inconsistent (L.map (sub_constr sigma) hyps)) /\ derivable hyps a)
          (ensures cconsistent (aimg (cs sigma) a) /\
                   atoms_derivable (gamma_star (L.map (sub_constr sigma) hyps))
                     (aimg (cs sigma) a)) =
  let gs = gamma_star hyps in
  if L.mem a gs then gs_img sigma hyps a
  else begin
    let ADisj t1 t2 = a in
    let s = cs sigma in
    gs_img sigma hyps (ADisj t2 t1);
    FStar.Classical.forall_intro (disj_mirror (csub s t1) (csub s t2));
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (derivable_flip (gamma_star (L.map (sub_constr sigma) hyps))))
  end

let entails_sub sigma hyps c =
  let hyps' = L.map (sub_constr sigma) hyps in
  if inconsistent hyps' then ()
  else begin
    FStar.Classical.move_requires (inconsistent_sub sigma) hyps;
    let s = cs sigma in
    let cc = canon_constr c in
    entails_elim hyps c;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (derivable_img sigma hyps));
    sub_consistent s cc;
    let aux (b: afact)
      : Lemma (requires in_atoms (csub_constr s cc) b) (ensures derivable hyps' b) =
      derivable_img sigma hyps (cover s cc b)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    canon_sub_cs sigma c;
    entails_intro hyps' (sub_constr sigma c)
  end

let ren_constr_as_sub (xi: ren) (c: constr)
  : Lemma (ren_constr xi c == sub_constr (ren_tsub xi) c) =
  match c with
  | CLacks _ t -> ren_ty_as_sub xi t
  | CDisj t1 t2 -> ren_ty_as_sub xi t1; ren_ty_as_sub xi t2

let rec ren_constrs_as_sub (xi: ren) (hs: list constr)
  : Lemma (ensures L.map (ren_constr xi) hs == L.map (sub_constr (ren_tsub xi)) hs) (decreases hs) =
  match hs with
  | [] -> ()
  | h :: tl -> ren_constr_as_sub xi h; ren_constrs_as_sub xi tl

let entails_ren xi hyps c =
  ren_constr_as_sub xi c;
  ren_constrs_as_sub xi hyps;
  entails_sub (ren_tsub xi) hyps c

(* Region maps. The tails of a canonical form are not rows, so each tail
   `t` has the single image `cmap f t`, and the known keys of `cmap f c`
   are the images of those of `c`. *)

let nonrow_tails (c: ctyp) : prop = forall (t: ctyp). L.mem t (row_tails c) ==> not (CRow? t)

let cc_nonrow (cc: cconstr) : prop =
  match cc with
  | CCLacks _ c -> nonrow_tails c
  | CCDisj c1 c2 -> nonrow_tails c1 /\ nonrow_tails c2

let canon_cc_nonrow (c: constr) : Lemma (cc_nonrow (canon_constr c)) =
  match c with
  | CLacks _ r ->
    FStar.Classical.forall_intro (FStar.Classical.move_requires (canon_tails_nonrow r))
  | CDisj r1 r2 ->
    FStar.Classical.forall_intro (FStar.Classical.move_requires (canon_tails_nonrow r1));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (canon_tails_nonrow r2))

let cmap_nonrow (f: region_ref -> region_ref) (t: ctyp)
  : Lemma (requires not (CRow? t)) (ensures not (CRow? (cmap f t))) = ()

let rec vkeys_nonrow (f: region_ref -> region_ref) (k: key) (ts: list ctyp)
  : Lemma (requires forall (t: ctyp). L.mem t ts ==> not (CRow? t))
          (ensures not (vkeys (cmap_vf f) k ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: tl -> cmap_nonrow f t; vkeys_nonrow f k tl

let rec vtails_nonrow (f: region_ref -> region_ref) (t': ctyp) (ts: list ctyp)
  : Lemma (requires forall (t: ctyp). L.mem t ts ==> not (CRow? t))
          (ensures vtails (cmap_vf f) t' ts = L.mem t' (L.map (cmap f) ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: tl -> cmap_nonrow f t; vtails_nonrow f t' tl

let cmap_keys (f: region_ref -> region_ref) (c: ctyp) (k: key)
  : Lemma (L.mem k (ckeys (cmap f c)) =
           (L.mem k (L.map (rmap_key f) (ckeys c)) || vkeys (cmap_vf f) k (row_tails c))) =
  cmap_view f c;
  let v = view_row c in
  let es = L.append (L.map (cmap_ent f) (fst v)) (flat_es (L.map (cmap_vf f) (snd v))) in
  keys_of_seteq k (row_entries (cmap f c)) es;
  keys_of_append (L.map (cmap_ent f) (fst v)) (flat_es (L.map (cmap_vf f) (snd v)));
  keys_of_cmap_ents f (fst v);
  mem_keys_flat (cmap_vf f) k (snd v)

let cmap_tails (f: region_ref -> region_ref) (c: ctyp) (t': ctyp)
  : Lemma (L.mem t' (row_tails (cmap f c)) = vtails (cmap_vf f) t' (row_tails c)) =
  cmap_view f c;
  mem_tails_flat (cmap_vf f) t' (row_tails c)

let rkeys_up (f: region_ref -> region_ref) (c: ctyp) (k: key)
  : Lemma (requires L.mem k (ckeys c)) (ensures L.mem (rmap_key f k) (ckeys (cmap f c))) =
  mem_map (rmap_key f) (ckeys c) k;
  cmap_keys f c (rmap_key f k)

let rtails_up (f: region_ref -> region_ref) (c t: ctyp)
  : Lemma (requires nonrow_tails c /\ L.mem t (row_tails c))
          (ensures L.mem (cmap f t) (row_tails (cmap f c))) =
  mem_map (cmap f) (row_tails c) t;
  vtails_nonrow f (cmap f t) (row_tails c);
  cmap_tails f c (cmap f t)

let rkeys_down (f: region_ref -> region_ref) (c: ctyp) (k': key)
  : Pure key (requires nonrow_tails c /\ L.mem k' (ckeys (cmap f c)))
             (ensures fun k -> L.mem k (ckeys c) /\ rmap_key f k == k') =
  cmap_keys f c k';
  vkeys_nonrow f k' (row_tails c);
  map_wit (rmap_key f) (ckeys c) k'

let rtails_down (f: region_ref -> region_ref) (c: ctyp) (t': ctyp)
  : Pure ctyp (requires nonrow_tails c /\ L.mem t' (row_tails (cmap f c)))
              (ensures fun t -> L.mem t (row_tails c) /\ cmap f t == t') =
  cmap_tails f c t';
  vtails_nonrow f t' (row_tails c);
  map_wit (cmap f) (row_tails c) t'

let amap (f: region_ref -> region_ref) (a: afact) : afact =
  match a with
  | ALacks k t -> ALacks (rmap_key f k) (cmap f t)
  | ADisj t1 t2 -> ADisj (cmap f t1) (cmap f t2)

let cmap_inconsistent (f: region_ref -> region_ref) (cc: cconstr)
  : Lemma (requires not (cconsistent cc)) (ensures not (cconsistent (cmap_constr f cc))) =
  match cc with
  | CCLacks k c -> rkeys_up f c k
  | CCDisj c1 c2 ->
    let k = common_key (ckeys c1) (ckeys c2) in
    rkeys_up f c1 k;
    rkeys_up f c2 k;
    FStar.Classical.move_requires
      (disjoint_keys_elim (ckeys (cmap f c1)) (ckeys (cmap f c2))) (rmap_key f k)

let cmap_atoms (f: region_ref -> region_ref) (cc: cconstr) (a: afact)
  : Lemma (requires cc_nonrow cc /\ in_atoms cc a)
          (ensures in_atoms (cmap_constr f cc) (amap f a)) =
  match cc, a with
  | CCLacks k c, ALacks _ t -> rtails_up f c t
  | CCDisj c1 c2, ALacks k t ->
    if L.mem k (ckeys c1) && L.mem t (row_tails c2) then begin
      rkeys_up f c1 k; rtails_up f c2 t
    end else begin
      rkeys_up f c2 k; rtails_up f c1 t
    end
  | CCDisj c1 c2, ADisj t1 t2 -> rtails_up f c1 t1; rtails_up f c2 t2

let cmap_consistent (f: region_ref -> region_ref) (cc: cconstr)
  : Lemma (requires cc_nonrow cc /\ cconsistent cc /\ rmap_injective_on f (cc_keys cc))
          (ensures cconsistent (cmap_constr f cc)) =
  match cc with
  | CCLacks k c ->
    if L.mem (rmap_key f k) (ckeys (cmap f c)) then begin
      let k0 = rkeys_down f c (rmap_key f k) in
      assert (L.mem k0 (cc_keys cc) /\ L.mem k (cc_keys cc))
    end
  | CCDisj c1 c2 ->
    let ks1 = ckeys (cmap f c1) in
    let ks2 = ckeys (cmap f c2) in
    if not (disjoint_keys ks1 ks2) then begin
      let k' = common_key ks1 ks2 in
      let k1 = rkeys_down f c1 k' in
      let k2 = rkeys_down f c2 k' in
      assert (L.mem k1 (cc_keys cc) /\ L.mem k2 (cc_keys cc));
      disjoint_keys_elim (ckeys c1) (ckeys c2) k1
    end

(* The atom of `cc` whose image is a given atom of `cmap_constr f cc`. *)
let rcover (f: region_ref -> region_ref) (cc: cconstr) (b: afact)
  : Pure afact (requires cc_nonrow cc /\ in_atoms (cmap_constr f cc) b)
               (ensures fun a -> in_atoms cc a /\ amap f a == b) =
  match cc, b with
  | CCLacks k c, ALacks _ t' -> ALacks k (rtails_down f c t')
  | CCDisj c1 c2, ALacks k' t' ->
    if L.mem k' (ckeys (cmap f c1)) && L.mem t' (row_tails (cmap f c2)) then
      ALacks (rkeys_down f c1 k') (rtails_down f c2 t')
    else ALacks (rkeys_down f c2 k') (rtails_down f c1 t')
  | CCDisj c1 c2, ADisj x y -> ADisj (rtails_down f c1 x) (rtails_down f c2 y)

let gs_rmap (f: region_ref -> region_ref) (hyps: list constr) (a: afact)
  : Lemma (requires not (inconsistent (L.map (rmap_constr f) hyps)) /\ L.mem a (gamma_star hyps))
          (ensures L.mem (amap f a) (gamma_star (L.map (rmap_constr f) hyps))) =
  let hyps' = L.map (rmap_constr f) hyps in
  let h = gs_source hyps a in
  let h' = rmap_constr f h in
  mem_map (rmap_constr f) hyps h;
  consistent_mem hyps' h';
  canon_rmap_constr f h;
  canon_cc_nonrow h;
  cmap_atoms f (canon_constr h) a;
  gs_intro hyps' h' (amap f a)

let derivable_rmap (f: region_ref -> region_ref) (hyps: list constr) (a: afact)
  : Lemma (requires not (inconsistent (L.map (rmap_constr f) hyps)) /\ derivable hyps a)
          (ensures derivable (L.map (rmap_constr f) hyps) (amap f a)) =
  if L.mem a (gamma_star hyps) then gs_rmap f hyps a else gs_rmap f hyps (flip a)

let entails_rmap f hyps c =
  let hyps' = L.map (rmap_constr f) hyps in
  if inconsistent hyps' then ()
  else begin
    if inconsistent hyps then begin
      let h = inconsistent_wit hyps in
      canon_rmap_constr f h;
      cmap_inconsistent f (canon_constr h);
      mem_map (rmap_constr f) hyps h;
      inconsistent_intro hyps' (rmap_constr f h)
    end;
    let cc = canon_constr c in
    canon_rmap_constr f c;
    canon_cc_nonrow c;
    entails_elim hyps c;
    cmap_consistent f cc;
    let aux (b: afact)
      : Lemma (requires in_atoms (cmap_constr f cc) b) (ensures derivable hyps' b) =
      derivable_rmap f hyps (rcover f cc b)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    entails_intro hyps' (rmap_constr f c)
  end

let rec known_keys_frn (t: typ) (k: key) (x: atom)
  : Lemma (requires L.mem k (known_keys t) /\ L.mem x (frn_key k)) (ensures L.mem x (frn_ty t))
          (decreases t) =
  match t with
  | TRowEmpty -> known_keys_empty ()
  | TRowExt en r ->
    mem_known_keys_ext k en r;
    if k = ent_key en then () else known_keys_frn r k x
  | TRowUnion a b ->
    mem_known_keys_union k a b;
    if L.mem k (known_keys a) then known_keys_frn a k x else known_keys_frn b k x
  | _ -> canon_nonrow t

let entails_open_region d a hyps c =
  let f = open_rr a d in
  let fresh (k: key) : prop = not (L.mem a (frn_key k)) in
  (match c with
   | CLacks k r ->
     let aux (k': key) : Lemma (requires L.mem k' (known_keys r)) (ensures fresh k') =
       FStar.Classical.move_requires (known_keys_frn r k') a
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
   | CDisj r1 r2 ->
     let aux (k': key)
       : Lemma (requires L.mem k' (L.append (known_keys r1) (known_keys r2))) (ensures fresh k') =
       FStar.Classical.move_requires (known_keys_frn r1 k') a;
       FStar.Classical.move_requires (known_keys_frn r2 k') a
     in
     FStar.Classical.forall_intro (FStar.Classical.move_requires aux));
  assert (forall (k: key). L.mem k (cc_keys (canon_constr c)) ==> fresh k);
  assert (rmap_injective_on f (cc_keys (canon_constr c)));
  entails_rmap f hyps c

(* Kind instantiation. As for region maps, each tail `t` of a canonical
   form has the single image `ckinst ks t`; the keys are unchanged. *)

let ckinst_nonrow (ks: list kind) (t: ctyp)
  : Lemma (requires not (CRow? t)) (ensures not (CRow? (ckinst ks t))) = ()

let rec vkeys_nonrow_k (ks: list kind) (k: key) (ts: list ctyp)
  : Lemma (requires forall (t: ctyp). L.mem t ts ==> not (CRow? t))
          (ensures not (vkeys (ckinst_vf ks) k ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: tl -> ckinst_nonrow ks t; vkeys_nonrow_k ks k tl

let rec vtails_nonrow_k (ks: list kind) (t': ctyp) (ts: list ctyp)
  : Lemma (requires forall (t: ctyp). L.mem t ts ==> not (CRow? t))
          (ensures vtails (ckinst_vf ks) t' ts = L.mem t' (L.map (ckinst ks) ts)) (decreases ts) =
  match ts with
  | [] -> ()
  | t :: tl -> ckinst_nonrow ks t; vtails_nonrow_k ks t' tl

let rec keys_of_ckinst_ents (ks: list kind) (es: list centry)
  : Lemma (ensures keys_of (L.map (ckinst_ent ks) es) == keys_of es) (decreases es) =
  match es with
  | [] -> ()
  | _ :: tl -> keys_of_ckinst_ents ks tl

let ckinst_keys (ks: list kind) (c: ctyp) (k: key)
  : Lemma (requires nonrow_tails c) (ensures L.mem k (ckeys (ckinst ks c)) = L.mem k (ckeys c)) =
  ckinst_view ks c;
  let v = view_row c in
  let es = L.append (L.map (ckinst_ent ks) (fst v)) (flat_es (L.map (ckinst_vf ks) (snd v))) in
  keys_of_seteq k (row_entries (ckinst ks c)) es;
  keys_of_append (L.map (ckinst_ent ks) (fst v)) (flat_es (L.map (ckinst_vf ks) (snd v)));
  keys_of_ckinst_ents ks (fst v);
  mem_keys_flat (ckinst_vf ks) k (snd v);
  vkeys_nonrow_k ks k (snd v)

let ckinst_tails (ks: list kind) (c: ctyp) (t': ctyp)
  : Lemma (requires nonrow_tails c)
          (ensures L.mem t' (row_tails (ckinst ks c)) = L.mem t' (L.map (ckinst ks) (row_tails c))) =
  ckinst_view ks c;
  mem_tails_flat (ckinst_vf ks) t' (row_tails c);
  vtails_nonrow_k ks t' (row_tails c)

let ktails_up (ks: list kind) (c t: ctyp)
  : Lemma (requires nonrow_tails c /\ L.mem t (row_tails c))
          (ensures L.mem (ckinst ks t) (row_tails (ckinst ks c))) =
  mem_map (ckinst ks) (row_tails c) t;
  ckinst_tails ks c (ckinst ks t)

let ktails_down (ks: list kind) (c: ctyp) (t': ctyp)
  : Pure ctyp (requires nonrow_tails c /\ L.mem t' (row_tails (ckinst ks c)))
              (ensures fun t -> L.mem t (row_tails c) /\ ckinst ks t == t') =
  ckinst_tails ks c t';
  map_wit (ckinst ks) (row_tails c) t'

let akinst (ks: list kind) (a: afact) : afact =
  match a with
  | ALacks k t -> ALacks k (ckinst ks t)
  | ADisj t1 t2 -> ADisj (ckinst ks t1) (ckinst ks t2)

let ckinst_consistent (ks: list kind) (cc: cconstr)
  : Lemma (requires cc_nonrow cc) (ensures cconsistent (ckinst_constr ks cc) = cconsistent cc) =
  match cc with
  | CCLacks k c -> ckinst_keys ks c k
  | CCDisj c1 c2 ->
    FStar.Classical.forall_intro (ckinst_keys ks c1);
    FStar.Classical.forall_intro (ckinst_keys ks c2);
    disjoint_keys_mem (ckeys c1) (ckeys c2);
    disjoint_keys_mem (ckeys (ckinst ks c1)) (ckeys (ckinst ks c2))

let ckinst_atoms (ks: list kind) (cc: cconstr) (a: afact)
  : Lemma (requires cc_nonrow cc /\ in_atoms cc a)
          (ensures in_atoms (ckinst_constr ks cc) (akinst ks a)) =
  match cc, a with
  | CCLacks k c, ALacks _ t -> ktails_up ks c t
  | CCDisj c1 c2, ALacks k t ->
    ckinst_keys ks c1 k;
    ckinst_keys ks c2 k;
    if L.mem k (ckeys c1) && L.mem t (row_tails c2) then ktails_up ks c2 t
    else ktails_up ks c1 t
  | CCDisj c1 c2, ADisj t1 t2 -> ktails_up ks c1 t1; ktails_up ks c2 t2

(* The atom of `cc` whose image is a given atom of `ckinst_constr ks cc`. *)
let kcover (ks: list kind) (cc: cconstr) (b: afact)
  : Pure afact (requires cc_nonrow cc /\ in_atoms (ckinst_constr ks cc) b)
               (ensures fun a -> in_atoms cc a /\ akinst ks a == b) =
  match cc, b with
  | CCLacks k c, ALacks _ t' -> ALacks k (ktails_down ks c t')
  | CCDisj c1 c2, ALacks k t' ->
    ckinst_keys ks c1 k;
    ckinst_keys ks c2 k;
    if L.mem k (ckeys (ckinst ks c1)) && L.mem t' (row_tails (ckinst ks c2)) then
      ALacks k (ktails_down ks c2 t')
    else ALacks k (ktails_down ks c1 t')
  | CCDisj c1 c2, ADisj x y -> ADisj (ktails_down ks c1 x) (ktails_down ks c2 y)

let gs_kinst (ks: list kind) (hyps: list constr) (a: afact)
  : Lemma (requires L.mem a (gamma_star hyps))
          (ensures L.mem (akinst ks a) (gamma_star (L.map (kinst_constr ks) hyps))) =
  let hyps' = L.map (kinst_constr ks) hyps in
  let h = gs_source hyps a in
  let h' = kinst_constr ks h in
  mem_map (kinst_constr ks) hyps h;
  canon_kinst_constr ks h;
  canon_cc_nonrow h;
  ckinst_consistent ks (canon_constr h);
  ckinst_atoms ks (canon_constr h) a;
  gs_intro hyps' h' (akinst ks a)

let derivable_kinst (ks: list kind) (hyps: list constr) (a: afact)
  : Lemma (requires derivable hyps a)
          (ensures derivable (L.map (kinst_constr ks) hyps) (akinst ks a)) =
  if L.mem a (gamma_star hyps) then gs_kinst ks hyps a else gs_kinst ks hyps (flip a)

let entails_kinst ks hyps c =
  let hyps' = L.map (kinst_constr ks) hyps in
  if inconsistent hyps then begin
    let h = inconsistent_wit hyps in
    canon_kinst_constr ks h;
    canon_cc_nonrow h;
    ckinst_consistent ks (canon_constr h);
    mem_map (kinst_constr ks) hyps h;
    inconsistent_intro hyps' (kinst_constr ks h)
  end else begin
    let cc = canon_constr c in
    canon_kinst_constr ks c;
    canon_cc_nonrow c;
    entails_elim hyps c;
    ckinst_consistent ks cc;
    let aux (b: afact)
      : Lemma (requires in_atoms (ckinst_constr ks cc) b) (ensures derivable hyps' b) =
      derivable_kinst ks hyps (kcover ks cc b)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    entails_intro hyps' (kinst_constr ks c)
  end

(* Weakening, consistency preservation, and cut. *)

let entails_weaken hyps hyps' c =
  if inconsistent hyps' then ()
  else begin
    if inconsistent hyps then inconsistent_intro hyps' (inconsistent_wit hyps);
    let aux (a: afact)
      : Lemma (requires L.mem a (gamma_star hyps)) (ensures L.mem a (gamma_star hyps')) =
      gs_intro hyps' (gs_source hyps a) a
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    entails_elim hyps c;
    entails_intro hyps' c
  end

let entails_consistent hyps c =
  entails_elim hyps c;
  FStar.Classical.forall_intro (mem_catoms (canon_constr c))

let entails_cut hyps c d =
  if inconsistent hyps then ()
  else begin
    entails_consistent hyps c;
    entails_elim (c :: hyps) d;
    entails_intro hyps d
  end

let rec cut_prefix (l hyps': list constr) (c: constr)
  : Lemma (requires (forall (h: constr). L.mem h l ==> entails hyps' h) /\
                    entails (L.append l hyps') c)
          (ensures entails hyps' c) (decreases l) =
  match l with
  | [] -> ()
  | h :: tl ->
    entails_weaken hyps' (L.append tl hyps') h;
    entails_cut (L.append tl hyps') h c;
    cut_prefix tl hyps' c

let entails_cut_all hyps hyps' c =
  entails_weaken hyps (L.append hyps hyps') c;
  cut_prefix hyps hyps' c
