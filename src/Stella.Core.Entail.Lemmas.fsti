(**
 * Facts about entailment (design §2.2). "Lemma N" refers to the numbered
 * list of lemmas of design §2.2.
 *
 *   - Membership: the atomic facts of a constraint and of `Γ*`, and
 *     inconsistency, read as membership conditions.
 *   - Entailment depends on constraints only up to `constr_eq`.
 *   - Inconsistency is characterized syntactically (lemma 2):
 *     an inconsistent hypothesis stays violated under every substitution,
 *     and a consistent list of hypotheses over row variables is satisfied
 *     at once by sending every row variable to `()`.
 *   - Entailment is preserved by every substitution and renaming, with no
 *     kinding hypothesis (lemma 3), by every kind instantiation, and by a
 *     region map that keeps the keys of the entailed constraint apart, in
 *     particular opening a region with a fresh atom.
 *   - Weakening, consistency preservation (lemma 6), cut (lemma 4), and cut
 *     of a list of entailed hypotheses.
 *)
module Stella.Core.Entail.Lemmas
open Stella.Core.Syntax
open Stella.Core.Subst
open Stella.Core.Subst.Lemmas.Typ
open Stella.Core.Region
open Stella.Core.Rows
open Stella.Core.Entail
module L = FStar.List.Tot

(** * Membership *)

(** The atomic facts of a canonical constraint, as a predicate. *)
let in_atoms (cc: cconstr) (a: afact) : bool =
  match cc, a with
  | CCLacks k c, ALacks k' t -> k' = k && L.mem t (row_tails c)
  | CCDisj c1 c2, ALacks k t ->
    (L.mem k (ckeys c1) && L.mem t (row_tails c2)) ||
    (L.mem k (ckeys c2) && L.mem t (row_tails c1))
  | CCDisj c1 c2, ADisj t1 t2 -> L.mem t1 (row_tails c1) && L.mem t2 (row_tails c2)
  | _ -> false

val mem_catoms (cc: cconstr) (a: afact) : Lemma (L.mem a (catoms cc) = in_atoms cc a)

val disjoint_keys_mem (ks1 ks2: list key)
  : Lemma (disjoint_keys ks1 ks2 <==> (forall (k: key). L.mem k ks1 ==> not (L.mem k ks2)))

val inconsistent_mem (hyps: list constr)
  : Lemma (inconsistent hyps <==> (exists (h: constr). L.mem h hyps /\ None? (decompose h)))

val mem_gamma_star (hyps: list constr) (a: afact)
  : Lemma (L.mem a (gamma_star hyps) <==>
           (exists (h: constr). L.mem h hyps /\ Some? (decompose h) /\
                           L.mem a (Some?.v (decompose h))))

val all_derivable_mem (gs l: list afact)
  : Lemma (all_derivable gs l <==> (forall (a: afact). L.mem a l ==> derivable_in gs a))

(** A hypothesis is entailed. *)
val entails_hyp (hyps: list constr) (c: constr)
  : Lemma (requires L.mem c hyps) (ensures entails hyps c)

(** * Type equality *)

val entails_constr_eq (hyps: list constr) (c c': constr)
  : Lemma (requires constr_eq c c') (ensures entails hyps c = entails hyps c')

(** Pointwise `constr_eq`. *)
let rec constrs_eq (hs hs': list constr) : Tot bool (decreases hs) =
  match hs, hs' with
  | [], [] -> true
  | h :: hs, h' :: hs' -> constr_eq h h' && constrs_eq hs hs'
  | _ -> false

val entails_constrs_eq (hs hs': list constr) (c: constr)
  : Lemma (requires constrs_eq hs hs') (ensures entails hs c = entails hs' c)

(** * Known keys under substitution

    The keys of entries contain no type variables, so a substitution keeps
    every known key; it may add more, through the substitutes of the
    tails. *)

val known_keys_sub (sigma: tsub) (k: key) (t: typ)
  : Lemma (requires L.mem k (known_keys t)) (ensures L.mem k (known_keys (sub_ty sigma t)))

val decompose_sub_none (sigma: tsub) (c: constr)
  : Lemma (requires None? (decompose c)) (ensures None? (decompose (sub_constr sigma c)))

val inconsistent_sub (sigma: tsub) (hyps: list constr)
  : Lemma (requires inconsistent hyps) (ensures inconsistent (L.map (sub_constr sigma) hyps))

(** * The inconsistency characterization (lemma 2; design §2.2 item 5)

    Both directions rest on every constraint being negative: it forbids
    keys and never requires one. A substitution only adds known keys, so an
    inconsistent hypothesis is violated by every instance (soundness), and
    `()` has no keys, so sending every row variable to `()` satisfies every
    consistent hypothesis (completeness). A positive constraint, one
    requiring a key to be present or a row to be non-empty, would break
    completeness: no single instance would satisfy all consistent
    hypotheses, and inconsistency could not be decided one hypothesis at a
    time. *)

(** Soundness: some hypothesis is violated by every instance. *)
val inconsistent_sound (hyps: list constr) (sigma: tsub)
  : Lemma (requires inconsistent hyps)
          (ensures exists (h: constr). L.mem h hyps /\ not (entails [] (sub_constr sigma h)))

(** Every member of `ts` is a type variable. *)
let rec var_tails (ts: list ctyp) : Tot bool (decreases ts) =
  match ts with
  | [] -> true
  | t :: ts -> CVar? t && var_tails ts

(** Every tail of the rows of `c` is a type variable. A well-kinded
    constraint satisfies this. *)
let var_tailed (c: constr) : bool =
  match canon_constr c with
  | CCLacks _ r -> var_tails (row_tails r)
  | CCDisj r1 r2 -> var_tails (row_tails r1) && var_tails (row_tails r2)

let rec var_tailed_all (hyps: list constr) : Tot bool (decreases hyps) =
  match hyps with
  | [] -> true
  | h :: hyps -> var_tailed h && var_tailed_all hyps

(** `σ∅`, sending every type variable to `()`. *)
let empty_rows (_: nat) : typ = TRowEmpty

(** Completeness, one constraint at a time. *)
val consistent_complete (c: constr)
  : Lemma (requires Some? (decompose c) /\ var_tailed c)
          (ensures entails [] (sub_constr empty_rows c))

(** Completeness: `σ∅` satisfies every consistent list of hypotheses over
    row variables. *)
val inconsistent_complete (hyps: list constr)
  : Lemma (requires not (inconsistent hyps) /\ var_tailed_all hyps)
          (ensures forall (h: constr). L.mem h hyps ==> entails [] (sub_constr empty_rows h))

(** * Preservation under substitution (lemma 3) *)

val entails_sub (sigma: tsub) (hyps: list constr) (c: constr)
  : Lemma (requires entails hyps c)
          (ensures entails (L.map (sub_constr sigma) hyps) (sub_constr sigma c))

val entails_ren (xi: ren) (hyps: list constr) (c: constr)
  : Lemma (requires entails hyps c)
          (ensures entails (L.map (ren_constr xi) hyps) (ren_constr xi c))

(** * Preservation under region maps

    A region map can merge keys: opening a region with an atom that already
    occurs turns `RegionKey (RBound 0) ∉ ( region (RFree a) | r )`
    into an inconsistent constraint. Entailment is preserved when the map
    is injective on the keys of the entailed constraint; the hypotheses are
    unrestricted. *)

(** The keys of a canonical constraint: the key of a Lacks constraint and
    the known keys of its rows. *)
let cc_keys (cc: cconstr) : list key =
  match cc with
  | CCLacks k c -> k :: ckeys c
  | CCDisj c1 c2 -> L.append (ckeys c1) (ckeys c2)

let rmap_injective_on (f: region_ref -> region_ref) (ks: list key) : prop =
  forall (k1 k2: key). L.mem k1 ks /\ L.mem k2 ks /\ rmap_key f k1 == rmap_key f k2 ==> k1 == k2

val entails_rmap (f: region_ref -> region_ref) (hyps: list constr) (c: constr)
  : Lemma (requires rmap_injective_on f (cc_keys (canon_constr c)) /\ entails hyps c)
          (ensures entails (L.map (rmap_constr f) hyps) (rmap_constr f c))

(** Opening a region with an atom that does not occur in the entailed
    constraint. *)
val entails_open_region (d: nat) (a: atom) (hyps: list constr) (c: constr)
  : Lemma (requires not (L.mem a (frn_constr c)) /\ entails hyps c)
          (ensures entails (L.map (rmap_constr (open_rr a d)) hyps) (rmap_constr (open_rr a d) c))

(** * Preservation under kind instantiation

    Kind instantiation keeps every key and maps each tail to one tail; tails
    may merge, as under substitution. *)

val entails_kinst (ks: list kind) (hyps: list constr) (c: constr)
  : Lemma (requires entails hyps c)
          (ensures entails (L.map (kinst_constr ks) hyps) (kinst_constr ks c))

(** * Weakening, consistency preservation, and cut *)

(** Weakening: more hypotheses entail more. *)
val entails_weaken (hyps hyps': list constr) (c: constr)
  : Lemma (requires entails hyps c /\ (forall (h: constr). L.mem h hyps ==> L.mem h hyps'))
          (ensures entails hyps' c)

(** Consistency preservation (lemma 6): adding an entailed
    constraint to consistent hypotheses keeps them consistent, and every
    atomic fact it adds is already derivable. *)
val entails_consistent (hyps: list constr) (c: constr)
  : Lemma (requires not (inconsistent hyps) /\ entails hyps c)
          (ensures not (inconsistent (c :: hyps)) /\ Some? (decompose c) /\
                   (forall (a: afact). L.mem a (Some?.v (decompose c)) ==> derivable hyps a) /\
                   (forall (a: afact). derivable (c :: hyps) a <==> derivable hyps a))

(** Cut (lemma 4). *)
val entails_cut (hyps: list constr) (c d: constr)
  : Lemma (requires entails hyps c /\ entails (c :: hyps) d) (ensures entails hyps d)

(** Cut of a list: hypotheses that are each entailed by `hyps'` can be
    replaced by `hyps'`. *)
val entails_cut_all (hyps hyps': list constr) (c: constr)
  : Lemma (requires (forall (h: constr). L.mem h hyps ==> entails hyps' h) /\ entails hyps c)
          (ensures entails hyps' c)
