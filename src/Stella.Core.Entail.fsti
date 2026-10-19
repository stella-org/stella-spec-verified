(**
 * Entailment of row constraints, `Γ ⊨ C` (design §2.2; spec 02 §Deciding
 * entailment).
 *
 * Entailment is decided against a list of hypotheses `hyps : list constr`.
 * The typing context passes its facts and its assumptions concatenated;
 * nothing here depends on the shape of a context.
 *
 * ## Decomposition
 *
 * A constraint is decomposed over the canonical forms of its rows into
 * *atomic facts*: `k ∉ t` and `t1 # t2`, where `t`, `t1`, `t2` are tails of
 * canonical forms (spec 02 §`Γ*`: decomposing assumptions into atomic
 * facts). In a well-kinded row every tail is a
 * `CVar`, so the atomic facts are those of the specification. Atoms over
 * arbitrary canonical tails, rather than over variable indices, keep
 * decomposition meaningful after any substitution, ill-kinded ones
 * included, so that entailment is preserved by every substitution.
 *
 * A constraint is *inconsistent* when its known part already violates it:
 * `k ∉ ρ` with `k ∈ knownKeys(ρ)`, or `ρ1 # ρ2` with a known key common to
 * both sides. Decomposition returns `None` exactly then.
 *
 * ## Entailment
 *
 *   - `Γ*` is the concatenation of the decompositions of the consistent
 *     hypotheses. Symmetry of `#` is its only closure (spec 02 §What
 *     entailment does not derive).
 *   - A list of hypotheses one of which is inconsistent entails every
 *     constraint (design §2.2 item 4).
 *   - Otherwise `C` is entailed when it is consistent and every atomic fact
 *     of its decomposition is derivable from `Γ*`. This is the procedure of
 *     spec 02 §Deciding entailment: the known-key condition is consistency of
 *     `C`, and the tail conditions are its atomic facts.
 *
 * Every definition reads the constraint through `canon_constr`, so
 * entailment depends only on constraints up to `constr_eq`.
 *)
module Stella.Core.Entail
open Stella.Core.Syntax
open Stella.Core.Rows
module L = FStar.List.Tot

(** * Atomic facts *)

(** An atomic fact (spec 02 §`Γ*`: decomposing assumptions into atomic
    facts). The name `atom` is taken by region atoms
    (`Stella.Core.Syntax.atom`). *)
type afact =
  | ALacks : key -> ctyp -> afact     (** k ∉ t *)
  | ADisj  : ctyp -> ctyp -> afact    (** t1 # t2 *)

(** `{ k ∉ t | t ∈ ts }` *)
let rec lacks_each (k: key) (ts: list ctyp) : Tot (list afact) (decreases ts) =
  match ts with
  | [] -> []
  | t :: ts -> ALacks k t :: lacks_each k ts

(** `{ k ∉ t | k ∈ ks, t ∈ ts }` *)
let rec lacks_all (ks: list key) (ts: list ctyp) : Tot (list afact) (decreases ks) =
  match ks with
  | [] -> []
  | k :: ks -> L.append (lacks_each k ts) (lacks_all ks ts)

(** `{ t1 # t2 | t2 ∈ ts }` *)
let rec disj_each (t1: ctyp) (ts: list ctyp) : Tot (list afact) (decreases ts) =
  match ts with
  | [] -> []
  | t2 :: ts -> ADisj t1 t2 :: disj_each t1 ts

(** `{ t1 # t2 | t1 ∈ ts1, t2 ∈ ts2 }` *)
let rec disj_all (ts1 ts2: list ctyp) : Tot (list afact) (decreases ts1) =
  match ts1 with
  | [] -> []
  | t1 :: ts1 -> L.append (disj_each t1 ts2) (disj_all ts1 ts2)

(** * Decomposition *)

(** No key of `ks1` is in `ks2`. Key lists may repeat a key (`ckeys`). *)
let rec disjoint_keys (ks1 ks2: list key) : Tot bool (decreases ks1) =
  match ks1 with
  | [] -> true
  | k :: ks1 -> not (L.mem k ks2) && disjoint_keys ks1 ks2

(** The known part of a canonical constraint does not violate it. *)
let cconsistent (cc: cconstr) : bool =
  match cc with
  | CCLacks k c -> not (L.mem k (ckeys c))
  | CCDisj c1 c2 -> disjoint_keys (ckeys c1) (ckeys c2)

(** The atomic facts of a canonical constraint, with `(F; T) = view_row c`:

      - `k ∉ c`: `k ∉ t` for `t ∈ T`;
      - `c1 # c2`: `k ∉ t` for `k ∈ dom(F1)`, `t ∈ T2`, and for
        `k ∈ dom(F2)`, `t ∈ T1`; and `t1 # t2` for `t1 ∈ T1`, `t2 ∈ T2`. *)
let catoms (cc: cconstr) : list afact =
  match cc with
  | CCLacks k c -> lacks_each k (row_tails c)
  | CCDisj c1 c2 ->
    L.append (lacks_all (ckeys c1) (row_tails c2))
      (L.append (lacks_all (ckeys c2) (row_tails c1)) (disj_all (row_tails c1) (row_tails c2)))

let cdecompose (cc: cconstr) : option (list afact) =
  if cconsistent cc then Some (catoms cc) else None

(** The decomposition of a constraint; `None` when it is inconsistent. *)
let decompose (c: constr) : option (list afact) = cdecompose (canon_constr c)

(** * Inconsistency and `Γ*` *)

(** Some hypothesis is inconsistent. *)
let rec inconsistent (hyps: list constr) : Tot bool (decreases hyps) =
  match hyps with
  | [] -> false
  | h :: hyps -> None? (decompose h) || inconsistent hyps

(** The atomic facts of the hypotheses. *)
let rec gamma_star (hyps: list constr) : Tot (list afact) (decreases hyps) =
  match hyps with
  | [] -> []
  | h :: hyps ->
    L.append (match decompose h with Some l -> l | None -> []) (gamma_star hyps)

(** An atomic fact follows from the facts `gs`: it is one of them, up to
    symmetry of `#`. *)
let derivable_in (gs: list afact) (a: afact) : bool =
  match a with
  | ALacks _ _ -> L.mem a gs
  | ADisj t1 t2 -> L.mem a gs || L.mem (ADisj t2 t1) gs

let derivable (hyps: list constr) (a: afact) : bool = derivable_in (gamma_star hyps) a

let rec all_derivable (gs: list afact) (l: list afact) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | a :: l -> derivable_in gs a && all_derivable gs l

(** * Entailment *)

(** `hyps ⊨ c` *)
let entails (hyps: list constr) (c: constr) : bool =
  inconsistent hyps ||
  (match decompose c with
   | None -> false
   | Some l -> all_derivable (gamma_star hyps) l)
