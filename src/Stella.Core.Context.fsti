(**
 * The local context `Γ` (design §4.2; spec 05 §Contexts).
 *
 * The specification's `Γ` is one ordered sequence of kind variables, type
 * variables, term variables, constraints, and regions. With one index
 * space per sort of binder, a record of separate components carries the
 * same information. Constraints are split into *facts*, which entering a
 * region adds and which hold under every well-scoped instantiation, and
 * *assumptions*, which `C => τ` and `Λ(_ : C)` add and which may contradict
 * one another (design §2.2).
 *
 * `regions` holds every region name in scope, run-time ones included: the
 * run-time region context `Γ_R` stands implicitly at the start of every
 * `Γ`, so a closed term is typed in a context whose `regions` is `Γ_R`,
 * and extending `Γ_R` is a weakening in `regions`. A region that a typing
 * rule opens statically is fresh when its atom is not in `regions`.
 *)
module Stella.Core.Context
open Stella.Core.Syntax
open Stella.Core.Subst
module L = FStar.List.Tot

(** The layout `( k1 : σ1, …, kn : σn )` of a region: its cells' keys and
    types. A layout is kinded under the context the region stands in
    (spec 05 §Regions). *)
type layout = list (key & typ)

(** `facts`, `assumps`, the layouts in `regions`, and `vars` are written
    over the indices of `tvars`. *)
type ctx = {
  nk      : nat;                    (** the kind variables in scope *)
  tvars   : list kind;              (** type variables; the head is index 0 *)
  facts   : list constr;            (** `RegionKey ℓ ∉ t`, added by region binders *)
  assumps : list constr;            (** constraints assumed by `C => τ` and `Λ(_ : C)` *)
  regions : list (atom & layout);   (** the region names in scope, with their layouts *)
  vars    : list typ;               (** term variables; the head is index 0 *)
}

(** The hypotheses entailment reads: the facts, then the assumptions. *)
let hyps (g: ctx) : list constr = L.append g.facts g.assumps

(** The region names in scope. *)
let rdom (g: ctx) : list atom = L.map fst g.regions

(** The context of a declaration of `Σ` with `n` kind variables: nothing
    else is in scope. *)
let decl_ctx (n: nat) : ctx =
  { nk = n; tvars = []; facts = []; assumps = []; regions = []; vars = [] }

(** * Extending a context *)

(** A renaming applied to the layout of a region. *)
let ren_region (xi: ren) (r: atom & layout) : atom & layout = (fst r, ren_layout xi (snd r))

(** Entering a type binder of kind `k`. Every type already in the context
    is shifted past the new variable, so a constraint about an outer
    variable never applies to the new one. *)
let push_tvar (g: ctx) (k: kind) : ctx =
  { g with
    tvars = k :: g.tvars;
    facts = L.map (ren_constr (shift 1)) g.facts;
    assumps = L.map (ren_constr (shift 1)) g.assumps;
    regions = L.map (ren_region (shift 1)) g.regions;
    vars = L.map (ren_ty (shift 1)) g.vars }

(** Entering a telescope of type binders, pushed in written order, so that
    the last one is index 0. *)
let rec push_tvars (g: ctx) (ks: list kind) : Tot ctx (decreases ks) =
  match ks with
  | [] -> g
  | k :: ks -> push_tvars (push_tvar g k) ks

(** Assuming a constraint. Satisfiability is not required (design §2.2). *)
let add_assump (g: ctx) (c: constr) : ctx = { g with assumps = c :: g.assumps }

(** Binding a term variable. *)
let push_var (g: ctx) (t: typ) : ctx = { g with vars = t :: g.vars }

(** `RegionKey (RFree a) ∉ TVar (d + j)` for every position `j` of `ks` that
    holds `Row Effect`. *)
let rec region_facts (a: atom) (d: nat) (ks: list kind) : Tot (list constr) (decreases ks) =
  match ks with
  | [] -> []
  | k :: ks ->
    if k = KRow EEffect then CLacks (RegionKey (RFree a)) (TVar d) :: region_facts a (d + 1) ks
    else region_facts a (d + 1) ks

(** Entering the body of a region opened with the atom `a` and the layout
    `l`. Every `Row Effect` variable in scope lacks `RegionKey a`, since
    whatever instantiates it is formed where `a` is not in scope; a
    variable bound later gets no such fact (spec 02 §Deciding entailment,
    spec 05 §Regions). *)
let enter_region (g: ctx) (a: atom) (l: layout) : ctx =
  { g with
    facts = L.append (region_facts a 0 g.tvars) g.facts;
    regions = (a, l) :: g.regions }
