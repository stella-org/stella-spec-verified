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

(** Assuming several constraints at once; `add_assump g c` is
    `add_assumps g [c]`, and nested `add_assump`s are one `add_assumps`
    with the last constraint first. *)
let add_assumps (g: ctx) (cs: list constr) : ctx = { g with assumps = L.append cs g.assumps }

(** Binding a term variable. *)
let push_var (g: ctx) (t: typ) : ctx = { g with vars = t :: g.vars }

(** Binding a telescope of term variables, pushed in written order, so that
    the last one is index 0: the members of `letrec` and the parameters of a
    join point (design §3.1). *)
let rec push_vars (g: ctx) (ts: list typ) : Tot ctx (decreases ts) =
  match ts with
  | [] -> g
  | t :: ts -> push_vars (push_var g t) ts

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

(** The facts of entering the region `a` alone, its name being in scope
    already: the body of an open region frame `region⟨a⟩ θ in e`, whose name
    is one of `Γ_R` (spec 06 §Run-time forms). *)
let add_region_facts (g: ctx) (a: atom) : ctx =
  { g with facts = L.append (region_facts a 0 g.tvars) g.facts }

(** * Mapping the types stored in a context

    Each map applies one operation to every type the context stores: the
    facts, the assumptions, the layouts in `regions`, and the term
    variables. It keeps the region names, so it preserves the region domain
    `rdom`. `ren_ctx_types` and `sub_ctx_types` keep `nk` and `tvars`,
    which the caller sets; `kinst_ctx ks nk` also instantiates the kinds of
    `tvars`, and takes the new `nk` from the caller. *)

(** A substitution applied to the layout of a region. *)
let sub_region (sigma: tsub) (r: atom & layout) : atom & layout = (fst r, sub_layout sigma (snd r))

(** A kind instantiation applied to the layout of a region. *)
let kinst_region (ks: list kind) (r: atom & layout) : atom & layout =
  (fst r, kinst_layout ks (snd r))

let ren_ctx_types (xi: ren) (g: ctx) : ctx =
  { g with
    facts = L.map (ren_constr xi) g.facts;
    assumps = L.map (ren_constr xi) g.assumps;
    regions = L.map (ren_region xi) g.regions;
    vars = L.map (ren_ty xi) g.vars }

let sub_ctx_types (sigma: tsub) (g: ctx) : ctx =
  { g with
    facts = L.map (sub_constr sigma) g.facts;
    assumps = L.map (sub_constr sigma) g.assumps;
    regions = L.map (sub_region sigma) g.regions;
    vars = L.map (sub_ty sigma) g.vars }

let kinst_ctx (ks: list kind) (nk: nat) (g: ctx) : ctx =
  { nk = nk;
    tvars = kinst_kinds ks g.tvars;
    facts = L.map (kinst_constr ks) g.facts;
    assumps = L.map (kinst_constr ks) g.assumps;
    regions = L.map (kinst_region ks) g.regions;
    vars = L.map (kinst_ty ks) g.vars }

(** * The region domain

    Every map of the stored types, entering a type binder, and assuming a
    constraint keep the region domain; entering a region adds its atom. *)

val rdom_ren_ctx_types (xi: ren) (g: ctx) : Lemma (rdom (ren_ctx_types xi g) == rdom g)

val rdom_sub_ctx_types (sigma: tsub) (g: ctx) : Lemma (rdom (sub_ctx_types sigma g) == rdom g)

val rdom_kinst_ctx (ks: list kind) (nk: nat) (g: ctx) : Lemma (rdom (kinst_ctx ks nk g) == rdom g)

val rdom_push_tvar (g: ctx) (k: kind) : Lemma (rdom (push_tvar g k) == rdom g)

val rdom_add_assumps (g: ctx) (cs: list constr) : Lemma (rdom (add_assumps g cs) == rdom g)

val rdom_add_assump (g: ctx) (c: constr) : Lemma (rdom (add_assump g c) == rdom g)

val rdom_enter_region (g: ctx) (a: atom) (l: layout)
  : Lemma (rdom (enter_region g a l) == a :: rdom g)

(** * The hypotheses *)

val hyps_ren_ctx_types (xi: ren) (g: ctx)
  : Lemma (hyps (ren_ctx_types xi g) == L.map (ren_constr xi) (hyps g))

val hyps_sub_ctx_types (sigma: tsub) (g: ctx)
  : Lemma (hyps (sub_ctx_types sigma g) == L.map (sub_constr sigma) (hyps g))

val hyps_kinst_ctx (ks: list kind) (nk: nat) (g: ctx)
  : Lemma (hyps (kinst_ctx ks nk g) == L.map (kinst_constr ks) (hyps g))

(** The hypotheses under a type binder are the shifted ones. *)
val hyps_push_tvar (g: ctx) (k: kind)
  : Lemma (hyps (push_tvar g k) == L.map (ren_constr (shift 1)) (hyps g))

val mem_hyps_add_assumps (g: ctx) (cs: list constr) (h: constr)
  : Lemma (L.mem h (hyps (add_assumps g cs)) <==> L.mem h cs \/ L.mem h (hyps g))

(** * Relation to entering a binder and assuming a constraint *)

(** Entering a type binder is renaming the stored types by `↑1`. *)
val push_tvar_ren (g: ctx) (k: kind)
  : Lemma (push_tvar g k == { ren_ctx_types (shift 1) g with tvars = k :: g.tvars })

val add_assump_assumps (g: ctx) (c: constr) : Lemma (add_assump g c == add_assumps g [c])

val ren_ctx_types_push_tvar (xi: ren) (g: ctx) (k: kind)
  : Lemma (ren_ctx_types (up_ren xi) (push_tvar g k) == push_tvar (ren_ctx_types xi g) k)

val sub_ctx_types_push_tvar (sigma: tsub) (g: ctx) (k: kind)
  : Lemma (sub_ctx_types (up_tsub sigma) (push_tvar g k) == push_tvar (sub_ctx_types sigma g) k)

val kinst_ctx_push_tvar (ks: list kind) (nk: nat) (g: ctx) (k: kind)
  : Lemma (kinst_ctx ks nk (push_tvar g k) == push_tvar (kinst_ctx ks nk g) (kinst_kind ks k))

val ren_ctx_types_add_assumps (xi: ren) (g: ctx) (cs: list constr)
  : Lemma (ren_ctx_types xi (add_assumps g cs) ==
           add_assumps (ren_ctx_types xi g) (L.map (ren_constr xi) cs))

val sub_ctx_types_add_assumps (sigma: tsub) (g: ctx) (cs: list constr)
  : Lemma (sub_ctx_types sigma (add_assumps g cs) ==
           add_assumps (sub_ctx_types sigma g) (L.map (sub_constr sigma) cs))

val kinst_ctx_add_assumps (ks: list kind) (nk: nat) (g: ctx) (cs: list constr)
  : Lemma (kinst_ctx ks nk (add_assumps g cs) ==
           add_assumps (kinst_ctx ks nk g) (L.map (kinst_constr ks) cs))

(** Instantiating the variable a type binder pushed gives back the stored
    types of the outer context. *)
val sub1_push_tvar (s: typ) (g: ctx) (k: kind)
  : Lemma ({ sub_ctx_types (scons s tvar) (push_tvar g k) with tvars = g.tvars } == g)
