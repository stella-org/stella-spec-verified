# Representation of Binders, Types, and Contexts

This document fixes how the Typed Core of Stella is represented in F*. It covers three things:

1. How binders are encoded
2. How type equality is defined
3. How the typing contexts are structured

Every later definition and proof (kinding, typing, reduction, and the soundness theorems) builds on these choices.

"The specification" means the Typed Core chapters of the Stella language documentation,
`docs/technical-references/03-Typed-Core/` in [stella-lang](https://github.com/stella-org/stella-lang).
A reference such as `spec 04 §Join points` names a chapter file by its number (`04-Terms-and-Matching.md`) and a heading within it. The chapters are 01 Kinds and Types, 02 Rows, 03 Effects, 04 Terms and Matching, 05 Typing Rules, 06 Semantics, 07 Core Type Checker, and 10 Initialization Safety. Design decisions such as D3 are numbered in `docs/technical-references/01-Introduction/03-Design-Decisions.md`. Within this document, a bare section number such as §2.1 refers to this document.

## 1. Binders

The Core has several classes of bound names. Each class uses the encoding that suits how its names are introduced and replaced.

| Class | Encoding |
| --- | --- |
| term variable `x` | de Bruijn index |
| type variable `a` | de Bruijn index, in an index space separate from term variables |
| join point `j` | de Bruijn index, in an index space of its own |
| kind variable `k` | index into the kind scheme of the enclosing declaration |
| region name `ℓ` | locally nameless: a bound occurrence is an index, a free one is an atom |
| by-need location `ν` | atom |

Terms used above:

- A **de Bruijn index** names a variable by the number of binders of the same class between the occurrence and its binder. Index 0 is the nearest binder. α-equivalent terms are therefore syntactically equal.
- **Locally nameless** representation uses indices for bound occurrences and *atoms* (globally unique names, here natural numbers) for free ones. Going under a binder *opens* it, replacing the bound index with a fresh atom.
- A **telescope** is a sequence of binders introduced together, such as the members of a `letrec` or the type parameters of a handler clause.

### 1.1 Term variables, type variables, and join points

The specification identifies Core terms up to α-equivalence (spec 01 §Names and binding). Its unique-binder convention (`TypeBinderShadows`, `RegionBinderShadows`) is a condition on the named representation that the Core type checker receives, not a rule of the language. With de Bruijn indices, α-equivalence is syntactic equality, so the convention has no counterpart here.

Each index space is shifted and substituted independently. Renaming and substitution are *parallel*: a renaming is a function `nat -> nat` and a substitution is a function from indices to types or terms. Under a binder, both are *lifted*: index 0 maps to itself, and every other index is mapped and then shifted. Shifting and single-variable substitution are special cases. Weakening of a typing judgement follows from a single renaming lemma, and the substitution lemma is stated for parallel substitutions.

A renaming passes unchanged under a binder of another sort. A term substitution carries terms, which mention every sort, so under `m` type binders its substitutes have their type indices shifted by `m`, and under a join binder their join indices are shifted by one. Join points are renamed but never substituted.

### 1.2 Kind variables

Kind polymorphism is prenex and appears only on declarations (spec 01 §Kind schemes, design decision D3). Kinds contain no binders. Instantiating a scheme `forall k̄. κ` at `κ̄'` is therefore a simultaneous replacement of kind variables, with no shifting.

### 1.3 Region names

A `region [ℓ] … in e` term binds the region name `ℓ` in `e`, its type annotations included (spec 03 §Regions of cells). At run time, opening a region replaces `ℓ` with a globally fresh name (spec 06 §Regions), which is exactly the *open* operation of a locally nameless representation. So:

- Inside an unopened region body, `ℓ` is a bound index (`RBound`).
- After opening, it is an atom (`RFree`).
- Run-time region names are atoms recorded in the global region context `Γ_R` (§4.5).

Types bind no region names. The typing judgement opens a region body with an atom before checking it, so every type the judgement handles is *locally closed* for regions: it contains no dangling `RBound`. Substituting a locally closed type or term therefore needs no capture avoidance for region binders, which the specification otherwise requires (spec 05 §Basic rules).

The typing rule for `region` uses **cofinite quantification**: the body must typecheck when opened with every atom outside some finite set. In F*, this is a constructor field of function type `(l:atom{l ∉ L}) -> typing …`, which is strictly positive. With this rule, weakening needs no lemma about renaming atoms.

## 2. Type equality

Type equality is equality of canonical forms:

```
ty_eq τ1 τ2  ≜  canon τ1 = canon τ2
```

`canon` normalizes rows recursively, including inside payloads, and leaves every other type former unchanged. Because type equality is a computation rather than an inductive relation closed under transitivity, the inversion lemmas that progress and preservation need are immediate when both sides use the same type former. For example, `Function τ1 ρ τ2 ≡ Function τ1' ρ' τ2'` implies that the components are equal. A row union can canonicalize to a non-row form (`a ⊎ ()` is `a`), so comparing against an arbitrary type goes through `canon`.

Kinding, entailment (`Γ ⊨ C`), and type equality are deterministic and syntax-directed, so all three are total functions. Only term typing is an inductive relation, because it has a conversion rule and has to cover the run-time forms.

### 2.1 Canonical form of rows

The canonical form of a row is a pair:

- a **set of entries**, each a pair of a key and the canonical form of its payload; and
- a **set of tails**, the canonical forms of the types that make up the unknown remainder.

In a well-kinded row every tail is a row variable. Canonicalization does not consult kinds, so a non-row type in a row position is also a tail (an *opaque tail*). Sets are sorted, duplicate-free lists under a total order on canonical forms, so equal sets are equal lists (`Stella.Core.OrdSet`).

The rows are built as follows:

- `()` has no entries and no tails.
- A row with no entries and exactly one tail is that tail. So `canon a = canon (a ⊎ ())`, and a row variable has the same canonical form wherever it stands.
- Union of rows is set union on both components, followed by normalization.

Several things follow from this definition:

- `canon` is total. Entries that agree on both key and payload collapse into one, and entries with the same key but different payloads remain distinct.
- Union is idempotent, commutative, and associative up to `ty_eq`: `r ⊎ r` and `r` have the same canonical form.
- `knownKeys(ρ)` is the key projection of the entries of `canon ρ`. A key that occurs with several payloads occurs several times.
- Canonicalization commutes with renaming, substitution, and the region operations of §1.3. `canon (τ[σ])` is determined by `canon τ` and `σ`:
  - each tail `t` is replaced by `canon (σ t)`, read as a row;
  - payloads are substituted as well;
  - the result is normalized again, because entries and tails can merge.

  Type equality is therefore preserved by every renaming and substitution, and by opening and closing regions, with no kinding hypothesis.
- On *sharp* rows (rows in which no key occurs twice, spec 02 §Sharpness), the entry set is the graph of a finite map, so this canonical form coincides with the specification's `nf`.

Ruling out repeated keys is the job of kinding, not of type equality.

### 2.2 Constraints and entailment

Core has two row constraints: Lacks, `k ∉ ρ`, and Disjoint, `ρ1 # ρ2` (spec 02 §Constraints). The rules are as follows.

1. **Forming a constraint.** A constrained type `C => τ` and a constraint abstraction `Λ(_ : C). v` require only that `C` is well formed (`Γ ⊢ C ok`, a kinding condition). They do not require `C` to be satisfiable.
2. **Discharging a constraint.** A constraint application `e [•]` requires `Γ ⊨ C`. This is the only place where the logical content of a constraint is checked.
3. **Two kinds of context entry.** A context records *facts* separately from *assumptions* (§4.2).
   - A fact is a constraint `RegionKey ℓ ∉ t` that entering a region adds (spec 02 §Deciding entailment). It holds for every instantiation, because a well-scoped substitution cannot carry `RegionKey ℓ` out of the scope of `ℓ`.
   - An assumption is a constraint introduced by `Λ(_ : C)`. Assumptions may contradict one another.
4. **Inconsistent contexts entail everything.** A context is *inconsistent* when its assumptions cannot all hold. Entailment in such a context is trivial:

   ```text
   inconsistent Γ
   ──────────────
       Γ ⊨ C
   ```

   This principle applies to entailment and to nothing else. Kinding and typing keep all their structural checks in an inconsistent context. An unbound index, an ill-kinded application such as `Int Int`, and an application at a mismatched kind are still rejected. Only the entailment premises of the kinding and typing rules, such as the sharpness side conditions of row extension and union, become trivially true.
5. **Deciding inconsistency.** Every constraint is negative (it forbids keys). So the assignment that sends every row variable to `()` satisfies any assumption whose known part is consistent, and it satisfies all such assumptions at once. Inconsistency is therefore decided one assumption at a time:

   ```text
   inconsistent(k ∉ ρ)    iff  k ∈ knownKeys(ρ)
   inconsistent(ρ1 # ρ2)  iff  knownKeys(ρ1) ∩ knownKeys(ρ2) ≠ ∅
   ```

   This characterization is a lemma about the present constraint language. A positive constraint, such as one requiring a key to be present or a row to be non-empty, would invalidate it.

Entailment is decided over a list of hypotheses, the context's facts followed by its assumptions (`Stella.Core.Entail`). An *atomic fact* is `k ∉ t` or `t1 # t2`, where `t`, `t1`, and `t2` are canonical tails (§2.1). Each hypothesis decomposes into atomic facts, and decomposing an inconsistent hypothesis fails. A constraint is entailed when its own decomposition succeeds and every atomic fact in it is among the hypotheses' facts, `#` being read symmetrically. Because atomic facts range over canonical tails rather than variables, substitution maps the facts of a hypothesis to the facts of its image.

The syntactic renaming and substitution operations know nothing about consistency. The lemmas connecting them to entailment and typing are:

1. canonicalization commutes with substitution (§2.1);
2. the inconsistency characterization above is sound and complete. Soundness: an inconsistent hypothesis is not entailed by the empty context under any substitution, because substitution never removes a known key. Completeness: a consistent hypothesis whose tails are all variables is entailed by the empty context once every variable is replaced with `()`;
3. entailment is preserved by every renaming and substitution: `Γ ⊨ C` implies `Γ[σ] ⊨ C[σ]`, with no condition on `σ`;
4. cut for entailment;
5. cut for kinding and typing: `Γ ⊨ C` and `Γ, C ⊢ J` imply `Γ ⊢ J`;
6. if `Γ` is consistent and `Γ ⊨ C`, then `Γ, C` is consistent, and each atomic fact it adds already follows from `Γ`;
7. entailment is preserved by adding hypotheses (weakening);
8. entailment is preserved by a region map that is injective on the keys of the entailed constraint. In particular, it is preserved by opening a region with an atom that does not occur in the entailed constraint, whatever the hypotheses are. Without that condition the lemma fails, because a region map can merge two keys: opening `RegionKey (RBound 0) ∉ ( RegionKey (RFree a) | r )` with `a` gives an inconsistent constraint.

The substitution lemma of the typing relation does need a kind-correct, well-scoped substitution that is locally closed for regions. Entailment alone needs none of these.

Together these give preservation for `(Λ(_ : C). v) [•] → v`, and type application needs no side condition. Progress is unaffected: evaluation runs on closed terms, whose empty context is consistent, and enters the body of a `Λ(_ : C)` only after the matching `[•]`.

## 3. Syntax

The abstract syntax is defined in `src/Stella.Core.Syntax.fsti`. Its type-level core is:

```fstar
type kind = KVar of nat | KType | KEffect | KRow of elt_kind | KArrow of kind & kind
and elt_kind = EType | EEffect

type region_ref = RBound of nat | RFree of atom
type key =
  | SymbolKey of string | TagKey of string | PositionKey of nat
  | EffectKey of qname  | RegionKey of region_ref

type typ =
  | TVar of nat | TCon of qname & list kind | TApp of typ & typ
  | TForall of kind & typ | TConstr of constr & typ
  | TRowEmpty | TRowExt of entry & typ | TRowUnion of typ & typ
and entry =
  | EntTy  of key & typ                          // k : τ
  | EntEff of option string & qname & list typ   // E τ̄, or s : E τ̄ when labelled
  | EntRegion of region_ref                      // region ℓ
and constr = CLacks of key & typ | CDisj of typ & typ
```

Expressions, decision trees, occurrences, handlers, and clauses are mutually inductive. The binding forms are:

| Form | Binds |
| --- | --- |
| `ELam`, `ELet` | one term variable |
| `ELetRec` | its members, as a telescope of term variables |
| `ELetJoin` | its parameters as term variables in the join body, and one join point in both the join body and the continuation |
| `DBind` | one term variable |
| a `full` clause | the clause's type binders, then `x` and `k` |
| a `fast` clause | the clause's type binders, then `x` |
| a return clause | one term variable |
| `ETyLam`, `TForall` | one type variable |
| `ERegion` | one region index |

The run-time forms of spec 06 §Run-time forms belong to the same type of expressions:

- `ESpine` is a global applied to an argument spine, `M.g ς`, which only reduction produces.
- `EMatch` descends a decision tree.
- `EOpenEffC` widens the ambient effect row of a computation.
- `EForce` and `EFill` operate on by-need locations.
- `ERegionOpen` is an open region frame, `region⟨ℓ⟩ θ in e`.
- `EOpaque` is an opaque value returned by a foreign implementation.

The predicate `is_source` excludes these forms.

`fail` is derived notation (spec 03 §Partiality) and is a function rather than a constructor. Its expansion names the effect `Partial` and the constructor `Prim.Unit`, which are passed to it as parameters, and the result type `τ`.

Evaluation contexts are defunctionalized: an evaluation context is a list of frames, and `Ev_k` and `Ev_ℓ` (spec 06 §Evaluation contexts) are predicates on such lists.

### 3.1 Index conventions

- The last binder of a telescope is index 0. This matches the contexts of §4.2, whose heads are index 0. A specification-level substitution `τ[ā := τ̄]` replaces index `i` with the `i`-th element of `τ̄` counted from the end, that is, `sub_ty (list_tsub (rev τ̄))`.
- The annotations of a handler clause, `x : σ` and `k : τ' -{ρ}-> β`, are under the clause's type binders.
- `KVar i` refers to the binders of a kind scheme in the order they are written.
- In an operation signature `forall (b̄ : κ̄'). σ ->* τ` of an effect `E (ā : κ̄)`, the operation's own binders `b̄` are inner and the effect's parameters `ā` are outer.
- `EMatch` holds the values of the scrutinees. The value at an occurrence is computed by following the occurrence's projection path from its scrutinee.
- Every substitute in a type or term substitution is locally closed for regions (§1.3). `lc_ty` and `lc_exp` in `Stella.Core.Region` express this.

## 4. Contexts

### 4.1 The global signature Σ

`Σ` is a parameter of every judgement and never changes during checking (spec 05 §Contexts). It is a record of lookup functions keyed by qualified names (`Stella.Core.Sig`):

- **`tycons`**: the number of kind variables of the scheme, the kind, and the class. The class is either intrinsic, with a canonical-value class (literal, function, record, variant, or opaque), or data, with the constructor names;
- **`ctors`**: the owning type, tag, arity, number of kind variables, and type;
- **`effects`**: the kinds of the parameters, and for each operation its signature `forall b̄. σ ->* τ` (index order as in §3.1);
- **`foreigns`**: the number of kind variables, the type, and whether the declaration asserts `#observ(none)`;
- **`values`**: the number of kind variables and the type.

The judgements assume a well-formed `Σ` (`Stella.Core.Sig.Wf`). Its kinding conditions are:

- a type constructor's kind is a well-formed quantifiable kind that produces `Type`;
- an effect's parameters are quantifiable;
- every declared type is kinded at `Type` under its kind variables.

### 4.2 The local context Γ

The specification's `Γ` is a single ordered sequence that mixes kind variables, type variables, term variables, constraints, and regions. With a separate index space per class, a record of separate components carries the same information (`Stella.Core.Context`):

```fstar
type ctx = {
  nk      : nat;                    // number of kind variables in scope
  tvars   : list kind;              // type variables; the head is index 0
  facts   : list constr;            // RegionKey ℓ ∉ t facts added by region binders
  assumps : list constr;            // constraints assumed by Λ(_ : C)
  regions : list (atom & layout);   // every region in scope, with its cell layout
  vars    : list typ;               // term variables; the head is index 0
}
```

`facts`, `assumps`, the layouts in `regions`, and the types in `vars` are written over the indices of `tvars`. The hypotheses of entailment are `facts` followed by `assumps`.

- **Entering a type binder** (`ETyLam`, `TForall`, the type binders of a clause) pushes onto `tvars` and shifts every type stored in the context. A constraint about an outer variable never applies to the new one, because it refers to a different index.
- **Entering a region** adds the region with its layout, and adds the fact `RegionKey ℓ ∉ t` for every `t` in `tvars` of kind `Row Effect`. Row variables bound later, inside the region, get no such fact (spec 02 §Deciding entailment).
- **`regions` holds every region name in scope**, including the run-time names that opening a region allocates (§4.5). This is how the specification's `Γ_R`, which stands in front of every `Γ`, is represented.
- **Well-formedness** of a context checks only structure. Every kind in `tvars` is a well-formed quantifiable kind, every fact and assumption is a well-formed constraint, and the indices are in scope. Whether the assumptions are consistent is a separate, computable predicate, `inconsistent` (§2.2).

### 4.3 The join-point context Δ

`Δ` is a list of triples: the parameter types, the result type, and the ambient effect row of a join point. It is empty in the following places (spec 04 §Join points):

- the bodies of `λ`, `Λ`, and constraint `Λ`;
- the handled computation, the return clause, and every operation clause of `handle`;
- the body of `region` and of an open frame `region⟨ℓ⟩`;
- the initializers of `letrec`, and the subterm of `fill`.

So `Δ` is never carried under a type binder, and its types never need shifting.

The syntactic predicate `jp_scoped n e` (`Stella.Core.Value`) holds when every `jump` in `e` targets a join point in scope, where `n` is the size of `Δ` at the root and `Δ` is emptied at the places above. Every well-typed term satisfies it. A `jp_scoped` value has no free join index, so the reduction `letjoin j … in v → v` returns `v` unchanged.

### 4.4 The occurrence context Ω

`Ω` maps occurrences to types and exists only while a decision tree is checked. An occurrence is a scrutinee index followed by a path of projections (spec 04 §Occurrences).

### 4.5 Run-time contexts and the store

Run-time terms involve two global contexts besides `Σ` (spec 06 §Run-time forms):

- `Γ_R` maps region atoms to cell layouts. Opening a region extends it.
- `Γ_N` maps by-need locations to types. `letrec` extends it.

`Γ_R` is the `regions` component of the context in which a closed run-time term is typed, so extending `Γ_R` is an instance of weakening the context (§4.2). `Γ_N` is a separate parameter of the term typing judgement:

```
typing : sig -> lctx -> ctx -> jctx -> exp -> typ -> (row:typ) -> Type
```

When the typing rule opens a region statically, it uses an atom that does not occur in `ctx.regions`. Store typing `⊢ N : Γ_N` is as in spec 06 §Run-time forms.

## 5. Relation to the specification

This formalization differs from the specification, or fills gaps in it, at the points below.

| Point in the specification | Treatment here |
| --- | --- |
| `nf` takes `F` to be a finite map from keys to payloads (spec 02 §Normal form), so it is undefined on rows that repeat a key. Type equality based on it is therefore not preserved by substitution: `r ⊎ r ≡ r` holds, but substituting `( x : Int )` for `r` gives a left-hand side with no normal form. | The canonical form of §2.1. It coincides with `nf` on sharp rows and is total. |
| Forming `Γ, C` requires `C` to be satisfiable (spec 05 §Contexts), while type application `e [σ]` checks only `Γ ⊢ σ : κ`. So instantiation can create an unsatisfiable `Λ(_ : C)` inside a value. For example, instantiating `Λ (r : Row Type). λ (u : Unit) / (). let y = Λ (_ : name ∉ r). … in u` at `( name : Int )` gives a term that has no type, which contradicts preservation. | §2.2: constraint abstractions require only well-formedness, and inconsistent contexts entail everything. |
| The run-time form `match θ dt` has no typing rule (spec 06 §Run-time forms). | A typing rule requires the values in `θ` to agree with the occurrence context. |
| The erased reduction relation `→ᵤ` used by the erasure property is not defined (spec 06 §Erasure). | It is defined before the erasure property is stated. |
| The decision-tree form `fail` stands for `leaf (perform Partial.abort [τ] Prim.Unit)`, but the tree grammar does not write `τ` (spec 04 §Decision trees). | The result type is an explicit argument of `fail` (§3). |
| A spine `M.g ς` is not listed among the run-time forms (spec 06 §Run-time forms), although only reduction produces one. | `ESpine` is a run-time form (§3). |
