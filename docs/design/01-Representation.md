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

Each index space is shifted and substituted independently. Renaming and substitution are *parallel*: a renaming is a function `nat -> nat` and a substitution is a function from indices to types or terms. Under a binder, both are *lifted*: index 0 maps to itself, and every other index is mapped and then shifted. Shifting and single-variable substitution are special cases. Weakening of a typing judgement follows from the renaming lemma of its index sort (`Stella.Core.Typing.Rename.Ty`, `.Tm`, and `Stella.Core.Typing.Join` for join points), and the substitution lemma is stated for parallel substitutions. Extending `Γ_N`, which is a parameter of the judgement rather than part of a context, has a lemma of its own (§4.5).

A renaming passes unchanged under a binder of another sort. A term substitution carries terms, which mention every sort, so under `m` type binders its substitutes have their type indices shifted by `m`, and under a join binder their join indices are shifted by one. Join points are renamed but never substituted.

### 1.2 Kind variables

Kind polymorphism is prenex and appears only on declarations (spec 01 §Kind schemes, design decision D3). Kinds contain no binders. Instantiating a scheme `forall k̄. κ` at `κ̄'` is therefore a simultaneous replacement of kind variables, with no shifting.

### 1.3 Region names

A `region [ℓ] … in e` term binds the region name `ℓ` in `e`, its type annotations included (spec 03 §Regions of cells). At run time, opening a region replaces `ℓ` with a globally fresh name (spec 06 §Regions), which is exactly the *open* operation of a locally nameless representation. So:

- Inside an unopened region body, `ℓ` is a bound index (`RBound`).
- After opening, it is an atom (`RFree`).
- Run-time region names are atoms recorded in the global region context `Γ_R` (§4.5).

Types bind no region names. The typing judgement opens a region body with an atom before checking it, so every type the judgement handles is *locally closed* for regions: it contains no dangling `RBound`. Substituting a locally closed type or term therefore needs no capture avoidance for region binders, which the specification otherwise requires (spec 05 §Basic rules).

The typing rule for `region` uses **cofinite quantification**: the body must typecheck when opened with every atom `a` that is neither a region name in scope nor a free region name of the body. In F*, this is a constructor field of function type `(a:atom{a ∉ rdom g ∧ a ∉ frn_exp body}) -> typing …`, which is strictly positive. The excluded set is determined by the context and the term, not stored in the derivation. Weakening, renaming, and substitution only enlarge it, and the atom that reduction allocates lies outside it, so no lemma about swapping atoms is needed.

The layout's keys are distinct by an explicit premise, because the sharpness of a row is entailed vacuously in an inconsistent context. The rule also kinds the answer type `β` and the residual row `ρ` in the context outside the region. A type kinded there is locally closed and mentions only region names in scope (`check_lc`, `check_fresh` in `Stella.Core.Kinding.Facts`), so neither `β` nor `ρ` mentions the atom the body is opened with. This is the specification's escape condition `ℓ ∉ frn(β) ∪ frn(ρ)`.

## 2. Type equality, constraints, and kinding

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

The substitution lemmas of kinding and typing do need a kind-correct, well-scoped substitution, the `sub_ok` condition of §2.3, and the typing lemma also needs it to be locally closed for regions. Entailment alone needs none of these.

Together these give preservation for `(Λ(_ : C). v) [•] → v`, and type application needs no side condition. Progress is unaffected: evaluation runs on closed terms, whose empty context is consistent, and enters the body of a `Λ(_ : C)` only after the matching `[•]`.

### 2.3 Kinding

Kinding is a pair of total, mutually recursive functions (`Stella.Core.Kinding`):

- `synth_kind` synthesizes the kind of a variable, a constructor, an application, a `forall`, or a constrained type;
- `check` checks a type against a given kind.

The row formers are only checked, because `()` has kind `Row Type` and `Row Effect` alike, so its kind cannot be synthesized. A type kinded `Row ε` is therefore row syntax or a row variable, never a constructor application, provided that every type constructor's kind and every type variable's kind is quantifiable (§4.1, §4.2).

Entailment is consulted in exactly two places: the sharpness premise of row extension (`key(ent) ∉ ρ`) and that of row union (`ρ1 # ρ2`). These are the only premises that an inconsistent context makes trivially true (§2.2). A constrained type `C => τ` checks that `C` is well formed and kinds `τ` with `C` added to the assumptions.

Kinding is preserved by context morphisms:

- A **renaming** `ξ` from `Γ` to `Γ'` (`ren_ok`) sends each type variable to one of the same kind. The image of each hypothesis of `Γ` must be entailed by the hypotheses of `Γ'`, and the regions of `Γ` must be in scope in `Γ'`.
- A **substitution** `σ` (`sub_ok`) has the same shape, except that each `σ i` is checked at the kind of `i`.

Because the hypothesis condition is entailment rather than membership, one lemma covers renaming, weakening (adding type variables, assumptions, facts, or regions), and cut. Under a binder, `σ` is lifted and the binder's assumptions are carried over as substituted assumptions without being discharged. A separate cut step discharges them where they are entailed.

A substitution preserves `check` but not the synthesized kind. Substituting row syntax such as `()` for a row variable turns a type whose kind is synthesized into one that can only be checked. So an argument that inverts a kinding derivation after a substitution has to go through `check`.

**Sharpness needs consistency.** In a consistent context, a kinded row has at most one payload per key (`Stella.Core.Kinding.Sharp.check_sharp`): a consistent entailment of `k ∉ ρ` means `k` is no known key of `ρ`, and one of `ρ1 # ρ2` means the two share none (`Stella.Core.Entail.Split`). In an inconsistent context a kinded row may hold two payloads at one key, so every lemma that reads a payload off a row takes consistency as a premise, and none derives it from `wf_ctx`. Under consistency a row splits at a key it holds: `ρ ≡ ( k : τ | ρ∖k )`, where `ρ∖k` (`row_drop`, `Stella.Core.Rows.Split`) removes the extensions at `k` from the syntax of `ρ`, is kinded wherever `ρ` is, and lacks `k`. Two extensions at one key that both lack it in their rests are equal only when their payloads and rests are. The entailments a sub-row inherits, such as `ρ # ρ3` and `k ∉ ρ3` from `( k : τ | ρ ) # ρ3`, hold in every context.

Kind instantiation `kinst ks` preserves kinding when every `ks` is a well-formed quantifiable kind and `Σ` is well formed. In a well-formed `Σ`, the kind of a type constructor is closed under its own kind variables, and the parameters of an effect mention no kind variable.

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

- `EMatch` descends a decision tree.
- `EOpenEffC` widens the ambient effect row of a computation.
- `EForce` and `EFill` operate on by-need locations.
- `ERegionOpen` is an open region frame, `region⟨ℓ⟩ θ in e`.
- `EOpaque` is an opaque value returned by a foreign implementation.

The predicate `is_source` excludes these forms.

**A global applied to arguments has a single representation.** It is the chain of `EApp`, `ETyApp`, and `ECApp` over `EGlobal q ks`, and chains are source syntax. The arguments of a chain (spec 05 §Chains of a constructor or a foreign) are read through a view: `decompose_global_app` returns the head, its kind vector, and the type, constraint, and value arguments in the order they are written. `Stella.Core.Spine` walks the declared type scheme along these arguments, as the specification's cursor does (spec 05 §The cursor):

- a type argument consumes a `forall` and extends the substitution;
- a constraint argument consumes a constraint arrow;
- a value argument consumes a function arrow.

`chain_cursor` runs the cursor over a whole chain, and a chain's type is the unconsumed declared remainder under the accumulated substitution. A chain is *saturated* when the unconsumed part of the **declared** type is none of these three. An arrow that appears only after instantiation does not count. A constructor-headed chain whose value arguments are values is a value. A foreign-headed chain is a value while it is unsaturated, and a redex once it is saturated with value arguments.

A chain headed by a constructor or a foreign also has a typing rule of its own (`T_Chain`, through the node-by-node judgement `chain_typing`), as in the specification (spec 05 §Typing a chain). Each node's cursor is recomputed from its prefix. Type arguments are kinded at the kinds the cursor gives, and constraint arguments are entailed. Value arguments are typed at the chain's ambient row against the pure arrows of the declared type. So a constructor or foreign applied to values has its type at every ambient row, which is what a value needs. The ordinary rules for application still apply to the nodes of a chain. Any derivation of a chain whose cursor is defined can be rebuilt with `chain_typing`, at a type equal to the cursor's instance (`Stella.Core.Typing.Chain`), and a typed constructor chain always has a defined cursor. A saturated foreign applied to further arguments is an ordinary application, and its cursor is undefined.

**Values do not depend on where they stand.** A well-typed run-time value has the same type at every well-kinded ambient row and under every join-point context (`Stella.Core.Typing.Values`). Function types are recognized through the class Σ records for the function type constructor (§4.1).

`fail` is derived notation (spec 03 §Partiality) and is a function rather than a constructor. Its expansion names the effect `Partial` and the constructor `Prim.Unit`, which are passed to it as parameters, and the result type `τ`.

Evaluation contexts are defunctionalized: an evaluation context is a list of frames, and `Ev_k` and `Ev_ℓ` (spec 06 §Evaluation contexts) are predicates on such lists.

### 3.1 Index conventions

- The last binder of a telescope is index 0. This matches the contexts of §4.2, whose heads are index 0. A specification-level substitution `τ[ā := τ̄]` replaces index `i` with the `i`-th element of `τ̄` counted from the end, that is, `sub_ty (list_tsub (rev τ̄))`.
- The annotations of a handler clause, `x : σ` and `k : τ' -{ρ}-> β`, are under the clause's type binders. They are compared by `ty_eq` with the operation's signature instantiated at the effect's arguments, and with `ρ` and `β` shifted past the clause's `m` binders.
- `perform k.op [σ̄]` on an element `E τ̄` instantiates the operation's argument and result types as `subst_ty 0 (rev σ̄) (subst_ty m (rev τ̄) σ)`, where `m = |σ̄|`. That is, the effect's parameters are instantiated first, under the operation's binders, and then the binders themselves.
- `KVar i` refers to the binders of a kind scheme in the order they are written.
- In an operation signature `forall (b̄ : κ̄'). σ ->* τ` of an effect `E (ā : κ̄)`, the operation's own binders `b̄` are inner and the effect's parameters `ā` are outer.
- `EMatch` holds the values of the scrutinees. The value at an occurrence is computed by following the occurrence's projection path from its scrutinee.
- Every substitute in a type or term substitution is locally closed for regions (§1.3). `lc_ty` and `lc_exp` in `Stella.Core.Region` express this.

## 4. Contexts

### 4.1 The global signature Σ

`Σ` is a parameter of every judgement and never changes during checking (spec 05 §Contexts). It is a record of lookup functions keyed by qualified names (`Stella.Core.Sig`):

- **`tycons`**: the number of kind variables of the scheme, the kind, and the class. The class is either intrinsic, with a canonical-value class (literal, function, record, variant, or opaque), or data, with the constructor names. Function types are the applications of a constructor whose class is function, and the saturation of an application chain (§3) consults this class;
- **`ctors`**: the owning type, tag, arity, number of kind variables, and type;
- **`effects`**: the kinds of the parameters, and for each operation its signature `forall b̄. σ ->* τ` (index order as in §3.1);
- **`foreigns`**: the number of kind variables, the type, and whether the declaration asserts `#observ(none)`;
- **`values`**: the number of kind variables and the type.

The judgements assume a well-formed `Σ` (`Stella.Core.Sig.Wf`). Its conditions are:

- a type constructor's kind is a well-formed quantifiable kind that produces `Type`;
- an effect's parameters are quantifiable, and its operations have distinct names;
- every declared type is kinded at `Type` under its kind variables;
- a name is at most one of a data constructor, a foreign, and a top-level value. The lookup that classifies the head of an application chain (§3) covers constructors and foreigns, and the lookup that types a global covers all three tables. Both are defined only for a name recorded in exactly one table.

The typing rules name the type constructors of `Prim` (`Stella.Core.Prim`), and `prim_wf` requires that `Σ` record them with the kinds and classes the rules assume:

- `Function` has kind `Type -> Row Effect -> Type -> Type` and class function;
- `Record` and `Variant` have kind `Row Type -> Type` and classes record and variant;
- `Int`, `Number`, `String`, `Char`, and `Boolean` have kind `Type` and class literal;
- `IO` has kind `Type -> Type` and class opaque;
- `Unit` is a data type whose only constructor is `Prim.Unit`.

No other type constructor has class function, record, or variant.

`globals_ok` fixes the shape of constructors and foreigns:

- a constructor's type is `forall k̄. forall ā. τ̄ -{()}-> T k̄ ā`, where `k̄` and `ā` are the kind and type parameters of its owner `T`, and its arity is `|τ̄|`. The arrows of the spine are pure; the field types `τ̄` may contain any arrows;
- the owner of a constructor and the constructor list of a data type agree in both directions, and the constructors of one type have distinct tags;
- every arrow of a foreign's type outside a constraint is pure (D23).

The metatheory of the typing relation assumes `sig_ok`, which is `sig_wf ∧ prim_wf ∧ globals_ok`. Without the constructor shape, a constructor `C : forall a. a -> T Int` would let a dispatch read a field at `Int` while the value holds any type.

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

- **Entering a type binder** (`ETyLam`, `TForall`, the type binders of a clause) pushes onto `tvars` and shifts every type stored in the context. A constraint about an outer variable never applies to the new one, because it refers to a different index. Renaming, substitution, and kind instantiation of a context act on the same stored types, the layouts in `regions` included, and leave the set of region names unchanged.
- **Entering a region** adds the region with its layout, and adds the fact `RegionKey ℓ ∉ t` for every `t` in `tvars` of kind `Row Effect`. Row variables bound later, inside the region, get no such fact (spec 02 §Deciding entailment).
- **`regions` holds every region name in scope**, including the run-time names that opening a region allocates (§4.5). This is how the specification's `Γ_R`, which stands in front of every `Γ`, is represented.
- **Well-formedness** of a context (`wf_ctx`) is preserved by every extension the typing rules make (`Stella.Core.Typing.Wf`). Entering a region needs no freshness for this.
- **Closedness.** A term typed in `g` under `Δ` is closed with respect to its binders. Its free type variables, term variables, and join points lie below the sizes of `g.tvars`, `g.vars`, and `Δ`, and it is locally closed for regions. Its free region names lie in the domain of `g.regions` (`Stella.Core.Typing.Scope`). This needs the keys of every layout in `g.regions` to be structural, which `wf_ctx` includes: a layout entry is well formed when its key is structural and its type is kinded at `Type`. Entering a region keeps it, because the layout is kinded as a `Row Type`. Distinct region names and distinct layout keys are not part of `wf_ctx`; they belong to the stronger run-time invariant `rctx_ok` (§4.5).
- **Join points.** Typing is preserved by a renaming of join points that maps `Δ` into `Δ'` entry by entry, and so by adding join points in front of `Δ`, with the term's join indices shifted (`Stella.Core.Typing.Join`). Join points added at the end of `Δ` need no shift, and a term typed at `Δ = []` is typed at every `Δ` unchanged (`typing_jp_append`, `typing_jp_nil`). These rely on the bodies that discard `Δ` being closed for join points, which every derivation shows with no condition on the context (`Stella.Core.Typing.Scope.typing_jp_scoped`), so none of them needs a well-formed context.
- **Renaming and weakening.** Typing is preserved by a type renaming `ξ` from `g` to `g'` (`ty_ren_ok`, assuming `sig_ok`): the kinding condition `ren_ok` holds, each term variable's type is the renamed one, and each region's layout, looked up by `assoc`, is the renamed one. Typing is also preserved by a term renaming (`tm_ren_ok`), which keeps the type variables and maps each term variable to one of the same type. Both conditions are re-established under every binder the rules use. Weakening by a binder, by hypotheses, or by a region is a corollary (`Stella.Core.Typing.Weaken`). In particular, adding a fresh region to `g.regions` is weakening.
- **Type substitution.** Typing is preserved by a type substitution `σ` from `g` to `g'` (`ty_sub_ok`, `Stella.Core.Typing.Subst.Ty`). The condition has three parts: the kinding condition `sub_ok` holds, every substitute is locally closed for regions, and each term variable's type and each region's layout is the substituted one. The theorems assume `sig_ok` and that the type variables of `g'` have quantifiable kinds (`tvars_wf`).
  - The fact `RegionKey ℓ ∉ j` that a region adds maps to `RegionKey ℓ ∉ σ j`. The region entered in `g'` entails it, because the tails of the row `σ j` are row variables of `g'`, and the region gives each of them a fact.
  - Without `tvars_wf`, a variable of kind `κ -> Row Effect` would make an application a tail, and no fact would cover it.
- **Kind instantiation.** Typing is preserved by kind instantiation (`Stella.Core.Typing.Kinst`). Instantiation can give a type variable the kind `Row Effect`, so the instance of a region body's context has at most the facts of the region entered in the instantiated context. Typing is then weakened to that context. A top-level value typed in its declaration context, with the regions `rs` of `Γ_R` it was installed under, unfolds at an instance of its kind scheme in every well-formed context that keeps the layouts of `rs`, at every `Δ` and every well-kinded row (`typing_global_unfold`). The context must keep the layouts and not only the names, because a value may read a cell of a region of `rs`.
- **Term substitution.** Typing is preserved by a term substitution `tm_sub_ok` (`Stella.Core.Typing.Subst.Tm`). It maps each term variable of `g` to one of three things: a variable of `g'` of the same type, a run-time value typed in `g'` at the empty row under no join point, or `force ν` for a location of that type, which `letrec` allocation substitutes for the members of a group. Every substitute is closed for join points and locally closed for regions. `Stella.Core.Typing.Subst.Tm.Inst` derives the instances for β, `let`, the parameters of a join point, a decision tree's `bind`, the term binders of a clause, and the members of an allocated group (`typing_subst_forces`). In β, the body of the `λ` is typed at `Δ = []`, and the contractum is typed at the `Δ` of the redex.
- **Cut.** An assumption that the hypotheses of `g` entail can be dropped (`Stella.Core.Typing.Cut`, §2.2 lemma 5). The identity term renaming already treats hypotheses by entailment, so cut needs no well-formedness of `Σ` or of the context.
- **Inversion.** Every derivation factors as a derivation whose last rule is not `T_Conv`, followed by at most one conversion, since conversions compose (`strip_conv`, `Stella.Core.Typing.Inversion`). The value forms `λ`, `Λ`, constraint `Λ`, `{}`, `extend`, the variant values and `openEff` invert at a target type of the matching shape: `ty_eq` is componentwise on two types of the same outer form, though not when one side is row syntax, because a row with one tail and no entries is that tail. A variant value inverts to the key and payload it carries, whether its last rule is the ordinary one or `T_VariantValue`. A chain has derivations by `T_Chain` and by its nodes, and is inverted to `chain_typing` (`Stella.Core.Typing.Chain`). The static value restriction implies the run-time value predicate (`Stella.Core.Typing.ValueForm`).
- **Well-formedness** of a context checks only structure. Every kind in `tvars` is a well-formed quantifiable kind, every fact and assumption is a well-formed constraint, every term variable's type and every layout entry is well formed, and the indices are in scope. Whether the assumptions are consistent is a separate, computable predicate, `inconsistent` (§2.2).

### 4.3 The join-point context Δ

`Δ` is a list of triples: the parameter types, the result type, and the ambient effect row of a join point. It holds exactly the join points that a `jump` may target from where it stands. `jump j (ē)` reads the types and the row of `j` from `Δ` and asks nothing else of its position. `Δ` is relative, in a discipline inspired by System F_J (Maurer, Downen, Ariola, and Peyton Jones, “Compiling without Continuations”, PLDI 2017): the `Δ` of a position depends only on the forms between it and the nearest non-tail position or boundary above it.

- **A non-tail position starts with `Δ = []`.** This covers both sides of an application, the value arguments of a chain, the bound side of `let`, the scrutinees of `case`, the values `θ` of `match`, the condition of `guard`, and the arguments of `jump`. It also covers every subterm of a record or variant operation, the base and payload of a variant value, the argument of `perform`, the value of `writeCell`, the initial values of `region`, and the operands of `[τ]`, `[•]`, and `openEff`.
- **`letjoin j (x̄ : τ̄) : τ = e1 in e2` adds `j` to the `Δ` it is given**, both for its definition `e1` (under the parameters) and for its continuation `e2`.
- **Tail-transparent positions inherit `Δ`.** These are the body of `let` and of `letrec`, the continuation of `letjoin`, the tree of `case` and of `match`, and the branches and leaves of a decision tree.
- **Boundaries also start with `Δ = []`** (spec 04 §Join points). These are:
  - the bodies of `λ`, `Λ`, and constraint `Λ`;
  - the handled computation and every clause of `handle`;
  - the body of `region`, and the body and cells of an open frame `region⟨ℓ⟩`;
  - the initializers of `letrec`;
  - the operand of `fill` and the operand of `openEffC`.

A `jump` to `j` therefore stands under the `letjoin` of `j` in a tail context `Tl` (spec 06 §Evaluation contexts) once the tail-transparent forms between them have reduced, wherever that `letjoin` stands. Reduction keeps this. For example, β-reduction moves the body of a `λ`, typed at `Δ = []`, to the position of the application, and weakening `Δ` (§4.2) types it there.

The discipline is a more direct and conservative variant of the one of F_J. F_J is a call-by-name language in which a jump may discard the evaluation context around it, so it keeps `Δ` in some positions that are not tail positions: the function of an application keeps `Δ`, and only the argument is checked under an empty `Δ`. Here a jump discards no context, and stands only in a `Tl` of its `letjoin`, as the call-by-value semantics has it. So every non-tail premise is checked under `Δ = []`.

`Stella.Core.Typing.Examples.Join` types a β-redex whose `λ` body jumps to its own join point, and its contractum on the bound side of a `let`, through the substitution lemma. It also types a join point in argument position jumped to from its continuation, and a join definition that jumps to itself. It shows that a jump out of a non-tail position, or out of any boundary, has no type.

`Δ` is never carried under a type binder, so its types never need shifting.

The syntactic predicate `jp_scoped n e` (`Stella.Core.Value`) holds when every `jump` in `e` targets a join point in scope. Here `n` is the size of `Δ` at the root, and `Δ` is emptied only at the boundaries, the operand of `openEffC` aside. The typing rules also empty `Δ` at non-tail positions, so `jp_scoped` over-approximates them, and every well-typed term satisfies it (`Stella.Core.Typing.Scope.typing_jp_scoped`). A `jp_scoped` value has no free join index, so the reduction `letjoin j … in v → v` returns `v` unchanged.

### 4.4 The occurrence context Ω

`Ω` maps occurrences to types and exists only while a decision tree is checked. An occurrence is a scrutinee index followed by a path of projections (spec 04 §Occurrences). `Ω` is a list, looked up most recent first. It is well formed (`octx_ok`) when each of its types is kinded at `Type`. The `Ω` of a `case` and of a `match` is well formed, and the refinements a dispatch makes keep it well formed.

The run-time form `match θ dt` descends a tree whose dispatches may already have refined `Ω`. Its typing rule writes an `Ω` in the derivation and justifies each entry `o ↦ τ` by a value of type `τ`. That value is found by following the path of `o` from the scrutinee values in `θ`.

### 4.5 Run-time contexts and the store

Run-time terms involve two global contexts besides `Σ` (spec 06 §Run-time forms):

- `Γ_R` maps region atoms to cell layouts. Opening a region extends it.
- `Γ_N` maps by-need locations to types. `letrec` extends it.

`Γ_R` is the `regions` component of the context in which a closed run-time term is typed, so extending `Γ_R` is an instance of weakening the context (§4.2). `Γ_N` is a separate parameter of the term typing judgement:

```
typing    : sig -> lctx -> ctx -> jctx -> exp -> typ -> (row:typ) -> Type
dt_typing : sig -> lctx -> ctx -> jctx -> octx -> dtree -> typ -> (row:typ) -> Type
```

The two are mutually inductive, with list and clause judgements beside them (`Stella.Core.Typing`).

When the typing rule opens a region statically, it uses an atom that does not occur in `ctx.regions`. Store typing `⊢ N : Γ_N` is as in spec 06 §Run-time forms.

`force` and `fill` kind the location's type in `closed_ctx g.regions`, the context with the region names of `g` and nothing else. New locations are allocated at the end of `Γ_N`, so a location is its position in the list, and `letrec` reduction and `force` use the same numbering. Extending `Γ_N` at its end preserves typing (`typing_lctx_ext`).

An open region frame `region⟨a⟩` kinds its answer type `β` and residual row `ρ` in `closed_ctx g.regions` as well, and types its body in `g` itself, adding no facts. Frames are created only in closed run-time terms, so this is no restriction at creation, and it makes the rule stable under type substitution.

`Γ_R` is well formed (`rctx_ok`, `Stella.Core.Typing.Runtime`) when its region names are distinct, each layout's keys are distinct and structural, and each cell type is kinded in `closed_ctx Γ_R`. Adding a fresh region whose layout is kinded there preserves it.

The typing rules read `Γ_N` unchanged under every binder, so its types must be closed: `lctx_ok` requires each of them to be kinded at `Type` with no kind variable, type variable, or constraint in scope. A location type may mention a run-time region, because a `letrec` inside an open region can give a member a type that mentions the region. So the regions of `Γ_R` are in scope when location types are kinded. Region atoms are never captured by a binder. `lctx_ok` reads only the domain of `Γ_R`, and a location type, having no type variable, is fixed by every type renaming and substitution.

## 5. Initialization safety

A recursive group is initialization-safe when each right-hand side, while it is evaluated, reads only members written before it (spec 10). The typing rule of `letrec` has this as a premise, so the judgement is part of the definition of the type system (`Stella.Core.Init`).

- **Sets, not witness maps.** spec 10 maps each member to the set of places where it is read. Those places only make the diagnostics deterministic. Here a read is a relation: `reads_imm … e m` (evaluating `e` reads member `m` before `e` has a value) and `reads_lat … e m` (the value of `e` may read `m` later).
- **Least fixed points are inductive relations.** spec 10 takes the least fixed point of monotone rules over a group. An inductive definition is such a fixed point by construction, so there is no iteration. The relations are mutually inductive over expressions and decision trees.
- **Members** are numbered by their written position, 0 being the first. In a local `letrec`, members are the term variables the group binds. In a top-level `rec` group, they are global names.
- **Environments follow the de Bruijn binders.** Each term variable in scope is one of the following:
  - a member;
  - a variable whose value reads nothing later (a λ parameter, a clause binder, anything bound outside the group);
  - a variable whose value reads what a given expression's value reads later (`let`, a decision tree's `bind`, a member of a nested group);
  - a join-point parameter, which reads what the arguments of the jumps to that join point read later.

  Each environment entry carries the expression and environment it refers to, so the nested fixed points need no cyclic structure.
- **Join points are read where they are jumped to.** A jump's argument reaches a parameter of the join point the jump targets. The target is found by comparing the depth of join binders at the jump with the depth at the `letjoin`. This syntactic count agrees with `Δ` on `jp_scoped` terms (§4.3).
- **Chains of constructors and foreigns.** A chain whose head is a constructor or a foreign builds a value without running what it is given, provided it has no more value arguments than the arrows of the head's declared type. Such a chain does not promote reads from later to now. An over-applied chain is an ordinary application of its saturated prefix.
- **Invariance.** The judgement reads no type and no kind, so it is invariant under type renaming, type substitution, and kind instantiation. It is also invariant under a term renaming or a term substitution lifted past the group's members. Such a map keeps the members fixed and replaces every outside variable with a term that reads nothing of the group. One simulation covers all five maps (`Stella.Core.Init.Sim`).
- **Run-time forms** have rules as well, because evaluation substitutes `force ν` for the members of an enclosing group into the initializers of a nested one (spec 06 §Recursive bindings):
  - `match` is read as `case`;
  - `openEffC` passes reads through;
  - `force` and `opaque` read nothing;
  - `fill` is read as `writeCell`;
  - an open region frame is read as `region`.

## 6. Relation to the specification

The specification here is the one revised by stella-lang's Proposal 14, *Core Soundness Repairs Found by Mechanization* (`docs/proposals/14-Core-Soundness-Repairs.md`), with its units U1–U3 applied. §6.1 lists what still differs from it. §6.2 records the problems this formalization found that the proposal has repaired, so that the link between the two developments is not lost.

### 6.1 Differences from the current specification

**On source terms, the typing relation over-approximates the specification's rules.** The rules are built so that every source term that the specification's rules type, with its annotations kinded as the reference Core type checker requires, is typed here at the same type. This inclusion is a design property and is not proved. The converse does not hold, because some rules type more than the specification's do:

- `T_VariantValue` re-types any variant value at a variant row that holds its injected key, whether the value was written in the source or produced by reduction;
- `T_Conv` converts the ambient row as well as the type.

The soundness theorems are stated for this relation, so they cover every program the specification accepts. The relation is not the acceptance relation of a type checker: a checker that implements the specification accepts a subset of the source terms typed here.

Items marked with a Proposal 14 number are the subject of that proposal and not yet in the specification.

| Point in the specification | Treatment here |
| --- | --- |
| The rule for an open region frame `region⟨ℓ⟩ θ in e` adds `RegionKey ℓ ∉ t` for every row variable in scope and kinds `β` and `ρ` in the current context (spec 06 §Run-time forms). A type substitution can then give a frame under a type binder a row that mentions `ℓ`, and the substituted frame has no type. (Proposal 14 S4.) | The frame's `β` and `ρ` are kinded in the context of the region names alone, and no facts are added (§4.5). |
| `switchKey` computes the residual row of its default as `nf(r') = ⟨ F ∖ k̄ ; T ⟩` (spec 05 §Join points and decision trees). Removing keys from a normal form does not commute with substitution when the context is inconsistent, because a substitution can merge entries. (Proposal 14 S5.) | The branches carry their keys and payload types, and the variant's row is split by type equality into the branch entries and a residual row (`key_split`). Type equality is preserved by every substitution. Payload and residual types are kinded by separate premises. |
| In a `switchKey` default, the occurrence takes the residual type, but the value at it is an `inject` whose annotation still holds the removed keys, and no rule types it at the residual (spec 05, spec 06 §Pattern matching). This contradicts preservation. (Proposal 14 S5.) | A variant value that already has a variant type also has every well-kinded variant type that holds its injected key at its payload type (`T_VariantValue`). The rule requires the ordinary derivation of the value, which checks every annotation it holds; without it, an annotation mentioning an unbound region would go unchecked. The rest of a variant's row has no run-time content. |
| The run-time form `match θ dt` has no typing rule (spec 06 §Run-time forms). (Proposal 14 S7.) | A typing rule requires the values in `θ` to agree with the occurrence context (§4.4). |
| The erased reduction relation `→ᵤ` used by the erasure property is not defined (spec 06 §Erasure). (Proposal 14 S7.) | It is defined before the erasure property is stated. |
| The decision-tree form `fail` stands for `leaf (perform Partial.abort [τ] Prim.Unit)`, but the tree grammar does not write `τ` (spec 04 §Decision trees). (Proposal 14 S7.) | The result type is an explicit argument of `fail` (§3). |
| The initialization-safety judgement gives no rule for the run-time forms (spec 10 §What an initializer reads), but reduction puts `force ν` into the initializers of a nested group (spec 06 §Recursive bindings). (Proposal 14 S7.) | Run-time forms have rules (§5), so the judgement is defined on every term that reduction produces. |
| The rule for `openEffC [ρ] e` asks only `Γ ⊨ r # ρ` (spec 06 §Run-time forms), and the rule for `force ν` only `(ν : σ) ∈ Γ_N`. (Proposal 14 S7.) | Both rules also kind what they introduce (`ρ`, and `σ`), as the rules of the source forms do, so that every derivation's type and row are well kinded. `force` and `fill` kind the location type in the context of the region names alone (§4.5). |
| Several source rules leave some of their annotations unkinded, such as the type of a `let` or the answer type of a `handle` (spec 05). (Proposal 14 S7.) | These annotations are kinded, as the Core type checker of the reference implementation does. |
| `region⟨ℓ⟩ θ` requires `dom(θ) = { k̄ }` (spec 06 §Run-time forms). | `θ` holds one value per cell, in the order of the layout. |
| `F(k)`, the payload a row's normal form holds at `k`, is read off the normal form in the rules for `perform` and the record-field occurrence (spec 05). Here a normal form holds canonical payloads, not types. | The derivation writes a type whose canonical form is the payload and which is kinded at `Type`. Kinding the row makes the entry unique, by sharpness. |
| The rules give the ambient row no conversion of its own (spec 05 §Basic rules converts types). | `T_Conv` converts the type and the ambient row together, up to type equality. |
| `jump` requires its own position to be a tail position, while `Δ` is carried unchanged into non-tail positions and emptied only at the boundaries (spec 05 §Join points and decision trees). Reduction does not preserve this. The body of a `λ` may hold `letjoin j … in jump j (…)` with the jump in tail position, and β-reduction can move that body into a non-tail position, such as the argument of another application, where the jump has no type. (Proposal 14 S8.) | `Δ` is relative, in a variant of the discipline of System F_J (§4.3): a non-tail position starts with `Δ = []`, and `jump` asks only that its target be in `Δ` (§4.3). |
| Preservation and Progress are stated for every rule of spec 06, with `Γ_R` and `Γ_N` extended by a step and `⊢ N : Γ_N` among the premises (spec 06 §Properties). | The development reaches them in stages. For the pure rules, which neither allocate nor open a region, Preservation keeps `Γ_R` and `Γ_N` and needs no store typing, and Progress is a single step for terms with no `perform`, `handle`, region, cell, `letrec`, `force`, or `fill` (`stage5_frag`). A `fail` leaf is a `perform`, so a decision tree with one is outside it. Global unfolding and a foreign can return such a term, so the single-step result does not yet chain into a run. |
| "`e` respects preconditions under `G`" bounds every call a run makes (spec 06 §Properties). | Progress takes `pre_ok`: every saturated foreign redex in evaluation position satisfies its erased precondition. This is the condition for one step. Preservation does not take it. |
| Coverage is a property of a configuration, `G covers N; e`, and a conclusion of Preservation under its own premise (spec 06 §Coverage, §Properties). | Coverage is stated of a term (`covers`), and `preservation_covers` carries it across a step. A foreign's result is covered relative to its arguments, as condition (3) asks. |

### 6.2 Problems found by this formalization and repaired upstream

Each of these was a point where the specification, as it then stood, failed a property this formalization proves. Proposal 14 repaired them, and the treatment here is the one the revised specification adopts.

| Problem in the earlier specification | Repair |
| --- | --- |
| `nf` took `F` to be a finite map from keys to payloads, so it was undefined on rows that repeat a key, and type equality based on it was not preserved by substitution: `r ⊎ r ≡ r` held, but substituting `( x : Int )` for `r` gave a left-hand side with no normal form. | Proposal 14 S1, applied in U1. Type equality is the equality of a total canonical form that keeps set semantics for rows (§2.1, spec 02 §Canonical form). |
| Forming `Γ, C` required `C` to be satisfiable, while type application `e [σ]` checked only `Γ ⊢ σ : κ`. So instantiation could create an unsatisfiable `Λ(_ : C)` inside a value. For example, instantiating `Λ (r : Row Type). λ (u : Unit) / (). let y = Λ (_ : name ∉ r). … in u` at `( name : Int )` gave a term with no type, which contradicted preservation. | Proposal 14 S2, applied in U1. Constraint abstractions require only well-formedness, and an inconsistent context entails every constraint while kinding and typing keep their structural checks (§2.2, spec 02 §Inconsistent assumptions). |
| A global applied to arguments was written in two ways: as an application chain, which the value restriction admitted as the body of a `Λ` (e.g. `Λ a. M.Cons [a] v1 v2`), and as a run-time spine `M.g ς`, with formation steps turning the first into the second. No evaluation context went under `Λ`, so such a body was a static value form but not a run-time value, and the term was stuck, which contradicted progress. Typing the spine only at the empty ambient row also broke preservation of `openEffC [ρ] v → v`. | Proposal 14 S3, applied in U3. The chain is the only representation, and it has its own typing rule, with value arguments at the chain's ambient row (§3, spec 05 §Chains of a constructor or a foreign). |
| Nothing tied a constructor's declared type to its owning type, its arity, or its tag, and nothing required the arrows of constructors and foreigns to be pure. A constructor `C : forall a. a -> T Int` let a dispatch read a field at `Int` while the value held any type. | Proposal 14 S6, applied in U2. A well-formed `Σ` fixes the shape of every constructor and foreign (§4.1, spec 05 §What `Σ` is held to). |

## 7. Reduction

The reduction relation of spec 06 is defined in `Stella.Core.Semantics.*`.

- **The global environment** `G` holds the definitions of top-level values and an entry for each foreign (`genv`, `Stella.Core.Semantics.Env`). A definition's kind scheme is read from `Σ`. `G` has no entries for constructors, which have nothing to unfold to, while the `G` of spec 06 lists them.
- **A foreign's entry** has three parts (spec 06 §Chains of a constructor or a foreign, §An ABI precondition is where condition (3) stops asking; D53):
  - a typed adapter `δᵀ_f`, which receives the chain's instance `⟨ κ̄ ; types(ᾱ) ⟩` and its value arguments and returns an annotated value or an ABI fault. The instance is ghost information used only to write the annotations the cursor computes, such as `M.Nil [τ]` or `opaque ω [IO τ]`;
  - an erased function `δᵤ_f` on the erased value arguments (`Stella.Core.Erase`), which is what a backend runs;
  - an erased precondition `Pᶜ_f` on the erased value arguments, so a precondition cannot tell apart two argument lists that erase alike.

  The foreign rule requires `Pᶜ_f` and reduces by the adapter. The rule of spec 06 also has the premise that `G` is Core-modelled; here the relation is defined for every `G` of this shape, and that premise is part of conformance, which every theorem assumes. Every part is a function of the call alone, with no host state, so an entry is a candidate for the correspondence contract of a Core-modelled foreign. The shape does not make `G` Core-modelled: conformance completes the contract, and an adapter that breaks erasure coherence has the same shape and does not conform. The host state, the general implementation, and the general conformance of spec 06, which also admits implementations whose outcome or precondition depends on state, are not represented. Three obligations are kept apart: conformance asks the implementer for an outcome wherever `Pᶜ_f` holds, `pre_ok` asks the program to call a foreign only inside `Pᶜ_f`, and an adapter that returns nothing is outside the relation, with no step.
- **Faults.** A foreign returns a value or an ABI fault. The initialization fault `φ_init` is a separate constructor of `fault`, which no foreign can produce.
- **Conformance** (`genv_ok sg ln rs G`) is spec 06 §Conformance of the global environment for a Core-modelled `G`. For a well-typed saturated call inside `Pᶜ_f`, condition (3) asks that the adapter and the erased function both return, that the adapter's outcome erase to the erased function's (erasure coherence, the whole outcome, a fault and its payload included), that a value have the instantiated result type under the call's contexts, and that every global it mentions be covered by `G` or occur among the arguments. A foreign returning its argument may hand back what the argument mentions, so coverage of the result is relative to the arguments. Condition (3) quantifies over the well-formed extensions of `rs` and `ln`, which keep every layout and every location type. At `rs = []` and `ln = []` every well-formed pair is an extension, so `genv_ok sg [] [] G` is conformance before any region or location exists, and it implies conformance at every `rs` and `ln`. Conformance is stable under extending `rs` with the same layouts and `ln` at its end. A call is one atomic step to the outcome the adapter gives, which is what the clauses of (3) on termination and on running no computation of its own ask.
- **Erasure** (`Stella.Core.Erase`) follows spec 06 §Erasure, except that a cell reference keeps its key where the specification writes the key's position in the layout. Under a fixed `Γ_R` the two carry the same information. A foreign's erased function does not depend on `Γ_R` while conformance ranges over every `Γ_R`, so an erased function may read a key that positional erasure would hide: the environments that conform here include those that conform under positional erasure, and a few more.
- **Configurations.** A step relates a list `R` of allocated region names, a store, and a term to the same three with a configuration, a term or a fault. Stage 5 of the development (the pure rules) leaves `R` and the store unchanged.
- **Evaluation contexts** are lists of frames, one frame per production of spec 06 `Ev`, innermost first (`Stella.Core.Semantics.Ctx`). A frame lists the positions the production requires to be values, and `frame_ok` checks them. The step relation closes the head rules under one frame at a time, which by induction is closure under every `Ev`. `Tl`, `Ev_k`, and `Ev_ℓ` are predicates on frame lists.
- **The join rule** moves the definition `e1` of `j` under the join binders of `Tl`: the reduct is `Tl[sub_tm (list_esub (rev v̄)) (ren_jp (shift n) e1)]`, where `n = |Tl|` and the `jump` has index `n`. Typing gives the reduct by join weakening by a prefix followed by the substitution of the parameters (§4.2, §4.3). The rule `letjoin … in v → v` keeps `v` unchanged, because a scoped value has no free join index (§4.3).
- **Pattern matching.** `θ` is the list of scrutinee values. A dispatch requires `θ(o)` to be defined, and its default applies where `θ(o)` is defined and its constructor, literal, or carried key names no branch.
- **Typing at a frame** (`Stella.Core.Typing.Plug`). A derivation of `F[e]`, for `e` not a value, gives one of `e` and a way to type `F[e']` from one of `e'` at the same judgement. The hole is typed under `Δ = []`, except under the continuation of a `letjoin`, where it is typed under the join point added to `Δ`. Its row is the frame's row, except under `openEffC`, `handle`, an open region frame, and `fill`. A chain headed by a constructor or a foreign may be typed by `T_Chain` around a redex in one of its arguments, so `F[e']` is retyped through `T_Chain` too, which needs the cursor of the chain to be kept. A step of a chain that is not a foreign redex keeps it (`step_chain_cursor`). Under `Tl` the hole is typed under one join point per frame in front of `Δ` (`tl_typing`).
- **Canonical forms** (`Stella.Core.Typing.Canonical`). A value of a function type is a `λ`, an `openEff`, or a chain whose declared remainder is a function type, and similarly for `forall` and constrained types. A record value is `{}` or an `extend`, and holds a field at every key its type holds, which needs a consistent context. A variant value carries a key, and `Variant ()` has no value. A value of a literal class is a literal, a value of a data type is a chain of one of its constructors, and an opaque value is `opaque ω [τ]`. A value reached through an occurrence of a `match` is defined and typed at the occurrence's type (`Stella.Core.Typing.Occ.occ_sound`).
- **Handlers** (`eff_head`, `Stella.Core.Semantics.Step`). The return clause, a `full` clause, and a `fast` clause are head rules of their own. A clause is found by a function of the operation name (`clause_of`), so a handler with two clauses for one operation still gives one step. The type binders of a clause are instantiated at the `perform`'s types in the order `push_tvars` binds them (`list_tsub (rev σ̄)`), before its term binders are substituted. The continuation of a `full` clause is `λ (y : τ′) / ρ. handle Ev_k[y] with h`, where `τ′` and `ρ` are read from the clause's continuation annotation with its type binders instantiated: the row `ρ` the `handle` stands at is written nowhere else in the term. A `fast` clause binds its body with `let y : τ′`, where `τ′` is the operation's result at the handler's effect arguments and the `perform`'s types. Both rules move `Ev_k` and the handler under one more term binder, by a renaming of frames that lifts past the binders each frame holds (`Stella.Core.Semantics.Ctx.Ren`).
- **Safety for the pure rules** (`Stella.Core.Safety.*`). A step from a well-typed closed term to a term preserves its type and its ambient row exactly, at any `Δ` (`preservation`, a ghost function because the derivations of an unfolded definition and of a foreign's result come from the props of conformance), and preserves coverage (`preservation_covers`). Under `sig_ok`, `rctx_ok`, `lctx_ok`, and conformance, a well-typed closed term of `stage5_frag` at row `()` that is covered and respects preconditions is a value or takes a step, to a term or to an ABI fault of a foreign (`progress_top`, `step_fault_shape`). The inner statement, at any `Δ` and row, adds a third outcome, a `jump` standing in a `Tl` to a join point outside it, which the enclosing `letjoin` resolves (`progress_in`). The derivation of the reduct exists only in ghost code, so an evaluator extracted from this development would need a step function that does not consult derivations.
