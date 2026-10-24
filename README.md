# The Stella Verified Specification

This repository formally verifies the core semantics and metatheory of
[the Stella programming language](https://github.com/stella-org/stella-lang).

## Overview

Stella is a strictly evaluated, pure functional language with first-class row calculus and syntax macros.

A Stella program is first parsed into a Concrete Syntax Tree (CST). Name resolution and macro expansion then turn it into a Surface AST containing unresolved metavariables. The Elaborator performs type inference, metavariable resolution, and zonking to lower this into the **Core** language. The Core is a minimal system built on a higher-kinded System F with rows and effects. An independent type checker validates every Core program, and the compiler rejects any program that fails this check.

Stella's correctness rests on that check. Syntax macros and the Elaborator run arbitrary user-defined functions, so they can misbehave and generate malformed programs, and the Core type checker is the last stage that can reject them.
The semantic correctness of the Core is thus Stella's primary **Trusted Computing Base** (TCB), and the language is only as stable as that foundation is sound.

This repository therefore deeply embeds the semantics of Stella Core in [F*, a proof-oriented programming language with SMT-assisted proof semi-automation](https://fstar-lang.org/), and formally verifies its semantic soundness, including progress and preservation.

## Current State

### What is PROVEN

The results listed as proven are checked by `make verify`, with no `admit` or `assume`.

Proven so far:

- Parallel renaming and substitution over the three index spaces (types, terms, join points), with the σ-calculus laws and the commutation of type and term substitution.
- Locally nameless operations on regions: substitution preserves local closure, and open and close are mutually inverse.
- Row canonicalization commutes with renaming and substitution, so both preserve type equality.
- The inconsistency check on constraint assumptions is sound and complete, and entailment is preserved by renaming, substitution, and adding assumptions.
- Kinding is preserved by renaming, substitution, and kind instantiation.
- Regularity: a well-typed term has a well-kinded type and ambient row, is locally closed, and mentions only regions in scope.
- Typing is preserved by renaming (and hence weakening), term substitution, type substitution, and kind instantiation, under a relative Δ discipline for join points inspired by System F_J.
- Cut: if Γ ⊨ C and Γ, C ⊢ J, then Γ ⊢ J.
- Generation lemmas that see through type conversion. Static value forms are values, and a well-typed term jumps only to join points in scope.
- Typing is preserved through the substitutions within reduction (β, `let`, join points, decision trees, and `letrec` allocation which replaces the members with `force ν`).
- A top-level value, instantiated at any kinds, is typed in every context that keeps the layouts of its regions.
- Row algebra: in a consistent context a kinded row holds one payload per key and splits at any key it holds. If `( k : τ | ρ ) ≡ ( k : τ′ | ρ′ )` and neither `ρ` nor `ρ′` holds `k`, then `τ ≡ τ′` and `ρ ≡ ρ′`.
- The reduction relation of the pure fragment is defined (global environment with typed foreign adapters and erasure coherence, evaluation contexts, head rules). For it: typing decomposes and recomposes at every evaluation frame, canonical forms hold at every elimination type, and the occurrences of a `match` are defined and typed.
- Effect handlers: return, `full`, and `fast` clauses reduce as the specification gives them, deep and multi-shot.
- Type safety for the pure and effect rules: a step that uses no rule of regions and cells preserves the exact type, ambient row, and coverage of a closed well-typed term. A closed well-typed term at the empty row that is covered, calls foreigns only inside their preconditions, and has no region, cell, `letrec`, `force`, or `fill` is a value or takes one step.
- Effect safety for the same rules: under a conforming global environment, from any closed term typed at the empty row, no sequence of such steps reaches a `perform` that no handler of its key encloses.
- Regions and cells: opening, closing, reading, and writing reduce as the specification gives them, a reference reaches the innermost frame of its name, and a continuation copies the region frames it captures.

Under review: preservation of type, ambient row, and coverage, and effect safety, for every rule of the reduction relation so far, the rules of regions and cells included. A step types its reduct under a region context that extends the redex's with the same layouts, an opening adding the region it allocates. One-step progress is not yet extended to regions and cells, and the rules of `letrec` must re-establish these results when they are added.

Planned:

- Preservation, progress, and effect safety extended to regions and cells, and to `letrec` with its store, and chained into type safety for whole runs.
- Initialization safety: a well-typed program never reads an uninitialized `letrec` binding, and in particular never re-enters an initializer that is still being evaluated (the `φ_init` fault).
- Erasure: each typed reduction step corresponds to zero or one step of the erased program, with the same faults.

### What is TRUSTED

What this repository establishes about Stella rests on the following, which it does not check.

- F* and its standard library as pinned by `flake.nix` (F* v2026.10.11), including the axioms the library assumes (such as `FStar.IndefiniteDescription`), and the Z3 SMT solver it ships with.
- Adequacy: the F* definitions of syntax, kinding, typing, and reduction faithfully encode the Typed Core chapters of the specification, as revised by stella-lang's Proposal 14. [Design §6.1](docs/design/01-Representation.md#61-differences-from-the-current-specification) lists the known differences.
- On source terms, the typing relation here includes the specification's: every source term the specification types is typed here at the same type. This inclusion is a design property and is not proved, and the soundness theorems reach the programs the specification accepts only through it.
- A well-formed global signature Σ (`sig_ok`). Checking declarations and modules (`Σ ⊢ decl ⊣ Σ'`) is not formalized.
- Foreign functions are supplied by entries in the global environment. Each entry contains a typed
  adapter, an erased implementation, and a precondition on erased arguments.
- The theorems assume that these entries conform to `Σ` and that the typed and erased results agree
  under erasure. Progress additionally assumes that every foreign call satisfies its precondition.
- Only *Core-modelled* foreigns are represented: foreigns whose behaviour depends on hidden state,
  such as `Base.Array.unsafe*`, are outside the model.

- Neither the Core typechecker nor STEAM (the Stella abstract machine) is verified against
  this typing and reduction relation. It is trusted to accept only programs the specification
  types and STEAM executes according to the reduction rules. Differential testing against an
  executable Core evaluator extracted from this development would strengthen this assumption,
  but no such evaluator exists yet.

## References

1. [Stella Repository](https://github.com/stella-org/stella-lang)
2. [The Stella Language References](https://github.com/stella-org/documentation)
