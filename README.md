# The Stella Verified Specification

This repository offers the formal verification of the core semantics and metatheory of
[the Stella programming language](https://github.com/stella-org/stella-lang).

## Overview

Stella is a strictly evaluated, pure functional language featuring first-class row calculus and powerful syntax macros.

A Stella program is first parsed into a Concrete Syntax Tree (CST). Through name resolution and macro expansion, it is then transformed into a Surface AST containing unresolved meta-variables. The Elaborator then performs type inference, meta-variable resolution, and zonking to lower this into the **Core** language. The Core is a minimalist system built upon a higher-kinded System F, enriched with rows and effects. It is validated by an independent type checker, and any program that fails this check is rejected by the compiler.

This is the cornerstone of Stella's correctness: even though syntax macros and the Elaborator run arbitrary user-defined functions—meaning they could behave erratically and generate malformed programs—the Core type checker acts as a final line of defense.
In other words, the semantic correctness of the Core is Stella's primary **Trusted Computing Base** (TCB). The stability of Stella as a language depends heavily on how bedrock-solid this foundation is.

To address this, this repository deeply embeds the semantics of Stella Core within [F*, a proof-oriented programming language with SMT-assisted proof semi-automation](https://fstar-lang.org/), and formally verifies its semantic soundness including progress, preservation.

## References

1. [Stella Repository](https://github.com/stella-org/stella-lang)
2. [The Stella Language References](https://github.com/stella-org/documentation)
