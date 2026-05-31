---
title: "Membership and emptiness are decidable for context-free languages"
description: "A formal Lean 4 proof that membership (via the CYK algorithm) and emptiness are computable for context-free languages."
parent: "Context-free"
nav_order: 8
---

# Membership and emptiness are decidable for context-free languages

## Statement

For context-free languages, two basic problems are **computable** (in the strong
`ComputablePred` sense, not merely abstractly decidable):

- **Membership** — does a given word belong to the language? Decided by the CYK
  algorithm.
- **Emptiness** — does the grammar generate any word at all?

(Universality and equivalence of context-free languages are, by contrast,
undecidable.)

## In Lean

- Membership: [`cf_membership_computable`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Decidability/Membership.lean) in `Classes/ContextFree/Decidability/Membership.lean` — a bitvector CYK implementation packaged as a `ComputablePred`.
- Emptiness: [`encoded_cf_emptiness_computable`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Decidability/Emptiness.lean) and [`encoded_cf_emptiness_decidable`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Decidability/Emptiness.lean) in `Classes/ContextFree/Decidability/Emptiness.lean` — a least-fixpoint computation of the productive nonterminals.

## Proof idea

Membership: convert to Chomsky normal form and run **CYK** — a dynamic-programming
table over all substrings recording which nonterminals derive each substring; the
word is accepted iff the start symbol covers the whole word. The implementation
encodes nonterminal sets as bitvectors so the whole thing is primitive recursive,
hence a `ComputablePred`. Emptiness: iterate the "productive nonterminal" operator
to a fixpoint; the language is nonempty iff the start symbol is productive.

## Keywords / also known as

context-free membership decidable, CYK algorithm Lean, CFG emptiness decidable,
deciding context-free membership, Cocke–Younger–Kasami, context-free word problem,
type-2 decidability.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
