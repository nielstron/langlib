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

- Membership: [`cf_membership_computable`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Decidability/Membership.lean) — a bitvector CYK implementation packaged as a `ComputablePred`.
- Emptiness: [`encoded_cf_emptiness_computable`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Decidability/Emptiness.lean) and [`encoded_cf_emptiness_decidable`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Decidability/Emptiness.lean) — a least-fixpoint computation of the productive nonterminals.

## Proof idea

Membership: convert the grammar to Chomsky normal form (`mathlib_cfg_of_cfg g |>.toCNF`)
and run **CYK** — a dynamic-programming table (`cykBuildTable`) over all substrings
recording which nonterminals derive each substring, with the final check
(`cykMemCheck`) asking whether the start symbol derives the whole word. Nonterminals
are first injected into `ℕ` and nonterminal *sets* are encoded as bitvectors
(`Nat.testBit`), so every table operation is shown `Primrec`; `cf_membership_computable`
packages the result as a `ComputablePred`.

Emptiness: compute the productive nonterminals by iterating the monotone
`productiveStep` operator `g.rules.card` times from `productiveInit`
(`productiveNTs`) — enough iterations to reach the fixpoint — and report nonempty iff
the start symbol is productive. `encoded_cf_emptiness_decidable` is the `Decidable`
instance and `encoded_cf_emptiness_computable` the `ComputablePred`, both uniform in
the encoded grammar.

## Keywords / also known as

context-free membership decidable, CYK algorithm Lean, CFG emptiness decidable,
deciding context-free membership, Cocke–Younger–Kasami, context-free word problem,
type-2 decidability.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
