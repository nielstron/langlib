---
title: "Every context-sensitive language is recursive (CS ⊆ Recursive)"
description: "A formal Lean 4 proof that every context-sensitive language is recursive (decidable), so CS ⊆ Recursive in the Chomsky hierarchy."
parent: "Context-sensitive"
nav_order: 3
---

# Every context-sensitive language is recursive (CS ⊆ Recursive)

## Statement

Every **context-sensitive language** (CSL) is **recursive** (i.e. decidable):
there is an algorithm that, given a word, always halts and correctly answers
whether the word is in the language. As a class inclusion, the context-sensitive
languages form a subset of the recursive languages, `CS ⊆ Recursive`.

## In Lean

In `Classes/ContextSensitive/Inclusion/Recursive.lean`:

- [`is_Recursive_of_is_CS`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/Recursive.lean) — pointwise: `is_CS L → is_Recursive L`.
- [`CS_subset_Recursive_class`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Inclusion/Recursive.lean) — class-level: `(CS : Set (Language T)) ⊆ Recursive`.

A second, grammar-first packaging of the same result appears in
[`CS_subset_Recursive`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextSensitive/Decidability/Computability.lean)
(`Classes/ContextSensitive/Decidability/Computability.lean`).

## Proof idea

A context-sensitive grammar is **non-contracting**: derivations never shrink, so a
word of length `n` can only be derived through sentential forms of length `≤ n`.
Hence membership is **recursively enumerable** (search all bounded derivations),
and so is non-membership — encoded as a *certificate search* over the
ε-eliminated non-contracting grammar. Having both `L` and `Lᶜ` recursively
enumerable, [Post's theorem](posts-theorem.html) (`is_Recursive_of_isRE_of_isRE_compl`)
concludes that `L` is recursive.

## Keywords / also known as

context-sensitive languages are recursive, CS ⊆ Recursive, every context-sensitive
language is decidable, CSL decidability, type-1 languages are decidable, LBA
languages are decidable, Chomsky hierarchy CS subset recursive.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
