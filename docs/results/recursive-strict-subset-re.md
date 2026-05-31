---
title: "Recursive ⊊ RE: recursive languages are a strict subset of recursively enumerable"
description: "A formal Lean 4 proof that the recursive (decidable) languages form a strict subclass of the recursively enumerable languages, witnessed by the halting problem."
parent: "Recursive"
nav_order: 4
---

# Recursive languages are a strict subclass of recursively enumerable languages (Recursive ⊊ RE)

## Statement

Every recursive (decidable) language is recursively enumerable, but **not** the
other way around: there is a recursively enumerable language that is not recursive.
Hence `Recursive ⊊ RE`. The witness is a halting-problem-style language that is
semi-decidable but not decidable.

## In Lean

In `Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean`:

- [`haltingUnaryLanguage_not_Recursive`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean) — a concrete RE language that is not recursive.
- [`Recursive_strict_subclass_RE_unit`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean) — strict inclusion over the unary alphabet.
- [`Recursive_strict_subclass_RE_of_nonempty`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean) — strict inclusion over any nonempty finite alphabet.
- [`Recursive_subclass_RE_and_exists_strict`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean) — class inclusion plus a strictness witness.

## Proof idea

The halting language is recursively enumerable: enumerate computations and accept
the moment one halts. If it were recursive, its complement would also be recursive,
hence RE; by [Post's theorem](posts-theorem.html) that would decide halting, a
contradiction. So the halting language witnesses `Recursive ⊊ RE`.

## Keywords / also known as

recursive strictly contained in recursively enumerable, decidable proper subset of
semidecidable, halting problem not recursive, Recursive ⊊ RE, RE not closed under
complement, undecidable but semidecidable language.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
