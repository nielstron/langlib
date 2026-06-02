---
title: "⊊ RE"
description: "A formal Lean 4 proof that the recursive (decidable) languages form a strict subclass of the recursively enumerable languages, witnessed by the halting problem."
parent: "Recursive"
nav_order: 3
---

# Recursive languages are a strict subclass of recursively enumerable languages (Recursive ⊊ RE)

## Statement

Every recursive (decidable) language is recursively enumerable, but **not** the
other way around: there is a recursively enumerable language that is not recursive.
Hence `Recursive ⊊ RE`. The witness is a halting-problem-style language that is
semi-decidable but not decidable.

## In Lean

- [`haltingUnaryLanguage_not_Recursive`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean) — a concrete RE language that is not recursive.
- [`Recursive_strict_subclass_RE_unit`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean) — strict inclusion over the unary alphabet.
- [`Recursive_strict_subclass_RE_of_nonempty`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean) — strict inclusion over any nonempty finite alphabet.
- [`Recursive_subclass_RE_and_exists_strict`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Recursive/Inclusion/StrictRecursivelyEnumerable.lean) — class inclusion plus a strictness witness.

## Proof idea

Inclusion `Recursive ⊆ RE` is `Recursive_subset_RE`. Strictness is **not** a
diagonalization; it is a closure-asymmetry argument run through the generic lemma
`strict_subset_of_subset_different_property`:
if `P ⊆ Q`, the class predicate `X = ClosedUnderComplement` holds of `P` but not of
`Q`, and `X` transports across pointwise class equivalence, then `P ⊂ Q`. Instantiated
with `P = is_Recursive`, `Q = is_RE`:

- `Recursive_closedUnderComplement` supplies `X P` (see
  [Recursive closed under complement](recursive-closed-under-complement.html));
- `RE_notClosedUnderComplement` (resp. `..._of_nonempty`) supplies `¬ X Q`.

The non-closure of RE is witnessed concretely by the unary halting language
`haltingUnaryLanguage`: a word
is accepted iff its length decodes (via `Nat.Partrec.Code.ofNatCode`) to a code that
halts on `0`. It is RE (`haltingUnaryLanguage_RE`) because `haltingUnaryTest` is a
computable bounded-evaluation search (`Nat.Partrec.Code.evaln`), but its complement is
not RE (`haltingUnary_complement_not_RE`), which reduces to Mathlib's
`ComputablePred.halting_problem_not_re`.

`haltingUnaryLanguage_not_Recursive` makes the same asymmetry explicit at the language
level: if the halting language were recursive then its complement would be recursive
(complement closure), hence RE (`Recursive_subset_RE`), contradicting
`haltingUnary_complement_not_RE`.

## Keywords / also known as

recursive strictly contained in recursively enumerable, decidable proper subset of
semidecidable, halting problem not recursive, Recursive ⊊ RE, RE not closed under
complement, undecidable but semidecidable language.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
