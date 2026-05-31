---
title: "Regular language membership is computable"
description: "A formal Lean 4 proof that membership in a regular language (DFA acceptance) is a computable predicate."
---

# Regular language membership is computable

## Statement

Membership in a regular language is **computable** in the strong `ComputablePred`
sense: there is an algorithm that runs a DFA on a word and always halts with the
correct accept/reject verdict. This is the strongest decidability guarantee, beyond
Mathlib's abstract `Decidable` instance.

## In Lean

In `Classes/Regular/Decidability/Membership.lean`:

- [`dfa_membership_computablePred`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Decidability/Membership.lean) — `ComputablePred (· ∈ M.accepts)` for a DFA `M`.

Related weaker (`Decidable`-only) results for emptiness, universality and
equivalence of regular languages live in the same
[`Decidability/`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Decidability)
directory.

## Proof idea

A DFA evaluates a word by folding its transition function over the input — a
primitive-recursive computation — and then checks membership in the (finite,
decidable) set of accepting states. Both pieces are computable, so the whole
acceptance predicate is a `ComputablePred`.

## Keywords / also known as

regular language membership decidable, DFA acceptance computable, deciding regular
membership, ComputablePred regular language, finite automaton word problem.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
