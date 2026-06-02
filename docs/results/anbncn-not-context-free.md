---
title: "{aⁿbⁿcⁿ} is indexed and context-sensitive but not context-free"
description: "Lean 4 formalizations of the classic separating language {aⁿbⁿcⁿ}: indexed, context-sensitive and recursively enumerable, but not context-free."
parent: "Context-free"
nav_order: 9
---

# The language {aⁿbⁿcⁿ}: indexed and context-sensitive, but not context-free

## Statement

The language `{aⁿbⁿcⁿ : n ≥ 0}` is the textbook example that separates the levels of
the Chomsky hierarchy. It is **indexed**, **context-sensitive** and **recursively
enumerable**, but it is **not context-free** (it fails the context-free pumping
lemma). Likewise `{aⁿbⁿ}` is **linear** (hence context-free) but not regular.

## In Lean

- `{aⁿbⁿcⁿ}` is indexed: [`Classes/Indexed/Examples/AnBnCn.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Indexed/Examples/AnBnCn.lean).
- `{aⁿbⁿcⁿ}` is recursively enumerable: [`Classes/RecursivelyEnumerable/Examples/AnBnCn.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/RecursivelyEnumerable/Examples/AnBnCn.lean).
- `{aⁿbⁿ}` is linear/context-free: [`Classes/ContextFree/Examples/AnBn.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Examples/AnBn.lean).

These examples supply the separating witnesses behind the
[strict Chomsky-hierarchy inclusions](chomsky-hierarchy-strict-inclusions.html).

## Proof idea

`{aⁿbⁿcⁿ}` is given by an explicit indexed grammar (and an unrestricted grammar for
the RE version). It is not context-free (`notCF_lang_eq_eq`, in
`Classes/ContextFree/Closure/Intersection.lean`): apply `CF_pumping` to
`aⁿ⁺¹bⁿ⁺¹cⁿ⁺¹` to get a decomposition `u v x y z` with `|vy| > 0` and `|vxy| ≤ n`.
The length bound forces the pumped factor `vy` to omit at least one of the three
letters. Pumping to `u v² x y² z` then keeps the omitted letter's count fixed at
`n+1` while `vy` contains at least one of the other two letters, raising its count
above `n+1` — contradicting the equal-count condition of `{aⁿbⁿcⁿ}`. The three
cases (whichever letter `vy` omits) are symmetric. See the
[pumping lemma for context-free languages](context-free-pumping-lemma.html).

## Keywords / also known as

anbncn not context-free, a^n b^n c^n indexed grammar, a^n b^n linear not regular,
classic non-context-free language, Chomsky hierarchy separating examples, pumping
lemma counterexample.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
