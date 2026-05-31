---
title: "Pumping lemma for linear languages"
description: "A formal Lean 4 proof of the pumping lemma for linear languages, used to show {0ⁿ1ⁿ2ᵐ3ᵐ} is context-free but not linear, hence Linear ⊊ CF."
parent: "Linear"
nav_order: 2
---

# Pumping lemma for linear languages

## Statement

Every linear language `L` has a constant `p` such that any word `w ∈ L` with
`|w| ≥ p` can be split as `w = u v x y z` with

- `v y` nonempty (`(v ++ y).length > 0`),
- the **outer** material bounded: `(u ++ v ++ y ++ z).length ≤ p`,
- `u vⁱ x yⁱ z ∈ L` for every `i`.

The decisive difference from the [context-free pumping lemma](context-free-pumping-lemma.html)
is the bound: there the *middle* `v x y` is bounded, while here the *outer* pieces
`u v y z` are bounded. This forces the pumped pieces `v` and `y` to lie close to the
two ends of `w`, which is exactly what a single-nonterminal "caterpillar" derivation
of a linear grammar produces.

## In Lean

- [`is_Linear.pumping`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Pumping/Pumping.lean) — the pumping lemma.
- [`Spine`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Pumping/Spine.lean) — the reified single-nonterminal derivation, with soundness/completeness against `grammar_derives`.
- [`L4_not_is_Linear`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Inclusion/StrictContextFree.lean) — `{0ⁿ1ⁿ2ᵐ3ᵐ}` is not linear.
- [`Linear_strict_subclass_CF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Inclusion/StrictContextFree.lean) — `Linear ⊊ CF`.

## Proof idea

A linear grammar rewrites the unique nonterminal of every sentential form, so a
derivation `B ⇒* w` of a terminal word is a single *spine*: a chain of rules
`Cᵢ → uᵢ Cᵢ₊₁ vᵢ` ending in a terminal rule `C → m`. This is reified as the
inductive `Spine`, proven equivalent to `grammar_derives`.

`splitAt` cuts a spine at a given depth into a top derivation `B ⇒* u·C·y` and an
inner spine `C ⇒* wᶜ`. Tracking the number of terminals produced by depth `k`
(`cnt`), a pigeonhole over the finitely many rule nonterminals finds two depths
`i < j` with the same nonterminal `C`, strictly increasing count, and `cnt j ≤ p`.
The segment between them gives the pump `C ⇒* v·C·y`, and iterating it yields
`u vⁱ x yⁱ z ∈ L`.

To separate `Linear` from `CF`, the language `{0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4` is
context-free (a concatenation of two copies of `{aⁿbⁿ}`). Applying the pumping
lemma to `0ᵖ1ᵖ2ᵖ3ᵖ`, the bound confines `v` to the leading `0`-block and `y` to the
trailing `3`-block; pumping down then unbalances either `#0 = #1` or `#2 = #3`,
contradicting membership.

## Keywords / also known as

linear pumping lemma, linear languages not closed, Linear proper subset context-free,
caterpillar derivation, single-nonterminal grammar, language class separation.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
