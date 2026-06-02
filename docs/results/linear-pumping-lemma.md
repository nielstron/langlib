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
- [`L4_not_is_Linear`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Inclusion/StrictContextFree.lean) — the concrete witness `{0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4` is not linear.
- [`Linear_strict_subclass_CF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Inclusion/StrictContextFree.lean) and [`Linear_strict_subclass_CF_of_card`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Inclusion/StrictContextFree.lean) — `Linear ⊊ CF` over `Fin 4`, and over any alphabet with `4 ≤ Fintype.card T`.
- [`Linear_not_closedUnderConcatenation`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Closure/Concatenation.lean) — corollary: `Linear` is not closed under concatenation (`{0ⁿ1ⁿ}·{2ᵐ3ᵐ}` is not linear).

## Proof idea

A linear grammar rewrites the unique nonterminal of every sentential form, so a
derivation `B ⇒* w` of a terminal word is a single *spine*: a chain of rules
`Cᵢ → uᵢ Cᵢ₊₁ vᵢ` (terminal `uᵢ`, `vᵢ`) ending in a terminal rule `C → m`. This is
reified as the inductive `Spine`; `exists_spine` (completeness) and `Spine.derives`
(soundness) tie it to `grammar_derives`.

The pumping length is `p = (S.card + 1) * (c + 1)`, where `S` is the finite set of
rule input-nonterminals and `c = maxRuleLen g` bounds the terminals one rule emits.
`Spine.splitAt s k` cuts the spine after `k` rules into a top derivation
`B ⇒* u·C·y` and an inner spine `C ⇒* wᶜ`; `Spine.cnt s k = |u| + |y|` counts the
terminals already emitted, which is monotone with increments `≤ c`
(`cnt_mono`, `cnt_step`) and reaches `≥ |w| − c` at full depth (`cnt_length_ge`).
The pigeonhole `exists_pump_indices` then finds depths `i < j` with the same
nonterminal `C` (`splitAt_add_C`), strictly increasing count, and `cnt j ≤ p`.
The segment between them is the self-embedding `C ⇒* v·C·y`; `pump_derives`
iterates it, and reassembling the top/inner derivations gives
`u vⁱ x yⁱ z ∈ L`. The bound `cnt j ≤ p` is exactly `|u v y z| ≤ p`.

To separate `Linear` from `CF`, the witness `L4 = {0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4` is
defined as `map f4 anbn * map g4 anbn` and is context-free (`L4_is_CF`, closure of
`CF` under concatenation). Applying the pumping lemma to `0ᵖ1ᵖ2ᵖ3ᵖ`, the outer
bound `|u v y z| ≤ p` confines `v` to the leading `0`-block and `y` to the trailing
`3`-block (`hv0`, `hy3`). Pumping down to `i = 0` deletes `v` and `y` while leaving
the `1`- and `2`-blocks untouched, so the symbol counts force `|v| = 0` and
`|y| = 0`, contradicting `v y` nonempty (`L4_not_is_Linear`). The result transports
to any alphabet with `4 ≤ Fintype.card T` by relabelling along an embedding
(`Linear_strict_subclass_CF_of_card`, using `is_Linear_of_map_injective`).
This concrete witness also shows that linear languages are not closed under concatenation, since {0ⁿ1ⁿ} and {2ᵐ3ᵐ} are both linear.


## Keywords / also known as

linear pumping lemma, linear languages not closed, Linear proper subset context-free,
caterpillar derivation, single-nonterminal grammar, language class separation.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
