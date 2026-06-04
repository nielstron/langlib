---
title: "Ogden's lemma"
description: "A formal Lean 4 proof of Ogden's lemma — the marked-position strengthening of the context-free pumping lemma."
parent: Pumping lemmas
nav_order: 2
grandparent: Context-free
---

# Ogden's lemma for context-free languages

## Statement

Ogden's lemma strengthens the [context-free pumping lemma](context-free-pumping-lemma.html)
by letting you **mark** distinguished positions that the pump is forced to touch.

For every context-free language `L` there is a constant `p` such that for any word
`w ∈ L`, if at least `p` of the positions of `w` are *marked*, then `w` splits as
`w = u v x y z` with

- **at least one marked position inside `v` or `y`** (so the pumped parts are not
  trivial with respect to the marks),
- **at most `p` marked positions inside `v x y`**, and
- every pumped word `u vⁱ x yⁱ z` (for all `i ≥ 0`) is again in `L`.

Taking *every* position to be marked recovers the ordinary pumping lemma, so Ogden's
lemma is strictly stronger. It proves non-context-freeness of languages the plain
pumping lemma cannot handle, and is the standard tool for showing **inherent
ambiguity** of context-free languages.

## In Lean

- [`CF_ogdens_lemma`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Basics/Ogden.lean) — Ogden's lemma for `is_CF` languages (project formulation).
- [`Language.IsContextFree.ogdens_lemma`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Basics/Ogden.lean) — the same result for Mathlib's `Language.IsContextFree`.

The marking is captured by a predicate `P : ℕ → Prop` on positions, and
`countMarkedIn P start len` counts how many marked positions fall in a span — this
is what makes the "≥ p marked" hypothesis and the "marked positions in `v x y` ≤ p"
conclusion precise.

## Proof idea

Put the grammar in Chomsky normal form (`toCNF`); the pumping constant is
`p = 2 ^ g.generators.card`. `CF_ogdens_lemma` and `Language.IsContextFree.ogdens_lemma`
both reduce to `ogdens_cnf` on CNF parse trees.

Instead of plain height, the argument uses the **marked branching height**
`markedHeight`: the maximum number of *branching* nodes — `node` rules where both
children have a marked descendant — on any root-to-leaf path. The marked count of a
subtree satisfies `mc ≤ 2 ^ markedHeight` (`mc_le_pow_markedHeight`), so a yield with
`≥ p` marked positions forces `markedHeight ≥ generators.card`.

`ogdens_restrict_mh` navigates down the marked path to a subtree of marked height
exactly `generators.card`. On that subtree `ogdens_marked_path_decomp` runs the core
pigeonhole: descending toward the more-marked child and recording branching
nonterminals in a finite set `s ⊆ g.generators`, once `generators.card` branching
nodes accumulate some nonterminal `n'` must repeat. Excising or duplicating the
subtree between the two occurrences of `n'` (`pumping_string`, via the
`ogden_pump_from_left` / `ogden_pump_from_right` cases) produces the family
`u vⁱ x yⁱ z ∈ g.language`. Because each step was taken along a *branching* node, the
repeated nonterminal brackets at least one marked position in `v` or `y`; the bounded
marked height caps the marked positions of `vxy` by `p`.

## Keywords / also known as

Ogden's lemma, marked pumping lemma for context-free languages, inherent ambiguity
of context-free languages, strengthening of the CFL pumping lemma, proving a
language is not context-free, Ogden's lemma Lean proof.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
