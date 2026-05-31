---
title: "Ogden's lemma for context-free languages"
description: "A formal Lean 4 proof of Ogden's lemma — the marked-position strengthening of the context-free pumping lemma."
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

In [`Classes/ContextFree/Basics/Ogden.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Basics/Ogden.lean):

- [`CF_ogdens_lemma`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Basics/Ogden.lean) — Ogden's lemma for `is_CF` languages (project formulation).
- [`Language.IsContextFree.ogdens_lemma`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Basics/Ogden.lean) — the same result for Mathlib's `Language.IsContextFree`.

The marking is captured by a predicate `P : ℕ → Prop` on positions, and
`countMarkedIn P start len` counts how many marked positions fall in a span — this
is what makes the "≥ p marked" hypothesis and the "marked positions in `v x y` ≤ p"
conclusion precise.

## Proof idea

Put the grammar in Chomsky normal form and look at the parse tree of `w`. Follow a
root-to-leaf path that always descends toward the subtree containing the most marked
positions (the *marked* path). If enough positions are marked, this path is long
enough that some nonterminal repeats on it. Excising or duplicating the subtree
between the two occurrences produces the family `u vⁱ x yⁱ z`; because the path was
chosen along the marks, the repeated nonterminal brackets at least one marked
position, giving the "marked position inside `v` or `y`" guarantee that the
unmarked pumping lemma lacks.

## Keywords / also known as

Ogden's lemma, marked pumping lemma for context-free languages, inherent ambiguity
of context-free languages, strengthening of the CFL pumping lemma, proving a
language is not context-free, Ogden's lemma Lean proof.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
