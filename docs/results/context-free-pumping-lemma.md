---
title: "Pumping lemma for context-free languages"
description: "A formal Lean 4 proof of the pumping lemma (and Ogden's lemma) for context-free languages."
---

# The pumping lemma for context-free languages

## Statement

For every context-free language `L` there is a constant `n` such that any word
`z ∈ L` with `|z| ≥ n` can be split as `z = u v w x y` with `|vwx| ≤ n` and
`vx ≠ ε`, so that all "pumped" words `u vⁱ w xⁱ y` (for every `i ≥ 0`) again lie in
`L`. This is the standard tool for proving that a language is **not** context-free.

## In Lean

In `Classes/ContextFree/Basics/Pumping.lean`:

- [`CF_pumping`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Basics/Pumping.lean) — the pumping lemma for `is_CF` languages.

A stronger refinement, **Ogden's lemma** (which lets you *mark* distinguished
positions that must be pumped), is in
[`Classes/ContextFree/Basics/Ogden.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Basics/Ogden.lean).
The detailed parse-tree machinery lives under
[`Classes/ContextFree/Pumping/`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Pumping).

## Proof idea

Put the grammar in Chomsky normal form. A sufficiently long word has a parse tree
deep enough that some nonterminal repeats on a root-to-leaf path. The subtree
between the two occurrences can be excised or duplicated arbitrarily, which yields
exactly the `u vⁱ w xⁱ y` pumping family; the depth bound gives `|vwx| ≤ n` and the
binary branching of CNF gives `vx ≠ ε`.

## Keywords / also known as

context-free pumping lemma, CFL pumping lemma, uvwxy theorem, Bar-Hillel lemma,
Ogden's lemma, proving a language is not context-free, pumping lemma Lean proof.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
