---
title: "Pumping lemma"
description: "A formal Lean 4 proof of the pumping lemma (and Ogden's lemma) for context-free languages."
parent: Pumping lemmas
nav_order: 1
grandparent: Context-free
---

# The pumping lemma for context-free languages

## Statement

For every context-free language `L` there is a constant `n` such that any word
`z ∈ L` with `|z| ≥ n` can be split as `z = u v w x y` with `|vwx| ≤ n` and
`vx ≠ ε`, so that all "pumped" words `u vⁱ w xⁱ y` (for every `i ≥ 0`) again lie in
`L`. This is the standard tool for proving that a language is **not** context-free.

## In Lean

The pumping lemma for `is_CF` languages is `CF_pumping`.

A stronger refinement, **Ogden's lemma** (which lets you *mark* distinguished
positions that must be pumped), is `CF_ogdens_lemma`.

## Proof idea

Put the grammar in Chomsky normal form (`toCNF`); the pumping length is
`n = 2 ^ g.generators.card`, where `generators` is the set of nonterminals appearing
on rule left-hand sides. `CF_pumping` transports the result from Mathlib's
`Language.IsContextFree.pumping` along `is_CF_iff_isContextFree`.

A word `w ∈ g.language` of length `≥ n` has a parse tree (`Derives.yield`). Since a
CNF tree of height `h` yields at most `2 ^ h` terminals, height `> generators.card`
is forced, so by pigeonhole (`pidgeonhole`, applied in
`subtree_repeat_root_height`) some nonterminal `n'` repeats on a root-to-leaf path:
two subtrees `p₁`, `p₂` of root label `n'` with `p₂` a strict subtree of `p₁` and
`p₁.height ≤ generators.card + 1`. Decomposing the outer tree (`subtree_decomposition`,
`strict_subtree_decomposition`) writes `w = u v x y z` with `x` the yield of `p₂`.
Because `p₂` is a *strict* subtree, `vy ≠ ε`; the height bound on `p₁` gives
`|vxy| ≤ n`. `pumping_string` iterates the derivation
`n' ⇒* v · n' · y` to obtain `n' ⇒* vⁱ · n' · yⁱ` for every `i`, yielding the family
`u vⁱ x yⁱ z ∈ g.language`.

## Keywords / also known as

context-free pumping lemma, CFL pumping lemma, uvwxy theorem, Bar-Hillel lemma,
Ogden's lemma, proving a language is not context-free, pumping lemma Lean proof.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
