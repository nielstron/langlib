---
title: "Linear grammars and the linear languages"
description: "Lean 4 definition of linear grammars and the linear language class, with formal proofs that regular ⊊ linear ⊆ context-free and that {aⁿbⁿ} is linear."
parent: "Linear"
nav_order: 1
---

# Linear grammars and the linear languages

## Statement

A **linear grammar** is a context-free grammar in which every rule's right-hand side
contains **at most one nonterminal** (so each sentential form has a single
nonterminal). The languages they generate, the **linear languages**, sit strictly
between the regular and the context-free languages:

> regular ⊊ **linear** ⊆ context-free.

The witness for the first strict inclusion is `{aⁿbⁿ}`, which is linear (one
nonterminal grows the word symmetrically from the middle) but not regular.

## In Lean

Definitions:

- [`grammar_linear`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Definition.lean) — predicate that a grammar is linear, via [`linear_output`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Definition.lean) (a sentential form has at most one nonterminal).
- [`is_Linear`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Definition.lean) / [`Linear`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Definition.lean) — the linear-language predicate and class.

Inclusions:

- [`RG_subclass_Linear`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Inclusion/Linear.lean) / [`is_Linear_of_is_RG`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Inclusion/Linear.lean) — every regular language is linear.
- [`RG_strict_subclass_Linear`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Inclusion/StrictLinear.lean) — regular is a **strict** subclass of linear.
- [`Linear_subclass_CF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Inclusion/ContextFree.lean) — every linear language is context-free.

Example:

- [`anbn_is_Linear`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Examples/AnBn.lean) — `{aⁿbⁿ}` is linear, via the explicit [`linear_grammar_anbn`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Examples/AnBn.lean).

## Proof idea

Linearity is `grammar_linear`: every rule is context-free (empty left/right context)
and its output satisfies `linear_output`, i.e. is either purely terminal or
`map terminal u ++ [nonterminal B] ++ map terminal v` (at most one nonterminal).

**`RG ⊆ Linear`.** A right-regular output (`aB`, `a`, or `ε`) is in particular a
linear output (`linear_output_of_right_regular`), so a right-regular grammar is
linear (`grammar_linear_of_right_regular`); `is_Linear_of_is_RG` reuses the same
grammar.

**Strictness.** The witness is `anbn = {aⁿbⁿ}`, shown linear by the explicit grammar
`linear_grammar_anbn` with rules `S → aSb` and `S → ε` (`anbn_is_Linear`, via
`linear_grammar_anbn_language`). It is not regular (`anbn_not_isRegular`). Pushing
the witness along an injective letter map (`map_anbn_is_Linear`,
`map_anbn_not_isRegular`) makes `RG_strict_subclass_Linear` hold over any nontrivial
alphabet: were `Linear ⊆ RG`, the mapped `anbn` would be regular, contradicting
non-regularity.

**`Linear ⊆ CF`.** A linear rule already satisfies the context-free condition
(`grammar_context_free_of_linear` just drops the `linear_output` clause), so
`is_CF_of_is_Linear` and `Linear_subclass_CF` are immediate. (Strictness of this
inclusion is in [the linear pumping lemma](linear-pumping-lemma.html).)

## Keywords / also known as

linear grammar, linear language, linear context-free grammar, regular subset linear
subset context-free, {a^n b^n} is linear, one-nonterminal grammar, Chomsky hierarchy
linear languages, Lean formalization.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
