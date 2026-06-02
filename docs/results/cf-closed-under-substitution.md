---
title: "Substitution"
description: "A formal Lean 4 proof that context-free languages are closed under substitution, with union, concatenation, homomorphism and Kleene star derived as corollaries."
parent: Closure
nav_order: 1
grandparent: Context-free
---

# Context-free languages are closed under substitution

## Statement

A **substitution** replaces each terminal symbol `a` by an entire language `f a`: a
word `a₁…aₙ` is mapped to the set of all concatenations `w₁…wₙ` with `wᵢ ∈ f aᵢ`, and
this is extended to a language `L.subst f`. The theorem is that if `L` is context-free
**and** every `f a` is context-free, then `L.subst f` is context-free.

Substitution is the **master closure operation** for context-free languages: union,
concatenation, homomorphism, and Kleene star all fall out of it as one-line
corollaries (below), which is why Langlib proves it as a standalone development.

## In Lean

The core result:

- [`CF_of_subst_CF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Substitution.lean) — `is_CF L → (∀ a, is_CF (f a)) → is_CF (L.subst f)`.
- [`Language.IsContextFree.subst`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Substitution/Core.lean) — the same statement for Mathlib's `Language.IsContextFree`; the grammar construction `ContextFreeGrammar.subst` and its correctness `ContextFreeGrammar.subst_language_eq` live here too.

### Corollaries (each reduces to substitution)

- [`CF_of_CF_u_CF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Union.lean) — **union**: substitute into the two-letter language `{a, b}` (`a ↦ L₁`, `b ↦ L₂`).
- [`CF_of_CF_c_CF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Concatenation.lean) — **concatenation**: substitute into the single word `{ab}` (`a ↦ L₁`, `b ↦ L₂`).
- [`CF_closed_under_homomorphism`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Homomorphism.lean) — **homomorphism**: substitute each `a` by the singleton language `{h(a)}`; [`CF_closed_under_epsfree_homomorphism`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Homomorphism.lean) is the ε-free variant.
- [`CF_of_star_CF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Star.lean) — **Kleene star**, via the substitution-based [`Language.IsContextFree.kstar`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Closure/Substitution/Core.lean).

(Direct, substitution-free constructions for union and concatenation are also given as
"bonus" grammars, `bonus_CF_of_CF_u_CF` and `bonus_CF_of_CF_c_CF`.)

## Proof idea

Given a context-free grammar `g` for `L` and grammars `F a` for each `f a`, the
construction `ContextFreeGrammar.subst g f` builds a single grammar whose nonterminals
are the disjoint union `g.NT ⊕ (Σ a, (F a).NT)`. Every `g`-rule is kept but each
terminal `a` on a right-hand side is redirected to the *start symbol* of `F a`; all
rules of every `F a` are lifted in (tagged with `a`). A derivation in the combined
grammar first runs the `g`-phase down to a string of `F`-start-symbols and then runs
each `F`-phase independently — the two phases commute because the `F`-rules never
touch `g`-nonterminals (`derives_commute_of_not_mem_output`). Matching these two
phases against the definition of `L.subst f` gives the language equality.

## Keywords / also known as

context-free closed under substitution, CFL substitution theorem, context-free
closure properties, union concatenation homomorphism Kleene star context-free,
substitution master closure operation, Lean formal proof.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
