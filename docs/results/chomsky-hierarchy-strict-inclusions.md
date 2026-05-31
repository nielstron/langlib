---
title: "Chomsky hierarchy"
description: "Lean 4 proofs that each level of the Chomsky hierarchy strictly contains the level below: Regular ⊊ DCFL ⊊ CFL ⊊ Indexed, and Recursive ⊊ RE."
nav_order: 2
---

# The Chomsky hierarchy is strict

## Statement

Each language class in the Chomsky hierarchy strictly contains the one below it.
Langlib already formalizes the following strict inclusions:

- **Regular ⊊ Deterministic context-free ⊊ Context-free ⊊ Context Sensitive ⊆ Recursive ⊊ Recursively enumerable **
- **Context-free ⊊ Indexed**
- **Regular ⊊ Linear ⊊ CFL**

## In Lean

- Regular ⊊ DCFL: [`RG_strict_subclass_DCF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Inclusion/StrictDeterministicContextFree.lean).
- Regular ⊊ Linear: [`Classes/Regular/Inclusion/StrictLinear.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Regular/Inclusion/StrictLinear.lean); Linear ⊆ CF: [`Classes/Linear/Inclusion/ContextFree.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/Linear/Inclusion/ContextFree.lean).
- DCFL ⊊ CFL: [`is_CF_of_is_DCF` / `DCF_subclass_CF`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Inclusion/ContextFree.lean) (strictness via [`Inclusion/StrictPushdown.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/Inclusion/StrictPushdown.lean)).
- CFL ⊊ Indexed: [`CF_strict_subclass_Indexed`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Inclusion/StrictIndexed.lean) and [`CF_subclass_Indexed_and_exists_strict`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Inclusion/StrictIndexed.lean).
- CF ⊆ CS: [`Classes/ContextFree/Inclusion/ContextSensitive.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/Inclusion/ContextSensitive.lean).
- Recursive ⊊ RE: see the [dedicated page](recursive-strict-subset-re.html).

## Proof idea

Each strict inclusion combines an *inclusion* (every grammar/automaton of the lower
class is one of the upper class) with a *separating witness* language that lives in
the upper class but provably not the lower one — e.g. a non-regular DCFL such as
`{aⁿbⁿ}`, and the indexed-but-not-context-free `{aⁿbⁿcⁿ}`.

## Keywords / also known as

Chomsky hierarchy strict, regular proper subset context-free, DCFL proper subset
CFL, context-free proper subset indexed, recursive proper subset recursively
enumerable, language class separations, proper containment Chomsky hierarchy.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
