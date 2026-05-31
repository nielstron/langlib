---
title: "Langlib's context-free languages equal Mathlib's IsContextFree"
description: "A formal Lean 4 proof that Langlib's notion of context-free language coincides with Mathlib's IsContextFree, and a verified Chomsky normal form."
parent: "Context-free"
nav_order: 4
---

# Langlib's context-free languages coincide with Mathlib's `IsContextFree`

## Statement

Langlib's predicate `is_CF` (context-free via its own grammar definition) agrees
exactly with Mathlib's `Language.IsContextFree`. This connects the development to the
broader Mathlib computability/formal-language library, so results transfer both
ways. The library also formalizes **Chomsky normal form** for context-free
grammars.

## In Lean

- Equivalence with Mathlib: [`is_CF_iff_isContextFree`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Grammars/ContextFree/EquivMathlibCFG.lean) in `Grammars/ContextFree/EquivMathlibCFG.lean`.
- Chomsky normal form: [`ChomskyNormalFormGrammar`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/ContextFree/NormalForms/ChomskyNormalForm.lean) and its `language` / `mem_language_iff` in `Classes/ContextFree/NormalForms/ChomskyNormalForm.lean`.

## Proof idea

Both definitions describe derivations of a context-free grammar; the proof
translates grammars in each direction, matching their generated languages.
Chomsky normal form is obtained by the standard pipeline — eliminate ε-rules, unit
rules, and long/terminal-mixing right-hand sides — each step shown to preserve the
language (minus the empty word).

## Keywords / also known as

context-free equals Mathlib IsContextFree, Langlib CFG Mathlib compatibility,
Chomsky normal form Lean, CNF context-free grammar, epsilon elimination unit
elimination, normalizing context-free grammars.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
