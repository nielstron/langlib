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

Both definitions describe terminal-yielding derivations of a context-free grammar;
they differ only in how a grammar is packaged (Langlib's `CF_grammar` carries a rule
*list*, Mathlib's `ContextFreeGrammar` a rule *finset* over `Symbol`). The proof
gives translations `mathlib_cfg_of_cfg` and `cfg_of_mathlib_cfg` between the two,
mapping rules symbol-by-symbol via `Symbol_of_symbol` / `symbol_of_Symbol`.
`CF_language_eq_mathlib_language` shows the generated languages agree, by induction
on the derivation relation in each direction (`CF_derives` vs.
`ContextFreeGrammar.Derives`), matching single rewrite steps via
`ContextFreeRule.Rewrites.exists_parts`. `is_CF_iff_isContextFree` combines this with
the round-trip identity `mathlib_cfg_of_cfg_of_mathlib_cfg`.

Chomsky normal form is obtained by the pipeline `toCNF =
eliminateEmpty.eliminateUnitRules.restrictTerminals.restrictLength`: eliminate
ε-rules, eliminate unit rules, replace terminals in mixed right-hand sides by fresh
nonterminals, then split long right-hand sides into binary ones. `toCNF_correct`
proves `g.language \ {[]} = g.toCNF.language` — each stage preserves the language up
to the empty word.

## Keywords / also known as

context-free equals Mathlib IsContextFree, Langlib CFG Mathlib compatibility,
Chomsky normal form Lean, CNF context-free grammar, epsilon elimination unit
elimination, normalizing context-free grammars.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
