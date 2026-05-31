---
title: "PDA = CFG: pushdown automata recognize exactly the context-free languages"
description: "A formal Lean 4 proof that pushdown automata and context-free grammars recognize exactly the same class of languages."
parent: "Context-free"
nav_order: 1
---

# Pushdown automata recognize exactly the context-free languages (PDA = CFG)

## Statement

A language is **context-free** if and only if it is recognized by a **pushdown
automaton** (PDA). The grammar model (context-free grammars) and the automaton
model (PDAs) define one and the same language class.

## In Lean

In `Automata/Pushdown/Equivalence/ContextFree.lean`:

- [`is_PDA_iff_isContextFree`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) — pointwise: `is_PDA L ↔ L.IsContextFree`.
- [`CF_eq_PDA_Class`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) — class equality `(CF : Set (Language T)) = PDA.Class`.
- [`is_PDA_of_isContextFree`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) and [`is_CF_of_is_PDA`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Pushdown/Equivalence/ContextFree.lean) — the two inclusions.

A related result, that **PDA acceptance by final state equals acceptance by empty
stack**, is proved in
[`FinalStateEmptyStackEquiv.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Pushdown/Basics/FinalStateEmptyStackEquiv.lean)
(`PDA_FS_subset_ES` and `PDA_ES_subset_FS`).

## Proof idea

From a CFG, build a one-state PDA that simulates leftmost derivations on its stack
(expand nonterminals, match terminals against the input). Conversely, from a PDA,
construct a grammar whose nonterminals are "triples" tracking the PDA's state
before and after popping a stack symbol; its derivations mirror accepting PDA runs.
Final-state and empty-stack acceptance are shown interconvertible, so either
acceptance mode characterizes the context-free languages.

## Keywords / also known as

PDA equals CFG, pushdown automata equal context-free grammars, context-free
languages are PDA-recognizable, CFG to PDA construction, PDA to CFG construction,
acceptance by final state equals acceptance by empty stack, Chomsky type-2
automaton characterization.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
