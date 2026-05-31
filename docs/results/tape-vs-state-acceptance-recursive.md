---
title: "Tape acceptance implies state acceptance for recursive languages"
description: "A formal Lean 4 proof that tape-symbol acceptance can be repackaged as final-state acceptance for recursive (decidable) Turing-machine languages."
parent: "Recursive"
nav_order: 3
---

# Tape acceptance implies state acceptance for recursive languages

## Statement

There are two natural ways to read off a Turing machine's verdict on an always-halting
computation: from the **state** it halts in, or from the **symbol written under the
head** when it halts.

Langlib proves the **forward direction**: every language recognized by *tape-symbol*
acceptance is also recognized by the usual *state-based* acceptance
(`is_Recursive_byTape L → is_Recursive L`). The converse — repackaging a
state-based machine so that it announces its verdict on the tape — is routine but is
**not yet formalized**, so this is currently a one-directional result rather than a
full equivalence.

The forward direction is the one that is actually needed: `Code → TM` translation
chains naturally expose their answer on the tape, and this result lets them be
repackaged as state-based recursive languages.

## In Lean

In `Automata/Recursive/Equivalence/TapeCharacterization.lean`:

- [`is_Recursive_of_byTape`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Recursive/Equivalence/TapeCharacterization.lean) — `is_Recursive_byTape L → is_Recursive L`.

The tape-acceptance predicate `is_Recursive_byTape` itself is defined in
[`Automata/Recursive/Basic/TapeCharacterization`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/Recursive/Basic/TapeCharacterization.lean).
The reverse implication (`is_Recursive L → is_Recursive_byTape L`) is not currently
in the library.

## Proof idea

Given a machine `M` that halts with its answer written under the head, the
`readerMachine` runs `M` unchanged; at the instant `M` would halt, it reads the
symbol `γ` under the head and transitions into a distinguished halting state
`Sum.inr (decide (γ = acceptSym))` that records the verdict. The state-based
acceptance predicate then just reads that Boolean off the halting state.

## Keywords / also known as

Turing machine tape acceptance vs state acceptance, accept by halting state vs
accept by output symbol, recursive language acceptance, TM0 reader machine,
deciding by tape symbol.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
