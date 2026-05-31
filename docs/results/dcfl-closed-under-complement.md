---
title: "DCFL is closed under complement"
description: "A formal Lean 4 proof that the complement of a deterministic context-free language is again deterministic context-free."
---

# Deterministic context-free languages are closed under complement

## Statement

If a language `L` is **deterministic context-free** (DCF) — i.e. recognized by a
deterministic pushdown automaton (DPDA) by final state — then its complement
`Lᶜ` is also deterministic context-free. The class **DCFL** is closed under
complementation.

This is the classic separating property between deterministic and general
context-free languages: ordinary (nondeterministic) context-free languages are
**not** closed under complement, while DCFLs are.

## In Lean

The headline theorem is
[`DCF_closedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean)
in `Classes/DeterministicContextFree/Closure/Complement.lean`.

Supporting theorems in the same file:

- [`DCF_decider_closedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean) — complementation at the level of *deciding* DPDA presentations.
- [`DCF_closedUnderComplement_of_decider_presentations`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean) — the bridge from decider presentations to the language class.

## Proof idea

A raw DPDA can loop forever (in epsilon moves) or get stuck, so you cannot
complement it just by flipping accepting and non-accepting states. The proof
first **totalizes** the DPDA into an equivalent *deciding* DPDA that always halts
and reads its entire input — see the companion page on
[DPDA totalization](dpda-totalization.html). Once you have a total, always-halting
DPDA presentation, the complement is obtained by complementing the set of
accepting final states, and totalization guarantees this still recognizes exactly
`Lᶜ`.

## Keywords / also known as

DCFL closed under complement, deterministic context-free languages complement,
DPDA complement, complement of a deterministic context-free language is
deterministic context-free, determinism closure property, complementation of
DPDA languages.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
