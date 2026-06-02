---
title: "Complement"
description: "A formal Lean 4 proof that the complement of a deterministic context-free language is again deterministic context-free."
parent: "Deterministic context-free"
nav_order: 2
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

The proof goes through **totalization**: a raw DPDA need not halt on every input, so the construction first turns it into an equivalent always-halting decider — see [DPDA totalization](dpda-totalization.html) — and only then flips its accepting states.

## In Lean

The headline theorem is
[`DCF_closedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean).

Supporting theorems:

- [`is_DCF_decider_complement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean) — complementation at the level of *deciding* DPDA presentations: `is_DCF_decider L → is_DCF_decider Lᶜ`.
- [`DCF_decider_closedUnderComplement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean) — the same, packaged as a `ClosedUnderComplement` statement.
- [`DCF_closedUnderComplement_of_decider_presentations`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Classes/DeterministicContextFree/Closure/Complement.lean) — the bridge: given `EveryDCFHasDeciderPresentation T`, the DCF class is closed under complement.

## Proof idea

A raw DPDA can diverge in forced epsilon moves or get stuck before reading the whole
input, so flipping accepting and non-accepting states does not complement the
language. The construction is the syntactic
[`DPDA.complement`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/ClosureProperties/Complement.lean):
keep `initial_state`, `start_symbol`, `transition`, `epsilon_transition`, and
`no_mixed`, and replace `final_states` by `final_statesᶜ`. Since reachability
depends only on the transitions, the complement DPDA has exactly the same runs
(`complement_toPDA_reaches`).

This complement is correct precisely when the DPDA **decides every input**
(`M.DecidesEveryInput`). `complement_acceptsByFinalState` shows that under totality
and acceptance consistency, `M.complement` accepts `(M.acceptsByFinalState)ᶜ`: a
word is rejected by `M` iff *no* reachable empty-input state is final, iff by
totality there is a reachable empty-input state and by consistency it is non-final,
iff `M.complement` accepts. `is_DCF_decider_complement` packages this, reusing the
same state and stack types and rechecking `DecidesEveryInput` for the complement.

To reach an arbitrary DCFL, `DCF_closedUnderComplement` first totalizes: every DCF
language has an equivalent deciding-DPDA presentation
([`everyDCFHasDeciderPresentation`](dpda-totalization.html)), to which the complement
construction then applies.

## Keywords / also known as

DCFL closed under complement, deterministic context-free languages complement,
DPDA complement, complement of a deterministic context-free language is
deterministic context-free, determinism closure property, complementation of
DPDA languages.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
