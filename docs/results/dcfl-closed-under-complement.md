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

The headline theorem is `DCF_closedUnderComplement`, a thin re-export of the
automaton-level `is_DCF_closedUnderComplement`.

Supporting theorems:

- `is_DCF_complement` — the language-level step `is_DCF L → is_DCF Lᶜ`: totalize an arbitrary DPDA, then complement it.
- `is_DCF_total_complement` — complementation at the level of *total* DPDA presentations: `is_DCF_total L → is_DCF_total Lᶜ`.
- `DPDA.complement_isTotal` — complementing a total DPDA yields a total DPDA.
- `DPDA.complement_acceptsByFinalState` — for a total DPDA, `M.complement` accepts `(M.acceptsByFinalState)ᶜ`.

## Proof idea

A raw DPDA can diverge in forced epsilon moves or get stuck before reading the whole
input, so flipping accepting and non-accepting states does not complement the
language. The construction is the syntactic `DPDA.complement`:
keep `initial_state`, `start_symbol`, `transition`, `epsilon_transition`, and
`no_mixed`, and replace `final_states` by `final_statesᶜ`. Since reachability
depends only on the transitions, the complement DPDA has exactly the same runs
(`complement_toPDA_reaches`).

This complement is correct precisely when the DPDA is **total**
(`M.IsTotal`). `complement_acceptsByFinalState` shows that under totality
and acceptance consistency, `M.complement` accepts `(M.acceptsByFinalState)ᶜ`: a
word is rejected by `M` iff *no* reachable empty-input state is final, iff by
totality there is a reachable empty-input state and by consistency it is non-final,
iff `M.complement` accepts. `complement_isTotal` shows the complement is again total,
reusing the same state and stack types.

To reach an arbitrary DCFL, `is_DCF_complement` first totalizes: every DPDA
has an equivalent total DPDA (`DPDA.exists_equivalent_total`), to which the complement
construction then applies.

## Keywords / also known as

DCFL closed under complement, deterministic context-free languages complement,
DPDA complement, complement of a deterministic context-free language is
deterministic context-free, determinism closure property, complementation of
DPDA languages.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
