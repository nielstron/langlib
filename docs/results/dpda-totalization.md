---
title: "DPDA totalization"
description: "Every deterministic pushdown automaton can be transformed into an equivalent total, always-halting deciding DPDA, formalized in Lean 4."
parent: "Deterministic context-free"
nav_order: 1
---

# DPDA totalization: every DPDA has an equivalent always-halting deciding DPDA

## Statement

A deterministic pushdown automaton (DPDA) may fail to read its whole input: it can
reject by getting stuck, or diverge in an infinite chain of epsilon (stack-only)
moves. **Totalization** rebuilds any DPDA into an equivalent *total*, always-halting
DPDA that consumes its entire input and ends in a well-defined accepting or
rejecting state, while recognizing exactly the same language.

This construction is the engine behind
[DCFL being closed under complement](dcfl-closed-under-complement.html): once a DPDA
is total, you can complement it by flipping its accepting states.

## In Lean

The target normal form is [`is_DCF_decider`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/Totalization/Definition.lean):
a final-state DPDA presentation `M` of `L` with
`M.DecidesEveryInput` — for every input `w`, `M` reaches some empty-input
configuration (totality), and all empty-input configurations reachable on `w` agree
on final-state membership (acceptance consistency). Key declarations:

- [`totalizer_is_DCF_decider`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/Totalization/Presentation.lean) — from a `RegularEpsilonAnalysis A` of `M`, the `totalizer A` is a deciding DPDA presentation of `M.acceptsByFinalState`; combines `totalizer_decides` and `totalizer_acceptsByFinalState_eq_original`.
- [`everyDPDAHasRegularEpsilonAnalysis`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/Totalization/Presentation.lean) — every finite DPDA admits a regular epsilon analysis, via the saturation construction `hasRegularEpsilonAnalysis`.
- [`everyDCFHasDeciderPresentation`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/Totalization/Presentation.lean) — consequently, every deterministic context-free language has a deciding DPDA presentation.

## Proof idea

The danger is unbounded *forced epsilon* (input-free) computation. A DPDA's
`no_mixed` condition makes each stack top either epsilon-driven or input-driven, so
between input symbols the machine runs a deterministic epsilon phase whose
control/stack motion `EpsilonStep` is captured by `epsilonNext?`. By
`epsilonPhase_stops_or_diverges`, each such phase either reaches an `EpsilonStable`
configuration (`EpsilonStopsAt`) or diverges (`EpsilonDiverges`); a divergent phase
never consumes input and so must be treated as a halting decision point.

**Regular epsilon analysis.** The totalizer needs to answer two questions about the
phase from a configuration `(q, γ)` using only finite, stack-regular lookahead,
packaged as a `RegularEpsilonAnalysis`: a per-state DFA
`stopDFA` deciding whether the phase reaches a stable configuration
(`stop_correct`), and a per-state DFA `acceptDFA` deciding whether the phase passes
through a final state (`accept_correct`). Existence
(`regularEpsilonAnalysisOfSaturation`) comes from a P-automaton **saturation**
construction over the finite state set `PAutState Q = Q ⊕ Unit`.
Both DFA queries are evaluated incrementally against the stack by storing, with each
stack symbol, the DFA transition summary `σ → σ` of the suffix below it
(`DFA.stackSummary`); since the DFA state type is finite, the
summary type is finite, so the totalizer's stack alphabet stays finite.

**The totalizer.** `totalizer A` has finite control `TotalState Q` with three
constructors: `init`, `sim q b` (simulating original state `q`, with boolean `b`
recording whether the original machine would accept if input ended at the current
stack), and a rejecting `drain`. On each input symbol it follows `M`'s
input-transition where one exists, recomputing the accept bit from the stack
summary; at a stack top whose epsilon phase does not stop (`stopsFromSummary` is
false, i.e. divergence) and at a missing input transition it moves to `drain` and
consumes the rest of the input. Epsilon transitions of the totalizer replay only
*stopping* phases of `M`. This yields `totalizer_total` (every input reaches an
empty-input configuration) and `totalizer_final_consistent` (acceptance
consistency), i.e. `totalizer_decides`, and
`totalizer_acceptsByFinalState_eq_original` (same language).

## Keywords / also known as

DPDA totalization, total deterministic pushdown automaton, making a DPDA halt,
always-halting DPDA, deciding DPDA, deterministic PDA completion, epsilon-loop
elimination for pushdown automata, DPDA decider presentation.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
