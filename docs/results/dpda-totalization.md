---
title: "DPDA totalization"
description: "Every deterministic pushdown automaton can be transformed into an equivalent total, always-halting deciding DPDA, formalized in Lean 4."
parent: "Deterministic context-free"
nav_order: 2
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

The construction lives in `Automata/DeterministicPushdown/Totalization/`. Key
declarations:

- [`totalizer_is_DCF_decider`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/Totalization/Presentation.lean) — the analyzed totalizer is a *deciding* DPDA presentation of the same language.
- [`everyDPDAHasRegularEpsilonAnalysis`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/Totalization/Presentation.lean) — every finite DPDA admits the regular epsilon analysis the totalizer needs.
- [`everyDCFHasDeciderPresentation`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/Totalization/Presentation.lean) — consequently, every deterministic context-free language has a deciding DPDA presentation.

The supporting modules — `AnnotatedStack`, `Construction`, `EpsilonPhase`,
`RegularAnalysis`, `Saturation`, `StackSummary` — build up the construction
piece by piece. See the umbrella file
[`Totalization.lean`](https://github.com/nielstron/langlib/blob/main/src/Langlib/Automata/DeterministicPushdown/Totalization.lean).

## Proof idea

The danger is unbounded epsilon (input-free) computation that either loops forever
or grows the stack without bound. The construction performs a **regular epsilon
analysis**: it summarizes each maximal epsilon phase via finite stack summaries and
detects looping/divergent phases, *saturating* the configuration so that the
machine can always make a decisive move on the next input symbol (or at end of
input) instead of diverging. The resulting *totalizer* halts on every input, reads
the whole word, and accepts exactly the original language.

## Keywords / also known as

DPDA totalization, total deterministic pushdown automaton, making a DPDA halt,
always-halting DPDA, deciding DPDA, deterministic PDA completion, epsilon-loop
elimination for pushdown automata, DPDA decider presentation.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
