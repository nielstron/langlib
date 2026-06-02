---
title: "Acceptance modes"
description: "A formal Lean 4 proof that pushdown automata accepting by final state and by empty stack recognize the same class of languages."
parent: "Equivalences"
grandparent: "Context-free"
nav_order: 3
---

# Final-state and empty-stack acceptance coincide

## Statement

A pushdown automaton can be equipped with either of two acceptance conditions: it accepts a
word **by final state** if some run on it ends in an accepting state, or **by empty stack**
if some run ends with the stack empty. For pushdown automata these two conditions define the
**same class** of languages — and hence, together with [PDA = CFG](pda-equals-cfg.html),
exactly the context-free languages.

## In Lean

- `PDA_FS_subset_ES` — every final-state language is also an empty-stack language.
- `PDA_ES_subset_FS` — and conversely.
- `is_PDA_finalState_iff_is_PDA_emptyStack` — the resulting equivalence on languages;
  `PDA_FinalStateClass_eq_EmptyStackClass` is the class-level statement, and
  `is_PDA_finalState_iff_is_PDA` identifies both with the canonical PDA class.

## Proof idea

Both directions augment the automaton with a fresh **bottom-of-stack marker** and two
bookkeeping states (`Fin 2`).

- **Final state → empty stack** (`PDA_FS_to_ES_pda`). The new machine first pushes `M`'s
  start symbol on top of a fresh marker `none`, then simulates `M` on the marked stack.
  Whenever `M` is in a final state it may take an ε-move into a *drain* state that pops the
  entire stack — marker included — to empty. The marker guarantees the stack is never
  emptied *during* simulation, so the new machine empties its stack exactly when `M` would
  have accepted by final state.
- **Empty stack → final state** (`PDA_ES_to_FS`). Symmetrically, the new machine simulates
  `M` above a fresh marker; when that marker becomes exposed — i.e. `M`'s own stack has
  emptied — it moves to a designated final state.

Each direction pairs a forward simulation (`simulation_reaches` / `ES_simulation_reaches`)
with a reachability invariant (`FSES_Inv` / `ESFS_Inv`) that is established at the initial
configuration and matched at accepting configurations, giving language equality.

## Keywords / also known as

PDA acceptance by final state equals acceptance by empty stack, empty-stack acceptance,
final-state acceptance, pushdown automaton acceptance modes, type-2 languages.

Formalized in Lean 4 with Mathlib, in [Langlib](https://github.com/nielstron/langlib).
