/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.Pushdown.Basics.PDA

/-! # Deterministic Pushdown Automata (DPDAs)

This file introduces deterministic pushdown automata (DPDAs) as a refinement of the
nondeterministic pushdown automata (PDAs) defined in `Grammars.Automata.Pushdown.Basics.PDA`.

## Overview

A DPDA is a PDA whose transition function is *deterministic*: at each step, the automaton has
at most one possible move. This is enforced in two ways:

1. The transition functions return `Option (Q × List S)` instead of `Set (Q × List S)`,
   so each `(state, input, stack-top)` triple determines at most one successor.

2. The `no_mixed` field ensures that if an ε-transition is defined for a given `(state, stack-top)`
   pair, then no input-reading transition is defined for that pair with any input symbol.

## Main declarations

- `DPDA` — the structure for a deterministic pushdown automaton
- `DPDA.toPDA` — forgetful embedding of a DPDA into the nondeterministic PDA framework
- `DPDA.acceptsByFinalState` — language accepted by a DPDA via final-state acceptance
- `DPDA.complement` — the DPDA obtained by complementing the set of accepting states

## References

* Hopcroft, Motwani, Ullman. *Introduction to Automata Theory, Languages, and Computation*,
  3rd ed. Section 6.4.
-/

open PDA

/-- A **Deterministic Pushdown Automaton (DPDA)** over state type `Q`,
    input alphabet `T`, and stack alphabet `S`.

    The key difference from a (nondeterministic) `PDA` is that the transition functions
    return `Option` values instead of `Set` values, enforcing at most one transition
    per configuration. The `no_mixed` field additionally requires that ε-transitions
    and input-reading transitions are mutually exclusive for each `(state, stack-top)` pair.

    **Determinism guarantee.** Given a configuration `(q, a :: w, Z :: γ)`:
    - If `M.epsilon_transition q Z = some (p, β)`, then the unique possible move is
      to go to `(p, a :: w, β ++ γ)` (the `no_mixed` condition ensures no input-reading
      transition is available).
    - Otherwise, if `M.transition q a Z = some (p, β)`, the unique possible move is
      `(p, w, β ++ γ)`.
    - If neither transition is defined, the machine is stuck (halts). -/
structure DPDA (Q T S : Type) [Fintype Q] [Fintype T] [Fintype S] where
  /-- Initial state -/
  initial_state : Q
  /-- Initial stack symbol -/
  start_symbol : S
  /-- Set of accepting (final) states -/
  final_states : Set Q
  /-- Transition on reading input symbol `a` with stack top `Z`.
      Returns `some (p, β)` where `p` is the new state and `β` replaces `Z` on the stack,
      or `none` if no transition is defined. -/
  transition : Q → T → S → Option (Q × List S)
  /-- ε-transition (no input consumed) with stack top `Z`.
      Returns `some (p, β)` where `p` is the new state and `β` replaces `Z` on the stack,
      or `none` if no transition is defined. -/
  epsilon_transition : Q → S → Option (Q × List S)
  /-- **Determinism constraint**: if an ε-transition is defined for `(q, Z)`, then
      no input-reading transition is defined for `(q, a, Z)` for any input symbol `a`. -/
  no_mixed : ∀ q Z, epsilon_transition q Z ≠ none → ∀ a, transition q a Z = none

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

namespace DPDA

/-- Embed a DPDA into the nondeterministic PDA framework by converting each `Option`
    transition to the corresponding singleton or empty set. -/
noncomputable def toPDA (M : DPDA Q T S) : PDA Q T S where
  initial_state := M.initial_state
  start_symbol := M.start_symbol
  final_states := M.final_states
  transition_fun q a Z :=
    match M.transition q a Z with
    | some p => {p}
    | none => ∅
  transition_fun' q Z :=
    match M.epsilon_transition q Z with
    | some p => {p}
    | none => ∅
  finite q a Z := by
    cases M.transition q a Z with
    | none => exact Set.toFinite ∅
    | some p => exact Set.toFinite {p}
  finite' q Z := by
    cases M.epsilon_transition q Z with
    | none => exact Set.toFinite ∅
    | some p => exact Set.toFinite {p}

/-- Language accepted by a DPDA via **final-state acceptance**:
    a word `w` is accepted iff the DPDA, starting from its initial configuration,
    can reach a configuration with empty input and an accepting state
    (with any remaining stack contents). -/
def acceptsByFinalState (M : DPDA Q T S) : Language T :=
  M.toPDA.acceptsByFinalState

/-- Construct the **complement DPDA** by replacing the set of accepting states
    with its complement. This is a syntactic operation that swaps which states
    are accepting.

    **Note:** This syntactic operation alone does NOT suffice to accept the complement
    language in general, because the original DPDA may fail to read all of its input
    (by getting stuck or looping on ε-transitions). The full complementation theorem
    (`is_DCFL_compl` in `Grammars.Classes.ContextFree.Basics.DCFL`) requires a more
    involved transformation that first ensures the DPDA always processes the entire
    input. This constructor is provided as a basic building block. -/
def complement (M : DPDA Q T S) : DPDA Q T S where
  initial_state := M.initial_state
  start_symbol := M.start_symbol
  final_states := M.final_statesᶜ
  transition := M.transition
  epsilon_transition := M.epsilon_transition
  no_mixed := M.no_mixed

@[simp]
theorem complement_final_states (M : DPDA Q T S) :
    M.complement.final_states = M.final_statesᶜ := rfl

@[simp]
theorem complement_transition (M : DPDA Q T S) :
    M.complement.transition = M.transition := rfl

@[simp]
theorem complement_epsilon_transition (M : DPDA Q T S) :
    M.complement.epsilon_transition = M.epsilon_transition := rfl

@[simp]
theorem complement_initial_state (M : DPDA Q T S) :
    M.complement.initial_state = M.initial_state := rfl

@[simp]
theorem complement_start_symbol (M : DPDA Q T S) :
    M.complement.start_symbol = M.start_symbol := rfl

@[simp]
theorem complement_complement (M : DPDA Q T S) :
    M.complement.complement.initial_state = M.initial_state
    ∧ M.complement.complement.start_symbol = M.start_symbol
    ∧ M.complement.complement.final_states = M.final_states
    ∧ M.complement.complement.transition = M.transition
    ∧ M.complement.complement.epsilon_transition = M.epsilon_transition := by
  simp [complement]

@[simp]
theorem complement_toPDA (M : DPDA Q T S) :
    M.complement.toPDA.initial_state = M.toPDA.initial_state := rfl

  -- TODO prove that the complement DPDA accepts the complement language

end DPDA
