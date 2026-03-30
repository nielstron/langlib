/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammars.Automata.DetPushdown.Basics.Inclusion
import Grammars.Automata.DetPushdown.Basics.Decides

open PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

namespace DPDA

/-- Construct the **complement DPDA** by replacing the set of accepting states
    with its complement. This is a syntactic operation that swaps which states
    are accepting. -/
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

/-- The complement DPDA has the same transition functions as the original. -/
theorem complement_toPDA_transition_fun (M : DPDA Q T S) :
    M.complement.toPDA.transition_fun = M.toPDA.transition_fun := rfl

/-- The complement DPDA has the same ε-transition functions as the original. -/
theorem complement_toPDA_transition_fun' (M : DPDA Q T S) :
    M.complement.toPDA.transition_fun' = M.toPDA.transition_fun' := rfl

/-- The multi-step reachability relation is the same for a DPDA and its complement,
    because the step function depends only on the transitions, not the accepting states. -/
theorem complement_toPDA_reaches (M : DPDA Q T S) (q q' : Q)
    (w : List T) (γ γ' : List S) :
    @PDA.Reaches _ _ _ _ _ _ M.complement.toPDA ⟨q, w, γ⟩ ⟨q', [], γ'⟩ ↔
    @PDA.Reaches _ _ _ _ _ _ M.toPDA ⟨q, w, γ⟩ ⟨q', [], γ'⟩ := by
  constructor
  · intro h
    exact PDA.reaches_of_same_transitions M.complement.toPDA M.toPDA
      (complement_toPDA_transition_fun M) (complement_toPDA_transition_fun' M)
      ⟨q, w, γ⟩ ⟨q', [], γ'⟩ h
  · intro h
    exact PDA.reaches_of_same_transitions M.toPDA M.complement.toPDA
      (complement_toPDA_transition_fun M).symm (complement_toPDA_transition_fun' M).symm
      ⟨q, w, γ⟩ ⟨q', [], γ'⟩ h

/-- For a DPDA that decides every input, the complemented DPDA accepts precisely the
    complement of the original language. -/
theorem complement_acceptsByFinalState (M : DPDA Q T S) (h : M.DecidesEveryInput) :
    M.complement.acceptsByFinalState = (M.acceptsByFinalState)ᶜ := by
  obtain ⟨htotal, hconsistent⟩ := h
  unfold DPDA.acceptsByFinalState PDA.acceptsByFinalState
  ext w
  change (∃ q ∈ M.final_statesᶜ, ∃ γ : List S,
    @PDA.Reaches Q T S _ _ _ M.complement.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩) ↔
    ¬(∃ q ∈ M.final_states, ∃ γ : List S,
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩)
  constructor
  · rintro ⟨q, hq_not_final, γ, hreach⟩
    rw [complement_toPDA_reaches] at hreach
    rintro ⟨q', hq'_final, γ', hreach'⟩
    exact hq_not_final ((hconsistent w q q' γ γ' hreach hreach').mpr hq'_final)
  · intro h_not_accept
    obtain ⟨q, γ, hreach⟩ := htotal w
    refine ⟨q, ?_, γ, (complement_toPDA_reaches M M.initial_state q w [M.start_symbol] γ).mpr hreach⟩
    intro hq_final
    exact h_not_accept ⟨q, hq_final, γ, hreach⟩

end DPDA
