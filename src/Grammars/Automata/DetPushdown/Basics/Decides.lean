/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.DetPushdown.Basics.DPDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A DPDA **decides every input** if:
    1. **Totality**: for each word `w`, the DPDA can reach some configuration with
       empty input from the initial configuration.
    2. **Acceptance consistency**: all reachable empty-input configurations for a
       given word `w` agree on whether the state is accepting or not. -/
def DecidesEveryInput (M : DPDA Q T S) : Prop :=
  (∀ w : List T, ∃ q γ, @PDA.Reaches Q T S _ _ _ M.toPDA
    ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩) ∧
  (∀ (w : List T) (q₁ q₂ : Q) (γ₁ γ₂ : List S),
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q₁, [], γ₁⟩ →
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q₂, [], γ₂⟩ →
    (q₁ ∈ M.final_states ↔ q₂ ∈ M.final_states))

/-- Every DCFL is recognized by a DPDA that decides every input. -/
lemma exists_total_dpda :
    ∀ {Q S : Type} [Fintype Q] [Fintype S] (M : DPDA Q T S),
    ∃ (Q' S' : Type) (_ : Fintype Q') (_ : Fintype S') (M' : DPDA Q' T S'),
      M'.acceptsByFinalState = M.acceptsByFinalState ∧ M'.DecidesEveryInput := by
  sorry

end DPDA
