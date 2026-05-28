import Langlib.Classes.DeterministicContextFree.Definition
import Langlib.Utilities.ClosurePredicates

/-! # Deciding Presentations for DCF Languages

This file isolates the target normal form used by DCF complement closure.  A
`is_DCF_decider` presentation is an ordinary final-state DPDA presentation whose
automaton reaches some empty-input configuration on every input, and whose
reachable empty-input configurations all agree on final-state membership.
-/

open PDA

variable {T : Type} [Fintype T]

/-- A deterministic context-free language represented by a DPDA that decides every input. -/
def is_DCF_decider (L : Language T) : Prop :=
  ∃ (Q S : Type) (_ : Fintype Q) (_ : Fintype S) (M : DPDA Q T S),
    M.DecidesEveryInput ∧ M.acceptsByFinalState = L

/-- Every deciding-DPDA language is a DCF in the ordinary final-state sense. -/
theorem is_DCF_of_is_DCF_decider {L : Language T} (hL : is_DCF_decider L) : is_DCF L := by
  obtain ⟨Q, S, hQ, hS, M, _hdec, hM⟩ := hL
  exact ⟨Q, S, hQ, hS, M, hM⟩

/-- The totalization/normalization principle needed for unconditional DCF complement
closure: every final-state DPDA language has an equivalent deciding-DPDA presentation. -/
def EveryDCFHasDeciderPresentation (T : Type) [Fintype T] : Prop :=
  ∀ L : Language T, is_DCF L → is_DCF_decider L

