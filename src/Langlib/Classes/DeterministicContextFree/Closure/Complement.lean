import Langlib.Automata.DeterministicPushdown.ClosureProperties.Complement
import Langlib.Classes.DeterministicContextFree.Totalization
import Langlib.Utilities.ClosurePredicates

/-! # Deterministic Context-Free Closure Under Complement

This file lifts the DPDA complement construction to the deterministic context-free
language level.  The totalization construction first replaces an arbitrary
final-state DPDA by an equivalent DPDA that decides every input, and the
automaton-level complement construction is then applied to that deciding DPDA.
-/

open PDA

variable {T : Type} [Fintype T]

/-- Complement closure for deterministic context-free languages with a deciding DPDA
presentation. -/
theorem is_DCF_decider_complement {L : Language T} (hL : is_DCF_decider L) :
    is_DCF_decider Lᶜ := by
  obtain ⟨Q, S, hQ, hS, M, hdec, hM⟩ := hL
  refine ⟨Q, S, hQ, hS, M.complement, ?_, ?_⟩
  · unfold DPDA.DecidesEveryInput at hdec ⊢
    constructor
    · intro w
      obtain ⟨q, γ, hreach⟩ := hdec.1 w
      exact ⟨q, γ, (DPDA.complement_toPDA_reaches M M.initial_state q w [M.start_symbol] γ).2 hreach⟩
    · intro w q₁ q₂ γ₁ γ₂ h₁ h₂
      rw [DPDA.complement_toPDA_reaches] at h₁
      rw [DPDA.complement_toPDA_reaches] at h₂
      simpa using not_congr (hdec.2 w q₁ q₂ γ₁ γ₂ h₁ h₂)
  · rw [DPDA.complement_acceptsByFinalState M hdec, hM]

/-- The deciding-DPDA presentation class is closed under complement. -/
theorem DCF_decider_closedUnderComplement :
    ClosedUnderComplement (α := T) is_DCF_decider :=
  fun _ => is_DCF_decider_complement

/-- If a language has a deciding-DPDA presentation, then its complement is a DCF. -/
theorem is_DCF_complement_of_is_DCF_decider {L : Language T} (hL : is_DCF_decider L) :
    is_DCF Lᶜ :=
  is_DCF_of_is_DCF_decider (is_DCF_decider_complement hL)

/-- Once arbitrary DPDAs are totalized, DCFs are closed under complement. -/
theorem DCF_closedUnderComplement_of_decider_presentations
    (htotal : EveryDCFHasDeciderPresentation T) :
    ClosedUnderComplement (α := T) is_DCF := by
  intro L hL
  exact is_DCF_complement_of_is_DCF_decider (htotal L hL)

/-- Once the regular epsilon analyses exist for all DPDAs, DCFs are closed under
complement via the analyzed totalizer. -/
theorem DCF_closedUnderComplement_of_regularEpsilonAnalysis
    (hanalysis : EveryDPDAHasRegularEpsilonAnalysis T) :
    ClosedUnderComplement (α := T) is_DCF :=
  DCF_closedUnderComplement_of_decider_presentations
    (everyDCFHasDeciderPresentation_of_regularEpsilonAnalysis hanalysis)

/-- Deterministic context-free languages are closed under complement. -/
theorem DCF_closedUnderComplement :
    ClosedUnderComplement (α := T) is_DCF :=
  DCF_closedUnderComplement_of_decider_presentations
    everyDCFHasDeciderPresentation
