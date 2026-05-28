import Langlib.Classes.DeterministicContextFree.Totalization.Construction
import Langlib.Classes.DeterministicContextFree.Totalization.Definition

/-! # Totalized Presentations

This file connects the analyzed DPDA totalizer to the language-level deciding
presentation used by complement closure.
-/

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
variable {M : DPDA Q T S}

noncomputable section

/-- The analyzed totalizer is a deciding DPDA presentation of the same language. -/
theorem totalizer_is_DCF_decider (A : M.RegularEpsilonAnalysis) :
    is_DCF_decider (M.acceptsByFinalState : Language T) := by
  refine
    ⟨TotalState Q, TotalStackSymbol A, inferInstance, inferInstance, totalizer A,
      totalizer_decides A, ?_⟩
  exact totalizer_acceptsByFinalState_eq_original A

end

end DPDA

variable {T : Type} [Fintype T]

/-- Every finite DPDA has the regular epsilon analysis required by the totalizer. -/
def EveryDPDAHasRegularEpsilonAnalysis (T : Type) [Fintype T] : Prop :=
  ∀ (Q S : Type) [Fintype Q] [Fintype S] (M : DPDA Q T S),
    M.HasRegularEpsilonAnalysis

/-- The saturation construction gives a regular epsilon analysis for every finite DPDA. -/
theorem everyDPDAHasRegularEpsilonAnalysis :
    EveryDPDAHasRegularEpsilonAnalysis T := by
  intro Q S _ _ M
  exact DPDA.hasRegularEpsilonAnalysis M

/-- Regular epsilon analyses for all DPDAs imply the normal form used by DCF
complement closure. -/
theorem everyDCFHasDeciderPresentation_of_regularEpsilonAnalysis
    (hanalysis : EveryDPDAHasRegularEpsilonAnalysis T) :
    EveryDCFHasDeciderPresentation T := by
  intro L hL
  obtain ⟨Q, S, hQ, hS, M, hM⟩ := hL
  obtain ⟨A⟩ := @hanalysis Q S hQ hS M
  rw [← hM]
  exact DPDA.totalizer_is_DCF_decider A

/-- Every DCF has an equivalent deciding-DPDA presentation. -/
theorem everyDCFHasDeciderPresentation :
    EveryDCFHasDeciderPresentation T :=
  everyDCFHasDeciderPresentation_of_regularEpsilonAnalysis
    everyDPDAHasRegularEpsilonAnalysis
