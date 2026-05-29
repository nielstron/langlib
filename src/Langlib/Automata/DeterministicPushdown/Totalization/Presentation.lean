module

public import Langlib.Automata.DeterministicPushdown.Totalization.Definition
public import Langlib.Automata.DeterministicPushdown.Totalization.RegularAnalysis
import Langlib.Automata.DeterministicPushdown.Totalization.Construction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



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
public theorem totalizer_is_DCF_decider (A : M.RegularEpsilonAnalysis) :
    is_DCF_decider (M.acceptsByFinalState : Language T) := by
  refine
    ⟨TotalState Q, TotalStackSymbol A, inferInstance, inferInstance, totalizer A,
      totalizer_decides A, ?_⟩
  exact totalizer_acceptsByFinalState_eq_original A

end

end DPDA

variable {T : Type} [Fintype T]

/-- Every finite DPDA has the regular epsilon analysis required by the totalizer. -/
@[expose]
public def EveryDPDAHasRegularEpsilonAnalysis (T : Type) [Fintype T] : Prop :=
  ∀ (Q S : Type) [Fintype Q] [Fintype S] (M : DPDA Q T S),
    M.HasRegularEpsilonAnalysis

/-- The saturation construction gives a regular epsilon analysis for every finite DPDA. -/
public theorem everyDPDAHasRegularEpsilonAnalysis :
    EveryDPDAHasRegularEpsilonAnalysis T := by
  intro Q S _ _ M
  exact DPDA.hasRegularEpsilonAnalysis M

/-- Regular epsilon analyses for all DPDAs imply the normal form used by DCF
complement closure. -/
public theorem everyDCFHasDeciderPresentation_of_regularEpsilonAnalysis
    (hanalysis : EveryDPDAHasRegularEpsilonAnalysis T) :
    EveryDCFHasDeciderPresentation T := by
  intro L hL
  obtain ⟨Q, S, hQ, hS, M, hM⟩ := hL
  obtain ⟨A⟩ := @hanalysis Q S hQ hS M
  rw [← hM]
  exact DPDA.totalizer_is_DCF_decider A

/-- Every DCF has an equivalent deciding-DPDA presentation. -/
public theorem everyDCFHasDeciderPresentation :
    EveryDCFHasDeciderPresentation T :=
  everyDCFHasDeciderPresentation_of_regularEpsilonAnalysis
    everyDPDAHasRegularEpsilonAnalysis
