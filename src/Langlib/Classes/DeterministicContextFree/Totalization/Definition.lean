module

public import Langlib.Classes.DeterministicContextFree.Definition
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

@[expose] public section

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

