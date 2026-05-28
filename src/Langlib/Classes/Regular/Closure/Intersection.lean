module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.Regular.Definition
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Examples.TopBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Topology.Sheaves.Presheaf
@[expose]
public section



/-! # Regular Closure Under Intersection

This file restates mathlib's closure of regular languages under intersection and
shows that the converse fails over any nontrivial alphabet.

## Main declarations

- `Language.IsRegular.inf'`
- `Language.not_iff_regular_intersection`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under intersection. -/
public theorem IsRegular.inf' {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (L₁ ⊓ L₂).IsRegular := by
  exact h₁.inf h₂

/-- The converse of intersection closure fails over any nontrivial alphabet. -/
theorem not_iff_regular_intersection [Nontrivial α] :
    ¬ (∀ (L₁ L₂ : Language α), (L₁ ⊓ L₂).IsRegular ↔ (L₁.IsRegular ∧ L₂.IsRegular)) := by
  intro h
  obtain ⟨L, hL⟩ := exists_nonRegular_language_of_nontrivial (T := α)
  have hinf : (L ⊓ ⊥).IsRegular := by
    rw [show L ⊓ (⊥ : Language α) = ⊥ by simp]
    exact isRegular_bot
  exact hL ((h L ⊥).mp hinf).1

end Language

/-- The class of regular languages is closed under intersection. -/
theorem RG_closedUnderIntersection [Fintype α] : ClosedUnderIntersection (α := α) is_RG := by
  intro L₁ L₂ h₁ h₂
  exact is_RG_of_isRegular (isRegular_of_is_RG h₁ |>.inf (isRegular_of_is_RG h₂))
