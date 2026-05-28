module

public import Langlib.Classes.Regular.Decidability.Emptiness
import Langlib.Classes.Regular.Closure.Intersection
import Langlib.Classes.Regular.Closure.Union
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
import Mathlib.Order.BourbakiWitt
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

/-! # Decidability of Equivalence for Regular Languages

This file proves that equivalence is decidable for regular languages.

The proof reduces equivalence to emptiness of the symmetric difference:
`L₁ = L₂ ↔ symmDiff L₁ L₂ = ∅`, and the symmetric difference is regular
(by closure under complement, intersection, and union).

## Main results

- `regular_equivalence_decidable` — equivalence of two regular languages is decidable.
-/

section Regular

variable {α : Type*}

lemma eq_iff_symmDiff_eq_bot (L₁ L₂ : Language α) :
    L₁ = L₂ ↔ symmDiff L₁ L₂ = ⊥ := by
  constructor <;> intro <;> rw [ symmDiff ] at * <;> aesop

lemma symmDiff_isRegular {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (symmDiff L₁ L₂).IsRegular := by
  convert Language.IsRegular.add' _ _ using 1;
  · convert Language.IsRegular.inf' h₁ ( Language.IsRegular.compl h₂ ) using 1;
  · convert Language.IsRegular.inf' h₂ ( Language.IsRegular.compl h₁ ) using 1

/-- Equivalence of two regular languages is decidable. -/
noncomputable def regular_equivalence_decidable
    [Fintype α] [DecidableEq α] (L₁ L₂ : Language α)
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    Decidable (L₁ = L₂) := by
  rw [eq_iff_symmDiff_eq_bot]
  exact regular_emptiness_decidable _ (symmDiff_isRegular h₁ h₂)

end Regular
