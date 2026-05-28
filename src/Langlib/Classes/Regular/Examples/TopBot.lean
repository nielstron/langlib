module

public import Mathlib.Computability.DFA
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

/-! # Trivial Regular Examples

This file provides the trivial regular-language witnesses `⊥` and `⊤`.
-/

namespace Language

variable {α : Type*}

/-- The empty language is regular. -/
theorem isRegular_bot : (⊥ : Language α).IsRegular := by
  rw [isRegular_iff]
  exact ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, by
    ext w
    simp [DFA.mem_accepts, DFA.eval]
    exact fun a => a.elim⟩

/-- The universal language is regular. -/
theorem isRegular_top : (⊤ : Language α).IsRegular := by
  rw [isRegular_iff]
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), (), Set.univ⟩, ?_⟩
  ext w
  constructor
  · intro _
    trivial
  · intro _
    simp [DFA.mem_accepts, DFA.eval, Set.mem_univ]

end Language
