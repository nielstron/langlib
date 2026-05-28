module

public import Langlib.Classes.Linear.Definition
public import Langlib.Classes.Regular.Definition
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

/-! # Regular Languages Included in Linear Languages

This file proves that every regular language is linear by showing that
right-regular productions are linear productions.

## Main results

- `is_Linear_of_is_RG`    — every regular language is linear
- `RG_subclass_Linear`    — `RG ⊆ Linear`
-/

open Language List Relation Classical

noncomputable section

variable {T : Type}

/-- A right-regular output has linear form. -/
theorem linear_output_of_right_regular {N : Type} {s : List (symbol T N)}
    (h : right_regular_output s) : linear_output s := by
  rcases h with ⟨a, B, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact Or.inr ⟨[a], B, [], by simp⟩
  · exact Or.inl (by intro x hx; simp at hx; exact ⟨a, hx⟩)
  · exact Or.inl (by simp)

/-- A right-regular grammar is linear. -/
theorem grammar_linear_of_right_regular {g : grammar T}
    (hg : grammar_right_regular g) : grammar_linear g := by
  intro r hr
  obtain ⟨h1, h2, h3⟩ := hg r hr
  exact ⟨h1, h2, linear_output_of_right_regular h3⟩

/-- Every regular language is linear. -/
theorem is_Linear_of_is_RG {L : Language T} (h : is_RG L) : is_Linear L := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g, grammar_linear_of_right_regular hg, rfl⟩

/-- The class of regular languages is a subclass of the linear languages. -/
theorem RG_subclass_Linear :
    (RG : Set (Language T)) ⊆ (Linear : Set (Language T)) := by
  intro L hL
  exact is_Linear_of_is_RG hL

end
