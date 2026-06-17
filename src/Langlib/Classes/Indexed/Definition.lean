module

public import Langlib.Grammars.Indexed.Definition
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



/-! # Indexed Languages

This file defines the class of indexed languages via indexed grammars.

## Main declarations

- `is_Indexed`
- `Indexed`
-/

variable {T : Type}

/-- Predicate that a language is an indexed language. -/
@[expose]
public def is_Indexed (L : Language T) : Prop :=
  ∃ g : IndexedGrammar T, g.Language = L

/-- The class of indexed languages. -/
@[expose]
public def Indexed : Set (Language T) :=
  setOf is_Indexed

/-- Predicate that a language has an indexed-grammar witness with no ε-productions. -/
def is_Indexed_noEpsilon (L : Language T) : Prop :=
  ∃ g : IndexedGrammar T, g.NoEpsilon' ∧ g.Language = L

/-- The class of indexed languages with an ε-free indexed-grammar witness. -/
def IndexedNoEpsilon : Set (Language T) :=
  setOf is_Indexed_noEpsilon

theorem is_Indexed_of_is_Indexed_noEpsilon {L : Language T}
    (h : is_Indexed_noEpsilon L) : is_Indexed L := by
  rcases h with ⟨g, _, hL⟩
  exact ⟨g, hL⟩

theorem IndexedNoEpsilon_subclass_Indexed :
    (IndexedNoEpsilon : Set (Language T)) ⊆ Indexed := by
  intro L hL
  exact is_Indexed_of_is_Indexed_noEpsilon hL
