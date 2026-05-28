module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.ContextFree.Closure.Substitution.Core
import Langlib.Grammars.ContextFree.EquivMathlibCFG
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

/-! # Context-Free Closure Under Kleene Star

This file derives closure under Kleene star from closure under substitution.

## Main declarations

- `CF_of_star_CF`
-/

variable {T : Type}

/-- The class of context-free languages is closed under Kleene star. -/
theorem CF_of_star_CF (L : Language T) :
    is_CF L → is_CF (KStar.kstar L) := by
  intro h
  rw [is_CF_iff_isContextFree]
  exact Language.IsContextFree.kstar ((is_CF_iff_isContextFree).mp h)

/-- The class of context-free languages is closed under Kleene star. -/
theorem CF_closedUnderKleeneStar : ClosedUnderKleeneStar (α := T) is_CF :=
  CF_of_star_CF
