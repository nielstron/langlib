module

public import Langlib.Utilities.LanguageOperations
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



/-! # String Homomorphism

A **string homomorphism** `h : α → List β` extends to words by concatenation:
`h(a₁a₂…aₙ) = h(a₁) ++ h(a₂) ++ … ++ h(aₙ)`.
The image of a language `L` under `h` is `{h(w) | w ∈ L}`.

This is a special case of substitution where each symbol `a` is mapped to the
singleton language `{h(a)}`.

-/

variable {α β : Type}

/-- The image of a language `L` under a string homomorphism `h`. -/
@[expose]
public def Language.homomorphicImage (L : Language α) (h : α → List β) : Language β :=
  L.subst (fun a => ({h a} : Language β))

/-- A string homomorphism is ε-free if no symbol maps to the empty string. -/
@[expose]
public def IsEpsFreeHomomorphism (h : α → List β) : Prop :=
  ∀ a, h a ≠ []
