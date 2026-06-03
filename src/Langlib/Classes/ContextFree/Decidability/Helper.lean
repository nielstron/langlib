module

public import Langlib.Utilities.ComputabilityPredicates
public import Langlib.Classes.ContextFree.Basics.EncodedCFG
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



/-- The language represented by an encoded context-free grammar. -/
@[expose]
public def contextFreeLanguageOf (G : EncodedCFG T) : Language T :=
  CF_language G.toCFGrammar

/-- The uniform membership predicate for encoded context-free grammars.

The input is a pair `(G, w)`, with both the encoded grammar and the word freshly
provided to the predicate. -/
def contextFreeMembershipPredicate (p : EncodedCFG T × List T) : Prop :=
  p.2 ∈ contextFreeLanguageOf p.1

/-- Uniform computability of membership for encoded context-free grammars,
relative to the language class `C`. -/
abbrev ContextFreeComputableMembership (T : Type) [Primcodable T]
    (C : Set (Language T)) : Prop :=
  ComputableMembership C (contextFreeLanguageOf : EncodedCFG T → Language T)
