module

public import Langlib.Classes.Recursive.Definition
public import Langlib.Classes.Recursive.Basics.Post
public import Langlib.Classes.Recursive.Inclusion.RecursivelyEnumerable
public import Langlib.Classes.Recursive.Closure.Complement
public import Mathlib.Computability.Halting
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



/-! # Computability of Membership

This file proves that membership in a recursive language is computable.

## Main results

- `Recursive_membership_computable` — membership in a recursive language is a
  `ComputablePred` (genuine computability in the theory-of-computation sense).
-/

variable {T : Type}

/-- **Membership in a recursive language is computable.** This is the genuine
theory-of-computation statement: from an always-halting decider we obtain a `ComputablePred`,
via Post's theorem applied to `L` and its (recursive, hence recognizable) complement.

This mirrors `CS_membership_computable` for context-sensitive languages. -/
public theorem Recursive_membership_computable
    [DecidableEq T] [Fintype T] [Primcodable T]
    {L : Language T} (hL : is_Recursive L) :
    ComputablePred (fun w : List T => w ∈ L) :=
  computablePred_of_isRE_of_isRE_compl
    (is_Recursive_implies_is_RE hL)
    (is_Recursive_implies_is_RE (is_Recursive_complement hL))
