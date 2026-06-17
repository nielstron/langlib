module

public import Langlib.Classes.Recursive.Definition
public import Langlib.Utilities.ClosurePredicates
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



/-! # Recursive Closure Under Complement

This file proves that the class of recursive (decidable) languages is closed under
complement.

Proof idea: given a TM0 decider `(Λ, M, accept)` for `L` that always halts, the
complement is decided by `(Λ, M, fun q => !accept q)` — the same machine with the
acceptance predicate negated.

## Main results

- `is_Recursive_complement` — if `L` is recursive then `Lᶜ` is recursive.
- `Recursive_complement_iff` — `L` is recursive iff `Lᶜ` is recursive.
-/

open Turing

variable {T : Type}

/-
The class of recursive languages is closed under complement.

Given a decider `(Λ, M, accept)` that always halts, we construct a decider for
`Lᶜ` by negating the acceptance predicate: `(Λ, M, fun q => !accept q)`.
-/
public theorem is_Recursive_complement {L : Language T} (hL : is_Recursive L) :
    is_Recursive Lᶜ := by
  obtain ⟨ Γ, hΓ, Λ, hΛ, hΛf, M, accept, hHalt, hCorrect ⟩ := hL;
  -- Construct the complement decider using the same machine M but with acceptance predicate `fun q => !accept q`.
  use Γ, hΓ, Λ, hΛ, hΛf, M, fun q => !accept q;
  grind

/-- A language is recursive iff its complement is recursive. -/
theorem Recursive_complement_iff {L : Language T} :
    is_Recursive Lᶜ ↔ is_Recursive L := by
  constructor
  · intro h
    have := is_Recursive_complement h
    rwa [compl_compl] at this
  · exact is_Recursive_complement
/-- The class of recursive languages is closed under complement. -/
public theorem Recursive_closedUnderComplement : ClosedUnderComplement (α := T) is_Recursive :=
  fun _L hL => is_Recursive_complement hL
