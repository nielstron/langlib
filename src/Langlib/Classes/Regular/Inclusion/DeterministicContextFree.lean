module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Regular.Definition
public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Automata.FiniteState.Inclusion.DeterministicPushdown
import Langlib.Automata.FiniteState.Equivalence.Regular
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
import Mathlib.Tactic.ENatToNat
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



/-! # Regular Languages Included in Deterministic Context-Free Languages

This file proves that every regular language over a finite alphabet is deterministic
context-free.

## Main results

- `is_DCF_of_is_RG` — every regular language is deterministic context-free
- `RG_subclass_DCF` — `RG ⊆ DCF`
-/

variable {T : Type} [Fintype T]

/-- Every right-regular language over a finite alphabet is a DCF. -/
public theorem is_DCF_of_is_RG {L : Language T} (h : is_RG L) : is_DCF L := by
  exact is_DPDA_of_is_DFA (isRegular_of_is_RG h)

public theorem RG_subclass_DCF :
  RG ⊆ (DCF : Set (Language T)) := by
  intro L
  exact is_DCF_of_is_RG
