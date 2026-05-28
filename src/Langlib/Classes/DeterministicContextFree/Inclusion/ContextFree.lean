module

/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Classes.ContextFree.Definition
import Langlib.Automata.DeterministicPushdown.Inclusion.Pushdown
import Langlib.Automata.Pushdown.Equivalence.ContextFree
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



/-! # DCFs are a subset of CFLs

This file shows that DCFs are a subset of the CFLs.

--/

-- ============================================================================
-- DCF inclusion into CFL
-- ============================================================================

public theorem is_CF_of_is_DCF {T : Type} [Fintype T] {L : Language T} (h : is_DCF L) : is_CF L := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  exact is_CF_of_is_PDA M.is_PDA_acceptsByFinalState

/-- The class of deterministic context-free languages is contained in the class of
    context-free languages. -/
public theorem DCF_subclass_CF {T : Type} [Fintype T] : (DCF : Set (Language T)) ⊆ CF :=
  fun _ h => is_CF_of_is_DCF h
