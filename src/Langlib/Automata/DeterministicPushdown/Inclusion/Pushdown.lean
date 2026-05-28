module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Automata.DeterministicPushdown.Definition
import Langlib.Automata.Pushdown.Basics.FinalStateEmptyStackEquiv
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

open PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

namespace DPDA

/-- Every language accepted by a DPDA via final-state acceptance is accepted by some PDA
    via empty-stack acceptance. -/
theorem is_PDA_acceptsByFinalState (M : DPDA Q T S) : is_PDA M.acceptsByFinalState :=
  PDA_FS_subset_ES M.toPDA

end DPDA

/-- The class of DPDA-recognizable languages is contained in the class of PDA-recognizable
    languages. -/
theorem DPDA_subclass_PDA {T : Type} [Fintype T] : (DPDA.Class : Set (Language T)) ⊆ PDA.Class := by
  intro L hL
  obtain ⟨Q, S, _, _, M, rfl⟩ := hL
  exact M.is_PDA_acceptsByFinalState
