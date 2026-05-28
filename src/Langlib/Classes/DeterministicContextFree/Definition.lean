module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Automata.DeterministicPushdown.Definition
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

/-! # Deterministic Context-Free Languages (DCFs)

This file defines deterministic context-free languages (DCFs) as a grammar class
and proves their basic inclusion into context-free languages.

## Definition

A language `L` is a **deterministic context-free language (DCF)** if there exists a
deterministic pushdown automaton (DPDA) that accepts `L` by final-state acceptance.

## Main results

- `is_CF_of_is_DCF` — Every DCF is context-free.
- `lang_aibjck_eq_union` — The language `{aⁱbʲcᵏ | i = j ∨ j = k}` equals the union of two CFLs.
- `lang_aibjck_CFL` — The language `{aⁱbʲcᵏ | i = j ∨ j = k}` is context-free.

## References

* Hopcroft, Motwani, Ullman. *Introduction to Automata Theory, Languages, and Computation*,
  3rd ed. Section 6.4.
-/

open PDA

variable {T : Type} [Fintype T]

-- ============================================================================
-- DCF definition and basic properties
-- ============================================================================

/-- A language `L` over a finite alphabet `T` is a **deterministic context-free language
    (DCF)** if there exists a DPDA that recognizes `L` via final-state acceptance. -/
def is_DCF (L : Language T) : Prop :=
  is_DPDA L

/-- The class of languages that are DCF -/
def DCF : Set (Language T) :=
  DPDA.Class
