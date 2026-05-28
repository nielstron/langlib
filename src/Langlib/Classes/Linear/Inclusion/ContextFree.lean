module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Linear.Definition
public import Langlib.Classes.ContextFree.Definition
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

/-! # Linear Language Inclusions

This file proves that every linear language is context-free.

## Main results

- `Linear_subclass_CF` — `Linear ⊆ CF`
-/

open Language List Relation Classical

noncomputable section

variable {T : Type}

/-- A linear output is trivially a valid context-free output (no additional restriction). -/
theorem grammar_context_free_of_linear {g : grammar T}
    (hg : grammar_linear g) : grammar_context_free g := by
  intro r hr
  exact ⟨(hg r hr).1, (hg r hr).2.1⟩

/-- Every linear language is context-free. -/
theorem is_CF_of_is_Linear {L : Language T} (h : is_Linear L) : is_CF L := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g, grammar_context_free_of_linear hg, rfl⟩

/-- The class of linear languages is a subclass of the context-free languages. -/
theorem Linear_subclass_CF :
    (Linear : Set (Language T)) ⊆ (CF : Set (Language T)) := by
  intro L hL
  exact is_CF_of_is_Linear hL
