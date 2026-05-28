module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Langlib.Grammars.RightRegular.UnrestrictedCharacterization
public import Mathlib.Computability.DFA
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
import Langlib.Grammars.Unrestricted.Toolbox
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



/-! # Regular Languages Included in Recursively Enumerable Languages

This file proves that every right-regular language is recursively enumerable.

## Main results

- `RG_subclass_RE` — every regular language is recursively enumerable
-/

open Relation Classical

noncomputable section

variable {T : Type}

/-- An RG transformation step corresponds to a grammar transformation step. -/
public lemma grammar_transforms_of_RG_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : RG_transforms g w₁ w₂) :
    grammar_transforms (grammar_of_RG g) w₁ w₂ := by
  obtain ⟨r, hr, u, v, hw1, hw2⟩ := h
  exact ⟨⟨[], r.lhs, [], r.output⟩,
    ⟨List.mem_map.mpr ⟨r, hr, rfl⟩, u, v, by simpa using hw1, by simpa using hw2⟩⟩

/-- A grammar transformation step from a converted RG corresponds to an RG step. -/
public lemma RG_transforms_of_grammar_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : grammar_transforms (grammar_of_RG g) w₁ w₂) :
    RG_transforms g w₁ w₂ := by
  obtain ⟨r, hr, u, v, hw1, hw2⟩ := h
  simp only [grammar_of_RG, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨r', hr', u, v, by simpa using hw1, by simpa using hw2⟩

/-- RG derives iff grammar derives (for the converted grammar). -/
public lemma RG_derives_iff_grammar_derives (g : RG_grammar T)
    (w₁ w₂ : List (symbol T g.nt)) :
    RG_derives g w₁ w₂ ↔ grammar_derives (grammar_of_RG g) w₁ w₂ := by
  constructor
  · intro h
    induction h with
    | refl => exact grammar_deri_self
    | tail _ hs ih =>
      exact grammar_deri_of_deri_tran ih (grammar_transforms_of_RG_transforms hs)
  · intro h
    induction h with
    | refl => exact RG_deri_self _
    | tail _ hs ih =>
      exact RG_deri_of_deri_tran ih (RG_transforms_of_grammar_transforms hs)

/-- Every right-regular language is recursively enumerable. -/
public theorem RG_subclass_RE {L : Language T} (h : is_RG L) : is_RE L := by
  obtain ⟨g, rfl⟩ := is_RG_implies_is_RG_via_rg h
  refine ⟨grammar_of_RG g, ?_⟩
  ext w
  simp only [grammar_language, RG_language]
  exact (RG_derives_iff_grammar_derives g _ _).symm

/-- Every Mathlib-regular language over a finite alphabet is recursively enumerable. -/
public theorem is_RE_of_isRegular [Fintype T] {L : Language T} (h : L.IsRegular) : is_RE L :=
  RG_subclass_RE (is_RG_of_isRegular h)

end
