module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Closure.Union
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




/-! # Context-Free Non-Closure Under Complement

This file derives failure of closure under complement from the corresponding intersection result.

Counterexample idea: if CFLs were closed under complement, then together with
closure under union they would also be closed under intersection by De Morgan's
law. This contradicts the explicit non-closure result for intersection.

## Main declarations

- `nnyCF_of_complement_CF`
-/

/-- The class of context-free languages isn't closed under complement. -/
public theorem nnyCF_of_complement_CF : ¬ (∀ L : Language (Fin 3),
    is_CF L  →  is_CF (Lᶜ)
) :=
by
  intro h
  have nny := nnyCF_of_CF_i_CF
  push_neg at nny
  rcases nny with ⟨L₁, L₂, ⟨hL₁, hL₂⟩, hyp_neg⟩
  specialize h
  have hu := CF_of_CF_u_CF (L₁ᶜ) (L₂ᶜ) ⟨h L₁ hL₁, h L₂ hL₂⟩
  have contra := h (L₁ᶜ + L₂ᶜ) hu
  apply hyp_neg
  -- golfed by Eric Wieser
  rwa [Language.add_def, Set.compl_union, compl_compl, compl_compl] at contra

/-- Context-free languages over `Fin 3` are not closed under complement. -/
public theorem CF_notClosedUnderComplement :
    ¬ ClosedUnderComplement (α := Fin 3) is_CF := by
  rw [ClosedUnderComplement]
  exact nnyCF_of_complement_CF

/-- Context-free languages are not closed under complement for any type with at least
    3 elements. That is, as long as `α` has at least 3 distinct elements, not all
    complements of context-free languages over `α` are context-free. -/
public theorem CF_notClosedUnderComplement_of_three {α : Type}
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ClosedUnderComplement (α := α) is_CF := by
  intro hcomp
  apply CF_notClosedUnderIntersection_of_three a b c hab hac hbc
  -- Derive closure under intersection from complement + union (De Morgan)
  intro L₁ L₂ hL₁ hL₂
  have hc₁ := hcomp L₁ hL₁
  have hc₂ := hcomp L₂ hL₂
  have hunion := CF_of_CF_u_CF L₁ᶜ L₂ᶜ ⟨hc₁, hc₂⟩
  have hcc := hcomp (L₁ᶜ + L₂ᶜ) hunion
  rwa [Language.add_def, Set.compl_union, compl_compl, compl_compl] at hcc

/-- Context-free languages are not closed under complement for any finite alphabet with
    at least three symbols. -/
public theorem CF_notClosedUnderComplement_of_card {α : Type} [Fintype α]
    (hα : 3 ≤ Fintype.card α) :
    ¬ ClosedUnderComplement (α := α) is_CF := by
  let π : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let e : Fin 3 ↪ α := (Fin.castLEEmb hα).trans π.symm.toEmbedding
  exact CF_notClosedUnderComplement_of_three
    (e 0) (e 1) (e 2)
    (fun h => by simpa using e.injective h)
    (fun h => by simpa using e.injective h)
    (fun h => by simpa using e.injective h)
