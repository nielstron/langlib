module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license; see licenses/Apache-2.0.txt.
-/
public import Langlib.Classes.DeterministicContextFree.Definition
public import Langlib.Classes.Regular.Definition
import Langlib.Automata.FiniteState.Equivalence.Regular
import Langlib.Classes.DeterministicContextFree.Closure.Bijection
import Langlib.Classes.DeterministicContextFree.Examples.AnBn
import Langlib.Classes.Regular.Examples.AnBn
import Langlib.Classes.Regular.Closure.Bijection
import Langlib.Classes.Regular.Inclusion.DeterministicContextFree
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



/-! # RG ⊊ DCF

This file uses the example language `{aⁿbⁿ}` to show that regular languages
form a strict subclass of deterministic context-free languages.

## Main results

- `RG_strict_subclass_DCF` — Regular languages are a strict subclass of DCFs.
- `RG_strict_subclass_DCF_of_card` — The inclusion over every finite alphabet with at
  least 2 elements.
-/

/-- Regular languages are a strict subclass of deterministic context-free languages over any
nontrivial alphabet. -/
theorem RG_strict_subclass_DCF {T : Type} [Fintype T] [Nontrivial T] :
    (RG : Set (Language T)) ⊂ (DCF : Set (Language T)) := by
  refine ⟨RG_subclass_DCF, ?_⟩
  intro hDCFsubsetRG
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  let f : Bool → T := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> try rfl
    · simp [f] at hxy
      exact False.elim (hab hxy)
    · simp [f] at hxy
      exact False.elim (hab hxy.symm)
  have hRG : Language.map f anbn ∈ (RG : Set (Language T)) :=
    hDCFsubsetRG (a := Language.map f anbn)
      (DCF_of_map_injective_DCF hf anbn anbn_is_DCF)
  have hreg : (Language.map f anbn).IsRegular := isRegular_of_is_RG hRG
  exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf hreg)

/-- Regular languages are a strict subclass of deterministic context-free languages over
every finite alphabet with at least 2 elements. -/
public theorem RG_strict_subclass_DCF_of_card {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (RG : Set (Language T)) ⊂ (DCF : Set (Language T)) := by
  let : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide) hT)
  exact RG_strict_subclass_DCF
