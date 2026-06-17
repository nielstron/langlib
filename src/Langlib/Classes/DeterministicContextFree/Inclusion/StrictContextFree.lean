module

/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.ContextFree.Definition
public import Langlib.Automata.DeterministicPushdown.Totalization.Definition
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.ContextFree.Closure.Complement
import Langlib.Classes.DeterministicContextFree.Closure.Complement
import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
import Langlib.Utilities.ClosurePredicates.Transport
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



/-! # DCFs are a strict subset of CFLs

This file records the closure-mismatch route to strictness for the inclusion
`DCF ⊆ CF`.

--/

/-- If deterministic context-free languages are closed under complement over `Fin 3`, then
they form a strict subclass of context-free languages over `Fin 3`.

This isolates the useful closure-property proof pattern behind the unconditional
strictness theorem below. -/
public theorem DCF_strict_subclass_CF_of_closedUnderComplement
    (hDCFcomp : ClosedUnderComplement (α := Fin 3) is_DCF) :
    (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3))) :=
  strict_subset_of_subset_different_property
    (P := is_DCF) (Q := is_CF)
    (fun _ hL => DCF_subclass_CF hL)
    (X := ClosedUnderComplement)
    (fun hiff => ClosedUnderComplement_of_iff hiff)
    hDCFcomp
    CF_notClosedUnderComplement

/-- If deterministic context-free languages are closed under complement over an alphabet
with three distinguished symbols, then they form a strict subclass of context-free
languages over that alphabet. -/
theorem DCF_strict_subclass_CF_of_closedUnderComplement_of_three {T : Type} [Fintype T]
    (a b c : T) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDCFcomp : ClosedUnderComplement (α := T) is_DCF) :
    (DCF : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  strict_subset_of_subset_different_property
    (P := is_DCF) (Q := is_CF)
    (fun _ hL => DCF_subclass_CF hL)
    (X := ClosedUnderComplement)
    (fun hiff => ClosedUnderComplement_of_iff hiff)
    hDCFcomp
    (CF_notClosedUnderComplement_of_three a b c hab hac hbc)

/-- If deterministic context-free languages are closed under complement over a finite alphabet
with at least three symbols, then they form a strict subclass of context-free languages over
that alphabet. -/
theorem DCF_strict_subclass_CF_of_closedUnderComplement_of_card {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T)
    (hDCFcomp : ClosedUnderComplement (α := T) is_DCF) :
    (DCF : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  strict_subset_of_subset_different_property
    (P := is_DCF) (Q := is_CF)
    (fun _ hL => DCF_subclass_CF hL)
    (X := ClosedUnderComplement)
    (fun hiff => ClosedUnderComplement_of_iff hiff)
    hDCFcomp
    (CF_notClosedUnderComplement_of_card hT)

/-- Deterministic context-free languages are a strict subclass of context-free
languages over a three-symbol alphabet. -/
public theorem DCF_strict_subclass_CF :
    (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3))) :=
  DCF_strict_subclass_CF_of_closedUnderComplement DCF_closedUnderComplement

/-- Deterministic context-free languages are a strict subclass of context-free languages
over any finite alphabet with at least three symbols. -/
theorem DCF_strict_subclass_CF_of_card {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (DCF : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  DCF_strict_subclass_CF_of_closedUnderComplement_of_card hT DCF_closedUnderComplement
