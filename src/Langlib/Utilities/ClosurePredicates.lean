module

/-
Copyright (c) 2026 Langlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Utilities.Homomorphism
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

/-! # Abstract Closure Predicates for Language Classes

This file defines predicates capturing common closure properties of language classes.

A language class `P : Language α → Prop` is *closed* under an operation if applying the
operation to languages in `P` yields another language in `P`.

For same-alphabet operations (union, intersection, complement, concatenation, Kleene star,
reversal, intersection/quotient with regular), closedness is expressed as a property of
`P : Language α → Prop`.

For cross-alphabet operations (string homomorphism, ε-free homomorphism), closedness is
expressed as a property of an alphabet-indexed predicate
`isP : ∀ {α : Type*}, Language α → Prop`.

## Main definitions

- `ClosedUnderUnion`
- `ClosedUnderIntersection`
- `ClosedUnderComplement`
- `ClosedUnderConcatenation`
- `ClosedUnderKleeneStar`
- `ClosedUnderReverse`
- `ClosedUnderIntersectionWithRegular`
- `ClosedUnderRightQuotient`
- `ClosedUnderRightQuotientWithRegular`
- `ClosedUnderHomomorphism`
- `ClosedUnderEpsFreeHomomorphism`
- `ClosedUnderInverseHomomorphism`
- `ClosedUnderSubstitution`
-/

variable {α : Type*}

/-- A language class is closed under union. -/
def ClosedUnderUnion (P : Language α → Prop) : Prop :=
  ∀ L₁ L₂ : Language α, P L₁ → P L₂ → P (L₁ + L₂)

/-- A language class is closed under intersection. -/
def ClosedUnderIntersection (P : Language α → Prop) : Prop :=
  ∀ L₁ L₂ : Language α, P L₁ → P L₂ → P (L₁ ⊓ L₂)

/-- A language class is closed under complement. -/
def ClosedUnderComplement (P : Language α → Prop) : Prop :=
  ∀ L : Language α, P L → P Lᶜ

/-- A language class is closed under concatenation. -/
def ClosedUnderConcatenation (P : Language α → Prop) : Prop :=
  ∀ L₁ L₂ : Language α, P L₁ → P L₂ → P (L₁ * L₂)

/-- A language class is closed under Kleene star. -/
def ClosedUnderKleeneStar (P : Language α → Prop) : Prop :=
  ∀ L : Language α, P L → P (KStar.kstar L)

/-- A language class is closed under language reversal. -/
def ClosedUnderReverse (P : Language α → Prop) : Prop :=
  ∀ L : Language α, P L → P L.reverse

/-- A language class is closed under intersection with regular languages. -/
def ClosedUnderIntersectionWithRegular (P : Language α → Prop) : Prop :=
  ∀ L : Language α, P L → ∀ R : Language α, R.IsRegular → P (L ⊓ R)

/-- A language class is closed under right quotient (with any language from the same class). -/
def ClosedUnderRightQuotient (P : Language α → Prop) : Prop :=
  ∀ L₁ L₂ : Language α, P L₁ → P L₂ → P (Language.rightQuotient L₁ L₂)

/-- A language class is closed under right quotient with regular languages. -/
def ClosedUnderRightQuotientWithRegular (P : Language α → Prop) : Prop :=
  ∀ L : Language α, P L → ∀ R : Language α, R.IsRegular → P (Language.rightQuotient L R)

/-- An alphabet-indexed language class is closed under string homomorphism.

Here `isP` is a predicate on languages that is uniform across alphabets.
Note: `Language.homomorphicImage` works in universe `Type`, so `isP` ranges over `Type`. -/
def ClosedUnderHomomorphism (isP : ∀ {α : Type}, Language α → Prop) : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] (L : Language α) (h : α → List β),
    isP L → isP (L.homomorphicImage h)

/-- An alphabet-indexed language class is closed under ε-free string homomorphism. -/
def ClosedUnderEpsFreeHomomorphism (isP : ∀ {α : Type}, Language α → Prop) : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] (L : Language α) (h : α → List β),
    IsEpsFreeHomomorphism h → isP L → isP (L.homomorphicImage h)

/-- An alphabet-indexed language class is closed under inverse string homomorphism.

The inverse homomorphic image of `L : Language β` under `h : α → List β` is
`{ w : List α | w.flatMap h ∈ L }`. Both alphabets are finite, matching the
finite-alphabet convention used by the other cross-alphabet closure predicates. -/
def ClosedUnderInverseHomomorphism (isP : ∀ {α : Type}, Language α → Prop) : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] (L : Language β) (h : α → List β),
    isP L → isP { w : List α | w.flatMap h ∈ L }

/-- An alphabet-indexed language class is closed under substitution.

Both alphabets are finite, matching the finite-alphabet convention used by the
TM-recognizability bridge and the other cross-alphabet closure predicates. -/
def ClosedUnderSubstitution (isP : ∀ {α : Type}, Language α → Prop) : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] (L : Language α) (f : α → Language β),
    isP L → (∀ a, isP (f a)) → isP (L.subst f)

/-! ## Strictness from property mismatch -/

/-- If `P ⊆ Q`, `P` has a class property `X`, `Q` does not, and `X` is invariant
under pointwise equivalence of language classes, then the inclusion `P ⊆ Q` is strict.

The invariance hypothesis is necessary: an arbitrary predicate transformer
`X : (Language α → Prop) → Prop` need not be transportable from `P` to an extensionally
equal class. -/
theorem strict_subset_of_subset_different_property
    {P Q : Language α → Prop} {X : (Language α → Prop) → Prop}
    (hsub : ∀ L, P L → Q L)
    (hX_iff : ∀ {R S : Language α → Prop}, (∀ L, R L ↔ S L) → X R → X S)
    (hPX : X P)
    (hQnotX : ¬ X Q) :
    (setOf P : Set (Language α)) ⊂ (setOf Q : Set (Language α)) := by
  refine ⟨hsub, ?_⟩
  intro hQsubP
  apply hQnotX
  refine hX_iff ?_ hPX
  intro L
  exact ⟨hsub L, fun hQL => hQsubP hQL⟩
