/-
Copyright (c) 2026 Langlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Utilities.Homomorphism
import Langlib.Utilities.LanguageOperations

/-! # Abstract Closure Predicates for Language Classes

This file defines predicates capturing common closure properties of language classes.

A language class `P : Set (Language α)` is *closed* under an operation if applying the
operation to languages in `P` yields another language in `P`.

For same-alphabet operations (union, intersection, complement, concatenation, Kleene star,
reversal, intersection/quotient with regular), closedness is expressed as a property of
`P : Set (Language α)`.

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
- `ClosedUnderRightQuotientWithRegular`
- `ClosedUnderHomomorphism`
- `ClosedUnderEpsFreeHomomorphism`
-/

variable {α : Type*}

/-- A language class is closed under union. -/
def ClosedUnderUnion (P : Set (Language α)) : Prop :=
  ∀ L₁ L₂ : Language α, L₁ ∈ P → L₂ ∈ P → L₁ + L₂ ∈ P

/-- A language class is closed under intersection. -/
def ClosedUnderIntersection (P : Set (Language α)) : Prop :=
  ∀ L₁ L₂ : Language α, L₁ ∈ P → L₂ ∈ P → L₁ ⊓ L₂ ∈ P

/-- A language class is closed under complement. -/
def ClosedUnderComplement (P : Set (Language α)) : Prop :=
  ∀ L : Language α, L ∈ P → Lᶜ ∈ P

/-- A language class is closed under concatenation. -/
def ClosedUnderConcatenation (P : Set (Language α)) : Prop :=
  ∀ L₁ L₂ : Language α, L₁ ∈ P → L₂ ∈ P → L₁ * L₂ ∈ P

/-- A language class is closed under Kleene star. -/
def ClosedUnderKleeneStar (P : Set (Language α)) : Prop :=
  ∀ L : Language α, L ∈ P → KStar.kstar L ∈ P

/-- A language class is closed under language reversal. -/
def ClosedUnderReverse (P : Set (Language α)) : Prop :=
  ∀ L : Language α, L ∈ P → L.reverse ∈ P

/-- A language class is closed under intersection with regular languages. -/
def ClosedUnderIntersectionWithRegular (P : Set (Language α)) : Prop :=
  ∀ L : Language α, L ∈ P → ∀ R : Language α, R.IsRegular → L ⊓ R ∈ P

/-- A language class is closed under right quotient with regular languages. -/
def ClosedUnderRightQuotientWithRegular (P : Set (Language α)) : Prop :=
  ∀ L : Language α, L ∈ P → ∀ R : Language α, R.IsRegular → Language.rightQuotient L R ∈ P

/-- An alphabet-indexed language class is closed under string homomorphism.

Here `isP` is a predicate on languages that is uniform across alphabets.
Note: `Language.homomorphicImage` works in universe `Type`, so `isP` ranges over `Type`. -/
def ClosedUnderHomomorphism (isP : ∀ {α : Type}, Language α → Prop) : Prop :=
  ∀ {α β : Type} (L : Language α) (h : α → List β),
    isP L → isP (L.homomorphicImage h)

/-- An alphabet-indexed language class is closed under ε-free string homomorphism. -/
def ClosedUnderEpsFreeHomomorphism (isP : ∀ {α : Type}, Language α → Prop) : Prop :=
  ∀ {α β : Type} (L : Language α) (h : α → List β),
    IsEpsFreeHomomorphism h → isP L → isP (L.homomorphicImage h)
