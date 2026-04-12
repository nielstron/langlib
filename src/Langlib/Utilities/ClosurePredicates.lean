/-
Copyright (c) 2026 Langlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Utilities.Homomorphism
import Langlib.Utilities.LanguageOperations

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
  ∀ {α β : Type} (L : Language α) (h : α → List β),
    isP L → isP (L.homomorphicImage h)

/-- An alphabet-indexed language class is closed under ε-free string homomorphism. -/
def ClosedUnderEpsFreeHomomorphism (isP : ∀ {α : Type}, Language α → Prop) : Prop :=
  ∀ {α β : Type} (L : Language α) (h : α → List β),
    IsEpsFreeHomomorphism h → isP L → isP (L.homomorphicImage h)

/-- An alphabet-indexed language class is closed under inverse string homomorphism.

The inverse homomorphic image of `L : Language β` under `h : α → List β` is
`{ w : List α | w.flatMap h ∈ L }`. -/
def ClosedUnderInverseHomomorphism (isP : ∀ {α : Type}, Language α → Prop) : Prop :=
  ∀ {α β : Type} (L : Language β) (h : α → List β),
    isP L → isP { w : List α | w.flatMap h ∈ L }

/-- An alphabet-indexed language class is closed under substitution.

The source alphabet is assumed finite so the predicate matches the regular-language
substitution theorem formalized in this library. -/
def ClosedUnderSubstitution (isP : ∀ {α : Type}, Language α → Prop) : Prop :=
  ∀ {α β : Type} [Fintype α] (L : Language α) (f : α → Language β),
    isP L → (∀ a, isP (f a)) → isP (L.subst f)
