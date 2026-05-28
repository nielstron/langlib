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

/-- Union closure is invariant under pointwise equivalence of language classes. -/
theorem ClosedUnderUnion_of_iff {P Q : Language α → Prop}
    (hiff : ∀ L, P L ↔ Q L) :
    ClosedUnderUnion P → ClosedUnderUnion Q := by
  intro hP L₁ L₂ hL₁ hL₂
  exact (hiff (L₁ + L₂)).1 (hP L₁ L₂ ((hiff L₁).2 hL₁) ((hiff L₂).2 hL₂))

/-- Intersection closure is invariant under pointwise equivalence of language classes. -/
theorem ClosedUnderIntersection_of_iff {P Q : Language α → Prop}
    (hiff : ∀ L, P L ↔ Q L) :
    ClosedUnderIntersection P → ClosedUnderIntersection Q := by
  intro hP L₁ L₂ hL₁ hL₂
  exact (hiff (L₁ ⊓ L₂)).1 (hP L₁ L₂ ((hiff L₁).2 hL₁) ((hiff L₂).2 hL₂))

/-- Complement closure is invariant under pointwise equivalence of language classes. -/
theorem ClosedUnderComplement_of_iff {P Q : Language α → Prop}
    (hiff : ∀ L, P L ↔ Q L) :
    ClosedUnderComplement P → ClosedUnderComplement Q := by
  intro hP L hQL
  exact (hiff Lᶜ).1 (hP L ((hiff L).2 hQL))

/-- Concatenation closure is invariant under pointwise equivalence of language classes. -/
theorem ClosedUnderConcatenation_of_iff {P Q : Language α → Prop}
    (hiff : ∀ L, P L ↔ Q L) :
    ClosedUnderConcatenation P → ClosedUnderConcatenation Q := by
  intro hP L₁ L₂ hL₁ hL₂
  exact (hiff (L₁ * L₂)).1 (hP L₁ L₂ ((hiff L₁).2 hL₁) ((hiff L₂).2 hL₂))

/-- Kleene-star closure is invariant under pointwise equivalence of language classes. -/
theorem ClosedUnderKleeneStar_of_iff {P Q : Language α → Prop}
    (hiff : ∀ L, P L ↔ Q L) :
    ClosedUnderKleeneStar P → ClosedUnderKleeneStar Q := by
  intro hP L hQL
  exact (hiff (KStar.kstar L)).1 (hP L ((hiff L).2 hQL))

/-- Reverse closure is invariant under pointwise equivalence of language classes. -/
theorem ClosedUnderReverse_of_iff {P Q : Language α → Prop}
    (hiff : ∀ L, P L ↔ Q L) :
    ClosedUnderReverse P → ClosedUnderReverse Q := by
  intro hP L hQL
  exact (hiff L.reverse).1 (hP L ((hiff L).2 hQL))

/-- Closure under intersection with regular languages is invariant under pointwise
equivalence of language classes. -/
theorem ClosedUnderIntersectionWithRegular_of_iff {P Q : Language α → Prop}
    (hiff : ∀ L, P L ↔ Q L) :
    ClosedUnderIntersectionWithRegular P → ClosedUnderIntersectionWithRegular Q := by
  intro hP L hQL R hR
  exact (hiff (L ⊓ R)).1 (hP L ((hiff L).2 hQL) R hR)

/-- Right-quotient closure is invariant under pointwise equivalence of language classes. -/
theorem ClosedUnderRightQuotient_of_iff {P Q : Language α → Prop}
    (hiff : ∀ L, P L ↔ Q L) :
    ClosedUnderRightQuotient P → ClosedUnderRightQuotient Q := by
  intro hP L₁ L₂ hL₁ hL₂
  exact (hiff (Language.rightQuotient L₁ L₂)).1
    (hP L₁ L₂ ((hiff L₁).2 hL₁) ((hiff L₂).2 hL₂))

/-- Closure under right quotient with regular languages is invariant under pointwise
equivalence of language classes. -/
theorem ClosedUnderRightQuotientWithRegular_of_iff {P Q : Language α → Prop}
    (hiff : ∀ L, P L ↔ Q L) :
    ClosedUnderRightQuotientWithRegular P → ClosedUnderRightQuotientWithRegular Q := by
  intro hP L hQL R hR
  exact (hiff (Language.rightQuotient L R)).1 (hP L ((hiff L).2 hQL) R hR)

/-- Homomorphism closure is invariant under pointwise equivalence of alphabet-indexed
language classes. -/
theorem ClosedUnderHomomorphism_of_iff
    {isP isQ : ∀ {α : Type}, Language α → Prop}
    (hiff : ∀ {β : Type} (L : Language β), isP L ↔ isQ L) :
    ClosedUnderHomomorphism isP → ClosedUnderHomomorphism isQ := by
  intro hP α β _ _ L h hQL
  exact (hiff (L.homomorphicImage h)).1 (hP L h ((hiff L).2 hQL))

/-- Epsilon-free homomorphism closure is invariant under pointwise equivalence of
alphabet-indexed language classes. -/
theorem ClosedUnderEpsFreeHomomorphism_of_iff
    {isP isQ : ∀ {α : Type}, Language α → Prop}
    (hiff : ∀ {β : Type} (L : Language β), isP L ↔ isQ L) :
    ClosedUnderEpsFreeHomomorphism isP → ClosedUnderEpsFreeHomomorphism isQ := by
  intro hP α β _ _ L h heps hQL
  exact (hiff (L.homomorphicImage h)).1 (hP L h heps ((hiff L).2 hQL))

/-- Inverse-homomorphism closure is invariant under pointwise equivalence of
alphabet-indexed language classes. -/
theorem ClosedUnderInverseHomomorphism_of_iff
    {isP isQ : ∀ {α : Type}, Language α → Prop}
    (hiff : ∀ {β : Type} (L : Language β), isP L ↔ isQ L) :
    ClosedUnderInverseHomomorphism isP → ClosedUnderInverseHomomorphism isQ := by
  intro hP α β _ _ L h hQL
  exact (hiff { w : List α | w.flatMap h ∈ L }).1 (hP L h ((hiff L).2 hQL))

/-- Substitution closure is invariant under pointwise equivalence of alphabet-indexed
language classes. -/
theorem ClosedUnderSubstitution_of_iff
    {isP isQ : ∀ {α : Type}, Language α → Prop}
    (hiff : ∀ {β : Type} (L : Language β), isP L ↔ isQ L) :
    ClosedUnderSubstitution isP → ClosedUnderSubstitution isQ := by
  intro hP α β _ _ L f hQL hfQ
  exact (hiff (L.subst f)).1
    (hP L f ((hiff L).2 hQL) (fun a => (hiff (f a)).2 (hfQ a)))

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
