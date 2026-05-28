module

public import Langlib.Utilities.ClosurePredicates
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



/-! # Transport for Closure Predicates

This file records that the standard language-class closure predicates are
extensional: they transport across pointwise equivalence of language classes.
-/

variable {α : Type*}

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
public theorem ClosedUnderComplement_of_iff {P Q : Language α → Prop}
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
