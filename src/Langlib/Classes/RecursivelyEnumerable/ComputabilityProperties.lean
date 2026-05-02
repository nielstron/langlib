import Langlib.Classes.RecursivelyEnumerable.Decidability.Membership
import Langlib.Classes.RecursivelyEnumerable.Decidability.Emptiness
import Langlib.Classes.RecursivelyEnumerable.Decidability.Universality
import Langlib.Classes.RecursivelyEnumerable.Decidability.Equivalence
import Langlib.Utilities.ComputabilityPredicates

/-!
# Uniform Computability Properties of Recursively Enumerable Languages

This file restates the TM0/partial-recursive-code undecidability results using the
abstract computability predicates from `Langlib.Utilities.ComputabilityPredicates`.

The encoded object is a `Nat.Partrec.Code`. For domain properties we view a code as
a language over the one-letter alphabet `Unit`: a word `w` is accepted exactly when
the code halts on input `w.length`. For equivalence of computed partial functions we
use a graph language over `(ℕ × ℕ)`, where the singleton word `[(n, y)]` records that
the code returns `y` on input `n`.

## Main results

- `recursivelyEnumerable_computableMembership_undecidable`
- `recursivelyEnumerable_computableEmptiness_undecidable`
- `recursivelyEnumerable_computableUniversality_undecidable`
- `recursivelyEnumerable_computableEquivalence_undecidable`
-/

open Nat.Partrec

/-- The domain language of a partial-recursive code, represented over `Unit`.

The word length is the program input. -/
def partrecCodeDomainLanguageOf (c : Code) : Language Unit :=
  fun w => (c.eval w.length).Dom

/-- The graph language of a partial-recursive code.

Only singleton words are meaningful: `[(n, y)]` means that the code returns `y` on
input `n`. -/
def partrecCodeGraphLanguageOf (c : Code) : Language (ℕ × ℕ)
  | [(n, y)] => y ∈ c.eval n
  | _ => False

theorem partrecCodeDomainLanguage_empty_iff (c : Code) :
    partrecCodeDomainLanguageOf c = (∅ : Set (List Unit)) ↔
      ∀ n, ¬(c.eval n).Dom := by
  constructor
  · intro h n hn
    have hw : (List.replicate n ()) ∈ partrecCodeDomainLanguageOf c := by
      change (c.eval (List.replicate n ()).length).Dom
      simpa using hn
    have : (List.replicate n ()) ∈ (∅ : Set (List Unit)) := by
      simpa [h] using hw
    exact this
  · intro h
    ext w
    constructor
    · intro hw
      exact False.elim (h w.length (by simpa [partrecCodeDomainLanguageOf] using hw))
    · intro hw
      exact False.elim hw

theorem partrecCodeDomainLanguage_universal_iff (c : Code) :
    partrecCodeDomainLanguageOf c = (Set.univ : Set (List Unit)) ↔
      ∀ n, (c.eval n).Dom := by
  constructor
  · intro h n
    have hw : (List.replicate n ()) ∈ partrecCodeDomainLanguageOf c := by
      rw [h]
      trivial
    have hw' : (c.eval (List.replicate n ()).length).Dom := hw
    simpa using hw'
  · intro h
    ext w
    constructor
    · intro _
      trivial
    · intro _
      simpa [partrecCodeDomainLanguageOf] using h w.length

theorem partrecCodeGraphLanguage_eq_iff (p : Code × Code) :
    partrecCodeGraphLanguageOf p.1 = partrecCodeGraphLanguageOf p.2 ↔
      p.1.eval = p.2.eval := by
  constructor
  · intro h
    funext n
    apply Part.ext
    intro y
    constructor
    · intro hy
      have hw : [(n, y)] ∈ partrecCodeGraphLanguageOf p.1 := by
        simpa [partrecCodeGraphLanguageOf] using hy
      have hw' : [(n, y)] ∈ partrecCodeGraphLanguageOf p.2 := by
        simpa [h] using hw
      simpa [partrecCodeGraphLanguageOf] using hw'
    · intro hy
      have hw : [(n, y)] ∈ partrecCodeGraphLanguageOf p.2 := by
        simpa [partrecCodeGraphLanguageOf] using hy
      have hw' : [(n, y)] ∈ partrecCodeGraphLanguageOf p.1 := by
        simpa [h] using hw
      simpa [partrecCodeGraphLanguageOf] using hw'
  · intro h
    ext w
    cases w with
    | nil =>
        change False ↔ False
        simp
    | cons head tail =>
        cases tail with
        | nil =>
            rcases head with ⟨n, y⟩
            change y ∈ p.1.eval n ↔ y ∈ p.2.eval n
            rw [h]
        | cons head' tail' =>
            change False ↔ False
            simp

/-- Membership for RE codes is not uniformly computable. -/
theorem recursivelyEnumerable_computableMembership_undecidable :
    ¬ComputableMembership partrecCodeDomainLanguageOf := by
  intro h
  apply RE_membership_undecidable'.2
  have h_nil : ComputablePred
      (fun c : Code => ([] : List Unit) ∈ partrecCodeDomainLanguageOf c) := by
    unfold ComputableMembership at h
    rcases h with ⟨dec, hcomp⟩
    letI : DecidablePred
        (fun c : Code => ([] : List Unit) ∈ partrecCodeDomainLanguageOf c) :=
      fun c => dec (c, ([] : List Unit))
    exact ⟨inferInstance,
      hcomp.comp (Computable.pair Computable.id (Computable.const ([] : List Unit)))⟩
  exact h_nil.of_eq fun c => by
    change (c.eval 0).Dom ↔ (c.eval 0).Dom
    rfl

/-- Emptiness for RE codes is not uniformly computable. -/
theorem recursivelyEnumerable_computableEmptiness_undecidable :
    ¬ComputableEmptiness partrecCodeDomainLanguageOf := by
  intro h
  apply RE_emptiness_undecidable
  unfold ComputableEmptiness at h
  exact h.of_eq fun c => partrecCodeDomainLanguage_empty_iff c

/-- Universality for RE codes is not uniformly computable. -/
theorem recursivelyEnumerable_computableUniversality_undecidable :
    ¬ComputableUniversality partrecCodeDomainLanguageOf := by
  intro h
  apply RE_universality_undecidable
  unfold ComputableUniversality at h
  exact h.of_eq fun c => partrecCodeDomainLanguage_universal_iff c

/-- Equivalence for RE codes is not uniformly computable. -/
theorem recursivelyEnumerable_computableEquivalence_undecidable :
    ¬ComputableEquivalence partrecCodeGraphLanguageOf := by
  intro h
  apply RE_equivalence_undecidable
  unfold ComputableEquivalence at h
  exact h.of_eq fun p => partrecCodeGraphLanguage_eq_iff p
