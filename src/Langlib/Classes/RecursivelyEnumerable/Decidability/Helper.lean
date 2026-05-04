import Mathlib
import Langlib.Utilities.ComputabilityPredicates

/-!
# Encodings for Uniform RE Computability Properties

This helper file provides concrete language views of `Nat.Partrec.Code` for the
uniform computability predicates used by the RE decidability files.
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

