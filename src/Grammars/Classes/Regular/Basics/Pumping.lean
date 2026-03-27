import Mathlib

/-! # Regular Pumping Lemma

This file provides a tiny wrapper around mathlib's pumping lemma for regular languages.

## Main declarations

- `Language.IsRegular.pumping'`
-/

namespace Language

variable {α : Type*}

/-- A regular language satisfies the pumping lemma. -/
theorem IsRegular.pumping' {L : Language α} (h : L.IsRegular) :
    ∃ n : ℕ, ∀ x ∈ L, n ≤ x.length →
      ∃ a b c : List α,
        x = a ++ b ++ c ∧
        a.length + b.length ≤ n ∧
        b ≠ [] ∧
        {a} * ({b}∗) * {c} ≤ L := by
  exact h.pumping

end Language
