import Mathlib

/-! # Existence of Non-Regular Languages

This file proves the existence of a non-regular language over `Bool`, using the
Myhill–Nerode theorem. The language `{aⁿbⁿ | n ∈ ℕ}` (encoded with `false` = a, `true` = b)
is shown to have infinitely many distinct left quotients, hence is not regular.

## Main declarations

- `anbn` — The language `{aⁿbⁿ | n ∈ ℕ}`.
- `anbn_not_isRegular` — Proof that `anbn` is not regular.
- `exists_nonRegular_language` — There exists a non-regular language over `Bool`.
-/

open Language List

/-- The language `{aⁿbⁿ}` over `Bool`, where `false` represents `a` and `true` represents `b`. -/
def anbn : Language Bool :=
  { w | ∃ n : ℕ, w = List.replicate n false ++ List.replicate n true }

/-- Left quotient of `anbn` by `replicate k false` contains `replicate k true`. -/
lemma anbn_leftQuotient_replicate_false (k : ℕ) :
    List.replicate k true ∈ anbn.leftQuotient (List.replicate k false) := by
  show List.replicate k false ++ List.replicate k true ∈ anbn
  exact ⟨k, rfl⟩

/-- Left quotient of `anbn` by `replicate k false` does NOT contain `replicate j true`
    when `j ≠ k`. -/
lemma anbn_leftQuotient_replicate_false_ne {k j : ℕ} (hjk : j ≠ k) :
    List.replicate j true ∉ anbn.leftQuotient (List.replicate k false) := by
  show ¬(List.replicate k false ++ List.replicate j true ∈ anbn)
  intro ⟨n, hn⟩
  have := congr_arg ( fun x : List Bool => x.count false ) hn ; norm_num at this;
  simp_all +decide [ List.count_replicate ]

/-- The left quotients of `anbn` indexed by `replicate k false` are pairwise distinct. -/
lemma anbn_leftQuotient_injective :
    Function.Injective (fun k : ℕ => anbn.leftQuotient (List.replicate k false)) := by
  intro k₁ k₂ h
  by_contra hne
  have hmem := anbn_leftQuotient_replicate_false k₁
  have : anbn.leftQuotient (List.replicate k₁ false) = anbn.leftQuotient (List.replicate k₂ false) := h
  rw [this] at hmem
  exact anbn_leftQuotient_replicate_false_ne hne hmem

/-- The range of left quotients of `anbn` is infinite. -/
lemma anbn_leftQuotient_range_infinite :
    ¬ (Set.range anbn.leftQuotient).Finite := by
  intro hfin
  have hsub : Set.range (fun k : ℕ => anbn.leftQuotient (List.replicate k false)) ⊆
      Set.range anbn.leftQuotient := by
    rintro _ ⟨k, rfl⟩
    exact ⟨List.replicate k false, rfl⟩
  exact Set.infinite_range_of_injective anbn_leftQuotient_injective (hfin.subset hsub)

/-- The language `{aⁿbⁿ}` is not regular. -/
theorem anbn_not_isRegular : ¬ anbn.IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  exact anbn_leftQuotient_range_infinite

/-- There exists a non-regular language over `Bool`. -/
theorem exists_nonRegular_language : ∃ L : Language Bool, ¬ L.IsRegular :=
  ⟨anbn, anbn_not_isRegular⟩