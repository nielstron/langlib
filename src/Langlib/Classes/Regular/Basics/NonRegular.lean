import Mathlib
import Langlib.Examples.AnBn
import Langlib.Classes.Regular.Closure.Bijection

/-! # Existence of Non-Regular Languages

This file proves the existence of a non-regular language, using the Myhill–Nerode
theorem. The language `{aⁿbⁿ | n ∈ ℕ}` (encoded with `false` = a, `true` = b) is shown
to have infinitely many distinct left quotients, hence is not regular.

## Main declarations

- `anbn_not_isRegular` — Proof that `anbn` is not regular.
- `exists_nonRegular_language` — There exists a non-regular language over `Bool`.
- `exists_nonRegular_language_of_nontrivial` — There exists a non-regular language over
  any nontrivial alphabet.
-/

open Language List

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

/-- Injective alphabet maps preserve the nonregularity of the `anbn` witness. -/
theorem map_anbn_not_isRegular {T : Type*} {f : Bool → T} (hf : Function.Injective f) :
    ¬ (Language.map f anbn).IsRegular := by
  intro h
  exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf h)

/-- There exists a non-regular language over any alphabet admitting an injective coding
of `Bool`. -/
theorem exists_nonRegular_language_of_injective_bool {T : Type*} (f : Bool → T)
    (hf : Function.Injective f) :
    ∃ L : Language T, ¬ L.IsRegular :=
  ⟨Language.map f anbn, map_anbn_not_isRegular hf⟩

/-- There exists a non-regular language over any alphabet with two distinguished symbols. -/
theorem exists_nonRegular_language_of_pair {T : Type*} (a b : T) (hab : a ≠ b) :
    ∃ L : Language T, ¬ L.IsRegular := by
  let f : Bool → T := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  exact exists_nonRegular_language_of_injective_bool f hf

/-- There exists a non-regular language over any nontrivial alphabet. -/
theorem exists_nonRegular_language_of_nontrivial {T : Type*} [Nontrivial T] :
    ∃ L : Language T, ¬ L.IsRegular := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  exact exists_nonRegular_language_of_pair a b hab

/-- There exists a non-regular language over any finite alphabet with at least two symbols. -/
theorem exists_nonRegular_language_of_card {T : Type*} [Fintype T] (hT : 2 ≤ Fintype.card T) :
    ∃ L : Language T, ¬ L.IsRegular := by
  let π : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let e : Fin 2 ↪ T := (Fin.castLEEmb hT).trans π.symm.toEmbedding
  exact exists_nonRegular_language_of_pair (e 0) (e 1) (by intro h; simpa using e.injective h)
