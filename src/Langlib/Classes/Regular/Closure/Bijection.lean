import Mathlib
import Langlib.Utilities.LanguageOperations

/-! # Regular Closure Under Terminal Bijection

This file packages regular-language transport lemmas for renaming terminals.

## Main declarations

- `Language.IsRegular.preimage`
- `Language.IsRegular.of_map_injective`
- `isRegular_of_bijemap_isRegular`
- `isRegular_of_bijemap_isRegular_rev`
- `isRegular_bijemap_iff_isRegular`
-/

namespace Language

/-- Regular languages are closed under preimage along `List.map`. -/
theorem IsRegular.preimage {α β : Type} {L : Language α} (h : L.IsRegular) (f : β → α) :
    Language.IsRegular (((List.map f) ⁻¹' L : Set (List β))) := by
  rcases h with ⟨σ, hσ, M, hM⟩
  exact ⟨σ, hσ, M.comap f, by simpa [hM] using (DFA.accepts_comap (M := M) f)⟩

/-- Injective alphabet maps reflect regularity. -/
theorem IsRegular.of_map_injective {α β : Type} {L : Language α} {f : α → β}
    (hf : Function.Injective f) (h : (Language.map f L).IsRegular) : L.IsRegular := by
  have hpre : Language.IsRegular (((List.map f) ⁻¹' Language.map f L : Set (List α))) := h.preimage f
  have hEq : (List.map f) ⁻¹' Language.map f L = L := by
    ext w
    constructor
    · change (∃ u ∈ L, List.map f u = List.map f w) → w ∈ L
      rintro ⟨u, hu, huw⟩
      simpa [hf.list_map huw] using hu
    · intro hw
      exact ⟨w, hw, rfl⟩
  simpa [hEq] using hpre

end Language

variable {T₁ T₂ : Type}

/-- Regular languages are closed under bijections of the terminal alphabet. -/
theorem isRegular_of_bijemap_isRegular (π : T₁ ≃ T₂) (L : Language T₁) :
    L.IsRegular → (Language.bijemapLang L π).IsRegular := by
  intro h
  simpa [Language.bijemapLang] using h.preimage π.symm

/-- Reverse direction of `isRegular_of_bijemap_isRegular`. -/
theorem isRegular_of_bijemap_isRegular_rev (π : T₁ ≃ T₂) (L : Language T₁) :
    (Language.bijemapLang L π).IsRegular → L.IsRegular := by
  intro h
  simpa [Language.bijemapLang_symm_bijemapLang] using
    isRegular_of_bijemap_isRegular π.symm (Language.bijemapLang L π) h

/-- A language is regular iff its image under a bijection of terminal alphabets is regular. -/
@[simp] theorem isRegular_bijemap_iff_isRegular (π : T₁ ≃ T₂) (L : Language T₁) :
    (Language.bijemapLang L π).IsRegular ↔ L.IsRegular := by
  constructor
  · exact isRegular_of_bijemap_isRegular_rev π L
  · exact isRegular_of_bijemap_isRegular π L
