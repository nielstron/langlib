import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Closure.Bijection
import Langlib.Classes.DeterministicContextFree.Closure.Bijection
import Langlib.Classes.DeterministicContextFree.Examples.AnBmCm
import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
import Langlib.Utilities.ClosurePredicates

/-! # Deterministic Context-Free Non-Closure Under Intersection

This file transfers the existing CFL intersection counterexample to DCFLs by giving
deterministic presentations of the two witness languages.
-/


/-- `{aⁿbⁿcⁿ | n ≥ 0}` is not deterministic context-free. -/
theorem notDCF_lang_eq_eq : ¬ is_DCF lang_eq_eq := by
  intro h
  exact notCF_lang_eq_eq (is_CF_of_is_DCF h)

/-- The existing CFL intersection witnesses also disprove DCFL intersection closure
once they are shown deterministic context-free. -/
theorem DCF_notClosedUnderIntersection_of_lang_eq_any_witnesses
    (hEqAny : is_DCF lang_eq_any) (hAnyEq : is_DCF lang_any_eq) :
    ¬ ClosedUnderIntersection (α := Fin 3) is_DCF := by
  intro hclosed
  apply notDCF_lang_eq_eq
  convert hclosed lang_eq_any lang_any_eq hEqAny hAnyEq
  ext w
  constructor
  · exact intersection_of_lang_eq_eq
  · exact lang_eq_eq_of_intersection

/-- Deterministic context-free languages over `Fin 3` are not closed under intersection. -/
theorem DCF_notClosedUnderIntersection :
    ¬ ClosedUnderIntersection (α := Fin 3) is_DCF :=
  DCF_notClosedUnderIntersection_of_lang_eq_any_witnesses
    DCFLIntersection.DCF_lang_eq_any
    DCFLIntersection.DCF_lang_any_eq

private lemma Language.map_inf_injective {α β : Type} {f : α → β} (hf : Function.Injective f)
    (L₁ L₂ : Language α) :
    Language.map f (L₁ ⊓ L₂) = Language.map f L₁ ⊓ Language.map f L₂ := by
  ext w
  constructor
  · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
    exact ⟨⟨v, hv1, rfl⟩, ⟨v, hv2, rfl⟩⟩
  · rintro ⟨⟨v1, hv1, hmap1⟩, ⟨v2, hv2, hmap2⟩⟩
    have heq : v1 = v2 := by
      apply List.map_injective_iff.mpr hf
      rw [hmap1, hmap2]
    subst heq
    exact ⟨v1, ⟨hv1, hv2⟩, hmap1⟩

/-- Deterministic context-free languages are not closed under intersection for any finite
alphabet containing three distinct symbols. -/
theorem DCF_notClosedUnderIntersection_of_three {α : Type} [Fintype α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ClosedUnderIntersection (α := α) is_DCF := by
  intro hclosed
  let f : Fin 3 → α := fun i => ![a, b, c] i
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hEqAny : is_DCF (Language.map f lang_eq_any) :=
    DCF_of_map_injective_DCF hf lang_eq_any DCFLIntersection.DCF_lang_eq_any
  have hAnyEq : is_DCF (Language.map f lang_any_eq) :=
    DCF_of_map_injective_DCF hf lang_any_eq DCFLIntersection.DCF_lang_any_eq
  have hinter : is_DCF (Language.map f (lang_eq_any ⊓ lang_any_eq)) := by
    rw [Language.map_inf_injective hf]
    exact hclosed (Language.map f lang_eq_any) (Language.map f lang_any_eq) hEqAny hAnyEq
  have hCFpre : is_CF (lang_eq_any ⊓ lang_any_eq) :=
    CF_of_map_injective_CF_rev hf _ (is_CF_of_is_DCF hinter)
  apply notCF_lang_eq_eq
  convert hCFpre
  ext w
  constructor
  · exact intersection_of_lang_eq_eq
  · exact lang_eq_eq_of_intersection

/-- Deterministic context-free languages are not closed under intersection for any finite
alphabet with at least three symbols. -/
theorem DCF_notClosedUnderIntersection_of_card {α : Type} [Fintype α]
    (hα : 3 ≤ Fintype.card α) :
    ¬ ClosedUnderIntersection (α := α) is_DCF := by
  let π : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let e : Fin 3 ↪ α := (Fin.castLEEmb hα).trans π.symm.toEmbedding
  exact DCF_notClosedUnderIntersection_of_three
    (e 0) (e 1) (e 2)
    (fun h => by simpa using e.injective h)
    (fun h => by simpa using e.injective h)
    (fun h => by simpa using e.injective h)
