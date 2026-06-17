module

public import Langlib.Classes.Regular.Examples.AnBn
@[expose]
public section



/-! # Existence of Non-Regular Languages

This file derives the existence of a non-regular language from the concrete witness
`anbn` and its non-regularity proof in `Langlib.Classes.Regular.Examples.AnBn`.

## Main declarations

- `exists_nonRegular_language` — There exists a non-regular language over `Bool`.
- `exists_nonRegular_language_of_nontrivial` — There exists a non-regular language over
  any nontrivial alphabet.
-/

open Language List

/-- There exists a non-regular language over `Bool`. -/
theorem exists_nonRegular_language : ∃ L : Language Bool, ¬ L.IsRegular :=
  ⟨anbn, anbn_not_isRegular⟩

/-- There exists a non-regular language over any alphabet admitting an injective coding
of `Bool`. -/
public theorem exists_nonRegular_language_of_injective_bool {T : Type*} (f : Bool → T)
    (hf : Function.Injective f) :
    ∃ L : Language T, ¬ L.IsRegular :=
  ⟨Language.map f anbn, map_anbn_not_isRegular hf⟩

/-- There exists a non-regular language over any alphabet with two distinguished symbols. -/
public theorem exists_nonRegular_language_of_pair {T : Type*} (a b : T) (hab : a ≠ b) :
    ∃ L : Language T, ¬ L.IsRegular := by
  let f : Bool → T := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  exact exists_nonRegular_language_of_injective_bool f hf

/-- There exists a non-regular language over any nontrivial alphabet. -/
public theorem exists_nonRegular_language_of_nontrivial {T : Type*} [Nontrivial T] :
    ∃ L : Language T, ¬ L.IsRegular := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  exact exists_nonRegular_language_of_pair a b hab

/-- There exists a non-regular language over any finite alphabet with at least two symbols. -/
public theorem exists_nonRegular_language_of_card {T : Type*} [Fintype T] (hT : 2 ≤ Fintype.card T) :
    ∃ L : Language T, ¬ L.IsRegular := by
  let π : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let e : Fin 2 ↪ T := (Fin.castLEEmb hT).trans π.symm.toEmbedding
  exact exists_nonRegular_language_of_pair (e 0) (e 1) (by intro h; simpa using e.injective h)
