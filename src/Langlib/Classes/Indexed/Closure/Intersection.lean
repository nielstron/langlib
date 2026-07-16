module

public import Langlib.Classes.Indexed.Closure.Injection
public import Langlib.Classes.Indexed.Examples.DiagonalNotIndexed
public import Langlib.Utilities.ClosurePredicates
import Mathlib.Data.Fintype.EquivFin

@[expose]
public section

/-!
# Indexed languages are not closed under intersection

Over `Bool`, the indexed languages

* `indexedIntersectionA = {(a b^n)^m | n,m > 0}` and
* `indexedIntersectionB = {a b^n (a b*)^(n-1) | n > 0}`

intersect in the non-indexed diagonal language
`indexedIntersectionH = {(a b^n)^n | n > 0}`.  Injective terminal relabelling
transports this counterexample to every alphabet containing two distinct
symbols.
-/

open IndexedIntersectionWitness

namespace IndexedIntersectionNonclosure

private lemma map_inf_of_injective {α β : Type} {f : α → β}
    (hf : Function.Injective f) (L₁ L₂ : Language α) :
    Language.map f (L₁ ⊓ L₂) = Language.map f L₁ ⊓ Language.map f L₂ := by
  ext w
  constructor
  · rintro ⟨v, ⟨hv₁, hv₂⟩, rfl⟩
    exact ⟨⟨v, hv₁, rfl⟩, ⟨v, hv₂, rfl⟩⟩
  · rintro ⟨⟨v₁, hv₁, hmap₁⟩, ⟨v₂, hv₂, hmap₂⟩⟩
    have hv : v₁ = v₂ := by
      apply List.map_injective_iff.mpr hf
      rw [hmap₁, hmap₂]
    subst v₂
    exact ⟨v₁, ⟨hv₁, hv₂⟩, hmap₁⟩

/-- Indexed languages over the binary alphabet are not closed under
intersection. -/
public theorem Indexed_notClosedUnderIntersection :
    ¬ ClosedUnderIntersection (α := Bool) is_Indexed := by
  intro hclosed
  apply indexedIntersectionH_notIndexed
  rw [← indexedIntersectionA_inter_indexedIntersectionB]
  exact hclosed indexedIntersectionA indexedIntersectionB
    indexedIntersectionA_isIndexed indexedIntersectionB_isIndexed

/-- An injection of the binary alphabet transports failure of indexed
intersection closure to the target alphabet. -/
public theorem Indexed_notClosedUnderIntersection_of_embedding {α : Type}
    (e : Bool ↪ α) :
    ¬ ClosedUnderIntersection (α := α) is_Indexed := by
  intro hclosed
  apply Indexed_notClosedUnderIntersection
  intro L₁ L₂ hL₁ hL₂
  have hmap₁ : is_Indexed (Language.map e L₁) :=
    Indexed_of_map_injective_Indexed e.injective L₁ hL₁
  have hmap₂ : is_Indexed (Language.map e L₂) :=
    Indexed_of_map_injective_Indexed e.injective L₂ hL₂
  have hinter : is_Indexed (Language.map e L₁ ⊓ Language.map e L₂) :=
    hclosed (Language.map e L₁) (Language.map e L₂) hmap₁ hmap₂
  rw [← map_inf_of_injective e.injective] at hinter
  exact Indexed_of_map_injective_Indexed_rev e.injective (L₁ ⊓ L₂) hinter

/-- Indexed languages are not closed under intersection over any alphabet
containing two specified distinct symbols. -/
public theorem Indexed_notClosedUnderIntersection_of_two {α : Type}
    (a b : α) (hab : a ≠ b) :
    ¬ ClosedUnderIntersection (α := α) is_Indexed := by
  let e : Bool ↪ α :=
    { toFun := fun bit => if bit then b else a
      inj' := by
        intro x y hxy
        cases x <;> cases y <;> simp_all }
  exact Indexed_notClosedUnderIntersection_of_embedding e

/-- Indexed languages are not closed under intersection over any finite
alphabet with at least two symbols. -/
public theorem Indexed_notClosedUnderIntersection_of_card {α : Type}
    [Fintype α] (hα : 2 ≤ Fintype.card α) :
    ¬ ClosedUnderIntersection (α := α) is_Indexed := by
  have hcard : Fintype.card Bool ≤ Fintype.card α := by
    simpa using hα
  obtain ⟨e : Bool ↪ α⟩ :=
    Function.Embedding.nonempty_of_card_le hcard
  exact Indexed_notClosedUnderIntersection_of_embedding e

end IndexedIntersectionNonclosure
