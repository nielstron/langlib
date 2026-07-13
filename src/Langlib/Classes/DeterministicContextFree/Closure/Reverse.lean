module

public import Langlib.Classes.DeterministicContextFree.Closure.Bijection
public import Langlib.Classes.DeterministicContextFree.Closure.Homomorphism
public import Langlib.Classes.DeterministicContextFree.Closure.InverseHomomorphism
public import Langlib.Classes.DeterministicContextFree.Closure.QuotientRegular
public import Langlib.Classes.Regular.Closure.Union
public import Langlib.Classes.Regular.Examples.SingletonWord

@[expose]
public section

/-!
# Deterministic Context-Free Languages Are Not Closed Under Reversal

The counterargument packages two DPDAs behind distinct leading markers.  If DCFLs
were closed under reversal, those markers would move to the right.  Regular right
quotient removes either marker, a second reversal restores the payloads, and inverse
homomorphism removes the payload tag.  This would make DCFLs closed under union,
contradicting the established union counterexample.

The construction first gives a five-symbol witness alphabet `Bool ⊕ Fin 3`.  An
injective relabelling then transports failure to every finite alphabet with at least
five symbols.
-/

open DCFHomomorphism

namespace DCFReverse

variable {T : Type} [Fintype T]

/-- The two one-letter branch markers. -/
private def choiceMarkers : Language (Bool ⊕ T) :=
  ({[Sum.inl false]} : Language (Bool ⊕ T)) + {[Sum.inl true]}

private theorem choiceMarkers_isRegular :
    (choiceMarkers (T := T)).IsRegular :=
  (singletonWordLanguage_isRegular [Sum.inl false]).add'
    (singletonWordLanguage_isRegular [Sum.inl true])

/-- Reversing a marked choice and removing its final marker leaves the union of
the two reversed, tagged payload languages. -/
private theorem reverse_markedChoice_quotient (L₁ L₂ : Language T) :
    (markedChoice L₁ L₂).reverse / choiceMarkers (T := T) =
      (Language.map (Sum.inr : T → Bool ⊕ T) L₁).reverse +
        (Language.map (Sum.inr : T → Bool ⊕ T) L₂).reverse := by
  ext x
  constructor
  · rintro ⟨v, hv, hxv⟩
    change v ∈
      ({[Sum.inl false]} : Language (Bool ⊕ T)) + {[Sum.inl true]} at hv
    rw [Language.mem_add] at hv
    rcases hv with hv | hv
    · have hv' : v = [Sum.inl false] := by simpa using hv
      subst v
      change (x ++ [Sum.inl false]).reverse ∈ markedChoice L₁ L₂ at hxv
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hxv
      simp only [markedChoice] at hxv
      rw [Language.mem_add]
      rcases hxv with ⟨w, hwEq, hw⟩ | ⟨w, hwEq, _⟩
      · left
        change x.reverse ∈ Language.map Sum.inr L₁
        exact ⟨w, hw, List.cons.inj hwEq |>.2.symm⟩
      · cases List.cons.inj hwEq |>.1
    · have hv' : v = [Sum.inl true] := by simpa using hv
      subst v
      change (x ++ [Sum.inl true]).reverse ∈ markedChoice L₁ L₂ at hxv
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hxv
      simp only [markedChoice] at hxv
      rw [Language.mem_add]
      rcases hxv with ⟨w, hwEq, _⟩ | ⟨w, hwEq, hw⟩
      · cases List.cons.inj hwEq |>.1
      · right
        change x.reverse ∈ Language.map Sum.inr L₂
        exact ⟨w, hw, List.cons.inj hwEq |>.2.symm⟩
  · rw [Language.mem_add]
    rintro (hx | hx)
    · change x.reverse ∈ Language.map Sum.inr L₁ at hx
      rcases hx with ⟨w, hw, hmap⟩
      refine ⟨[Sum.inl false], ?_, ?_⟩
      · change [Sum.inl false] ∈
          ({[Sum.inl false]} : Language (Bool ⊕ T)) + {[Sum.inl true]}
        rw [Language.mem_add]
        exact Or.inl (Set.mem_singleton _)
      · change (x ++ [Sum.inl false]).reverse ∈ markedChoice L₁ L₂
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
        simp only [markedChoice]
        exact Or.inl ⟨w, by simp [hmap], hw⟩
    · change x.reverse ∈ Language.map Sum.inr L₂ at hx
      rcases hx with ⟨w, hw, hmap⟩
      refine ⟨[Sum.inl true], ?_, ?_⟩
      · change [Sum.inl true] ∈
          ({[Sum.inl false]} : Language (Bool ⊕ T)) + {[Sum.inl true]}
        rw [Language.mem_add]
        exact Or.inr (Set.mem_singleton _)
      · change (x ++ [Sum.inl true]).reverse ∈ markedChoice L₁ L₂
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
        simp only [markedChoice]
        exact Or.inr ⟨w, by simp [hmap], hw⟩

/-- Inverse-tagging the union of two tagged languages recovers their union. -/
private theorem inverse_tagged_union (L₁ L₂ : Language T) :
    ({w : List T |
      w.flatMap (fun a => [(Sum.inr a : Bool ⊕ T)]) ∈
        Language.map (Sum.inr : T → Bool ⊕ T) L₁ +
          Language.map (Sum.inr : T → Bool ⊕ T) L₂} : Language T) =
      L₁ + L₂ := by
  ext w
  have hflat : w.flatMap (fun a => [(Sum.inr a : Bool ⊕ T)]) =
      w.map (Sum.inr : T → Bool ⊕ T) := by
    induction w with
    | nil => rfl
    | cons a w ih => simp [ih]
  change
    (w.flatMap (fun a => [(Sum.inr a : Bool ⊕ T)]) ∈
      Language.map (Sum.inr : T → Bool ⊕ T) L₁ +
        Language.map (Sum.inr : T → Bool ⊕ T) L₂) ↔ w ∈ L₁ + L₂
  rw [hflat]
  rw [Language.mem_add, Language.mem_add]
  constructor
  · rintro (⟨u, hu, heq⟩ | ⟨u, hu, heq⟩)
    · left
      have : u = w := List.map_injective_iff.mpr Sum.inr_injective heq
      simpa [this] using hu
    · right
      have : u = w := List.map_injective_iff.mpr Sum.inr_injective heq
      simpa [this] using hu
  · rintro (hw | hw)
    · exact Or.inl ⟨w, hw, rfl⟩
    · exact Or.inr ⟨w, hw, rfl⟩

/-- Reversal closure together with regular-quotient closure would force ordinary
union closure on the payload alphabet. -/
private theorem union_of_reverse_and_regularQuotient
    (hreverse : ClosedUnderReverse (α := Bool ⊕ T) is_DCF)
    (hquotient : ClosedUnderRightQuotientWithRegular (α := Bool ⊕ T) is_DCF)
    {L₁ L₂ : Language T} (hL₁ : is_DCF L₁) (hL₂ : is_DCF L₂) :
    is_DCF (L₁ + L₂) := by
  have hmarked : is_DCF (markedChoice L₁ L₂) := DCF_markedChoice hL₁ hL₂
  have hreversed : is_DCF (markedChoice L₁ L₂).reverse :=
    hreverse (markedChoice L₁ L₂) hmarked
  have hstripped : is_DCF
      ((Language.map (Sum.inr : T → Bool ⊕ T) L₁).reverse +
        (Language.map (Sum.inr : T → Bool ⊕ T) L₂).reverse) := by
    have h := hquotient (markedChoice L₁ L₂).reverse hreversed
      (choiceMarkers (T := T)) choiceMarkers_isRegular
    change is_DCF
      ((markedChoice L₁ L₂).reverse / (choiceMarkers (T := T))) at h
    rwa [reverse_markedChoice_quotient] at h
  have htagged : is_DCF
      (Language.map (Sum.inr : T → Bool ⊕ T) L₁ +
        Language.map (Sum.inr : T → Bool ⊕ T) L₂) := by
    have h := hreverse _ hstripped
    simpa using h
  have hinverse := DCF_closedUnderInverseHomomorphism
    (Language.map (Sum.inr : T → Bool ⊕ T) L₁ +
      Language.map (Sum.inr : T → Bool ⊕ T) L₂)
    (fun a : T => [(Sum.inr a : Bool ⊕ T)]) htagged
  rwa [inverse_tagged_union] at hinverse

end DCFReverse

/-- If regular right quotient is available, DCFLs over the five-symbol marked
alphabet cannot be closed under reversal. -/
public theorem DCF_notClosedUnderReverse_of_regularQuotient
    (hquotient : ClosedUnderRightQuotientWithRegular
      (α := Bool ⊕ Fin 3) is_DCF) :
    ¬ ClosedUnderReverse (α := Bool ⊕ Fin 3) is_DCF := by
  intro hreverse
  apply DCF_notClosedUnderUnion
  intro L₁ L₂ hL₁ hL₂
  exact DCFReverse.union_of_reverse_and_regularQuotient
    hreverse hquotient hL₁ hL₂

/-- Deterministic context-free languages over the five-symbol marked alphabet are
not closed under reversal. -/
public theorem DCF_notClosedUnderReverse :
    ¬ ClosedUnderReverse (α := Bool ⊕ Fin 3) is_DCF :=
  DCF_notClosedUnderReverse_of_regularQuotient
    DCF_closedUnderRightQuotientWithRegular

private theorem Language.map_reverse {α β : Type} (f : α → β) (L : Language α) :
    Language.map f L.reverse = (Language.map f L).reverse := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (w.map f).reverse ∈ Language.map f L
    exact ⟨w.reverse, hw, by simp⟩
  · intro hx
    change x.reverse ∈ Language.map f L at hx
    rcases hx with ⟨w, hw, hmap⟩
    refine ⟨w.reverse, Language.reverse_mem_reverse.mpr hw, ?_⟩
    have := congrArg List.reverse hmap
    simpa [List.map_reverse] using this

/-- DCFL reversal non-closure transports through any embedding of the five-symbol
witness alphabet. -/
public theorem DCF_notClosedUnderReverse_of_embedding {α : Type} [Fintype α]
    (e : (Bool ⊕ Fin 3) ↪ α) :
    ¬ ClosedUnderReverse (α := α) is_DCF := by
  intro hclosed
  apply DCF_notClosedUnderReverse
  intro L hL
  have hmapped : is_DCF (Language.map e L) :=
    DCF_of_map_injective_DCF e.injective L hL
  have hreversed : is_DCF (Language.map e L).reverse :=
    hclosed (Language.map e L) hmapped
  rw [← Language.map_reverse] at hreversed
  exact DCF_of_map_injective_DCF_rev e.injective L.reverse hreversed

/-- DCFLs are not closed under reversal over any finite alphabet with at least five
symbols. -/
public theorem DCF_notClosedUnderReverse_of_card {α : Type} [Fintype α]
    (hα : 5 ≤ Fintype.card α) :
    ¬ ClosedUnderReverse (α := α) is_DCF := by
  let πW : (Bool ⊕ Fin 3) ≃ Fin (Fintype.card (Bool ⊕ Fin 3)) :=
    Fintype.equivFin (Bool ⊕ Fin 3)
  let πA : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have hWA : Fintype.card (Bool ⊕ Fin 3) ≤ Fintype.card α := by
    simpa using hα
  exact DCF_notClosedUnderReverse_of_embedding
    (πW.toEmbedding.trans ((Fin.castLEEmb hWA).trans πA.symm.toEmbedding))

end
