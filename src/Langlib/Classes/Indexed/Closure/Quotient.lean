module

public import Langlib.Classes.Indexed.Closure.Injection
public import Langlib.Classes.Indexed.Examples.AbnPowMCopy
public import Langlib.Classes.Indexed.Examples.AbnPowN
public import Langlib.Utilities.ClosurePredicates

@[expose]
public section

/-!
# Indexed languages are not closed under arbitrary right quotient

For the binary intersection witnesses `A` and `B`, the balanced-copy
numerator and denominator from `Langlib.Examples.AbnPowMCopy` have
right quotient equal to the injective image of
`A ∩ B = {(a b^n)^n | n > 0}`.  Both operands are indexed, while the
shrinking theorem shows that this diagonal quotient is not indexed.
-/

open List

/-- The quotient result itself is not indexed. -/
public theorem abnPowMCopy_quotient_not_is_Indexed :
    ¬ is_Indexed (abnPowMCopy / abnPowMCopyDenominator) := by
  rw [abnPowMCopy_quotient_eq_abnPowN]
  intro hmap
  exact abnPowN_not_is_Indexed
    (Indexed_of_map_injective_Indexed_rev copyCode_injective
      abnPowN hmap)

/-- Indexed languages over the three-symbol copy alphabet are not closed under
arbitrary right quotient. -/
public theorem Indexed_notClosedUnderRightQuotient :
    ¬ ClosedUnderRightQuotient (α := CopyLetter) is_Indexed := by
  intro hclosed
  exact abnPowMCopy_quotient_not_is_Indexed
    (hclosed abnPowMCopy abnPowMCopyDenominator
      abnPowMCopy_is_Indexed abnPowMCopyDenominator_is_Indexed)

private theorem Language.map_rightQuotient_of_injective
    {alpha beta : Type} {f : alpha → beta} (hf : Function.Injective f)
    (L R : Language alpha) :
    Language.map f (Language.rightQuotient L R) =
      Language.rightQuotient (Language.map f L) (Language.map f R) := by
  ext w
  constructor
  · rintro ⟨u, ⟨v, hvR, huvL⟩, rfl⟩
    exact ⟨v.map f, ⟨v, hvR, rfl⟩, ⟨u ++ v, huvL, by simp⟩⟩
  · rintro ⟨v, ⟨v₀, hv₀R, rfl⟩, ⟨z, hzL, hz⟩⟩
    have hz' : z.map f = w ++ v₀.map f := by simpa using hz
    obtain ⟨w₀, v₁, hz_eq, hw₀, hv₁⟩ := List.map_eq_append_iff.mp hz'
    have hv₁_eq : v₁ = v₀ := List.map_injective_iff.mpr hf hv₁
    subst v₁
    rw [← hw₀]
    refine ⟨w₀, ⟨v₀, hv₀R, ?_⟩, rfl⟩
    change L (w₀ ++ v₀)
    change L z at hzL
    simpa [hz_eq] using hzL

/-- Nonclosure transports to every alphabet containing the three-symbol
witness alphabet. -/
public theorem Indexed_notClosedUnderRightQuotient_of_embedding
    {alpha : Type} (e : CopyLetter ↪ alpha) :
    ¬ ClosedUnderRightQuotient (α := alpha) is_Indexed := by
  intro hclosed
  apply Indexed_notClosedUnderRightQuotient
  intro L R hL hR
  have hq := hclosed (Language.map e L) (Language.map e R)
    (Indexed_of_map_injective_Indexed e.injective L hL)
    (Indexed_of_map_injective_Indexed e.injective R hR)
  rw [← Language.map_rightQuotient_of_injective e.injective] at hq
  exact Indexed_of_map_injective_Indexed_rev e.injective _ hq

/-- Indexed languages are not closed under arbitrary right quotient over every
finite alphabet with at least three symbols. -/
public theorem Indexed_notClosedUnderRightQuotient_of_card
    {alpha : Type} [Fintype alpha] (halpha : 3 ≤ Fintype.card alpha) :
    ¬ ClosedUnderRightQuotient (α := alpha) is_Indexed := by
  let piC : CopyLetter ≃ Fin (Fintype.card CopyLetter) :=
    Fintype.equivFin CopyLetter
  let piA : alpha ≃ Fin (Fintype.card alpha) := Fintype.equivFin alpha
  have hCA : Fintype.card CopyLetter ≤ Fintype.card alpha := by
    rw [show Fintype.card CopyLetter = 3 by rfl]
    exact halpha
  exact Indexed_notClosedUnderRightQuotient_of_embedding
    (piC.toEmbedding.trans ((Fin.castLEEmb hCA).trans piA.symm.toEmbedding))
