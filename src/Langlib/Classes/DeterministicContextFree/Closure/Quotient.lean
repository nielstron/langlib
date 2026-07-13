module

public import Langlib.Classes.ContextFree.Closure.Quotient
public import Langlib.Classes.DeterministicContextFree.Examples.A2nBnPosStar
public import Langlib.Classes.DeterministicContextFree.Examples.BnAnPosStarB
public import Langlib.Classes.DeterministicContextFree.Closure.Bijection
public import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
public import Langlib.Utilities.ClosurePredicates

/-!
# Deterministic Context-Free Right Quotients

This file proves that deterministic context-free languages are not closed under
right quotient.  The witness is the same quotient used for CFL non-closure:

* `quotientNumerator = {a^(2n)b^n | n >= 1}*`
* `quotientDenominator = {b^n a^n | n >= 1}* {b}`

Both witness languages are deterministic context-free, by the DPDAs in
`DeterministicContextFree/Examples`.  If DCFLs were closed under right quotient,
their quotient would be a DCFL and therefore context-free, contradicting the
CFL pumping argument already proved in `ContextFree/Closure/Quotient`.
-/

open Language

/-- Deterministic context-free languages are not closed under right quotient. -/
public theorem DCF_notClosedUnderRightQuotient :
    ¬ ClosedUnderRightQuotient (α := Bool) is_DCF := by
  intro hclosed
  exact notCF_quotient
    (is_CF_of_is_DCF
      (hclosed quotientNumerator quotientDenominator
        DCFA2nBnPosStar.DCF_quotientNumerator
        DCFBnAnPosStarB.DCF_quotientDenominator))

private theorem Language.map_rightQuotient_injective {α β : Type} {f : α → β}
    (hf : Function.Injective f) (L R : Language α) :
    Language.map f (Language.rightQuotient L R) =
      Language.rightQuotient (Language.map f L) (Language.map f R) := by
  ext w
  constructor
  · rintro ⟨u, ⟨v, hvR, huvL⟩, rfl⟩
    exact ⟨v.map f, ⟨v, hvR, rfl⟩, ⟨u ++ v, huvL, by simp⟩⟩
  · rintro ⟨v, ⟨v₀, hv₀R, hv⟩, ⟨z, hzL, hz⟩⟩
    subst v
    have hz' : z.map f = w ++ v₀.map f := by simpa using hz
    obtain ⟨w₀, v₁, hz_eq, hw₀, hv₁⟩ := List.map_eq_append_iff.mp hz'
    have hv₁_eq : v₁ = v₀ := List.map_injective_iff.mpr hf hv₁
    subst v₁
    rw [← hw₀]
    exact ⟨w₀, ⟨v₀, hv₀R, by simpa [hz_eq] using hzL⟩, rfl⟩

/-- DCFLs are not closed under right quotient over any finite alphabet into which the
binary witness alphabet embeds. -/
public theorem DCF_notClosedUnderRightQuotient_of_embedding {α : Type} [Fintype α]
    (e : Bool ↪ α) :
    ¬ ClosedUnderRightQuotient (α := α) is_DCF := by
  intro hclosed
  apply DCF_notClosedUnderRightQuotient
  intro L R hL hR
  have hmL : is_DCF (Language.map e L) :=
    DCF_of_map_injective_DCF e.injective L hL
  have hmR : is_DCF (Language.map e R) :=
    DCF_of_map_injective_DCF e.injective R hR
  have hq := hclosed (Language.map e L) (Language.map e R) hmL hmR
  rw [← Language.map_rightQuotient_injective e.injective] at hq
  exact DCF_of_map_injective_DCF_rev e.injective _ hq

/-- DCFLs are not closed under right quotient over any finite alphabet with at least
two symbols. -/
public theorem DCF_notClosedUnderRightQuotient_of_card {α : Type} [Fintype α]
    (hα : 2 ≤ Fintype.card α) :
    ¬ ClosedUnderRightQuotient (α := α) is_DCF := by
  let πB : Bool ≃ Fin (Fintype.card Bool) := Fintype.equivFin Bool
  let πA : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have hBA : Fintype.card Bool ≤ Fintype.card α := by simpa using hα
  exact DCF_notClosedUnderRightQuotient_of_embedding
    (πB.toEmbedding.trans ((Fin.castLEEmb hBA).trans πA.symm.toEmbedding))
