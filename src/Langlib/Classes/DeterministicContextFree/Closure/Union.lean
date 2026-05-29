module

public import Langlib.Classes.DeterministicContextFree.Closure.Complement
public import Langlib.Classes.DeterministicContextFree.Closure.Intersection



/-! # Deterministic Context-Free Non-Closure Under Union

Deterministic context-free languages are closed under complement but not under
intersection.  If they were also closed under union, De Morgan's law would make
them closed under intersection, contradicting the existing intersection
counterexample.
-/

variable {T : Type} [Fintype T]

omit [Fintype T] in
private theorem language_inter_eq_compl_union_compl (L₁ L₂ : Language T) :
    L₁ ⊓ L₂ = (L₁ᶜ + L₂ᶜ)ᶜ := by
  ext w
  simp only [Language.add_def]
  change w ∈ L₁ ∧ w ∈ L₂ ↔ ¬ (w ∈ L₁ᶜ ⊔ L₂ᶜ)
  rw [show (L₁ᶜ ⊔ L₂ᶜ : Set (List T)) = Set.union L₁ᶜ L₂ᶜ by rfl]
  change w ∈ L₁ ∧ w ∈ L₂ ↔ ¬ (w ∉ L₁ ∨ w ∉ L₂)
  tauto

/-- DCFL union closure would imply DCFL intersection closure. -/
public theorem DCF_closedUnderIntersection_of_closedUnderUnion
    (hunion : ClosedUnderUnion (α := T) is_DCF) :
    ClosedUnderIntersection (α := T) is_DCF := by
  intro L₁ L₂ hL₁ hL₂
  rw [language_inter_eq_compl_union_compl]
  exact DCF_closedUnderComplement (L₁ᶜ + L₂ᶜ)
    (hunion L₁ᶜ L₂ᶜ
      (DCF_closedUnderComplement L₁ hL₁)
      (DCF_closedUnderComplement L₂ hL₂))

/-- Deterministic context-free languages over `Fin 3` are not closed under union. -/
public theorem DCF_notClosedUnderUnion :
    ¬ ClosedUnderUnion (α := Fin 3) is_DCF := by
  intro hunion
  exact DCF_notClosedUnderIntersection
    (DCF_closedUnderIntersection_of_closedUnderUnion hunion)

/-- Deterministic context-free languages are not closed under union for any finite
alphabet containing three distinct symbols. -/
public theorem DCF_notClosedUnderUnion_of_three {α : Type} [Fintype α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ClosedUnderUnion (α := α) is_DCF := by
  intro hunion
  exact DCF_notClosedUnderIntersection_of_three a b c hab hac hbc
    (DCF_closedUnderIntersection_of_closedUnderUnion hunion)

/-- Deterministic context-free languages are not closed under union for any finite
alphabet with at least three symbols. -/
public theorem DCF_notClosedUnderUnion_of_card {α : Type} [Fintype α]
    (hα : 3 ≤ Fintype.card α) :
    ¬ ClosedUnderUnion (α := α) is_DCF := by
  intro hunion
  exact DCF_notClosedUnderIntersection_of_card hα
    (DCF_closedUnderIntersection_of_closedUnderUnion hunion)
