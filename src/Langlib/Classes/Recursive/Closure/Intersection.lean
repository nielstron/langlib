module

public import Langlib.Classes.Recursive.Decidability.Membership

/-!
# Recursive Closure Under Intersection

This file proves that recursive languages are closed under intersection.

The proof reuses the existing computability bridge: recursive languages have computable
membership predicates, Boolean conjunction composes those deciders, and a total computable
Boolean decider yields a recursive language.
-/

variable {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]

/-- Recursive languages over finite, primcodable alphabets are closed under intersection. -/
public theorem is_Recursive_intersection {L₁ L₂ : Language T}
    (h₁ : is_Recursive L₁) (h₂ : is_Recursive L₂) :
    is_Recursive (L₁ ⊓ L₂) := by
  obtain ⟨f₁, hf₁, hs₁⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable h₁)
  obtain ⟨f₂, hf₂, hs₂⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable h₂)
  refine is_Recursive_of_computable_decide (L₁ ⊓ L₂) (fun w => f₁ w && f₂ w)
    ((Primrec.and.to_comp).comp hf₁ hf₂) ?_
  intro w
  have hw₁ : w ∈ L₁ ↔ f₁ w = true := by
    simpa using (iff_of_eq (congrFun hs₁ w))
  have hw₂ : w ∈ L₂ ↔ f₂ w = true := by
    simpa using (iff_of_eq (congrFun hs₂ w))
  rw [Language.mem_inf]
  simp [hw₁, hw₂, Bool.and_eq_true]

/-- The class of recursive languages is closed under intersection. -/
public theorem Recursive_closedUnderIntersection :
    ClosedUnderIntersection (α := T) is_Recursive :=
  fun _ _ h₁ h₂ => is_Recursive_intersection h₁ h₂
