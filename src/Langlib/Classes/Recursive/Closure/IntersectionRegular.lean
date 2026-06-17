module

public import Langlib.Classes.Recursive.Decidability.Membership
public import Langlib.Classes.Regular.Decidability.Membership

/-!
# Recursive Closure Under Intersection With Regular Languages

This file proves that recursive languages are closed under intersection with a regular
language.

The proof composes the computable membership predicate for the recursive language with the
DFA-derived computable membership predicate for the regular language.
-/

variable {T : Type} [DecidableEq T] [Fintype T] [Primcodable T]

/-- Recursive languages are closed under intersection with regular languages. -/
public theorem is_Recursive_intersection_regular {L R : Language T}
    (hL : is_Recursive L) (hR : R.IsRegular) :
    is_Recursive (L ⊓ R) := by
  obtain ⟨fL, hfL, hsL⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable hL)
  obtain ⟨fR, hfR, hsR⟩ :=
    ComputablePred.computable_iff.mp (regular_membership_computablePred R hR)
  refine is_Recursive_of_computable_decide (L ⊓ R) (fun w => fL w && fR w)
    ((Primrec.and.to_comp).comp hfL hfR) ?_
  intro w
  have hwL : w ∈ L ↔ fL w = true := by
    simpa using (iff_of_eq (congrFun hsL w))
  have hwR : w ∈ R ↔ fR w = true := by
    simpa using (iff_of_eq (congrFun hsR w))
  rw [Language.mem_inf]
  simp [hwL, hwR, Bool.and_eq_true]

/-- The class of recursive languages is closed under intersection with regular languages. -/
public theorem Recursive_closedUnderIntersectionWithRegular :
    ClosedUnderIntersectionWithRegular (α := T) is_Recursive :=
  fun _ hL _ hR => is_Recursive_intersection_regular hL hR
