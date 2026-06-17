module

public import Langlib.Automata.FiniteState.Equivalence.Regular
public import Langlib.Classes.Recursive.Inclusion.ByTapeFromComputable
public import Langlib.Classes.Regular.Decidability.Membership

@[expose]
public section

/-! # Regular Languages Included in Recursive Languages

This file proves that every regular language over a finite, encodable alphabet is
recursive, by composing the existing computable regular-membership predicate with
the generic construction of a recursive language from a total computable Boolean
decider.

## Main results

- `is_Recursive_of_isRegular` — every Mathlib-regular language is recursive.
- `is_Recursive_of_is_RG` — every right-regular grammar language is recursive.
- `RG_subclass_Recursive` — class-level inclusion `RG ⊆ Recursive`.
-/

variable {T : Type}

/-- Every Mathlib-regular language over a finite alphabet is recursive. -/
public theorem is_Recursive_of_isRegular [Fintype T] [DecidableEq T] [Primcodable T]
    {L : Language T} (hL : L.IsRegular) : is_Recursive L := by
  classical
  obtain ⟨f, hf, hspec⟩ :=
    ComputablePred.computable_iff.mp (regular_membership_computablePred L hL)
  exact is_Recursive_of_computable_decide L f hf fun w => by
    rw [congrFun hspec w]

/-- Every right-regular grammar language over a finite alphabet is recursive. -/
public theorem is_Recursive_of_is_RG [Fintype T] [DecidableEq T] [Primcodable T]
    {L : Language T} (hL : is_RG L) : is_Recursive L :=
  is_Recursive_of_isRegular (isRegular_of_is_RG hL)

/-- The regular languages are included in the recursive languages. -/
public theorem RG_subclass_Recursive [Fintype T] [DecidableEq T] [Primcodable T] :
    (RG : Set (Language T)) ⊆ (Recursive : Set (Language T)) :=
  fun _ hL => is_Recursive_of_is_RG hL
