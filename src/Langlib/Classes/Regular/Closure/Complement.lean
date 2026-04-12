import Mathlib
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
import Langlib.Utilities.ClosurePredicates

/-! # Regular Closure Under Complement (Iff)

This file proves that a language is regular if and only if its complement is regular.

## Main declarations

- `Language.isRegular_compl_iff`
-/

namespace Language

variable {α : Type*}

/-- A language is regular if and only if its complement is regular. -/
theorem isRegular_compl_iff {L : Language α} :
    Lᶜ.IsRegular ↔ L.IsRegular := by
  constructor
  · intro h
    rw [← compl_compl L]
    exact h.compl
  · exact IsRegular.compl

end Language

/-- The class of regular languages is closed under complement. -/
theorem RG_closedUnderComplement [Fintype α] : ClosedUnderComplement (α := α) is_RG := by
  intro L hL
  exact is_RG_of_isRegular (isRegular_of_is_RG hL |>.compl)
