import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.DeterministicContextFree.Examples.AnBmCm
import Langlib.Classes.DeterministicContextFree.Examples.AnBnCn
import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
import Langlib.Utilities.ClosurePredicates

/-! # Deterministic Context-Free Non-Closure Under Intersection

This file transfers the existing CFL intersection counterexample to DCFLs by giving
deterministic presentations of the two witness languages.
-/


/-- `{aⁿbⁿcⁿ | n ≥ 0}` is not deterministic context-free. -/
theorem notDCF_lang_eq_eq : ¬ is_DCF lang_eq_eq := by
  intro h
  exact notCF_lang_eq_eq (is_CF_of_is_DCF h)

/-- The existing CFL intersection witnesses also disprove DCFL intersection closure
once they are shown deterministic context-free. -/
theorem DCF_notClosedUnderIntersection_of_lang_eq_any_witnesses
    (hEqAny : is_DCF lang_eq_any) (hAnyEq : is_DCF lang_any_eq) :
    ¬ ClosedUnderIntersection (α := Fin 3) is_DCF := by
  intro hclosed
  apply notDCF_lang_eq_eq
  convert hclosed lang_eq_any lang_any_eq hEqAny hAnyEq
  ext w
  constructor
  · exact intersection_of_lang_eq_eq
  · exact lang_eq_eq_of_intersection

/-- Deterministic context-free languages over `Fin 3` are not closed under intersection. -/
theorem DCF_notClosedUnderIntersection :
    ¬ ClosedUnderIntersection (α := Fin 3) is_DCF :=
  DCF_notClosedUnderIntersection_of_lang_eq_any_witnesses
    DCFLIntersection.DCF_lang_eq_any
    DCFLIntersection.DCF_lang_any_eq
