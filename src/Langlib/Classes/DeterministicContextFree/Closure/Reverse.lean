module

public import Langlib.Classes.DeterministicContextFree.Closure.Homomorphism
public import Langlib.Utilities.LanguageOperations

/-!
# Deterministic Context-Free Reverse Reductions

This file records small reductions around the missing DCFL reverse and right-quotient
nonclosure facts.
-/

variable {T : Type} [Fintype T]

/-- DCFL reverse closure would imply closure under right quotient by a singleton word. -/
public theorem DCF_closedUnderRightQuotientSingleton_of_closedUnderReverse
    (hrev : ClosedUnderReverse (α := T) is_DCF)
    (L : Language T) (x : List T) (hL : is_DCF L) :
    is_DCF (L / ({x} : Language T)) := by
  have hrevL : is_DCF L.reverse := hrev L hL
  have hleft : is_DCF (x.reverse \\ L.reverse) :=
    DCFHomomorphism.DCF_leftQuotient_word x.reverse hrevL
  have hresult : is_DCF ((x.reverse \\ L.reverse).reverse) :=
    hrev (x.reverse \\ L.reverse) hleft
  rw [Language.reverse_leftQuotient_eq_rightQuotient_reverse_singleton] at hresult
  simpa [Language.reverse_reverse] using hresult
