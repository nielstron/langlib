module

public import Langlib.Classes.Recursive.Closure.QuotientRegular
public import Langlib.Classes.Regular.Inclusion.Recursive

@[expose]
public section

/-!
# Recursive Non-Closure Under Right Quotient

Recursive languages are not closed under right quotient.  This follows from the stronger
counterexample for right quotient by a regular language, since every regular language is
recursive.
-/

/-- Recursive languages are not closed under right quotient. -/
public theorem Recursive_notClosedUnderRightQuotient :
    ¬ ClosedUnderRightQuotient (α := Bool) is_Recursive := by
  intro hclosed
  exact Recursive_notClosedUnderRightQuotientWithRegular (by
    intro L hL R hR
    exact hclosed L R hL (is_Recursive_of_isRegular hR))

end
