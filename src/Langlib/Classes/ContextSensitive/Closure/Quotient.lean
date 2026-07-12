module

public import Langlib.Automata.FiniteState.Equivalence.Regular
public import Langlib.Classes.ContextFree.Inclusion.ContextSensitive
public import Langlib.Classes.ContextSensitive.Closure.QuotientRegular
public import Langlib.Classes.Regular.Inclusion.ContextFree

@[expose]
public section

/-!
# Context-Sensitive Languages Are Not Closed Under Right Quotient

The failure already occurs when the denominator is regular, so arbitrary right-quotient
closure is impossible as well.
-/

/-- Context-sensitive languages are not closed under arbitrary right quotient. -/
public theorem CS_notClosedUnderRightQuotient :
    ¬ ClosedUnderRightQuotient (α := Option Unit) is_CS := by
  intro hclosed
  apply CS_notClosedUnderRightQuotientWithRegular
  intro L hL R hR
  exact hclosed L R hL (is_CS_of_is_CF (is_CF_of_is_RG ((is_RG_iff_isRegular).mpr hR)))

end
