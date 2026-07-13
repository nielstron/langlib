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

/-- Context-sensitive languages are not closed under arbitrary right quotient over any
finite alphabet into which the binary witness alphabet embeds. -/
public theorem CS_notClosedUnderRightQuotient_of_embedding {α : Type} [Fintype α]
    (e : Option Unit ↪ α) :
    ¬ ClosedUnderRightQuotient (α := α) is_CS := by
  intro hclosed
  apply CS_notClosedUnderRightQuotientWithRegular_of_embedding e
  intro L hL R hR
  exact hclosed L R hL (is_CS_of_is_CF (is_CF_of_is_RG ((is_RG_iff_isRegular).mpr hR)))

/-- Context-sensitive languages are not closed under arbitrary right quotient over any
finite alphabet with at least two symbols. -/
public theorem CS_notClosedUnderRightQuotient_of_card {α : Type} [Fintype α]
    (hα : 2 ≤ Fintype.card α) :
    ¬ ClosedUnderRightQuotient (α := α) is_CS := by
  intro hclosed
  apply CS_notClosedUnderRightQuotientWithRegular_of_card hα
  intro L hL R hR
  exact hclosed L R hL (is_CS_of_is_CF (is_CF_of_is_RG ((is_RG_iff_isRegular).mpr hR)))

end
