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

/-- Recursive languages are not closed under arbitrary right quotient over any finite
alphabet into which the binary witness alphabet embeds. -/
public theorem Recursive_notClosedUnderRightQuotient_of_embedding {α : Type}
    [Fintype α] (e : Bool ↪ α) :
    ¬ ClosedUnderRightQuotient (α := α) is_Recursive := by
  letI : DecidableEq α := Classical.decEq α
  letI : Primcodable α :=
    Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.truncEquivFin α).out
  intro hclosed
  apply Recursive_notClosedUnderRightQuotientWithRegular_of_embedding e
  intro L hL R hR
  exact hclosed L R hL (is_Recursive_of_isRegular hR)

/-- Recursive languages are not closed under arbitrary right quotient over any finite
alphabet with at least two symbols. -/
public theorem Recursive_notClosedUnderRightQuotient_of_card {α : Type}
    [Fintype α] (hα : 2 ≤ Fintype.card α) :
    ¬ ClosedUnderRightQuotient (α := α) is_Recursive := by
  letI : DecidableEq α := Classical.decEq α
  letI : Primcodable α :=
    Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.truncEquivFin α).out
  intro hclosed
  apply Recursive_notClosedUnderRightQuotientWithRegular_of_card hα
  intro L hL R hR
  exact hclosed L R hL (is_Recursive_of_isRegular hR)

end
