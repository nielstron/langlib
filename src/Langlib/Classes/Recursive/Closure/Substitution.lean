module

public import Langlib.Classes.Recursive.Closure.Homomorphism
public import Langlib.Classes.Recursive.Inclusion.Regular
public import Langlib.Utilities.ClosurePredicates

/-!
# Recursive Substitution Reductions

This file records reductions around the missing recursive substitution and
homomorphism nonclosure facts.
-/

/-- Recursive closure under substitution would imply recursive closure under homomorphism. -/
public theorem Recursive_closedUnderHomomorphism_of_closedUnderSubstitution
    (hsubst : ClosedUnderSubstitution is_Recursive) :
    ClosedUnderHomomorphism is_Recursive := by
  intro α β _ _ L h hL
  have hsingletons : ∀ a, is_Recursive (({h a} : Language β)) :=
    fun a => is_Recursive_singleton_word (h a)
  exact hsubst L (fun a => ({h a} : Language β)) hL hsingletons

/-- Recursive homomorphism nonclosure implies recursive substitution nonclosure. -/
public theorem Recursive_notClosedUnderSubstitution_of_notClosedUnderHomomorphism
    (hhom : ¬ ClosedUnderHomomorphism is_Recursive) :
    ¬ ClosedUnderSubstitution is_Recursive := by
  intro hsubst
  exact hhom (Recursive_closedUnderHomomorphism_of_closedUnderSubstitution hsubst)

/-- Once the bounded-halting source is known recursive, recursive languages cannot be
closed under substitution. -/
public theorem Recursive_notClosedUnderSubstitution_of_boundedHaltingSource_recursive
    (hbounded : is_Recursive boundedHaltingSource) :
    ¬ ClosedUnderSubstitution is_Recursive :=
  Recursive_notClosedUnderSubstitution_of_notClosedUnderHomomorphism
    (Recursive_notClosedUnderHomomorphism_of_boundedHaltingSource_recursive hbounded)
