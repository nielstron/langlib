module

public import Langlib.Classes.Recursive.Closure.Homomorphism
public import Langlib.Classes.Recursive.Examples.SingletonWord

@[expose]
public section

/-!
# Recursive Non-Closure Under Substitution

Recursive languages are not closed under finite-alphabet substitution.  If they were,
then substituting each source symbol by the singleton language containing its homomorphic
image would imply closure under arbitrary string homomorphism, contradicting
`Recursive_notClosedUnderHomomorphism`.
-/

/-- Recursive languages are not closed under substitution. -/
public theorem Recursive_notClosedUnderSubstitution :
    ¬ ClosedUnderSubstitution is_Recursive := by
  intro hsubst
  exact Recursive_notClosedUnderHomomorphism (by
    intro α β _ _ L h hL
    classical
    haveI : DecidableEq β := Classical.decEq _
    haveI : Primcodable β :=
      Primcodable.ofEquiv (Fin (Fintype.card β)) (Fintype.truncEquivFin β).out
    have hsingle : ∀ a : α, is_Recursive ({h a} : Language β) := by
      intro a
      exact singletonWordLanguage_is_Recursive (h a)
    have hsub : is_Recursive (L.subst fun a => ({h a} : Language β)) :=
      hsubst L (fun a => ({h a} : Language β)) hL hsingle
    simpa [Language.homomorphicImage] using hsub)

end
