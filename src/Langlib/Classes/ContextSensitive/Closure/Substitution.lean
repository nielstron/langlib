module

public import Langlib.Classes.ContextSensitive.Closure.Homomorphism
public import Langlib.Classes.ContextSensitive.Examples.SingletonWord

@[expose]
public section

/-!
# Context-Sensitive Non-Closure Under Substitution

Context-sensitive languages are not closed under finite-alphabet substitution. If they were,
then substituting each source symbol by the singleton language containing its homomorphic image
would imply closure under arbitrary string homomorphism, contradicting
`CS_notClosedUnderHomomorphism`.
-/

/-- Context-sensitive languages are not closed under substitution. -/
public theorem CS_notClosedUnderSubstitution :
    ¬ ClosedUnderSubstitution is_CS := by
  intro hsubst
  exact CS_notClosedUnderHomomorphism (by
    intro α β _ _ L h hL
    have hsingle : ∀ a : α, is_CS ({h a} : Language β) := by
      intro a
      exact singletonWordLanguage_is_CS (h a)
    have hsub : is_CS (L.subst fun a => ({h a} : Language β)) :=
      hsubst L (fun a => ({h a} : Language β)) hL hsingle
    simpa [Language.homomorphicImage] using hsub)

end
