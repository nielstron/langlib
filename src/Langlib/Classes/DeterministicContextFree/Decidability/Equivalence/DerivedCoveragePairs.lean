module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedRepeat
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TailEliminationSupport

@[expose]
public section

/-!
# Viewing schema coverages as derived path pairs

Balancing-result constructors return active-schema coverages.  Their concrete
pair and certificate derivation are exactly the data required by
`TracePath.DerivedPairAt`.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Forget the schema presentation and retain the certificate-derived pair at
the corresponding path level. -/
public def ActiveSchemaCoverage.toDerivedPairAt
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {width level : ℕ} {word : List (Label Action)}
    (coverage :
      ActiveSchemaCoverage g initialLeft initialRight width word)
    (hword : word = path.word level) :
    path.DerivedPairAt level := by
  subst word
  exact
    { left := coverage.left
      right := coverage.right
      derivation := coverage.derivation }

/-- Witnessed active coverages yield the same derived pair. -/
public def WitnessedActiveSchemaCoverage.toDerivedPairAt
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {width level : ℕ} {word : List (Label Action)}
    (coverage :
      WitnessedActiveSchemaCoverage g initialLeft initialRight width word)
    (hword : word = path.word level) :
    path.DerivedPairAt level :=
  coverage.coverage.toDerivedPairAt hword

/-- Bounded witnessed coverages also yield the underlying derived pair. -/
public def BoundedWitnessedActiveSchemaCoverage.toDerivedPairAt
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {bound width level : ℕ} {arguments : List RegularTerm}
    {word : List (Label Action)}
    (coverage : BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight bound width arguments word)
    (hword : word = path.word level) :
    path.DerivedPairAt level :=
  coverage.witnessed.toDerivedPairAt hword

end EncodedFirstOrderGrammar

end DCFEquivalence
