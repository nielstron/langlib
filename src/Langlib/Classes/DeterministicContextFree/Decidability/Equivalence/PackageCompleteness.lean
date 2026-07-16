module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalCertificateLifting
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OpenSoundBasis
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SelfCertifyingPackage

@[expose]
public section

/-!
# From a stable sufficient basis to a positive package

The query certificate may be constructed in the original grammar and replayed
in the critical-marker extension.  Consequently, package completeness has one
additional, sharply isolated obligation: every canonical critical instance of
the same fixed original open-sound basis must have a root certificate in that
extension.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Canonical critical instances of the bounded original open-sound basis are
all derivable under that same basis in the marker extension. -/
@[expose] public def CriticalInstancesDerivableAt
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  ∀ schema ∈ g.boundedOpenSoundBasis bound,
    CertificateDerivable (g.withCriticalMarkers bound)
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity))
      (g.boundedOpenSoundBasis bound) (.nop [])

/-- An original query derivation and stable critical-instance derivations
assemble into the exact finite witness consumed by the positive semidecider. -/
public theorem hasSelfCertifyingPackage_of_boundedOpenSound_derivations
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (bound : ℕ)
    (hquery : CertificateDerivable g initialLeft initialRight
      (g.boundedOpenSoundBasis bound) (.nop []))
    (hcritical : g.CriticalInstancesDerivableAt bound) :
    HasSelfCertifyingPackage (g, (initialLeft, initialRight)) := by
  let basis := g.boundedOpenSoundBasis bound
  have hbasis : ∀ schema ∈ basis,
      schema.left.WellFormed g.ranks schema.arity ∧
        schema.right.WellFormed g.ranks schema.arity := by
    intro schema hschema
    have hmem := (g.mem_boundedOpenSoundBasis_iff bound schema).mp hschema
    have hwell := hmem.2.2.2.1
    unfold basisPairWellFormedCode at hwell
    rw [Bool.and_eq_true] at hwell
    exact hwell
  have hcount : ∀ schema ∈ basis, schema.arity ≤ bound := by
    intro schema hschema
    exact (g.mem_boundedOpenSoundBasis_iff bound schema).mp hschema |>.1
  have hqueryExtended : CertificateDerivable (g.withCriticalMarkers bound)
      initialLeft initialRight basis (.nop []) := by
    simpa [basis, liftCriticalJudgment] using
      hquery.withCriticalMarkers bound
  apply exists_acceptedSelfCertifyingWitness_of_derivations
    (input := (g, (initialLeft, initialRight))) bound basis
      hbasis hcount hqueryExtended
  intro schema hschema
  exact hcritical schema hschema

end EncodedFirstOrderGrammar

end DCFEquivalence
