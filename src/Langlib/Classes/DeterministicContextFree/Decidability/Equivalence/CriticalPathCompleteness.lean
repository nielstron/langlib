module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.GroundStepPreservation
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BasisPathCompactness
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PackageCompleteness

@[expose]
public section

/-!
# Stable path coverage for canonical critical instances

The ordinary active-stair theorem constructs certificates in the grammar in
which it runs.  For the self-certifying package, however, the critical-marker
extension must reuse one fixed basis of original open-sound schemas.  This
file states the exact compactness-layer invariant still needed: every infinite
path from every canonical critical instance reaches that original basis.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Every canonical critical instance of the bounded original basis is
covered, along every infinite path in the marker extension, by that same
original basis. -/
@[expose] public def CriticalInstancesEveryPathCoveredAt
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  ∀ schema ∈ g.boundedOpenSoundBasis bound,
    (g.withCriticalMarkers bound).EveryPathCoveredBy
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity))
      (g.boundedOpenSoundBasis bound)

/-- Stable path coverage is exactly strong enough for path compactness to
produce all critical-instance certificates required by the package checker. -/
public theorem criticalInstancesDerivableAt_of_everyPathCovered
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ}
    (hcovered : g.CriticalInstancesEveryPathCoveredAt bound) :
    g.CriticalInstancesDerivableAt bound := by
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
  let family := criticalInstanceFamily_of_originalBasis
    g hg basis bound hbasis hcount
  have hgExtended := g.withCriticalMarkers_wellFormed hg bound
  intro schema hschema
  have hmem := (g.mem_boundedOpenSoundBasis_iff bound schema).mp hschema
  have hopen := hmem.2.2.2
  have hequivalent : (g.withCriticalMarkers bound).TraceEquivalent
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity)) := by
    have hwell := hopen.1
    unfold basisPairWellFormedCode at hwell
    rw [Bool.and_eq_true] at hwell
    exact critical_traceEquivalent_of_open hg hmem.1
      hwell.1 hwell.2 hopen.2
  have hground : (g.withCriticalMarkers bound).groundPairCode
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity)) = true := by
    simpa [family, criticalInstanceFamily_of_originalBasis] using
      family.critical_ground schema hschema
  apply (g.withCriticalMarkers bound).derivable_nop_of_everyPathCoveredBy
    (guardedContextLaws_of_wellFormed hgExtended)
    (preservesGroundSteps_of_wellFormed hgExtended)
    hground hequivalent
  exact hcovered schema hschema

end EncodedFirstOrderGrammar

end DCFEquivalence
