module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerWidthReduction
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalPathCompleteness

@[expose]
public section

/-!
# Stable residual coverage implies critical-instance path coverage

This module isolates the remaining constructive obligation in the exact form
needed by package completeness.  Every critical-instance path must reach a
nonempty lifted-original prefix with an original open-sound residual schema
whose local presentation bound fits inside the one fixed global bound.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Every canonical critical-instance path reaches marker-stable coverage by
an original open-sound schema within the fixed global presentation bound. -/
@[expose] public def CriticalInstancesMarkerStableCoveredAt
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  ∀ schema ∈ g.boundedOpenSoundBasis bound,
    ∀ path : TracePath (g.withCriticalMarkers bound)
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity)),
      ∃ n localBound arity,
        ∃ stable : MarkerStableBoundedOpenSchemaCoverage g bound
          (schema.left.instantiate (g.criticalArguments schema.arity))
          (schema.right.instantiate (g.criticalArguments schema.arity))
          localBound arity (path.word n),
          localBound ≤ bound ∧
            g.OpenSoundBasisPair stable.coverage.schema

/-- Width reduction may expose the stronger endpoint directly: every critical
path reaches a zero-active-width regular schema which is marker-stable and
fits inside the fixed original bound.  Open soundness of its residual schema
is then a theorem, not an additional hypothesis. -/
@[expose] public def CriticalInstancesMarkerStableWidthZeroAt
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  ∀ schema ∈ g.boundedOpenSoundBasis bound,
    ∀ path : TracePath (g.withCriticalMarkers bound)
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity)),
      ∃ n localBound arity,
        ∃ _stable : MarkerStableBoundedActiveSchemaCoverage g bound
          (schema.left.instantiate (g.criticalArguments schema.arity))
          (schema.right.instantiate (g.criticalArguments schema.arity))
          localBound 0 arity (path.word n),
          localBound ≤ bound

/-- Marker-stable residual coverage discharges the exact arbitrary-basis path
obligation used by critical-instance compactness. -/
public theorem criticalInstancesEveryPathCovered_of_markerStable
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    (hstable : g.CriticalInstancesMarkerStableCoveredAt bound) :
    g.CriticalInstancesEveryPathCoveredAt bound := by
  intro schema hschema path
  obtain ⟨n, localBound, arity, stable, hbound, hopen⟩ :=
    hstable schema hschema path
  refine ⟨n, ⟨?_⟩⟩
  exact stable.toOriginalOpenSoundBasisCoverage bound hbound hopen

/-- The marker-stable path invariant already suffices for all canonical
critical-instance root certificates over the same original bounded basis. -/
public theorem criticalInstancesDerivableAt_of_markerStable
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ}
    (hstable : g.CriticalInstancesMarkerStableCoveredAt bound) :
    g.CriticalInstancesDerivableAt bound := by
  apply criticalInstancesDerivableAt_of_everyPathCovered hg
  exact criticalInstancesEveryPathCovered_of_markerStable hstable

/-- A marker-stable width-zero endpoint supplies the exact original-basis path
coverage required for all canonical critical instances. -/
public theorem criticalInstancesEveryPathCovered_of_markerStableWidthZero
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ}
    (hstable : g.CriticalInstancesMarkerStableWidthZeroAt bound) :
    g.CriticalInstancesEveryPathCoveredAt bound := by
  intro schema hschema path
  obtain ⟨n, localBound, arity, stable, hbound⟩ :=
    hstable schema hschema path
  have hmem := (g.mem_boundedOpenSoundBasis_iff bound schema).mp hschema
  have hopen := hmem.2.2.2
  have hwell := hopen.1
  unfold basisPairWellFormedCode at hwell
  rw [Bool.and_eq_true] at hwell
  have hinitial : (g.withCriticalMarkers bound).TraceEquivalent
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity)) :=
    critical_traceEquivalent_of_open hg hmem.1
      hwell.1 hwell.2 hopen.2
  have hgExtended := g.withCriticalMarkers_wellFormed hg bound
  refine ⟨n, ⟨?_⟩⟩
  exact stable.toOriginalOpenSoundBasisCoverage_of_width_zero
    (guardedContextLaws_of_wellFormed hgExtended)
    hinitial bound hbound

/-- Consequently, marker-stable width reduction already yields every
critical-instance root certificate over the same original basis. -/
public theorem criticalInstancesDerivableAt_of_markerStableWidthZero
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ}
    (hstable : g.CriticalInstancesMarkerStableWidthZeroAt bound) :
    g.CriticalInstancesDerivableAt bound := by
  apply criticalInstancesDerivableAt_of_everyPathCovered hg
  exact criticalInstancesEveryPathCovered_of_markerStableWidthZero hg hstable

/-- A marker-stable witnessed stair base supplies one fixed original bound
which covers every canonical critical-instance path.  Width reduction may
permute the concrete argument tuple; only the residual schema is inserted
into the fixed basis. -/
public theorem exists_criticalInstancesEveryPathCovered_of_uniformMarkerStableStairBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {width : ℕ}
    (hstair : g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    ∃ bound, g.CriticalInstancesEveryPathCoveredAt bound := by
  obtain ⟨growth, hzero⟩ := hstair.reduceToZero hg
  let bound := growth 0
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
  refine ⟨bound, ?_⟩
  intro schema hschema path
  have hmem := (g.mem_boundedOpenSoundBasis_iff bound schema).mp hschema
  have hopen := hmem.2.2.2
  have hwell := hopen.1
  unfold basisPairWellFormedCode at hwell
  rw [Bool.and_eq_true] at hwell
  have hinitial : (g.withCriticalMarkers bound).TraceEquivalent
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity)) :=
    critical_traceEquivalent_of_open hg hmem.1
      hwell.1 hwell.2 hopen.2
  have hground : (g.withCriticalMarkers bound).groundPairCode
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity)) = true := by
    simpa [basis, family, criticalInstanceFamily_of_originalBasis] using
      family.critical_ground schema hschema
  have laws := guardedContextLaws_of_wellFormed
    (g.withCriticalMarkers_wellFormed hg bound)
  rcases hzero bound
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity))
      hground hinitial path with heventually | hsequence
  · obtain ⟨n, residualWidth, arguments, stable, hopenResidual⟩ :=
      heventually
    refine ⟨n, ⟨?_⟩⟩
    exact stable.toOriginalOpenSoundBasisCoverage bound
      (by simp [bound]) hopenResidual
  · obtain ⟨sequence⟩ := hsequence
    obtain ⟨stable⟩ := sequence.covered 0
    refine ⟨sequence.levels 0, ⟨?_⟩⟩
    exact stable.toOriginalOpenSoundBasisCoverage_of_width_zero
      laws hinitial bound (by simp [bound])

/-- Hence a uniform marker-stable stair base already yields all critical root
certificates for some single original presentation bound. -/
public theorem exists_criticalInstancesDerivableAt_of_uniformMarkerStableStairBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {width : ℕ}
    (hstair : g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    ∃ bound, g.CriticalInstancesDerivableAt bound := by
  obtain ⟨bound, hcovered⟩ :=
    exists_criticalInstancesEveryPathCovered_of_uniformMarkerStableStairBase
      hg hstair
  exact ⟨bound, criticalInstancesDerivableAt_of_everyPathCovered
    hg hcovered⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
