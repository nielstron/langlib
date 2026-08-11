module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalStablePathCompleteness
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FirstOrderCompleteness

@[expose]
public section

/-!
# Complete sufficient bases from marker-stable stairs

The ordinary active stair supplies root certificates for arbitrary equivalent
ground queries.  The marker-stable stair supplies path coverage for every
canonical critical instance.  Its bound is chosen above the ordinary query
bound, so both halves use one and the same original open-sound basis.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Enlarging the presentation bound only adds rows to the original
open-sound basis. -/
public theorem boundedOpenSoundBasis_mono
    (g : EncodedFirstOrderGrammar Action) {bound bound' : ℕ}
    (hbound : bound ≤ bound') :
    ∀ schema ∈ g.boundedOpenSoundBasis bound,
      schema ∈ g.boundedOpenSoundBasis bound' := by
  intro schema hschema
  have hmem := (g.mem_boundedOpenSoundBasis_iff bound schema).mp hschema
  apply (g.mem_boundedOpenSoundBasis_iff bound' schema).mpr
  exact ⟨hmem.1.trans hbound,
    hmem.2.1.trans hbound,
    hmem.2.2.1.trans hbound,
    hmem.2.2.2⟩

/-- A certificate remains derivable when its finite basis is enlarged. -/
public theorem CertificateDerivable.monoBasis
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {basis basis' : List BasisPair}
    {judgment : CertificateJudgment Action}
    (h : CertificateDerivable g initialLeft initialRight basis judgment)
    (hsubset : ∀ schema ∈ basis, schema ∈ basis') :
    CertificateDerivable g initialLeft initialRight basis' judgment := by
  induction h with
  | «axiom» hground => exact .axiom hground
  | transition hpair happrox hleft hright hground ih =>
      exact .transition ih happrox hleft hright hground
  | limit houter hshorter houterContext hreplacementContext hfocus
      hnontrivial hlength houterMatch hshorterLeft hshorterRight hground
      ihOuter ihShorter =>
      exact .limit ihOuter ihShorter houterContext hreplacementContext
        hfocus hnontrivial hlength houterMatch hshorterLeft hshorterRight
        hground
  | symmetry hpair ih => exact .symmetry ih
  | @basis word left right pairRef schema arguments hpair hschema hnonempty
      hschemaWellFormed hargumentCount harguments hleft hright ih =>
      have hmem : schema ∈ basis := List.mem_of_getElem? hschema
      obtain ⟨pairRef', hpairRef', hschema'⟩ :=
        List.mem_iff_getElem.mp (hsubset schema hmem)
      apply CertificateDerivable.basis ih
        (pairRef := pairRef') (schema := schema) (arguments := arguments)
      · exact List.getElem?_eq_some_iff.mpr ⟨hpairRef', hschema'⟩
      · exact hnonempty
      · exact hschemaWellFormed
      · exact hargumentCount
      · exact harguments
      · exact hleft
      · exact hright
  | @progression word left right hpair happrox hchildren ihPair ihChildren =>
      apply CertificateDerivable.progression ihPair happrox
      intro label hlabel
      exact ihChildren label hlabel
  | rejection hpair hreject ih =>
      exact .rejection ih hreject

/-- The marker-stable stair can choose its critical presentation bound above
any prescribed lower bound.  This synchronizes it with an independently
obtained ordinary-query basis. -/
public theorem exists_criticalInstancesEveryPathCovered_of_uniformMarkerStableStairBase_ge
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {width lowerBound : ℕ}
    (hstair : g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    ∃ bound, lowerBound ≤ bound ∧
      g.CriticalInstancesEveryPathCoveredAt bound := by
  obtain ⟨growth, hzero⟩ := hstair.reduceToZero hg
  let bound := lowerBound + growth 0
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
  refine ⟨bound, by simp [bound], ?_⟩
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

/-- An ordinary active stair and a uniform marker-stable stair together give
one complete bounded original open-sound basis. -/
public theorem hasCompleteOpenSoundBound_of_activeAndMarkerStableStairBases
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {queryWidth criticalWidth : ℕ}
    (hqueryStair : g.HasActiveStairBase queryWidth)
    (hcriticalStair :
      g.HasUniformMarkerStableWitnessedRegularActiveStairBase criticalWidth) :
    g.HasCompleteOpenSoundBound := by
  have laws := guardedContextLaws_of_wellFormed hg
  have hgroundSteps : g.PreservesGroundSteps := by
    intro label source target hsource hstep
    exact preservesGroundSteps_of_wellFormed hg hsource hstep
  obtain ⟨queryBound, hquery⟩ :=
    derivable_nop_of_activeStairBase hg laws hgroundSteps hqueryStair
  obtain ⟨bound, hqueryBound, hcritical⟩ :=
    exists_criticalInstancesEveryPathCovered_of_uniformMarkerStableStairBase_ge
      hg hcriticalStair (lowerBound := queryBound)
  refine ⟨bound, ?_, hcritical⟩
  intro initialLeft initialRight hground hequivalent
  exact (hquery initialLeft initialRight hground hequivalent).monoBasis
    (g.boundedOpenSoundBasis_mono hqueryBound)

/-- The constructive pivot analysis naturally produces witnessed regular
stairs.  This variant keeps those witnesses through width reduction and pairs
them directly with the marker-stable critical-instance stair. -/
public theorem hasCompleteOpenSoundBound_of_witnessedAndMarkerStableStairBases
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {queryWidth criticalWidth : ℕ}
    (hqueryStair : g.HasWitnessedRegularActiveStairBase queryWidth)
    (hcriticalStair :
      g.HasUniformMarkerStableWitnessedRegularActiveStairBase criticalWidth) :
    g.HasCompleteOpenSoundBound := by
  have laws := guardedContextLaws_of_wellFormed hg
  have hgroundSteps : g.PreservesGroundSteps := by
    intro label source target hsource hstep
    exact preservesGroundSteps_of_wellFormed hg hsource hstep
  obtain ⟨queryBound, hquery⟩ :=
    derivable_nop_of_witnessedRegularActiveStairBase
      hg laws hgroundSteps hqueryStair
  obtain ⟨bound, hqueryBound, hcritical⟩ :=
    exists_criticalInstancesEveryPathCovered_of_uniformMarkerStableStairBase_ge
      hg hcriticalStair (lowerBound := queryBound)
  refine ⟨bound, ?_, hcritical⟩
  intro initialLeft initialRight hground hequivalent
  exact (hquery initialLeft initialRight hground hequivalent).monoBasis
    (g.boundedOpenSoundBasis_mono hqueryBound)

section Computability

variable [Primcodable Action]

/-- The actual balancing theorem is needed only for exposing-normal-form
grammars.  This stronger-promise wrapper is the endpoint consumed by the
compressed DPDA translation. -/
public theorem
    traceEquivalence_computablePredOnPromise_of_witnessedAndMarkerStableStairBasesOnExposing
    (hstair : ∀ g : EncodedFirstOrderGrammar Action,
      g.WellFormed → g.ExposingNormalForm →
      ∃ queryWidth criticalWidth,
        g.HasWitnessedRegularActiveStairBase queryWidth ∧
          g.HasUniformMarkerStableWitnessedRegularActiveStairBase
            criticalWidth) :
    ComputablePredOnPromise (ValidExposingTracePair (Action := Action))
      (fun input : TracePair Action =>
        input.1.TraceEquivalent input.2.1 input.2.2) := by
  apply
    traceEquivalence_computablePredOnPromise_of_completeOpenSoundBoundsOnExposing
  intro g hg hnormal
  obtain ⟨queryWidth, criticalWidth, hquery, hcritical⟩ :=
    hstair g hg hnormal
  exact hasCompleteOpenSoundBound_of_witnessedAndMarkerStableStairBases
    hg hquery hcritical

/-- The preceding sufficient-basis theorem plugs directly into the final
first-order trace-equivalence decision wrapper. -/
public theorem traceEquivalence_computablePredOnPromise_of_activeAndMarkerStableStairBases
    (hstair : ∀ g : EncodedFirstOrderGrammar Action,
      g.WellFormed →
      ∃ queryWidth criticalWidth,
        g.HasActiveStairBase queryWidth ∧
          g.HasUniformMarkerStableWitnessedRegularActiveStairBase
            criticalWidth) :
    ComputablePredOnPromise (ValidTracePair (Action := Action))
      (fun input : TracePair Action =>
        input.1.TraceEquivalent input.2.1 input.2.2) := by
  apply traceEquivalence_computablePredOnPromise_of_completeOpenSoundBounds
  intro g hg
  obtain ⟨queryWidth, criticalWidth, hquery, hcritical⟩ := hstair g hg
  exact hasCompleteOpenSoundBound_of_activeAndMarkerStableStairBases
    hg hquery hcritical

/-- Final first-order trace-equivalence wrapper for the witnessed regular
stair interface produced by the structured pivot construction. -/
public theorem traceEquivalence_computablePredOnPromise_of_witnessedAndMarkerStableStairBases
    (hstair : ∀ g : EncodedFirstOrderGrammar Action,
      g.WellFormed →
      ∃ queryWidth criticalWidth,
        g.HasWitnessedRegularActiveStairBase queryWidth ∧
          g.HasUniformMarkerStableWitnessedRegularActiveStairBase
            criticalWidth) :
    ComputablePredOnPromise (ValidTracePair (Action := Action))
      (fun input : TracePair Action =>
        input.1.TraceEquivalent input.2.1 input.2.2) := by
  apply traceEquivalence_computablePredOnPromise_of_completeOpenSoundBounds
  intro g hg
  obtain ⟨queryWidth, criticalWidth, hquery, hcritical⟩ := hstair g hg
  exact hasCompleteOpenSoundBound_of_witnessedAndMarkerStableStairBases
    hg hquery hcritical

end Computability

end EncodedFirstOrderGrammar

end DCFEquivalence
