module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.MarkerStableSufficientBasis

@[expose]
public section

/-!
# Unified completeness from marker-stable stairs

The self-certifying package checks its query certificate in the same
critical-marker extension as the critical-instance certificates.  Therefore
one uniform marker-stable stair theorem can supply both halves: at one fixed
marker count, width-zero marker-stable coverage puts every equivalent ground
query path under the same bounded basis of original open-sound schemas.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Global shape well-formedness over a rank table implies that every
application node uses a symbol, and the declared arity, from that table. -/
public theorem usesOriginalSymbols_of_shapeWellFormed
    {ranks : List ℕ} {term : RegularTerm}
    (hshape : term.ShapeWellFormed ranks) :
    term.UsesOriginalSymbols ranks := by
  intro X children hnode
  unfold ShapeWellFormed shapeWellFormedCode at hshape
  rw [Bool.and_eq_true] at hshape
  have hnodeShape := (List.all_eq_true.mp hshape.2) _ hnode
  change (match ranks[X]? with
    | none => false
    | some rank =>
        decide (children.length = rank) &&
          children.all fun child =>
            decide (child < term.nodes.length)) = true at hnodeShape
  cases hrank : ranks[X]? with
  | none =>
      rw [hrank] at hnodeShape
      contradiction
  | some rank =>
      rw [hrank, Bool.and_eq_true] at hnodeShape
      exact ⟨rank, rfl, of_decide_eq_true hnodeShape.1⟩

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- An equivalent original ground pair remains equivalent after adjoining any
finite family of critical markers. -/
public theorem traceEquivalent_withCriticalMarkers_of_groundPairCode
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (count : ℕ) {left right : RegularTerm}
    (hground : g.groundPairCode left right = true)
    (hequivalent : g.TraceEquivalent left right) :
    (g.withCriticalMarkers count).TraceEquivalent left right := by
  unfold groundPairCode at hground
  rw [Bool.and_eq_true] at hground
  have hleftGround :=
    (RegularTerm.groundCode_eq_true_iff g.ranks left).mp hground.1
  have hrightGround :=
    (RegularTerm.groundCode_eq_true_iff g.ranks right).mp hground.2
  exact g.traceEquivalent_withCriticalMarkers_of_originalSymbols hg count
    (RegularTerm.usesOriginalSymbols_of_shapeWellFormed hleftGround.1)
    (RegularTerm.usesOriginalSymbols_of_shapeWellFormed hrightGround.1)
    hequivalent

/-- At one marker count, one bounded original open-sound basis covers every
path from every equivalent ground pair in the marker extension. -/
@[expose] public def MarkerStableUnifiedPathBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  ∀ initialLeft initialRight,
    (g.withCriticalMarkers bound).groundPairCode
        initialLeft initialRight = true →
    (g.withCriticalMarkers bound).TraceEquivalent
        initialLeft initialRight →
    (g.withCriticalMarkers bound).EveryPathCoveredBy
      initialLeft initialRight (g.boundedOpenSoundBasis bound)

/-- A uniform marker-stable stair base yields one marker count and one
original bounded basis covering every equivalent ground query in that
extension. -/
public theorem exists_markerStableUnifiedPathBound_of_uniformStairBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {width : ℕ}
    (hstair : g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    ∃ bound, g.MarkerStableUnifiedPathBound bound := by
  obtain ⟨growth, hzero⟩ := hstair.reduceToZero hg
  let bound := growth 0
  refine ⟨bound, ?_⟩
  intro initialLeft initialRight hground hequivalent path
  have hgExtended := g.withCriticalMarkers_wellFormed hg bound
  have laws := guardedContextLaws_of_wellFormed hgExtended
  rcases hzero bound initialLeft initialRight hground hequivalent path with
    heventually | hsequence
  · obtain ⟨n, residualWidth, arguments, stable, hopen⟩ := heventually
    refine ⟨n, ⟨?_⟩⟩
    exact stable.toOriginalOpenSoundBasisCoverage bound
      (by simp [bound]) hopen
  · obtain ⟨sequence⟩ := hsequence
    obtain ⟨stable⟩ := sequence.covered 0
    refine ⟨sequence.levels 0, ⟨?_⟩⟩
    exact stable.toOriginalOpenSoundBasisCoverage_of_width_zero
      laws hequivalent bound (by simp [bound])

/-- The derivability form of unified marker-stable completeness.  It is
deliberately stated for arbitrary ground queries of the marker extension, so
both the user query and all canonical critical instances are special cases. -/
@[expose] public def MarkerStableUnifiedDerivableAt
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  ∀ initialLeft initialRight,
    (g.withCriticalMarkers bound).groundPairCode
        initialLeft initialRight = true →
    (g.withCriticalMarkers bound).TraceEquivalent
        initialLeft initialRight →
    CertificateDerivable (g.withCriticalMarkers bound)
      initialLeft initialRight (g.boundedOpenSoundBasis bound) (.nop [])

/-- Unified path coverage implies unified root derivability under the same
fixed basis. -/
public theorem markerStableUnifiedDerivableAt_of_pathBound
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} (hcovered : g.MarkerStableUnifiedPathBound bound) :
    g.MarkerStableUnifiedDerivableAt bound := by
  intro initialLeft initialRight hground hequivalent
  have hgExtended := g.withCriticalMarkers_wellFormed hg bound
  exact (g.withCriticalMarkers bound).derivable_nop_of_everyPathCoveredBy
    (guardedContextLaws_of_wellFormed hgExtended)
    (preservesGroundSteps_of_wellFormed hgExtended)
    hground hequivalent
    (hcovered initialLeft initialRight hground hequivalent)

/-- A uniform marker-stable stair base alone supplies one unified derivability
bound. -/
public theorem exists_markerStableUnifiedDerivableAt_of_uniformStairBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {width : ℕ}
    (hstair : g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    ∃ bound, g.MarkerStableUnifiedDerivableAt bound := by
  obtain ⟨bound, hcovered⟩ :=
    exists_markerStableUnifiedPathBound_of_uniformStairBase hg hstair
  exact ⟨bound,
    markerStableUnifiedDerivableAt_of_pathBound hg hcovered⟩

/-- The query-derivation API matching the actual self-certifying package:
the query certificate already lives in the chosen marker extension. -/
public theorem hasSelfCertifyingPackage_of_extended_boundedOpenSound_derivations
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (bound : ℕ)
    (hquery : CertificateDerivable (g.withCriticalMarkers bound)
      initialLeft initialRight (g.boundedOpenSoundBasis bound) (.nop []))
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
  apply exists_acceptedSelfCertifyingWitness_of_derivations
    (input := (g, (initialLeft, initialRight))) bound basis
      hbasis hcount
  · simpa [basis] using hquery
  · intro schema hschema
    exact hcritical schema (by simpa [basis] using hschema)

/-- Unified derivability includes every canonical critical instance of the
same bounded original basis. -/
public theorem criticalInstancesDerivableAt_of_markerStableUnified
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} (hunified : g.MarkerStableUnifiedDerivableAt bound) :
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
  intro schema hschema
  have hmem := (g.mem_boundedOpenSoundBasis_iff bound schema).mp hschema
  have hopen := hmem.2.2.2
  have hwell := hopen.1
  unfold basisPairWellFormedCode at hwell
  rw [Bool.and_eq_true] at hwell
  have hequivalent : (g.withCriticalMarkers bound).TraceEquivalent
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity)) :=
    critical_traceEquivalent_of_open hg hmem.1
      hwell.1 hwell.2 hopen.2
  have hground : (g.withCriticalMarkers bound).groundPairCode
      (schema.left.instantiate (g.criticalArguments schema.arity))
      (schema.right.instantiate (g.criticalArguments schema.arity)) = true := by
    simpa [basis, family, criticalInstanceFamily_of_originalBasis] using
      family.critical_ground schema hschema
  exact hunified
    (schema.left.instantiate (g.criticalArguments schema.arity))
    (schema.right.instantiate (g.criticalArguments schema.arity))
    hground hequivalent

/-- Additive replacement for `CompleteOpenSoundBound` whose query certificate
is stated in the grammar where the package checker actually validates it. -/
@[expose] public def ExtendedCompleteOpenSoundBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  (∀ initialLeft initialRight,
      g.groundPairCode initialLeft initialRight = true →
      g.TraceEquivalent initialLeft initialRight →
      CertificateDerivable (g.withCriticalMarkers bound)
        initialLeft initialRight (g.boundedOpenSoundBasis bound) (.nop [])) ∧
    g.CriticalInstancesDerivableAt bound

/-- A grammar admits one complete original basis whose query and critical
certificates are all checked in the same marker extension. -/
@[expose] public def HasExtendedCompleteOpenSoundBound
    (g : EncodedFirstOrderGrammar Action) : Prop :=
  ∃ bound, g.ExtendedCompleteOpenSoundBound bound

/-- Unified marker-stable derivability gives the extended complete-bound API
consumed by package completeness. -/
public theorem extendedCompleteOpenSoundBound_of_markerStableUnified
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} (hunified : g.MarkerStableUnifiedDerivableAt bound) :
    g.ExtendedCompleteOpenSoundBound bound := by
  refine ⟨?_, criticalInstancesDerivableAt_of_markerStableUnified
    hg hunified⟩
  intro initialLeft initialRight hground hequivalent
  exact hunified initialLeft initialRight
    (g.groundPairCode_withCriticalMarkers bound
      initialLeft initialRight hground)
    (g.traceEquivalent_withCriticalMarkers_of_groundPairCode
      hg bound hground hequivalent)

/-- One uniform marker-stable stair theorem now supplies the whole positive
completeness package; no separate ordinary-query stair is needed. -/
public theorem hasExtendedCompleteOpenSoundBound_of_uniformMarkerStableStairBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {width : ℕ}
    (hstair : g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    g.HasExtendedCompleteOpenSoundBound := by
  obtain ⟨bound, hunified⟩ :=
    exists_markerStableUnifiedDerivableAt_of_uniformStairBase hg hstair
  exact ⟨bound,
    extendedCompleteOpenSoundBound_of_markerStableUnified hg hunified⟩

/-- An extended complete bound gives the exact positive package required for
every valid equivalent original ground query. -/
public theorem hasSelfCertifyingPackage_of_extendedCompleteOpenSoundBound
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} (hcomplete : g.ExtendedCompleteOpenSoundBound bound)
    {initialLeft initialRight : RegularTerm}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hequivalent : g.TraceEquivalent initialLeft initialRight) :
    HasSelfCertifyingPackage (g, (initialLeft, initialRight)) :=
  hasSelfCertifyingPackage_of_extended_boundedOpenSound_derivations
    bound
    (hcomplete.1 initialLeft initialRight hground hequivalent)
    hcomplete.2

/-- Direct package completeness from the sole uniform marker-stable stair
hypothesis. -/
public theorem hasSelfCertifyingPackage_of_uniformMarkerStableStairBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {width : ℕ}
    (hstair : g.HasUniformMarkerStableWitnessedRegularActiveStairBase width)
    {initialLeft initialRight : RegularTerm}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hequivalent : g.TraceEquivalent initialLeft initialRight) :
    HasSelfCertifyingPackage (g, (initialLeft, initialRight)) := by
  obtain ⟨bound, hcomplete⟩ :=
    hasExtendedCompleteOpenSoundBound_of_uniformMarkerStableStairBase
      hg hstair
  exact hasSelfCertifyingPackage_of_extendedCompleteOpenSoundBound
    hcomplete hground hequivalent

section Computability

variable [Primcodable Action]

/-- Marker-stable unified completeness on exposing-normal-form grammars is
enough for promise-decidable first-order trace equivalence. -/
public theorem
    traceEquivalence_computablePredOnPromise_of_uniformMarkerStableStairBasesOnExposing
    (hstair : ∀ g : EncodedFirstOrderGrammar Action,
      g.WellFormed → g.ExposingNormalForm →
      ∃ width,
        g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    ComputablePredOnPromise (ValidExposingTracePair (Action := Action))
      (fun input : TracePair Action =>
        input.1.TraceEquivalent input.2.1 input.2.2) := by
  apply
    traceEquivalence_computablePredOnPromise_of_package_complete_under
      (fun input hpromise => hpromise.1)
  intro input hpromise hequivalent
  obtain ⟨width, hmarker⟩ :=
    hstair input.1 hpromise.1.1 hpromise.2
  have hground : input.1.groundPairCode
      input.2.1 input.2.2 = true := by
    unfold groundPairCode
    rw [Bool.and_eq_true]
    exact
      ⟨(RegularTerm.groundCode_eq_true_iff _ _).mpr hpromise.1.2.2.1,
        (RegularTerm.groundCode_eq_true_iff _ _).mpr hpromise.1.2.2.2⟩
  exact hasSelfCertifyingPackage_of_uniformMarkerStableStairBase
    hpromise.1.1 hmarker hground hequivalent

/-- Non-normal-form wrapper for clients that establish the uniform
marker-stable theorem on every well-formed grammar. -/
public theorem
    traceEquivalence_computablePredOnPromise_of_uniformMarkerStableStairBases
    (hstair : ∀ g : EncodedFirstOrderGrammar Action,
      g.WellFormed →
      ∃ width,
        g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    ComputablePredOnPromise (ValidTracePair (Action := Action))
      (fun input : TracePair Action =>
        input.1.TraceEquivalent input.2.1 input.2.2) := by
  apply traceEquivalence_computablePredOnPromise_of_package_complete
  intro input hvalid hequivalent
  obtain ⟨width, hmarker⟩ := hstair input.1 hvalid.1
  have hground : input.1.groundPairCode
      input.2.1 input.2.2 = true := by
    unfold groundPairCode
    rw [Bool.and_eq_true]
    exact
      ⟨(RegularTerm.groundCode_eq_true_iff _ _).mpr hvalid.2.2.1,
        (RegularTerm.groundCode_eq_true_iff _ _).mpr hvalid.2.2.2⟩
  exact hasSelfCertifyingPackage_of_uniformMarkerStableStairBase
    hvalid.1 hmarker hground hequivalent

end Computability

end EncodedFirstOrderGrammar

end DCFEquivalence
