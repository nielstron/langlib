module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SuccessorExposureRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaPivotResidual

@[expose]
public section

/-!
# Exposed-successor rows over a fixed pivot presentation

This is the fixed-argument analogue of `ExposedSuccessorResult`.  The active
side still exposes one concrete immediate successor.  On the pivot side, the
same shorter word is reflected through an already selected deep schema, so
the resulting residual continues to use the one argument tuple fixed by the
pivot-path construction.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- One shorter exposed-successor row whose pivot residual is expressed over
an externally fixed argument tuple. -/
public structure BalancingSegment.SchemaExposedSuccessorResult
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    {initialLeft initialRight : RegularTerm}
    (stem : List (Label Action)) (child : ℕ)
    (pivotSchema : RegularTerm) (arguments : List RegularTerm)
    (arity width : ℕ) where
  word : List Action
  word_length_lt : word.length < bound
  activeTarget : RegularTerm
  pivotTarget : RegularTerm
  active_run : g.runActions? word active = some activeTarget
  active_matches : activeTarget.UnfoldingEquivalent (active.withRoot child)
  pivot_run : g.runActions? word pivot = some pivotTarget
  shorter_derivation :
    CertificateDerivable g initialLeft initialRight []
      (.pair (stem ++ word.map Sum.inl) activeTarget pivotTarget)
  pivotResidual : RegularTerm
  pivot_symbolic_run :
    g.runActions? word pivotSchema = some pivotResidual
  pivot_instance_matches :
    (pivotResidual.instantiate arguments).UnfoldingEquivalent pivotTarget
  argument_count : arguments.length = arity
  pivot_supported :
    RegularTerm.SupportedByPrefix g.ranks arity width pivotResidual
  pivot_hasPrefixWitness : pivotResidual.HasPrefixWitness width
  pivot_size_le :
    pivotResidual.nodes.length ≤
      g.residualNodeBound word.length pivotSchema.nodes.length

/-- A selected normal-form exposing word yields a shorter certificate row and
a supported pivot residual over the supplied fixed arguments. -/
public theorem BalancingSegment.exists_schemaExposedSuccessorResult
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hexposureBound : g.exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)}
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    {pivotSchema : RegularTerm} {arguments : List RegularTerm}
    {arity width : ℕ}
    (hpivotSupported : RegularTerm.SupportedByPrefix g.ranks
      arity width pivotSchema)
    (hpivotWitness : pivotSchema.HasPrefixWitness width)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hpivotDepth : pivotSchema.ApplicationDepth bound)
    (hargumentsLength : arguments.length = arity)
    (hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed)
    (hpivotInstance :
      (pivotSchema.instantiate arguments).UnfoldingEquivalent pivot)
    (position : g.SuccessorPosition)
    {children : List ℕ} {child : ℕ}
    (hroot : active.rootApplication? = some (position.1.val, children))
    (hchild : children[position.2.val]? = some child) :
    Nonempty (segment.SchemaExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem child pivotSchema arguments arity width) := by
  let word := g.exposingWord hnormal position
  have hwordExposure : g.ExposesSuccessor position word :=
    g.exposingWord_exposes hnormal position
  have hwordLength : word.length < bound :=
    lt_of_lt_of_le
      (g.exposingWord_length_lt_exposureBound hnormal position)
      hexposureBound
  obtain ⟨activeTarget, pivotTarget, hactiveRun,
      hactiveMatches, hpivotRun⟩ :=
    segment.exists_pivotTarget_for_exposedSuccessor
      hg hactive position hwordExposure hwordLength hroot hchild
  have hderivation :
      CertificateDerivable g initialLeft initialRight []
        (.pair (stem ++ word.map Sum.inl) activeTarget pivotTarget) :=
    houter.follow_runActions
      (preservesGroundSteps_of_wellFormed hg) hequivalent
      hactiveRun hpivotRun
  have hpivotDepthWord : pivotSchema.ApplicationDepth word.length :=
    hpivotDepth.mono (Nat.le_of_lt hwordLength)
  obtain ⟨pivotResidual, hpivotSymbolic, hpivotMatch,
      hargumentCount, hpivotResidualSupported, hpivotSize⟩ :=
    exists_supportedSchemaResidual hg hpivotSupported hpadding
      hpivotDepthWord hargumentsLength hargumentsClosed hpivotInstance
      (RegularTerm.referenceClosed_of_ground hpivot) hpivotRun
  have hpivotResidualWitness : pivotResidual.HasPrefixWitness width :=
    hpivotWitness.runActions hg hpadding hpivotSupported.1 hpivotSymbolic
  exact ⟨
    { word := word
      word_length_lt := hwordLength
      activeTarget := activeTarget
      pivotTarget := pivotTarget
      active_run := hactiveRun
      active_matches := hactiveMatches
      pivot_run := hpivotRun
      shorter_derivation := hderivation
      pivotResidual := pivotResidual
      pivot_symbolic_run := hpivotSymbolic
      pivot_instance_matches := hpivotMatch
      argument_count := hargumentCount
      pivot_supported := hpivotResidualSupported
      pivot_hasPrefixWitness := hpivotResidualWitness
      pivot_size_le := hpivotSize }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
