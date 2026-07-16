module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerConservativity
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TracePathRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StairBases
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BasisPathCompactness
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RegularStairBases

@[expose]
public section

/-!
# Marker-stable residual-schema coverage

A canonical critical instance is executed in a grammar extended by fresh
marker symbols, but every symbolic head reached before a marker is exposed is
still a schema over the original rank table.  This file packages that fact in
a form whose presentation bound mentions only the original schema.  In
particular, the bound is independent of the number of markers in the ambient
extension.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The exact finite presentation bound of one original open schema pair. -/
@[expose] public def originalSchemaBound
    (arity : ℕ) (left right : RegularTerm) : ℕ :=
  max arity (max left.nodes.length right.nodes.length)

public theorem arity_le_originalSchemaBound
    (arity : ℕ) (left right : RegularTerm) :
    arity ≤ originalSchemaBound arity left right :=
  Nat.le_max_left _ _

public theorem left_size_le_originalSchemaBound
    (arity : ℕ) (left right : RegularTerm) :
    left.nodes.length ≤ originalSchemaBound arity left right :=
  le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

public theorem right_size_le_originalSchemaBound
    (arity : ℕ) (left right : RegularTerm) :
    right.nodes.length ≤ originalSchemaBound arity left right :=
  le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- The padded arity for a finite head with `width` active marker tails.  It is
computed solely from the original rank table. -/
@[expose] public def originalHeadArity
    (g : EncodedFirstOrderGrammar Action) (width : ℕ) : ℕ :=
  max width (g.ranks.foldr max 0)

/-- A common original run from an open-equivalent pair produces another
open-sound schema row, provided the two residual graph presentations are
well-formed at the retained arity. -/
public theorem openSoundBasisPair_of_original_residual
    {g : EncodedFirstOrderGrammar Action}
    {arity : ℕ} {left right leftResidual rightResidual : RegularTerm}
    {word : List (Label Action)}
    (hleftResidual : leftResidual.WellFormed g.ranks arity)
    (hrightResidual : rightResidual.WellFormed g.ranks arity)
    (hequivalent : g.TraceEquivalent left right)
    (hleftRun : g.run? word left = some leftResidual)
    (hrightRun : g.run? word right = some rightResidual) :
    g.OpenSoundBasisPair (arity, leftResidual, rightResidual) := by
  constructor
  · unfold basisPairWellFormedCode
    rw [Bool.and_eq_true]
    exact ⟨hleftResidual, hrightResidual⟩
  · exact hequivalent.residual hleftRun hrightRun

/-- A bounded residual presentation in a marker extension which retains the
two pieces of information lost by the ordinary coverage interface: its word is
a nonempty lift of an original word, and its schema is well formed over the
original rank table.  Its arguments are exactly the fixed critical-marker
tuple of the declared arity. -/
public structure MarkerStableBoundedOpenSchemaCoverage
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (initialLeft initialRight : RegularTerm)
    (bound arity : ℕ) (word : List (Label (Action ⊕ ℕ))) where
  coverage : BoundedOpenSchemaCoverage (g.withCriticalMarkers count)
    initialLeft initialRight bound (g.criticalArguments arity) word
  schema_arity : coverage.schema.arity = arity
  original_schema_wellFormed :
    g.basisPairWellFormedCode coverage.schema = true
  originalWord : List (Label Action)
  originalWord_nonempty : originalWord ≠ []
  word_eq : word = originalWord.map liftCriticalLabel

/-- Marker-stable bounded active coverage.  This is the regular-schema form
retained through tail elimination: execution and ground arguments live in the
marker extension, while the schema itself remains certified over the original
rank table and the argument tuple remains the fixed critical tuple. -/
public structure MarkerStableBoundedActiveSchemaCoverage
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (initialLeft initialRight : RegularTerm)
    (bound width arity : ℕ) (word : List (Label (Action ⊕ ℕ))) where
  coverage : BoundedActiveSchemaCoverage (g.withCriticalMarkers count)
    initialLeft initialRight bound width (g.criticalArguments arity) word
  schema_arity : coverage.coverage.schema.arity = arity
  original_schema_wellFormed :
    g.basisPairWellFormedCode coverage.coverage.schema = true
  originalWord : List (Label Action)
  originalWord_nonempty : originalWord ≠ []
  word_eq : word = originalWord.map liftCriticalLabel

namespace MarkerStableBoundedOpenSchemaCoverage

/-- Both finite heads in a marker-stable coverage use only original symbols. -/
public theorem schema_usesOriginalSymbols
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound arity : ℕ} {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedOpenSchemaCoverage g count
      initialLeft initialRight bound arity word) :
    stable.coverage.schema.left.UsesOriginalSymbols g.ranks ∧
      stable.coverage.schema.right.UsesOriginalSymbols g.ranks := by
  have hwell := stable.original_schema_wellFormed
  unfold basisPairWellFormedCode at hwell
  rw [Bool.and_eq_true] at hwell
  exact ⟨RegularTerm.usesOriginalSymbols_of_wellFormed hwell.1,
    RegularTerm.usesOriginalSymbols_of_wellFormed hwell.2⟩

/-- Once its original schema is selected into a fixed basis, marker-stable
coverage is immediately usable by arbitrary-basis path compactness. -/
public def toBasisCoverage
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound arity : ℕ} {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedOpenSchemaCoverage g count
      initialLeft initialRight bound arity word)
    (basis : List BasisPair)
    (hmem : stable.coverage.schema ∈ basis) :
    BasisCoverage (g.withCriticalMarkers count)
      initialLeft initialRight basis word :=
  { left := stable.coverage.left
    right := stable.coverage.right
    derivation := stable.coverage.derivation.rebasePair
    schema := stable.coverage.schema
    schema_mem := hmem
    arguments := g.criticalArguments arity
    word_nonempty := stable.coverage.word_nonempty
    schema_wellFormed := stable.coverage.schema_wellFormed
    argument_count := stable.coverage.argument_count
    arguments_ground := stable.coverage.arguments_ground
    left_matches := stable.coverage.left_matches
    right_matches := stable.coverage.right_matches }

/-- If the marker-stable schema is open-sound in the original grammar and its
local presentation bound fits in `globalBound`, it is covered by the fixed
original bounded basis, while the derivation remains in the marker extension. -/
public def toOriginalOpenSoundBasisCoverage
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {localBound arity : ℕ} {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedOpenSchemaCoverage g count
      initialLeft initialRight localBound arity word)
    (globalBound : ℕ) (hbound : localBound ≤ globalBound)
    (hopen : g.OpenSoundBasisPair stable.coverage.schema) :
    BasisCoverage (g.withCriticalMarkers count)
      initialLeft initialRight (g.boundedOpenSoundBasis globalBound) word := by
  apply stable.toBasisCoverage (g.boundedOpenSoundBasis globalBound)
  apply (g.mem_boundedOpenSoundBasis_iff
    globalBound stable.coverage.schema).mpr
  exact
    ⟨le_trans stable.coverage.arity_le hbound,
      le_trans stable.coverage.left_size_le hbound,
      le_trans stable.coverage.right_size_le hbound,
      hopen⟩

end MarkerStableBoundedOpenSchemaCoverage

namespace MarkerStableBoundedActiveSchemaCoverage

/-- At active width zero, marker-stable regular coverage yields an open-sound
row of the original grammar, not merely of the marker extension. -/
public theorem originalOpenSoundPair_of_width_zero
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound arity : ℕ} {word : List (Label (Action ⊕ ℕ))}
    (laws : (g.withCriticalMarkers count).GuardedContextLaws)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (stable : MarkerStableBoundedActiveSchemaCoverage g count
      initialLeft initialRight bound 0 arity word) :
    g.OpenSoundBasisPair stable.coverage.coverage.schema := by
  have hopenExtended :=
    stable.coverage.coverage.openSoundPair_of_width_zero laws hinitial
  exact ⟨stable.original_schema_wellFormed,
    traceEquivalent_of_withCriticalMarkers g count hopenExtended.2⟩

/-- Width-zero marker-stable active coverage is directly covered by the fixed
original bounded open-sound basis whenever its local bound fits globally. -/
public def toOriginalOpenSoundBasisCoverage_of_width_zero
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {localBound arity : ℕ} {word : List (Label (Action ⊕ ℕ))}
    (laws : (g.withCriticalMarkers count).GuardedContextLaws)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (stable : MarkerStableBoundedActiveSchemaCoverage g count
      initialLeft initialRight localBound 0 arity word)
    (globalBound : ℕ) (hbound : localBound ≤ globalBound) :
    BasisCoverage (g.withCriticalMarkers count)
      initialLeft initialRight (g.boundedOpenSoundBasis globalBound) word := by
  let active := stable.coverage.coverage
  have hopen : g.OpenSoundBasisPair active.schema :=
    stable.originalOpenSoundPair_of_width_zero laws hinitial
  have hmem : active.schema ∈ g.boundedOpenSoundBasis globalBound := by
    apply (g.mem_boundedOpenSoundBasis_iff globalBound active.schema).mpr
    exact
      ⟨le_trans stable.coverage.arity_le hbound,
        le_trans stable.coverage.left_size_le hbound,
        le_trans stable.coverage.right_size_le hbound,
        hopen⟩
  exact
    { left := active.left
      right := active.right
      derivation := active.derivation.rebasePair
      schema := active.schema
      schema_mem := hmem
      arguments := active.arguments
      word_nonempty := active.word_nonempty
      schema_wellFormed := active.schema_wellFormed
      argument_count := active.argument_count
      arguments_ground := active.arguments_ground
      left_matches := active.left_matches
      right_matches := active.right_matches }

end MarkerStableBoundedActiveSchemaCoverage

/-- Package a nonempty original-action prefix of a critical-instance path once
its two residuals have been represented by schemas over the original ranks and
the fixed critical-marker tuple.  The resulting bound is the exact original
schema presentation bound and therefore cannot depend on `count`. -/
public def TracePath.markerStableCoverage_of_originalSchemas
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {initialLeft initialRight : RegularTerm}
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (n arity : ℕ) (hcount : arity ≤ count)
    (leftSchema rightSchema : RegularTerm)
    (hleftWellFormed : leftSchema.WellFormed g.ranks arity)
    (hrightWellFormed : rightSchema.WellFormed g.ranks arity)
    (originalWord : List (Label Action))
    (horiginalWord : originalWord ≠ [])
    (hword : path.word n = originalWord.map liftCriticalLabel)
    (hleftMatches : RegularTerm.unfoldingEquivalentCode (path.left n)
      (leftSchema.instantiate (g.criticalArguments arity)) = true)
    (hrightMatches : RegularTerm.unfoldingEquivalentCode (path.right n)
      (rightSchema.instantiate (g.criticalArguments arity)) = true) :
    MarkerStableBoundedOpenSchemaCoverage g count
      initialLeft initialRight
      (originalSchemaBound arity leftSchema rightSchema) arity
      (path.word n) := by
  let schema : BasisPair := (arity, leftSchema, rightSchema)
  have hgExtended := g.withCriticalMarkers_wellFormed hg count
  have hschemaExtended :
      (g.withCriticalMarkers count).basisPairWellFormedCode schema = true := by
    unfold schema basisPairWellFormedCode
    rw [Bool.and_eq_true]
    exact ⟨wellFormed_extendedRanks g count hleftWellFormed,
      wellFormed_extendedRanks g count hrightWellFormed⟩
  have hschemaOriginal : g.basisPairWellFormedCode schema = true := by
    unfold schema basisPairWellFormedCode
    rw [Bool.and_eq_true]
    exact ⟨hleftWellFormed, hrightWellFormed⟩
  have hargumentsGround :
      (g.withCriticalMarkers count).groundArgumentsCode
        (g.criticalArguments arity) = true := by
    unfold groundArgumentsCode
    apply List.all_eq_true.mpr
    intro argument hargument
    apply (RegularTerm.groundCode_eq_true_iff
      (g.withCriticalMarkers count).ranks argument).mpr
    exact criticalArguments_ground_of_le g hcount argument hargument
  have hwordNonempty : path.word n ≠ [] := by
    intro hempty
    rw [hword] at hempty
    exact horiginalWord (List.map_eq_nil_iff.mp hempty)
  let coverage : BoundedOpenSchemaCoverage
      (g.withCriticalMarkers count) initialLeft initialRight
      (originalSchemaBound arity leftSchema rightSchema)
      (g.criticalArguments arity) (path.word n) :=
    { schema := schema
      left := path.left n
      right := path.right n
      derivation := path.pair_derivable
        (preservesGroundSteps_of_wellFormed hgExtended)
        hground hinitial n
      word_nonempty := hwordNonempty
      schema_wellFormed := hschemaExtended
      argument_count := criticalArguments_length g arity
      arguments_ground := hargumentsGround
      left_matches := hleftMatches
      right_matches := hrightMatches
      arity_le := arity_le_originalSchemaBound
        arity leftSchema rightSchema
      left_size_le := left_size_le_originalSchemaBound
        arity leftSchema rightSchema
      right_size_le := right_size_le_originalSchemaBound
        arity leftSchema rightSchema }
  exact
    { coverage := coverage
      schema_arity := rfl
      original_schema_wellFormed := hschemaOriginal
      originalWord := originalWord
      originalWord_nonempty := horiginalWord
      word_eq := hword }

/-- Finite heads ranked by the original grammar automatically provide the
original well-formed schemas required by marker-stable coverage.  Their padded
arity is `originalHeadArity g width`, hence remains independent of `count`. -/
public def TracePath.markerStableCoverage_of_originalFiniteHeads
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ} {initialLeft initialRight : RegularTerm}
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (n width : ℕ) (hcount : g.originalHeadArity width ≤ count)
    (leftHead rightHead : FiniteHead)
    (hleftActive : leftHead.VariablesBelow width)
    (hrightActive : rightHead.VariablesBelow width)
    (hleftRanked : leftHead.RankedBy g.ranks)
    (hrightRanked : rightHead.RankedBy g.ranks)
    (originalWord : List (Label Action))
    (horiginalWord : originalWord ≠ [])
    (hword : path.word n = originalWord.map liftCriticalLabel)
    (hleftMatches : RegularTerm.unfoldingEquivalentCode (path.left n)
      (leftHead.toRegularTerm.instantiate
        (g.criticalArguments (g.originalHeadArity width))) = true)
    (hrightMatches : RegularTerm.unfoldingEquivalentCode (path.right n)
      (rightHead.toRegularTerm.instantiate
        (g.criticalArguments (g.originalHeadArity width))) = true) :
    MarkerStableBoundedOpenSchemaCoverage g count
      initialLeft initialRight
      (originalSchemaBound (g.originalHeadArity width)
        leftHead.toRegularTerm rightHead.toRegularTerm)
      (g.originalHeadArity width) (path.word n) := by
  have hleftWellFormed : leftHead.toRegularTerm.WellFormed g.ranks
      (g.originalHeadArity width) := by
    apply (FiniteHead.toRegularTerm_wellFormed hleftRanked).mono
    exact FiniteHead.retainedVariableBound_le hleftActive hleftRanked
  have hrightWellFormed : rightHead.toRegularTerm.WellFormed g.ranks
      (g.originalHeadArity width) := by
    apply (FiniteHead.toRegularTerm_wellFormed hrightRanked).mono
    exact FiniteHead.retainedVariableBound_le hrightActive hrightRanked
  exact path.markerStableCoverage_of_originalSchemas hg hground hinitial
    n (g.originalHeadArity width) hcount
    leftHead.toRegularTerm rightHead.toRegularTerm
    hleftWellFormed hrightWellFormed originalWord horiginalWord hword
    hleftMatches hrightMatches

end EncodedFirstOrderGrammar

end DCFEquivalence
