module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerWidthReduction
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailPresentationWidening

@[expose]
public section

/-!
# Marker-stable widening of fixed-tail presentations

The ordinary fixed-tail constructor produces witnessed regular-schema
coverages in a critical-marker extension.  Once each selected row is
certified to use an original schema and its path word is certified as the
lift of a nonempty original word, those coverages can be packaged in the
marker-stable interface and widened to grammar-uniform active-width and arity
bounds.

Widening changes neither schema graph.  It raises only the declared arity,
appends inactive ground filler arguments, and retains the original word
certificate verbatim.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace BoundedWitnessedActiveSchemaCoverage

/-- Attach the original-schema and lifted-original-word facts to an ordinary
witnessed coverage in a critical-marker extension. -/
public def toMarkerStable
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (source : BoundedWitnessedActiveSchemaCoverage
      (g.withCriticalMarkers count) initialLeft initialRight
      bound width arguments word)
    (horiginalSchema :
      g.basisPairWellFormedCode
        source.witnessed.coverage.schema = true)
    (originalWord : List (Label Action))
    (horiginalWord : originalWord ≠ [])
    (hword : word = originalWord.map liftCriticalLabel) :
    MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments word :=
  { bounded := source
    original_schema_wellFormed := horiginalSchema
    originalWord := originalWord
    originalWord_nonempty := horiginalWord
    word_eq := hword }

end BoundedWitnessedActiveSchemaCoverage

namespace MarkerStableBoundedWitnessedActiveSchemaCoverage

/-- Widen one marker-stable witnessed row while retaining its original schema
and word certificates. -/
public def widen
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {sourceBound sourceWidth targetBound targetWidth targetArity : ℕ}
    {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (source : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight sourceBound sourceWidth arguments word)
    (filler : RegularTerm)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (hwidth : sourceWidth ≤ targetWidth)
    (harity :
      source.bounded.witnessed.coverage.schema.arity ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity)
    (hbound : sourceBound ≤ targetBound)
    (htargetArityBound : targetArity ≤ targetBound) :
    MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight targetBound targetWidth
      (RegularTerm.padInactiveArguments arguments filler targetArity)
      word := by
  let widened := source.bounded.widen filler hfiller
    hwidth harity htargetWidth hbound htargetArityBound
  have hparts := source.original_schema_wellFormed_parts
  have hleftWellFormed :
      source.bounded.witnessed.coverage.schema.left.WellFormed
        g.ranks targetArity :=
    RegularTerm.WellFormed.mono harity hparts.1
  have hrightWellFormed :
      source.bounded.witnessed.coverage.schema.right.WellFormed
        g.ranks targetArity :=
    RegularTerm.WellFormed.mono harity hparts.2
  have horiginalSchema :
      g.basisPairWellFormedCode
        widened.witnessed.coverage.schema = true := by
    change g.basisPairWellFormedCode
      (source.bounded.witnessed.coverage.schema
        |>.widenArity targetArity) = true
    unfold basisPairWellFormedCode BasisPair.widenArity
    rw [Bool.and_eq_true]
    exact ⟨hleftWellFormed, hrightWellFormed⟩
  exact
    { bounded := widened
      original_schema_wellFormed := horiginalSchema
      originalWord := source.originalWord
      originalWord_nonempty := source.originalWord_nonempty
      word_eq := source.word_eq }

end MarkerStableBoundedWitnessedActiveSchemaCoverage

namespace WitnessedRegularActiveStairSequence

/-- Package an ordinary witnessed stair in a marker extension as a
marker-stable stair once every selected row has an original schema and every
selected path prefix is a lifted nonempty original word. -/
public def toMarkerStable
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {growth : ℕ → ℕ}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (source : WitnessedRegularActiveStairSequence
      (g.withCriticalMarkers count) initialLeft initialRight
      width growth path)
    (originalWord : ℕ → List (Label Action))
    (horiginalWord : ∀ j, originalWord j ≠ [])
    (hword : ∀ j,
      path.word (source.levels j) =
        (originalWord j).map liftCriticalLabel)
    (horiginalCoverage : ∀ j,
      ∃ coverage : BoundedWitnessedActiveSchemaCoverage
        (g.withCriticalMarkers count) initialLeft initialRight
        (growth j) width source.arguments
        (path.word (source.levels j)),
      g.basisPairWellFormedCode
        coverage.witnessed.coverage.schema = true) :
    MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight width growth path := by
  refine
    { arguments := source.arguments
      levels := source.levels
      levels_strictMono := source.levels_strictMono
      covered := ?_ }
  intro j
  obtain ⟨coverage, horiginalSchema⟩ := horiginalCoverage j
  exact ⟨coverage.toMarkerStable
    horiginalSchema
    (originalWord j) (horiginalWord j) (hword j)⟩

end WitnessedRegularActiveStairSequence

namespace MarkerStableWitnessedRegularActiveStairSequence

/-- Widen every row of a marker-stable stair to one exact common active width
and declared schema arity. -/
public def widen
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {sourceWidth targetWidth targetArity : ℕ}
    {growth : ℕ → ℕ}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (source : MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight sourceWidth growth path)
    (filler : RegularTerm)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (hwidth : sourceWidth ≤ targetWidth)
    (harity : source.arguments.length ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight targetWidth
      (fun j => max targetArity (growth j)) path := by
  refine
    { arguments := RegularTerm.padInactiveArguments
        source.arguments filler targetArity
      levels := source.levels
      levels_strictMono := source.levels_strictMono
      covered := ?_ }
  intro j
  obtain ⟨coverage⟩ := source.covered j
  have hcoverageArity :
      coverage.bounded.witnessed.coverage.schema.arity ≤
        targetArity := by
    calc
      coverage.bounded.witnessed.coverage.schema.arity =
          coverage.bounded.witnessed.coverage.arguments.length :=
        coverage.bounded.witnessed.coverage.argument_count.symm
      _ = source.arguments.length :=
        congrArg List.length coverage.bounded.arguments_eq
      _ ≤ targetArity := harity
  exact ⟨coverage.widen filler hfiller hwidth
    hcoverageArity htargetWidth
    (Nat.le_max_right targetArity (growth j))
    (Nat.le_max_left targetArity (growth j))⟩

end MarkerStableWitnessedRegularActiveStairSequence

namespace WitnessedRegularActiveStairSequence

/-- Package a marker-extension stair and widen it in one step. -/
public def toMarkerStableWidened
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {sourceWidth targetWidth targetArity : ℕ}
    {growth : ℕ → ℕ}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (source : WitnessedRegularActiveStairSequence
      (g.withCriticalMarkers count) initialLeft initialRight
      sourceWidth growth path)
    (originalWord : ℕ → List (Label Action))
    (horiginalWord : ∀ j, originalWord j ≠ [])
    (hword : ∀ j,
      path.word (source.levels j) =
        (originalWord j).map liftCriticalLabel)
    (horiginalCoverage : ∀ j,
      ∃ coverage : BoundedWitnessedActiveSchemaCoverage
        (g.withCriticalMarkers count) initialLeft initialRight
        (growth j) sourceWidth source.arguments
        (path.word (source.levels j)),
      g.basisPairWellFormedCode
        coverage.witnessed.coverage.schema = true)
    (filler : RegularTerm)
    (hfiller : filler.Ground (g.withCriticalMarkers count).ranks)
    (hwidth : sourceWidth ≤ targetWidth)
    (harity : source.arguments.length ≤ targetArity)
    (htargetWidth : targetWidth ≤ targetArity) :
    MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight targetWidth
      (fun j => max targetArity (growth j)) path :=
  (source.toMarkerStable originalWord horiginalWord hword
    horiginalCoverage).widen filler hfiller hwidth harity htargetWidth

end WitnessedRegularActiveStairSequence

end EncodedFirstOrderGrammar

end DCFEquivalence
