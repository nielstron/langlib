module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerExposure
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerStableCoverage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.WidthReduction

@[expose]
public section

/-!
# Marker-stable width reduction

The operational derivation lives in a critical-marker extension, but every
regular schema and every exposure used by the width induction is certified in
the original grammar.  Consequently the growth recurrence uses the original
`boundedExposureBound`, independently of the marker count.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

@[simp] public theorem withCriticalMarkers_rankMax
    (g : EncodedFirstOrderGrammar Action) (count : ℕ) :
    (g.withCriticalMarkers count).ranks.foldr max 0 =
      g.ranks.foldr max 0 := by
  have hzeros : (List.replicate count 0).foldr max 0 = 0 := by
    induction count with
    | zero => rfl
    | succ count ih => simp [List.replicate_succ, ih]
  rw [withCriticalMarkers_ranks, List.foldr_append, hzeros]

/-- A bounded witnessed active row in the marker extension whose schema and
path prefix both come from the original grammar.  The argument tuple is
arbitrary: width reduction permutes it at every elimination step. -/
public structure MarkerStableBoundedWitnessedActiveSchemaCoverage
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (initialLeft initialRight : RegularTerm)
    (bound width : ℕ) (arguments : List RegularTerm)
    (word : List (Label (Action ⊕ ℕ))) where
  bounded : BoundedWitnessedActiveSchemaCoverage
    (g.withCriticalMarkers count) initialLeft initialRight
      bound width arguments word
  original_schema_wellFormed :
    g.basisPairWellFormedCode bounded.witnessed.coverage.schema = true
  originalWord : List (Label Action)
  originalWord_nonempty : originalWord ≠ []
  word_eq : word = originalWord.map liftCriticalLabel

/-- A terminal witnessed row needs only an original well-formed schema.
Unlike nonterminal stair rows, its path word may already contain a fresh
marker action. -/
public structure TerminalMarkerStableBoundedWitnessedActiveSchemaCoverage
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (initialLeft initialRight : RegularTerm)
    (bound width : ℕ) (arguments : List RegularTerm)
    (word : List (Label (Action ⊕ ℕ))) where
  bounded : BoundedWitnessedActiveSchemaCoverage
    (g.withCriticalMarkers count) initialLeft initialRight
      bound width arguments word
  original_schema_wellFormed :
    g.basisPairWellFormedCode bounded.witnessed.coverage.schema = true

namespace TerminalMarkerStableBoundedWitnessedActiveSchemaCoverage

/-- Raising only the presentation bound preserves terminal marker
stability. -/
public def mono
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound bound' width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (terminal : TerminalMarkerStableBoundedWitnessedActiveSchemaCoverage
      g count initialLeft initialRight bound width arguments word)
    (hbound : bound ≤ bound') :
    TerminalMarkerStableBoundedWitnessedActiveSchemaCoverage
      g count initialLeft initialRight bound' width arguments word :=
  { terminal with bounded := terminal.bounded.mono hbound }

/-- A terminal row whose original schema is open-sound is immediately covered
by the bounded original basis.  No restriction on its concrete path word is
needed. -/
public def toOriginalOpenSoundBasisCoverage
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {localBound width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (terminal : TerminalMarkerStableBoundedWitnessedActiveSchemaCoverage
      g count initialLeft initialRight localBound width arguments word)
    (globalBound : ℕ) (hbound : localBound ≤ globalBound)
    (hopen : g.TraceEquivalent
      terminal.bounded.witnessed.coverage.schema.left
      terminal.bounded.witnessed.coverage.schema.right) :
    BasisCoverage (g.withCriticalMarkers count)
      initialLeft initialRight (g.boundedOpenSoundBasis globalBound) word := by
  let active := terminal.bounded.witnessed.coverage
  have hmem : active.schema ∈ g.boundedOpenSoundBasis globalBound := by
    apply (g.mem_boundedOpenSoundBasis_iff globalBound active.schema).mpr
    exact
      ⟨le_trans terminal.bounded.arity_le hbound,
        le_trans terminal.bounded.left_size_le hbound,
        le_trans terminal.bounded.right_size_le hbound,
        terminal.original_schema_wellFormed, hopen⟩
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

end TerminalMarkerStableBoundedWitnessedActiveSchemaCoverage

namespace MarkerStableBoundedWitnessedActiveSchemaCoverage

/-- Forget the lifted-original word certificate when a row is used only as a
terminal open-sound endpoint. -/
public def toTerminal
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments word) :
    TerminalMarkerStableBoundedWitnessedActiveSchemaCoverage
      g count initialLeft initialRight bound width arguments word :=
  { bounded := stable.bounded
    original_schema_wellFormed := stable.original_schema_wellFormed }

public theorem original_schema_wellFormed_parts
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments word) :
    stable.bounded.witnessed.coverage.schema.left.WellFormed g.ranks
        stable.bounded.witnessed.coverage.schema.arity ∧
      stable.bounded.witnessed.coverage.schema.right.WellFormed g.ranks
        stable.bounded.witnessed.coverage.schema.arity := by
  have hwell := stable.original_schema_wellFormed
  unfold basisPairWellFormedCode at hwell
  simpa only [Bool.and_eq_true] using hwell

public theorem left_supported_original
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments word) :
    RegularTerm.SupportedByPrefix g.ranks
      stable.bounded.witnessed.coverage.schema.arity width
      stable.bounded.witnessed.coverage.schema.left := by
  exact ⟨stable.original_schema_wellFormed_parts.1,
    stable.bounded.witnessed.coverage.left_supported.2⟩

public theorem right_supported_original
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments word) :
    RegularTerm.SupportedByPrefix g.ranks
      stable.bounded.witnessed.coverage.schema.arity width
      stable.bounded.witnessed.coverage.schema.right := by
  exact ⟨stable.original_schema_wellFormed_parts.2,
    stable.bounded.witnessed.coverage.right_supported.2⟩

public theorem rank_padding_original
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments word) :
    g.ranks.foldr max 0 ≤
      stable.bounded.witnessed.coverage.schema.arity := by
  rw [← withCriticalMarkers_rankMax g count]
  exact stable.bounded.witnessed.coverage.rank_padding

/-- Reindexing an active argument preserves marker stability and doubles only
the ordinary local presentation bound. -/
public def moveParameterToActiveLast
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments word)
    (hwidth : 0 < width) (x : ℕ) (hx : x < width) :
    MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight (bound + bound) width
      (RegularTerm.moveArgumentToActiveLast arguments width x) word := by
  let source := stable.bounded.witnessed.coverage
  let moved := stable.bounded.moveParameterToActiveLast hwidth x hx
  have hwell := stable.original_schema_wellFormed_parts
  have hxArity : x < source.schema.arity :=
    hx.trans_le source.left_supported.2.1
  have hwidthArity : width ≤ source.schema.arity :=
    source.left_supported.2.1
  have hlastArity : width - 1 < source.schema.arity := by
    omega
  have hmovedWellFormed :
      g.basisPairWellFormedCode moved.witnessed.coverage.schema = true := by
    unfold basisPairWellFormedCode
    rw [Bool.and_eq_true]
    constructor
    · change
        (RegularTerm.moveParameterToActiveLast source.schema.left
          source.schema.arity width x).WellFormed g.ranks
            source.schema.arity
      unfold RegularTerm.moveParameterToActiveLast
      exact RegularTerm.swapParameters_wellFormed hwell.1
        hxArity hlastArity
    · change
        (RegularTerm.moveParameterToActiveLast source.schema.right
          source.schema.arity width x).WellFormed g.ranks
            source.schema.arity
      unfold RegularTerm.moveParameterToActiveLast
      exact RegularTerm.swapParameters_wellFormed hwell.2
        hxArity hlastArity
  exact
    { bounded := moved
      original_schema_wellFormed := hmovedWellFormed
      originalWord := stable.originalWord
      originalWord_nonempty := stable.originalWord_nonempty
      word_eq := stable.word_eq }

public def mono
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound bound' width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments word)
    (hbound : bound ≤ bound') :
    MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound' width arguments word :=
  { stable with bounded := stable.bounded.mono hbound }

/-- A marker-stable witnessed row whose original schema is open-sound is
covered by the fixed bounded basis of the original grammar.  The concrete
argument tuple may have been permuted by width reduction. -/
public def toOriginalOpenSoundBasisCoverage
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {localBound width : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight localBound width arguments word)
    (globalBound : ℕ) (hbound : localBound ≤ globalBound)
    (hopen : g.TraceEquivalent
      stable.bounded.witnessed.coverage.schema.left
      stable.bounded.witnessed.coverage.schema.right) :
    BasisCoverage (g.withCriticalMarkers count)
      initialLeft initialRight (g.boundedOpenSoundBasis globalBound) word := by
  exact stable.toTerminal.toOriginalOpenSoundBasisCoverage
    globalBound hbound hopen

/-- At active width zero, the preceding adapter obtains original open
soundness from the regular-schema theorem in the marker extension. -/
public def toOriginalOpenSoundBasisCoverage_of_width_zero
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {localBound : ℕ} {arguments : List RegularTerm}
    {word : List (Label (Action ⊕ ℕ))}
    (laws : (g.withCriticalMarkers count).GuardedContextLaws)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight localBound 0 arguments word)
    (globalBound : ℕ) (hbound : localBound ≤ globalBound) :
    BasisCoverage (g.withCriticalMarkers count)
      initialLeft initialRight (g.boundedOpenSoundBasis globalBound) word := by
  have hopenExtended :=
    stable.bounded.witnessed.coverage.openSoundPair_of_width_zero laws hinitial
  exact stable.toOriginalOpenSoundBasisCoverage globalBound hbound
    (traceEquivalent_of_withCriticalMarkers g count hopenExtended.2)

end MarkerStableBoundedWitnessedActiveSchemaCoverage

/-- A marker-stable witnessed regular stair fixes one (possibly permuted)
ground argument tuple across all selected levels. -/
public structure MarkerStableWitnessedRegularActiveStairSequence
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (initialLeft initialRight : RegularTerm)
    (width : ℕ) (growth : ℕ → ℕ)
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight) where
  arguments : List RegularTerm
  levels : ℕ → ℕ
  levels_strictMono : StrictMono levels
  covered : ∀ j, Nonempty
    (MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight (growth j) width arguments
        (path.word (levels j)))

namespace MarkerStableWitnessedRegularActiveStairSequence

public def toRegular
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {growth : ℕ → ℕ}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (sequence : MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight width growth path) :
    RegularActiveStairSequence (g.withCriticalMarkers count)
      initialLeft initialRight width growth path :=
  { arguments := sequence.arguments
    levels := sequence.levels
    levels_strictMono := sequence.levels_strictMono
    covered := fun j => by
      obtain ⟨coverage⟩ := sequence.covered j
      exact ⟨coverage.bounded.toBoundedActiveSchemaCoverage⟩ }

public def moveParameterToActiveLast
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {growth : ℕ → ℕ}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (sequence : MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight width growth path)
    (hwidth : 0 < width) (x : ℕ) (hx : x < width) :
    MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight width (fun j => growth j + growth j) path :=
  { arguments := RegularTerm.moveArgumentToActiveLast
      sequence.arguments width x
    levels := sequence.levels
    levels_strictMono := sequence.levels_strictMono
    covered := fun j => by
      obtain ⟨coverage⟩ := sequence.covered j
      exact ⟨coverage.moveParameterToActiveLast hwidth x hx⟩ }

end MarkerStableWitnessedRegularActiveStairSequence

/-- A path has already reached an original open-sound marker-stable row within
the stated global bound. -/
@[expose] public def EventuallyMarkerStableOpenSound
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (initialLeft initialRight : RegularTerm) (bound : ℕ)
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight) : Prop :=
  ∃ n width arguments,
    ∃ stable : TerminalMarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments (path.word n),
      g.TraceEquivalent stable.bounded.witnessed.coverage.schema.left
        stable.bounded.witnessed.coverage.schema.right

public theorem EventuallyMarkerStableOpenSound.mono
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm} {bound bound' : ℕ}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (heventually : EventuallyMarkerStableOpenSound g count
      initialLeft initialRight bound path)
    (hbound : bound ≤ bound') :
    EventuallyMarkerStableOpenSound g count initialLeft initialRight
      bound' path := by
  obtain ⟨n, width, arguments, stable, hopen⟩ := heventually
  exact ⟨n, width, arguments, stable.mono hbound, hopen⟩

/-- Prepared elimination with the additional original-rank fact needed to
show that tying preserves marker stability. -/
public structure MarkerStablePreparedTailElimination
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (initialLeft initialRight : RegularTerm)
    (bound width : ℕ) (originalArguments : List RegularTerm)
    (stem : List (Label (Action ⊕ ℕ))) where
  prepared : PreparedTailElimination (g.withCriticalMarkers count)
    initialLeft initialRight bound (g.boundedExposureBound bound)
      width originalArguments stem
  replacement_wellFormed_original : prepared.replacement.WellFormed g.ranks
    prepared.arguments.length

/-- Select and prepare an exposure in the original grammar, then replay it in
the marker extension.  The resulting exposure bound is exactly the original
grammar's bound. -/
public theorem MarkerStableBoundedWitnessedActiveSchemaCoverage.exists_preparedTailElimination
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (laws : (g.withCriticalMarkers count).GuardedContextLaws)
    (hgroundSteps : (g.withCriticalMarkers count).PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm}
    (hinitialEquivalent : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    {bound width : ℕ} {arguments : List RegularTerm}
    {stem : List (Label (Action ⊕ ℕ))}
    (stable : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight bound width arguments stem)
    (hwidth : 0 < width)
    (hinequivalent : ¬(g.withCriticalMarkers count).TraceEquivalent
      stable.bounded.witnessed.coverage.schema.left
      stable.bounded.witnessed.coverage.schema.right) :
    Nonempty (MarkerStablePreparedTailElimination g count
      initialLeft initialRight bound width arguments stem) := by
  let extended := g.withCriticalMarkers count
  let coverage := stable.bounded.witnessed.coverage
  have hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  have hleftOriginal := stable.left_supported_original
  have hrightOriginal := stable.right_supported_original
  have hleftUses := RegularTerm.usesOriginalSymbols_of_wellFormed
    hleftOriginal.1
  have hrightUses := RegularTerm.usesOriginalSymbols_of_wellFormed
    hrightOriginal.1
  have hinequivalentOriginal : ¬g.TraceEquivalent
      coverage.schema.left coverage.schema.right := by
    intro hequivalent
    apply hinequivalent
    exact traceEquivalent_withCriticalMarkers_of_originalSymbols g hg count
      hleftUses hrightUses hequivalent
  have hpair : coverage.schema ∈ g.basisPairsUpTo bound := by
    apply (g.mem_basisPairsUpTo_iff bound coverage.schema).mpr
    exact ⟨stable.bounded.arity_le, stable.bounded.left_size_le,
      stable.bounded.right_size_le, stable.original_schema_wellFormed⟩
  have hoffending := g.chosenOffendingWord_spec hinequivalentOriginal
  have hinstanceExtended :=
    coverage.instantiated_traceEquivalent laws hinitialEquivalent
  have hinstanceOriginal := traceEquivalent_of_withCriticalMarkers g count
    hinstanceExtended
  obtain ⟨originalEquation, horiginalCost⟩ :=
    g.exists_boundedExposedEquation_of_offending_referenceClosed hg
      hleftOriginal.1 hrightOriginal.1 coverage.argument_count
      coverage.arguments_referenceClosed hinstanceOriginal
      (g.chosenOffendingWord coverage.schema) hoffending
  have hactive :=
    originalEquation.variableIndex_lt_width_of_extendedGround g hg count
      hleftOriginal hrightOriginal coverage.argument_count
      coverage.arguments_areGround
  let extendedEquation := originalEquation.withCriticalMarkers hg count
    hleftOriginal.1 hrightOriginal.1 coverage.arguments_areGround
      hinstanceExtended
  obtain ⟨targets⟩ := coverage.exposedCertificateTargets hgExtended laws
    hgroundSteps hinitialEquivalent extendedEquation
  have hvariable : originalEquation.variableIndex <
      coverage.arguments.length := by
    rw [coverage.argument_count]
    exact hactive.trans_le hleftOriginal.2.1
  obtain ⟨argument, hargument, horientation⟩ :=
    targets.orientation_with_argument hvariable
  let exposed : ActiveExposedCertificate extended
      initialLeft initialRight width coverage :=
    { equation := extendedEquation
      variableIndex_lt_width := hactive
      targets := targets
      argument := argument
      argument_at := hargument
      orientation := horientation }
  have horiginalCost' : originalEquation.presentationCost ≤
      g.schemaExposureBound coverage.schema := by
    simpa [schemaExposureBound] using horiginalCost
  have hextendedCost : exposed.equation.presentationCost ≤
      g.boundedExposureBound bound := by
    change extendedEquation.presentationCost ≤ g.boundedExposureBound bound
    rw [ExposedEquation.presentationCost_withCriticalMarkers]
    exact horiginalCost'.trans
      (g.schemaExposureBound_le_boundedExposureBound hpair)
  obtain ⟨prepared, hreplacement⟩ :=
    stable.bounded.exists_preparedTailElimination_of_exposed hgExtended
      hwidth exposed hextendedCost
  have hleftResidual := hleftOriginal.residual hg
    stable.rank_padding_original originalEquation.left_run
  have hrightResidual := hrightOriginal.residual hg
    stable.rank_padding_original originalEquation.right_run
  have hxArity : originalEquation.variableIndex < coverage.schema.arity :=
    hactive.trans_le hleftOriginal.2.1
  have hwidthArity : width ≤ coverage.schema.arity := hleftOriginal.2.1
  have hlastArity : width - 1 < coverage.schema.arity := by omega
  have hpreparedLength : prepared.arguments.length = coverage.schema.arity := by
    rw [prepared.arguments_eq_moved,
      RegularTerm.moveArgumentToActiveLast,
      RegularTerm.swapArguments_length, ← stable.bounded.arguments_eq,
      coverage.argument_count]
  have hreplacementWellFormed : prepared.replacement.WellFormed g.ranks
      prepared.arguments.length := by
    rcases hreplacement with hright | hleft
    · have hmoved :
          (RegularTerm.moveParameterToActiveLast
            originalEquation.rightResidual coverage.schema.arity width
              originalEquation.variableIndex).WellFormed g.ranks
            coverage.schema.arity := by
        unfold RegularTerm.moveParameterToActiveLast
        exact RegularTerm.swapParameters_wellFormed hrightResidual.1
          hxArity hlastArity
      rw [show prepared.replacement =
          RegularTerm.moveParameterToActiveLast
            originalEquation.rightResidual coverage.schema.arity width
              originalEquation.variableIndex by
        simpa [exposed, extendedEquation,
          ExposedEquation.withCriticalMarkers] using hright]
      simpa [hpreparedLength] using hmoved
    · have hmoved :
          (RegularTerm.moveParameterToActiveLast
            originalEquation.leftResidual coverage.schema.arity width
              originalEquation.variableIndex).WellFormed g.ranks
            coverage.schema.arity := by
        unfold RegularTerm.moveParameterToActiveLast
        exact RegularTerm.swapParameters_wellFormed hleftResidual.1
          hxArity hlastArity
      rw [show prepared.replacement =
          RegularTerm.moveParameterToActiveLast
            originalEquation.leftResidual coverage.schema.arity width
              originalEquation.variableIndex by
        simpa [exposed, extendedEquation,
          ExposedEquation.withCriticalMarkers] using hleft]
      simpa [hpreparedLength] using hmoved
  exact ⟨
    { prepared := prepared
      replacement_wellFormed_original := hreplacementWellFormed }⟩

/-- Applying a marker-stable prepared equation to a later marker-stable row
preserves original-schema well-formedness. -/
public theorem MarkerStablePreparedTailElimination.exists_eliminatedCoverage
    {g : EncodedFirstOrderGrammar Action} {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {originalArguments : List RegularTerm}
    {stem : List (Label (Action ⊕ ℕ))}
    (stablePrepared : MarkerStablePreparedTailElimination g count
      initialLeft initialRight bound width originalArguments stem)
    (hwidth : 0 < width)
    {outerBound : ℕ} {word : List (Label (Action ⊕ ℕ))}
    (outer : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight outerBound width
        stablePrepared.prepared.arguments word)
    (hlength : (stem ++ stablePrepared.prepared.suffix).length <
      word.length) :
    Nonempty (MarkerStableBoundedWitnessedActiveSchemaCoverage g count
      initialLeft initialRight
      (outerBound + outerBound *
        (g.boundedExposureBound bound + bound + 1))
      (width - 1) stablePrepared.prepared.arguments word) := by
  let prepared := stablePrepared.prepared
  obtain ⟨target, hleftSchema, hrightSchema⟩ :=
    prepared.exists_eliminatedCoverage hwidth outer.bounded hlength
  let outerCoverage := outer.bounded.witnessed.coverage
  have houterWell := outer.original_schema_wellFormed_parts
  have hargumentsArity : prepared.arguments.length =
      outerCoverage.schema.arity := by
    rw [← outer.bounded.arguments_eq, outerCoverage.argument_count]
  have hleftOuter : outerCoverage.schema.left.WellFormed g.ranks
      prepared.arguments.length := by
    simpa [hargumentsArity] using houterWell.1
  have hrightOuter : outerCoverage.schema.right.WellFormed g.ranks
      prepared.arguments.length := by
    simpa [hargumentsArity] using houterWell.2
  have hwidthArguments : width ≤ prepared.arguments.length := by
    rw [prepared.argument_count]
    exact prepared.width_le_arity
  have hx : width - 1 < prepared.arguments.length := by
    omega
  have hleftTied := RegularTerm.tieInto_wellFormed hleftOuter
    stablePrepared.replacement_wellFormed_original hx
  have hrightTied := RegularTerm.tieInto_wellFormed hrightOuter
    stablePrepared.replacement_wellFormed_original hx
  have htargetArity : target.witnessed.coverage.schema.arity =
      prepared.arguments.length := by
    calc
      target.witnessed.coverage.schema.arity =
          target.witnessed.coverage.arguments.length :=
        target.witnessed.coverage.argument_count.symm
      _ = prepared.arguments.length :=
        congrArg List.length target.arguments_eq
  have htargetOriginal :
      g.basisPairWellFormedCode target.witnessed.coverage.schema = true := by
    unfold basisPairWellFormedCode
    rw [Bool.and_eq_true]
    constructor
    · rw [hleftSchema]
      simpa [htargetArity] using hleftTied
    · rw [hrightSchema]
      simpa [htargetArity] using hrightTied
  exact ⟨
    { bounded := target
      original_schema_wellFormed := htargetOriginal
      originalWord := outer.originalWord
      originalWord_nonempty := outer.originalWord_nonempty
      word_eq := outer.word_eq }⟩

/-- One marker-stable width step uses the original grammar's growth
recurrence, even though all concrete derivations live in the extension. -/
public theorem MarkerStableWitnessedRegularActiveStairSequence.reduceWidth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (laws : (g.withCriticalMarkers count).GuardedContextLaws)
    (hgroundSteps : (g.withCriticalMarkers count).PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm}
    (hinitialEquivalent : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    {width : ℕ} {growth : ℕ → ℕ}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (sequence : MarkerStableWitnessedRegularActiveStairSequence g count
      initialLeft initialRight width growth path)
    (hwidth : 0 < width) :
    EventuallyMarkerStableOpenSound g count initialLeft initialRight
        (g.widthReductionGrowth growth 0) path ∨
      Nonempty (MarkerStableWitnessedRegularActiveStairSequence g count
        initialLeft initialRight (width - 1)
          (g.widthReductionGrowth growth) path) := by
  obtain ⟨initial⟩ := sequence.covered 0
  by_cases hequivalent : (g.withCriticalMarkers count).TraceEquivalent
      initial.bounded.witnessed.coverage.schema.left
      initial.bounded.witnessed.coverage.schema.right
  · left
    have hopen := traceEquivalent_of_withCriticalMarkers g count hequivalent
    exact ⟨sequence.levels 0, width, sequence.arguments,
      (initial.mono
        (growth_zero_le_widthReductionGrowth g growth)).toTerminal,
      hopen⟩
  · obtain ⟨stablePrepared⟩ := initial.exists_preparedTailElimination
      hg laws hgroundSteps hinitialEquivalent hwidth hequivalent
    let prepared := stablePrepared.prepared
    let moved := sequence.moveParameterToActiveLast hwidth
      prepared.selectedIndex prepared.selectedIndex_lt_width
    let offset := prepared.suffix.length + 1
    have hmovedArguments : moved.arguments = prepared.arguments := by
      simpa [moved, prepared] using prepared.arguments_eq_moved.symm
    right
    refine ⟨
      { arguments := prepared.arguments
        levels := fun j => sequence.levels (offset + j)
        levels_strictMono := by
          intro i j hij
          exact sequence.levels_strictMono
            (Nat.add_lt_add_left hij offset)
        covered := ?_ }⟩
    intro j
    obtain ⟨outer⟩ := moved.covered (offset + j)
    let outerBound := growth (offset + j) + growth (offset + j)
    let word := path.word (sequence.levels (offset + j))
    have htype :
        MarkerStableBoundedWitnessedActiveSchemaCoverage g count
            initialLeft initialRight outerBound width moved.arguments word =
          MarkerStableBoundedWitnessedActiveSchemaCoverage g count
            initialLeft initialRight outerBound width prepared.arguments word :=
      congrArg (fun arguments =>
        MarkerStableBoundedWitnessedActiveSchemaCoverage g count
          initialLeft initialRight outerBound width arguments word)
        hmovedArguments
    have houter : MarkerStableBoundedWitnessedActiveSchemaCoverage g count
        initialLeft initialRight outerBound width prepared.arguments word := by
      apply htype.mp
      simpa [moved, outerBound, word] using outer
    have hlength :
        (path.word (sequence.levels 0) ++ prepared.suffix).length <
          word.length := by
      simpa [offset, word, Nat.add_assoc] using
        sequence.toRegular.appendedWord_lt_after_drop prepared.suffix j
    obtain ⟨eliminated⟩ :=
      stablePrepared.exists_eliminatedCoverage hwidth houter hlength
    have hoffset : offset ≤
        g.boundedExposureBound (growth 0) + 1 := by
      dsimp [offset]
      have hsuffix := prepared.suffix_length_le
      omega
    have hshift : growth (offset + j) ≤
        stairWindowMax growth
          (g.boundedExposureBound (growth 0) + 1) j :=
      growth_shift_le_stairWindowMax growth hoffset
    have houterBound : outerBound ≤
        let window := stairWindowMax growth
          (g.boundedExposureBound (growth 0) + 1) j
        window + window := by
      dsimp [outerBound]
      exact Nat.add_le_add hshift hshift
    have hbound :
        outerBound + outerBound *
            (g.boundedExposureBound (growth 0) + growth 0 + 1) ≤
          g.widthReductionGrowth growth j := by
      unfold widthReductionGrowth
      dsimp
      exact Nat.add_le_add houterBound
        (Nat.mul_le_mul houterBound (le_refl _))
    exact ⟨eliminated.mono hbound⟩

/-- A single growth function works uniformly for every marker count.  This is
the shared-bound packaging needed when the final presentation bound is also
used as the number of critical markers. -/
@[expose] public def HasUniformMarkerStableWitnessedRegularActiveStairBase
    (g : EncodedFirstOrderGrammar Action) (width : ℕ) : Prop :=
  ∃ growth : ℕ → ℕ,
    ∀ count initialLeft initialRight,
      (g.withCriticalMarkers count).groundPairCode
          initialLeft initialRight = true →
      (g.withCriticalMarkers count).TraceEquivalent
          initialLeft initialRight →
      ∀ path : TracePath (g.withCriticalMarkers count)
        initialLeft initialRight,
        EventuallyMarkerStableOpenSound g count initialLeft initialRight
            (growth 0) path ∨
          Nonempty (MarkerStableWitnessedRegularActiveStairSequence g count
            initialLeft initialRight width growth path)

public theorem HasUniformMarkerStableWitnessedRegularActiveStairBase.reduceWidth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {width : ℕ}
    (hstair : g.HasUniformMarkerStableWitnessedRegularActiveStairBase width)
    (hwidth : 0 < width) :
    g.HasUniformMarkerStableWitnessedRegularActiveStairBase (width - 1) := by
  obtain ⟨growth, hstair⟩ := hstair
  refine ⟨g.widthReductionGrowth growth, ?_⟩
  intro count initialLeft initialRight hground hequivalent path
  have hgExtended := g.withCriticalMarkers_wellFormed hg count
  have laws := guardedContextLaws_of_wellFormed hgExtended
  have hgroundSteps : (g.withCriticalMarkers count).PreservesGroundSteps := by
    intro label source target hsource hstep
    exact preservesGroundSteps_of_wellFormed hgExtended hsource hstep
  rcases hstair count initialLeft initialRight hground hequivalent path with
    heventually | hsequence
  · exact Or.inl (heventually.mono
      (growth_zero_le_widthReductionGrowth g growth))
  · obtain ⟨sequence⟩ := hsequence
    exact sequence.reduceWidth hg laws hgroundSteps hequivalent hwidth

/-- Iterating the count-independent one-step theorem eliminates every active
parameter while retaining one growth function for all marker extensions. -/
public theorem HasUniformMarkerStableWitnessedRegularActiveStairBase.reduceToZero
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {width : ℕ}
    (hstair : g.HasUniformMarkerStableWitnessedRegularActiveStairBase width) :
    g.HasUniformMarkerStableWitnessedRegularActiveStairBase 0 := by
  induction width with
  | zero => simpa using hstair
  | succ width ih =>
      apply ih
      simpa using hstair.reduceWidth hg (by omega)

end EncodedFirstOrderGrammar

end DCFEquivalence
