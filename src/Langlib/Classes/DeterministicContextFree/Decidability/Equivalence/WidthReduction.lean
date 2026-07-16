module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedExposure
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StairBoundMonotonicity
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TailEliminationSupport

@[expose]
public section

/-!
# Eliminating one active parameter from a regular stair

The first part of width reduction turns a bounded inequivalent level-zero
coverage into one uniformly oriented shorter equation.  Its exposed argument
is moved to the last active slot, and the opposite residual is reindexed by
the same transposition.  The resulting package is independent of which side
originally exposed the variable.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Reindexed data extracted from one inequivalent level-zero coverage. -/
public structure PreparedTailElimination
    (g : EncodedFirstOrderGrammar Action)
    (initialLeft initialRight : RegularTerm)
    (bound exposure width : ℕ) (originalArguments : List RegularTerm)
    (stem : List (Label Action)) where
  arguments : List RegularTerm
  selectedIndex : ℕ
  selectedIndex_lt_width : selectedIndex < width
  arguments_eq_moved : arguments =
    RegularTerm.moveArgumentToActiveLast originalArguments width selectedIndex
  arity : ℕ
  argument_count : arguments.length = arity
  arguments_ground : ∀ argument ∈ arguments,
    argument.Ground g.ranks
  width_le_arity : width ≤ arity
  replacement : RegularTerm
  replacement_supported : RegularTerm.SupportedByPrefix
    g.ranks arity width replacement
  replacement_witness : replacement.HasPrefixWitness width
  replacement_nonvariable :
    ¬replacement.UnfoldingEquivalent
      (RegularTerm.variableTerm (width - 1))
  replacement_size_le : replacement.nodes.length ≤
    exposure + bound
  suffix : List (Label Action)
  suffix_length_le : suffix.length ≤ exposure
  shorterLeft : RegularTerm
  shorterRight : RegularTerm
  shorter_derivation : CertificateDerivable g initialLeft initialRight []
    (.pair (stem ++ suffix) shorterLeft shorterRight)
  last_argument : RegularTerm
  last_argument_at : arguments[width - 1]? = some last_argument
  shorterLeft_matches : shorterLeft.UnfoldingEquivalent last_argument
  shorterRight_matches : shorterRight.UnfoldingEquivalent
    (replacement.instantiate arguments)

private theorem ExposedEquation.residual_size_le_presentationCost_left
    {g : EncodedFirstOrderGrammar Action}
    {left right : RegularTerm} {arguments : List RegularTerm}
    (equation : ExposedEquation g left right arguments) :
    equation.leftResidual.nodes.length ≤ equation.presentationCost := by
  unfold ExposedEquation.presentationCost
  omega

private theorem ExposedEquation.residual_size_le_presentationCost_right
    {g : EncodedFirstOrderGrammar Action}
    {left right : RegularTerm} {arguments : List RegularTerm}
    (equation : ExposedEquation g left right arguments) :
    equation.rightResidual.nodes.length ≤ equation.presentationCost := by
  unfold ExposedEquation.presentationCost
  omega

private theorem ExposedEquation.suffix_length_le_presentationCost
    {g : EncodedFirstOrderGrammar Action}
    {left right : RegularTerm} {arguments : List RegularTerm}
    (equation : ExposedEquation g left right arguments) :
    (equation.word.map
      fun action => (Sum.inl action : Label Action)).length ≤
        equation.presentationCost := by
  simp only [List.length_map]
  unfold ExposedEquation.presentationCost
  omega

/-- Maximum of a growth function over every shift up to `radius`. -/
@[expose] public def stairWindowMax
    (growth : ℕ → ℕ) (radius j : ℕ) : ℕ :=
  ((List.range (radius + 1)).map fun offset => growth (offset + j))
    |>.foldr max 0

public theorem growth_shift_le_stairWindowMax
    (growth : ℕ → ℕ) {radius offset j : ℕ}
    (hoffset : offset ≤ radius) :
    growth (offset + j) ≤ stairWindowMax growth radius j := by
  unfold stairWindowMax
  apply List.le_max_of_le
  · exact List.mem_map.mpr
      ⟨offset, List.mem_range.mpr (by omega), rfl⟩
  · exact le_rfl

/-- Uniform growth bound after one tail elimination.  The finite window
absorbs the path-dependent, but uniformly bounded, number of dropped levels. -/
noncomputable def widthReductionGrowth
    (g : EncodedFirstOrderGrammar Action) (growth : ℕ → ℕ)
    (j : ℕ) : ℕ :=
  let exposure := g.boundedExposureBound (growth 0)
  let window := stairWindowMax growth (exposure + 1) j
  let outer := window + window
  outer + outer * (exposure + growth 0 + 1)

public theorem growth_zero_le_widthReductionGrowth
    (g : EncodedFirstOrderGrammar Action) (growth : ℕ → ℕ) :
    growth 0 ≤ g.widthReductionGrowth growth 0 := by
  have hwindow : growth (0 + 0) ≤
      stairWindowMax growth (g.boundedExposureBound (growth 0) + 1) 0 :=
    growth_shift_le_stairWindowMax growth (by omega)
  have hzero : growth 0 ≤
      stairWindowMax growth (g.boundedExposureBound (growth 0) + 1) 0 := by
    simpa using hwindow
  unfold widthReductionGrowth
  dsimp
  exact hzero.trans
    ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))

/-- If the schema pair of a bounded regular coverage is already open-trace
equivalent, that selected path level is an open-sound stopping point. -/
public def BoundedWitnessedActiveSchemaCoverage.toBoundedOpenSoundCoverage
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm} {word}
    (bounded : BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight bound width arguments word)
    (hequivalent : g.TraceEquivalent
      bounded.witnessed.coverage.schema.left
      bounded.witnessed.coverage.schema.right) :
    BoundedOpenSoundCoverage g initialLeft initialRight bound word :=
  let coverage := bounded.witnessed.coverage
  { left := coverage.left
    right := coverage.right
    derivation := coverage.derivation
    schema := coverage.schema
    arguments := coverage.arguments
    word_nonempty := coverage.word_nonempty
    arity_le := bounded.arity_le
    left_size_le := bounded.left_size_le
    right_size_le := bounded.right_size_le
    open_sound := ⟨coverage.schema_wellFormed, hequivalent⟩
    argument_count := coverage.argument_count
    arguments_ground := coverage.arguments_ground
    left_matches := coverage.left_matches
    right_matches := coverage.right_matches }

/-- Moving a supplied bounded exposure into the final active slot produces
the uniformly oriented equation consumed by every later stair level.  The
explicit `exposure` parameter allows the equation to have been selected in a
smaller conservative grammar. -/
public theorem BoundedWitnessedActiveSchemaCoverage.exists_preparedTailElimination_of_exposed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    {bound exposure width : ℕ} {arguments : List RegularTerm}
    {stem : List (Label Action)}
    (bounded : BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
      bound width arguments stem)
    (hwidth : 0 < width)
    (exposed : ActiveExposedCertificate g initialLeft initialRight width
      bounded.witnessed.coverage)
    (hexposedBound : exposed.equation.presentationCost ≤ exposure) :
    ∃ prepared : PreparedTailElimination g initialLeft initialRight
        bound exposure width arguments stem,
      (prepared.replacement = RegularTerm.moveParameterToActiveLast
          exposed.equation.rightResidual
          bounded.witnessed.coverage.schema.arity width
          exposed.equation.variableIndex) ∨
        (prepared.replacement = RegularTerm.moveParameterToActiveLast
          exposed.equation.leftResidual
          bounded.witnessed.coverage.schema.arity width
          exposed.equation.variableIndex) := by
  let coverage := bounded.witnessed.coverage
  let equation := exposed.equation
  let x := equation.variableIndex
  have hxWidth : x < width := exposed.variableIndex_lt_width
  have hwidthArity : width ≤ coverage.schema.arity :=
    coverage.left_supported.2.1
  have hxArity : x < coverage.schema.arity := hxWidth.trans_le hwidthArity
  have hlastArity : width - 1 < coverage.schema.arity := by
    omega
  let movedArguments := RegularTerm.moveArgumentToActiveLast
    coverage.arguments width x
  have hmovedArgumentsEq : movedArguments =
      RegularTerm.moveArgumentToActiveLast arguments width x := by
    exact congrArg
      (fun tuple => RegularTerm.moveArgumentToActiveLast tuple width x)
      bounded.arguments_eq
  have hmovedLength : movedArguments.length = coverage.schema.arity := by
    dsimp [movedArguments]
    rw [RegularTerm.moveArgumentToActiveLast,
      RegularTerm.swapArguments_length, coverage.argument_count]
  have hmovedGround : ∀ argument ∈ movedArguments,
      argument.Ground g.ranks := by
    apply RegularTerm.swapArguments_forall_mem
      (P := fun argument => argument.Ground g.ranks)
    · simpa [coverage.argument_count] using hxArity
    · simpa [coverage.argument_count] using hlastArity
    · exact coverage.arguments_areGround
  have hlastArgument : movedArguments[width - 1]? =
      some exposed.argument := by
    rw [RegularTerm.moveArgumentToActiveLast_getElem? hwidth hxWidth
      (by rw [coverage.argument_count]; exact hwidthArity)]
    exact exposed.argument_at
  have hleftResidualSupported := coverage.left_supported.residual hg
    coverage.rank_padding equation.left_run
  have hrightResidualSupported := coverage.right_supported.residual hg
    coverage.rank_padding equation.right_run
  have hleftResidualWitness := bounded.witnessed.left_witness.runActions
    hg coverage.rank_padding coverage.left_supported.1 equation.left_run
  have hrightResidualWitness := bounded.witnessed.right_witness.runActions
    hg coverage.rank_padding coverage.right_supported.1 equation.right_run
  have moved_nonvariable
      (source : RegularTerm)
      (hsource : RegularTerm.SupportedByPrefix g.ranks
        coverage.schema.arity width source)
      (hsourceNonvariable :
        ¬source.UnfoldingEquivalent (RegularTerm.variableTerm x)) :
      ¬(RegularTerm.moveParameterToActiveLast source
          coverage.schema.arity width x).UnfoldingEquivalent
        (RegularTerm.variableTerm (width - 1)) := by
    intro hmovedVariable
    have hmovedRoot := rootNode?_variable_of_unfoldingEquivalent
      hmovedVariable.symm
      (RegularTerm.variableTerm_rootNode? (width - 1))
    let identity := RegularTerm.identityArguments coverage.schema.arity
    let movedIdentity := RegularTerm.moveArgumentToActiveLast
      identity width x
    have hidentityLength : identity.length = coverage.schema.arity := by
      simp [identity]
    have hidentityClosed : ∀ argument ∈ identity,
        argument.ReferenceClosed := by
      simpa [identity] using
        (RegularTerm.identityArguments_referenceClosed coverage.schema.arity)
    have hmovedIdentityClosed : ∀ argument ∈ movedIdentity,
        argument.ReferenceClosed := by
      apply RegularTerm.swapArguments_forall_mem
      · simpa [identity] using hxArity
      · simpa [identity] using hlastArity
      · exact hidentityClosed
    have hlastIdentity : movedIdentity[width - 1]? =
        some (RegularTerm.variableTerm x) := by
      rw [RegularTerm.moveArgumentToActiveLast_getElem? hwidth hxWidth
        (by simpa [identity] using hwidthArity)]
      exact RegularTerm.identityArguments_getElem? hxArity
    have hmovedInstance :=
      RegularTerm.instantiate_unfoldingEquivalent_argument hmovedRoot
        hlastIdentity (RegularTerm.variableTerm_referenceClosed x)
    have hfixed :=
      RegularTerm.moveParameterToActiveLast_fixedInstance hsource
        hwidth hxWidth hidentityLength hidentityClosed
    have hidentity := RegularTerm.instantiate_identity_unfoldingEquivalent
      hsource.1
    exact hsourceNonvariable
      (hidentity.symm.trans (hfixed.symm.trans hmovedInstance))
  rcases exposed.orientation with horientation | horientation
  · let replacement := RegularTerm.moveParameterToActiveLast
      equation.rightResidual coverage.schema.arity width x
    have hvariableResidual :=
      unfoldingEquivalent_variableTerm_of_rootNode?
        (schema := equation.leftResidual)
        (x := x) horientation.1
    have hsourceNonvariable :
        ¬equation.rightResidual.UnfoldingEquivalent
          (RegularTerm.variableTerm x) := by
      intro hequivalent
      exact horientation.2.2
        (hequivalent.trans hvariableResidual.symm)
    have hreplacementSupported :=
      hrightResidualSupported.moveParameterToActiveLast hwidth hxWidth
    have hreplacementWitness :=
      hrightResidualWitness.moveParameterToActiveLast
        (RegularTerm.referenceClosed_of_wellFormed
          hrightResidualSupported.1)
        hwidthArity hwidth hxWidth
    have hfixed :=
      RegularTerm.moveParameterToActiveLast_fixedInstance
        hrightResidualSupported
        hwidth hxWidth coverage.argument_count
          coverage.arguments_referenceClosed
    have hreplacementSize : replacement.nodes.length ≤
        exposure + bound := by
      dsimp [replacement]
      rw [RegularTerm.moveParameterToActiveLast,
        RegularTerm.swapParameters_nodes_length hxArity hlastArity]
      have hresidual :=
        equation.residual_size_le_presentationCost_right.trans
          hexposedBound
      exact Nat.add_le_add hresidual bounded.arity_le
    refine ⟨
      { arguments := movedArguments
        selectedIndex := x
        selectedIndex_lt_width := hxWidth
        arguments_eq_moved := hmovedArgumentsEq
        arity := coverage.schema.arity
        argument_count := hmovedLength
        arguments_ground := hmovedGround
        width_le_arity := hwidthArity
        replacement := replacement
        replacement_supported := hreplacementSupported
        replacement_witness := hreplacementWitness
        replacement_nonvariable := moved_nonvariable
          equation.rightResidual hrightResidualSupported hsourceNonvariable
        replacement_size_le := hreplacementSize
        suffix := equation.word.map Sum.inl
        suffix_length_le :=
          equation.suffix_length_le_presentationCost.trans hexposedBound
        shorterLeft := exposed.targets.leftTarget
        shorterRight := exposed.targets.rightTarget
        shorter_derivation := exposed.targets.derivation
        last_argument := exposed.argument
        last_argument_at := hlastArgument
        shorterLeft_matches := horientation.2.1
        shorterRight_matches :=
          exposed.targets.right_matches.trans hfixed.symm }, Or.inl rfl⟩
  · let replacement := RegularTerm.moveParameterToActiveLast
      equation.leftResidual coverage.schema.arity width x
    have hvariableResidual :=
      unfoldingEquivalent_variableTerm_of_rootNode?
        (schema := equation.rightResidual)
        (x := x) horientation.1
    have hsourceNonvariable :
        ¬equation.leftResidual.UnfoldingEquivalent
          (RegularTerm.variableTerm x) := by
      intro hequivalent
      exact horientation.2.2
        (hequivalent.trans hvariableResidual.symm)
    have hreplacementSupported :=
      hleftResidualSupported.moveParameterToActiveLast hwidth hxWidth
    have hreplacementWitness :=
      hleftResidualWitness.moveParameterToActiveLast
        (RegularTerm.referenceClosed_of_wellFormed
          hleftResidualSupported.1)
        hwidthArity hwidth hxWidth
    have hfixed :=
      RegularTerm.moveParameterToActiveLast_fixedInstance
        hleftResidualSupported
        hwidth hxWidth coverage.argument_count
          coverage.arguments_referenceClosed
    have hreplacementSize : replacement.nodes.length ≤
        exposure + bound := by
      dsimp [replacement]
      rw [RegularTerm.moveParameterToActiveLast,
        RegularTerm.swapParameters_nodes_length hxArity hlastArity]
      have hresidual :=
        equation.residual_size_le_presentationCost_left.trans
          hexposedBound
      exact Nat.add_le_add hresidual bounded.arity_le
    refine ⟨
      { arguments := movedArguments
        selectedIndex := x
        selectedIndex_lt_width := hxWidth
        arguments_eq_moved := hmovedArgumentsEq
        arity := coverage.schema.arity
        argument_count := hmovedLength
        arguments_ground := hmovedGround
        width_le_arity := hwidthArity
        replacement := replacement
        replacement_supported := hreplacementSupported
        replacement_witness := hreplacementWitness
        replacement_nonvariable := moved_nonvariable
          equation.leftResidual hleftResidualSupported hsourceNonvariable
        replacement_size_le := hreplacementSize
        suffix := equation.word.map Sum.inl
        suffix_length_le :=
          equation.suffix_length_le_presentationCost.trans hexposedBound
        shorterLeft := exposed.targets.rightTarget
        shorterRight := exposed.targets.leftTarget
        shorter_derivation := .symmetry exposed.targets.derivation
        last_argument := exposed.argument
        last_argument_at := hlastArgument
        shorterLeft_matches := horientation.2.1
        shorterRight_matches :=
          exposed.targets.left_matches.trans hfixed.symm }, Or.inr rfl⟩

/-- Moving an inequivalent exposure into the final active slot produces the
uniformly oriented equation consumed by every later stair level. -/
public theorem BoundedWitnessedActiveSchemaCoverage.exists_preparedTailElimination
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm}
    {bound width : ℕ} {arguments : List RegularTerm}
    {stem : List (Label Action)}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    (bounded : BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
      bound width arguments stem)
    (hwidth : 0 < width)
    (hinequivalent : ¬g.TraceEquivalent
      bounded.witnessed.coverage.schema.left
        bounded.witnessed.coverage.schema.right) :
    Nonempty (PreparedTailElimination g initialLeft initialRight
      bound (g.boundedExposureBound bound) width arguments stem) := by
  let ordinary := bounded.toBoundedActiveSchemaCoverage
  obtain ⟨exposed, hexposedBound⟩ :=
    ordinary.exists_boundedActiveExposedCertificate hg laws hgroundSteps
      hinitialEquivalent hinequivalent
  obtain ⟨prepared, _⟩ :=
    bounded.exists_preparedTailElimination_of_exposed hg hwidth
      exposed hexposedBound
  exact ⟨prepared⟩

/-- Apply a prepared shorter equation to one later coverage.  The active
width drops by one, and a coarse bound accounts for tying the replacement
graph into both outer schemas. -/
public theorem PreparedTailElimination.exists_eliminatedCoverage
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {bound exposure width : ℕ} {originalArguments : List RegularTerm}
    {stem : List (Label Action)}
    (prepared : PreparedTailElimination g initialLeft initialRight
      bound exposure width originalArguments stem)
    (hwidth : 0 < width)
    {outerBound : ℕ} {word : List (Label Action)}
    (outer : BoundedWitnessedActiveSchemaCoverage g
      initialLeft initialRight outerBound width prepared.arguments word)
    (hlength : (stem ++ prepared.suffix).length < word.length) :
    ∃ target : BoundedWitnessedActiveSchemaCoverage g
        initialLeft initialRight
        (outerBound + outerBound *
          (exposure + bound + 1))
        (width - 1) prepared.arguments word,
      target.witnessed.coverage.schema.left =
          RegularTerm.tieInto outer.witnessed.coverage.schema.left
            prepared.replacement prepared.arguments.length (width - 1) ∧
        target.witnessed.coverage.schema.right =
          RegularTerm.tieInto outer.witnessed.coverage.schema.right
            prepared.replacement prepared.arguments.length (width - 1) := by
  let raw := outer.witnessed.coverage
  let sourceCoverage : ActiveSchemaCoverage g initialLeft initialRight
      width word :=
    { left := raw.left
      right := raw.right
      derivation := raw.derivation
      schema := raw.schema
      arguments := prepared.arguments
      word_nonempty := raw.word_nonempty
      schema_wellFormed := raw.schema_wellFormed
      rank_padding := raw.rank_padding
      left_supported := raw.left_supported
      right_supported := raw.right_supported
      argument_count := by
        simpa only [← outer.arguments_eq] using raw.argument_count
      arguments_ground := by
        simpa only [← outer.arguments_eq] using raw.arguments_ground
      left_matches := by
        simpa only [← outer.arguments_eq] using raw.left_matches
      right_matches := by
        simpa only [← outer.arguments_eq] using raw.right_matches }
  let source : WitnessedActiveSchemaCoverage g initialLeft initialRight
      width word :=
    { coverage := sourceCoverage
      left_witness := by
        change raw.schema.left.HasPrefixWitness width
        exact outer.witnessed.left_witness
      right_witness := by
        change raw.schema.right.HasPrefixWitness width
        exact outer.witnessed.right_witness }
  have hx : width - 1 < prepared.arguments.length := by
    rw [prepared.argument_count]
    have hwidthArity := prepared.width_le_arity
    omega
  have hlast : prepared.arguments[width - 1] = prepared.last_argument := by
    have hlastAt := prepared.last_argument_at
    rw [List.getElem?_eq_getElem hx] at hlastAt
    exact Option.some.inj hlastAt
  have hleftSchemaWellFormed :
      source.coverage.schema.left.WellFormed g.ranks
        prepared.arguments.length := by
    rw [source.coverage.argument_count]
    exact source.coverage.left_supported.1
  have hrightSchemaWellFormed :
      source.coverage.schema.right.WellFormed g.ranks
        prepared.arguments.length := by
    rw [source.coverage.argument_count]
    exact source.coverage.right_supported.1
  have hreplacementWellFormed :
      prepared.replacement.WellFormed g.ranks
        prepared.arguments.length := by
    simpa only [prepared.argument_count] using
      prepared.replacement_supported.1
  have hleftMatch : source.coverage.left.UnfoldingEquivalent
      (source.coverage.schema.left.instantiate prepared.arguments) :=
    (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
      source.coverage.left_matches
  have hrightMatch : source.coverage.right.UnfoldingEquivalent
      (source.coverage.schema.right.instantiate prepared.arguments) :=
    (RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mp
      source.coverage.right_matches
  have hshorterLeft : prepared.shorterLeft.UnfoldingEquivalent
      prepared.arguments[width - 1] := by
    simpa only [hlast] using prepared.shorterLeft_matches
  obtain ⟨result⟩ := exists_tailEliminatedPair
    source.coverage.derivation prepared.shorter_derivation
    hleftSchemaWellFormed hrightSchemaWellFormed
    hreplacementWellFormed hx prepared.arguments_ground
    prepared.replacement_nonvariable hlength hleftMatch hrightMatch
    hshorterLeft prepared.shorterRight_matches
  let target := result.toWitnessedActiveSchemaCoverage source hwidth
    hreplacementWellFormed prepared.replacement_witness
    prepared.replacement_nonvariable
  have harityBound : prepared.arguments.length ≤ outerBound := by
    rw [source.coverage.argument_count]
    exact outer.arity_le
  have hreplacementPlusOne : prepared.replacement.nodes.length + 1 ≤
      exposure + bound + 1 :=
    Nat.add_le_add_right prepared.replacement_size_le 1
  have hleftSize :
      (RegularTerm.tieInto source.coverage.schema.left
        prepared.replacement prepared.arguments.length
          (width - 1)).nodes.length ≤
        outerBound + outerBound *
          (exposure + bound + 1) := by
    exact (RegularTerm.tieInto_nodes_length_le
      source.coverage.schema.left prepared.replacement hx).trans
        (Nat.add_le_add outer.left_size_le
          (Nat.mul_le_mul harityBound hreplacementPlusOne))
  have hrightSize :
      (RegularTerm.tieInto source.coverage.schema.right
        prepared.replacement prepared.arguments.length
          (width - 1)).nodes.length ≤
        outerBound + outerBound *
          (exposure + bound + 1) := by
    exact (RegularTerm.tieInto_nodes_length_le
      source.coverage.schema.right prepared.replacement hx).trans
        (Nat.add_le_add outer.right_size_le
          (Nat.mul_le_mul harityBound hreplacementPlusOne))
  refine ⟨
    { witnessed := target
      arguments_eq := ?_
      arity_le := ?_
      left_size_le := ?_
      right_size_le := ?_ }, ?_, ?_⟩
  · rfl
  · change prepared.arguments.length ≤
      outerBound + outerBound *
        (exposure + bound + 1)
    exact harityBound.trans (Nat.le_add_right _ _)
  · change
      (RegularTerm.tieInto source.coverage.schema.left
        prepared.replacement prepared.arguments.length
          (width - 1)).nodes.length ≤
        outerBound + outerBound *
          (exposure + bound + 1)
    exact hleftSize
  · change
      (RegularTerm.tieInto source.coverage.schema.right
        prepared.replacement prepared.arguments.length
          (width - 1)).nodes.length ≤
        outerBound + outerBound *
          (exposure + bound + 1)
    exact hrightSize
  · rfl
  · rfl

/-- One witnessed regular stair either stops immediately at an open-sound
row or yields a witnessed stair with one fewer active parameter. -/
public theorem WitnessedRegularActiveStairSequence.reduceWidth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {initialLeft initialRight : RegularTerm}
    (hinitialEquivalent : g.TraceEquivalent initialLeft initialRight)
    {width : ℕ} {growth : ℕ → ℕ}
    {path : TracePath g initialLeft initialRight}
    (sequence : WitnessedRegularActiveStairSequence g
      initialLeft initialRight width growth path)
    (hwidth : 0 < width) :
    g.EventuallyBoundedOpenSound initialLeft initialRight
        (g.widthReductionGrowth growth 0) path ∨
      Nonempty (WitnessedRegularActiveStairSequence g
        initialLeft initialRight (width - 1)
          (g.widthReductionGrowth growth) path) := by
  obtain ⟨initial⟩ := sequence.covered 0
  by_cases hequivalent : g.TraceEquivalent
      initial.witnessed.coverage.schema.left
      initial.witnessed.coverage.schema.right
  · left
    let stopped := initial.toBoundedOpenSoundCoverage hequivalent
    refine ⟨sequence.levels 0, ⟨stopped.mono ?_⟩⟩
    exact growth_zero_le_widthReductionGrowth g growth
  · obtain ⟨prepared⟩ := initial.exists_preparedTailElimination
      hg laws hgroundSteps hinitialEquivalent hwidth hequivalent
    let moved := sequence.moveParameterToActiveLast hwidth
      prepared.selectedIndex prepared.selectedIndex_lt_width
    let offset := prepared.suffix.length + 1
    have hmovedArguments : moved.arguments = prepared.arguments := by
      simpa [moved] using prepared.arguments_eq_moved.symm
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
        BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
            outerBound width moved.arguments word =
          BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
            outerBound width prepared.arguments word :=
      congrArg (fun arguments =>
        BoundedWitnessedActiveSchemaCoverage g initialLeft initialRight
          outerBound width arguments word) hmovedArguments
    have houter : BoundedWitnessedActiveSchemaCoverage g
        initialLeft initialRight outerBound width prepared.arguments word := by
      apply htype.mp
      simpa [moved, outerBound, word] using outer
    have hlength :
        (path.word (sequence.levels 0) ++ prepared.suffix).length <
          word.length := by
      simpa [offset, word, Nat.add_assoc] using
        sequence.toRegular.appendedWord_lt_after_drop prepared.suffix j
    obtain ⟨eliminated, _, _⟩ :=
      prepared.exists_eliminatedCoverage hwidth houter hlength
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

/-- Width reduction is uniform over all queries and paths, so it lowers the
witnessed stair-base property itself. -/
public theorem HasWitnessedRegularActiveStairBase.reduceWidth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {width : ℕ}
    (hstair : g.HasWitnessedRegularActiveStairBase width)
    (hwidth : 0 < width) :
    g.HasWitnessedRegularActiveStairBase (width - 1) := by
  obtain ⟨growth, hstair⟩ := hstair
  refine ⟨g.widthReductionGrowth growth, ?_⟩
  intro initialLeft initialRight hground hequivalent path
  rcases hstair initialLeft initialRight hground hequivalent path with
    hbounded | hsequence
  · exact Or.inl (hbounded.mono
      (growth_zero_le_widthReductionGrowth g growth))
  · obtain ⟨sequence⟩ := hsequence
    exact sequence.reduceWidth hg laws hgroundSteps hequivalent hwidth

/-- Iterating the one-step theorem eliminates every active parameter. -/
public theorem HasWitnessedRegularActiveStairBase.reduceToZero
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {width : ℕ}
    (hstair : g.HasWitnessedRegularActiveStairBase width) :
    g.HasWitnessedRegularActiveStairBase 0 := by
  induction width with
  | zero => simpa using hstair
  | succ width ih =>
      apply ih
      simpa using hstair.reduceWidth hg laws hgroundSteps (by omega)

/-- Any finite-head active stair base reaches the ordinary width-zero regular
interface after structural tail elimination. -/
public theorem HasActiveStairBase.reduceToRegularZero
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {width : ℕ} (hstair : g.HasActiveStairBase width) :
    g.HasRegularActiveStairBase 0 :=
  (hstair.toWitnessedRegular.reduceToZero hg laws hgroundSteps).toRegular

/-- The completed width induction turns any finite-head stair base into one
fixed bounded original open-sound basis of root certificates. -/
public theorem derivable_nop_of_activeStairBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {width : ℕ} (hstair : g.HasActiveStairBase width) :
    ∃ bound,
      ∀ initialLeft initialRight,
        g.groundPairCode initialLeft initialRight = true →
        g.TraceEquivalent initialLeft initialRight →
        CertificateDerivable g initialLeft initialRight
          (g.boundedOpenSoundBasis bound) (.nop []) :=
  derivable_nop_of_regularActiveStairBase_zero laws hgroundSteps
    (hstair.reduceToRegularZero hg laws hgroundSteps)

/-- A witnessed regular active stair already has the precise interface used by
the width-reduction induction, so it yields the same bounded root-certificate
basis without first forgetting its witnesses. -/
public theorem derivable_nop_of_witnessedRegularActiveStairBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (laws : g.GuardedContextLaws)
    (hgroundSteps : g.PreservesGroundSteps)
    {width : ℕ} (hstair : g.HasWitnessedRegularActiveStairBase width) :
    ∃ bound,
      ∀ initialLeft initialRight,
        g.groundPairCode initialLeft initialRight = true →
        g.TraceEquivalent initialLeft initialRight →
        CertificateDerivable g initialLeft initialRight
          (g.boundedOpenSoundBasis bound) (.nop []) :=
  derivable_nop_of_regularActiveStairBase_zero laws hgroundSteps
    (hstair.reduceToZero hg laws hgroundSteps).toRegular

end EncodedFirstOrderGrammar

end DCFEquivalence
