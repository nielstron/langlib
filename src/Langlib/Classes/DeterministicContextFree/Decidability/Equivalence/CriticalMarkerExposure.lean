module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.ActiveExposure
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerConservativity

@[expose]
public section

/-!
# Count-independent exposure in critical-marker extensions

Exposure is performed by the original grammar so that its presentation bound
cannot mention the number of fresh markers.  The common arguments need only be
ground in the marker extension: the resulting concrete original run is lifted
to that extension before groundness is used to rule out an out-of-range
exposed variable.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- An ordinary-action run is preserved literally by a critical-marker
extension. -/
public theorem withCriticalMarkers_runActions?_lift
    (g : EncodedFirstOrderGrammar Action) (count : ℕ)
    (word : List Action) (term : RegularTerm) :
    (g.withCriticalMarkers count).runActions? (word.map Sum.inl) term =
      g.runActions? word term := by
  unfold runActions?
  simpa [List.map_map, Function.comp_def, liftCriticalLabel] using
    g.withCriticalMarkers_run?_lift count (word.map Sum.inl) term

/-- The common lifted prefix preserves equivalence of instantiated residuals
in the marker extension. -/
public theorem ExposedEquation.instantiatedEquivalent_withCriticalMarkers
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (count : ℕ)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground (g.withCriticalMarkers count).ranks)
    (hsourceEquivalent : (g.withCriticalMarkers count).TraceEquivalent
      (left.instantiate arguments) (right.instantiate arguments))
    (equation : ExposedEquation g left right arguments) :
    (g.withCriticalMarkers count).TraceEquivalent
      (equation.leftResidual.instantiate arguments)
      (equation.rightResidual.instantiate arguments) := by
  let extended := g.withCriticalMarkers count
  have hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  have laws := guardedContextLaws_of_wellFormed hgExtended
  have hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hleftExtended : left.WellFormed extended.ranks arity :=
    wellFormed_extendedRanks g count hleft
  have hrightExtended : right.WellFormed extended.ranks arity :=
    wellFormed_extendedRanks g count hright
  have hleftLifted : extended.runActions? (equation.word.map Sum.inl) left =
      some equation.leftResidual := by
    rw [withCriticalMarkers_runActions?_lift]
    exact equation.left_run
  have hrightLifted : extended.runActions? (equation.word.map Sum.inl) right =
      some equation.rightResidual := by
    rw [withCriticalMarkers_runActions?_lift]
    exact equation.right_run
  obtain ⟨leftConcrete, hleftConcreteRun, hleftResidualConcrete⟩ :=
    extended.runActions?_instantiate hgExtended
      (equation.word.map Sum.inl) hleftExtended hargumentsClosed hleftLifted
  obtain ⟨rightConcrete, hrightConcreteRun, hrightResidualConcrete⟩ :=
    extended.runActions?_instantiate hgExtended
      (equation.word.map Sum.inl) hrightExtended hargumentsClosed hrightLifted
  have hconcreteEquivalent : extended.TraceEquivalent
      leftConcrete rightConcrete := by
    apply hsourceEquivalent.residual
    · simpa [runActions?] using hleftConcreteRun
    · simpa [runActions?] using hrightConcreteRun
  have hleftSchemaClosed :=
    RegularTerm.referenceClosed_of_wellFormed hleftExtended
  have hrightSchemaClosed :=
    RegularTerm.referenceClosed_of_wellFormed hrightExtended
  have hleftSourceClosed := RegularTerm.instantiate_referenceClosed
    hleftSchemaClosed hargumentsClosed
  have hrightSourceClosed := RegularTerm.instantiate_referenceClosed
    hrightSchemaClosed hargumentsClosed
  have hleftConcreteClosed := extended.runActions?_preserves_referenceClosed
    hgExtended (equation.word.map Sum.inl) hleftSourceClosed hleftConcreteRun
  have hrightConcreteClosed := extended.runActions?_preserves_referenceClosed
    hgExtended (equation.word.map Sum.inl) hrightSourceClosed hrightConcreteRun
  have hleftResidualClosed := extended.runActions?_preserves_referenceClosed
    hgExtended (equation.word.map Sum.inl) hleftSchemaClosed hleftLifted
  have hrightResidualClosed := extended.runActions?_preserves_referenceClosed
    hgExtended (equation.word.map Sum.inl) hrightSchemaClosed hrightLifted
  have hleftResidualInstanceClosed :=
    RegularTerm.instantiate_referenceClosed hleftResidualClosed
      hargumentsClosed
  have hrightResidualInstanceClosed :=
    RegularTerm.instantiate_referenceClosed hrightResidualClosed
      hargumentsClosed
  have hleftEquivalent : extended.TraceEquivalent
      (equation.leftResidual.instantiate arguments) leftConcrete :=
    laws.traceEquivalent_of_unfoldingEquivalentCode
      hleftResidualInstanceClosed hleftConcreteClosed
      ((RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        hleftResidualConcrete)
  have hrightEquivalent : extended.TraceEquivalent
      (equation.rightResidual.instantiate arguments) rightConcrete :=
    laws.traceEquivalent_of_unfoldingEquivalentCode
      hrightResidualInstanceClosed hrightConcreteClosed
      ((RegularTerm.unfoldingEquivalentCode_eq_true_iff _ _).mpr
        hrightResidualConcrete)
  exact hleftEquivalent.trans
    (hconcreteEquivalent.trans hrightEquivalent.symm)

/-- Replay an original exposed equation as an equation of the marker
extension.  The residual graphs and exposed variable are unchanged; only the
ordinary action word is injected into the enlarged action alphabet. -/
public def ExposedEquation.withCriticalMarkers
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (count : ℕ)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground (g.withCriticalMarkers count).ranks)
    (hsourceEquivalent : (g.withCriticalMarkers count).TraceEquivalent
      (left.instantiate arguments) (right.instantiate arguments))
    (equation : ExposedEquation g left right arguments) :
    ExposedEquation (g.withCriticalMarkers count) left right arguments :=
  { word := equation.word.map Sum.inl
    leftResidual := equation.leftResidual
    rightResidual := equation.rightResidual
    variableIndex := equation.variableIndex
    left_run := by
      rw [withCriticalMarkers_runActions?_lift]
      exact equation.left_run
    right_run := by
      rw [withCriticalMarkers_runActions?_lift]
      exact equation.right_run
    orientation := equation.orientation
    instantiated_equivalent :=
      equation.instantiatedEquivalent_withCriticalMarkers hg count
        hleft hright hargumentsGround hsourceEquivalent }

@[simp] public theorem ExposedEquation.presentationCost_withCriticalMarkers
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (count : ℕ)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground (g.withCriticalMarkers count).ranks)
    (hsourceEquivalent : (g.withCriticalMarkers count).TraceEquivalent
      (left.instantiate arguments) (right.instantiate arguments))
    (equation : ExposedEquation g left right arguments) :
    (equation.withCriticalMarkers hg count hleft hright hargumentsGround
      hsourceEquivalent).presentationCost = equation.presentationCost := by
  simp [ExposedEquation.withCriticalMarkers,
    ExposedEquation.presentationCost]

private theorem variable_lt_of_run_extendedGround
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (count : ℕ)
    {arity : ℕ} {schema residual : RegularTerm}
    {arguments : List RegularTerm} {x : ℕ} (word : List Action)
    (hschema : schema.WellFormed g.ranks arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground (g.withCriticalMarkers count).ranks)
    (hrun : g.runActions? word schema = some residual)
    (hroot : residual.rootNode? = some (.inl x)) :
    x < arity := by
  by_contra hnot
  have hnone : arguments[x]? = none := by
    apply List.getElem?_eq_none
    omega
  have hargumentsClosed : ∀ argument ∈ arguments,
      argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  obtain ⟨concrete, hconcreteRun, hresidualConcrete⟩ :=
    g.runActions?_instantiate hg word hschema hargumentsClosed hrun
  have hschemaExtended : schema.WellFormed
      (g.withCriticalMarkers count).ranks arguments.length := by
    apply wellFormed_extendedRanks g count
    simpa [hargumentsLength] using hschema
  have hsourceGround := RegularTerm.instantiate_ground hschemaExtended
    hargumentsGround
  have hgExtended := g.withCriticalMarkers_wellFormed hg count
  have hconcreteRunExtended :
      (g.withCriticalMarkers count).runActions? (word.map Sum.inl)
          (schema.instantiate arguments) = some concrete := by
    rw [withCriticalMarkers_runActions?_lift]
    exact hconcreteRun
  have hconcreteGround : concrete.Ground
      (g.withCriticalMarkers count).ranks := by
    apply PreservesGroundSteps.ground_of_run
      (preservesGroundSteps_of_wellFormed hgExtended) hsourceGround
    simpa [runActions?] using hconcreteRunExtended
  have hresidualClosed := runActions?_preserves_referenceClosed
    hg word (RegularTerm.referenceClosed_of_wellFormed hschema) hrun
  have hinstantiatedRoot := instantiate_rootNode?_variable_none
    hresidualClosed hroot hnone
  have hconcreteRoot := rootNode?_variable_of_unfoldingEquivalent
    hresidualConcrete hinstantiatedRoot
  obtain ⟨symbol, children, happlication⟩ :=
    hconcreteGround.exists_rootApplication
  unfold RegularTerm.rootApplication? at happlication
  rw [hconcreteRoot] at happlication
  simp at happlication

/-- An equation exposed in the original grammar still selects a genuine
argument position when the common substitution is ground only in a marker
extension. -/
public theorem ExposedEquation.variableIndex_lt_of_extendedGround
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (count : ℕ)
    {arity : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : left.WellFormed g.ranks arity)
    (hright : right.WellFormed g.ranks arity)
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground (g.withCriticalMarkers count).ranks)
    (equation : ExposedEquation g left right arguments) :
    equation.variableIndex < arity := by
  rcases equation.orientation with hleftOrientation | hrightOrientation
  · exact variable_lt_of_run_extendedGround g hg count equation.word
      hleft hargumentsLength hargumentsGround equation.left_run
      hleftOrientation.1
  · exact variable_lt_of_run_extendedGround g hg count equation.word
      hright hargumentsLength hargumentsGround equation.right_run
      hrightOrientation.1

/-- Prefix support then places the exposed variable in the active prefix,
without introducing the marker count into the exposure bound. -/
public theorem ExposedEquation.variableIndex_lt_width_of_extendedGround
    (g : EncodedFirstOrderGrammar Action) (hg : g.WellFormed)
    (count : ℕ)
    {arity width : ℕ} {left right : RegularTerm}
    {arguments : List RegularTerm}
    (hleft : RegularTerm.SupportedByPrefix g.ranks arity width left)
    (hright : RegularTerm.SupportedByPrefix g.ranks arity width right)
    (hargumentsLength : arguments.length = arity)
    (hargumentsGround : ∀ argument ∈ arguments,
      argument.Ground (g.withCriticalMarkers count).ranks)
    (equation : ExposedEquation g left right arguments) :
    equation.variableIndex < width := by
  apply equation.variableIndex_lt_width_of_lt g hg hleft hright
  exact equation.variableIndex_lt_of_extendedGround g hg count
    hleft.1 hright.1 hargumentsLength hargumentsGround

end EncodedFirstOrderGrammar

end DCFEquivalence
