module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedBaseProtectedDepth
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotProgressRebasing

@[expose]
public section

/-!
# Fixed-tail presentations from operational non-sinking

The semantic `ExposesBy` predicate admits empty-word self-exposure on cyclic
regular terms.  Fixed-tail reflection only needs the operational fact that
the symbolic depth-prefix run does not enter a boundary variable.  Positive
protected application depth, together with fixed-base non-sinking, proves
that fact directly.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Fixed-base non-sinking prevents every proper symbolic prefix of a
positive depth-prefix schema from reaching a variable. -/
public theorem depthPrefix_noVariableBefore_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base : RegularTerm} (hbase : base.Ground g.ranks)
    (depth : ℕ) (hdepth : 0 < depth)
    {word : List Action}
    (hnever : g.NeverSinksFromBase base word) :
    g.NoVariableBefore
      (base.depthPrefix depth).head.toRegularTerm word := by
  intro stem suffix hword _hsuffix residual x hrun
  have hneverStem : g.NeverSinksFromBase base stem := by
    intro initialSegment remainder hstem hsinks
    apply hnever initialSegment (remainder ++ suffix)
    · calc
        word = stem ++ suffix := hword
        _ = (initialSegment ++ remainder) ++ suffix := by rw [hstem]
        _ = initialSegment ++ (remainder ++ suffix) := by
          rw [List.append_assoc]
    · exact hsinks
  have happlicationDepth :
      residual.ApplicationDepth depth :=
    depthPrefix_residual_applicationDepth_of_neverSinksFromBase
      hg hbase depth hrun hneverStem
  intro hvariable
  have hvariableRoot :
      residual.rootNode? = some (.inl x) :=
    rootNode?_variable_of_unfoldingEquivalent
      hvariable.symm
      (RegularTerm.variableTerm_rootNode? x)
  cases depth with
  | zero => omega
  | succ depth =>
      obtain ⟨Y, children, hroot, _hchildren⟩ :=
        happlicationDepth
      have happlicationRoot :
          residual.rootNode? = some (.inr (Y, children)) := by
        simpa [RegularTerm.rootNode?] using
          RegularTerm.nodeAt?_root_of_rootApplication? hroot
      rw [hvariableRoot] at happlicationRoot
      simp at happlicationRoot

/-- Fixed-tail reflection factored at its exact semantic requirement: absence
of a variable on proper symbolic prefixes. -/
public theorem exists_fixedTailResidual_of_noVariableBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler target : RegularTerm}
    (hterm : term.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) {word : List Action}
    (hrun : g.runActions? word term = some target)
    (hnoVariable :
      g.NoVariableBefore
        (term.depthPrefix depth).head.toRegularTerm word) :
    Nonempty (FixedTailResidual g term filler depth word target) := by
  let decomposition := term.depthPrefix depth
  let schema := decomposition.head.toRegularTerm
  let arguments := decomposition.paddedArguments g.ranks filler
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid term depth
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hterm depth
  have hschemaSupported :
      RegularTerm.SupportedByPrefix g.ranks
        (decomposition.schemaArity g.ranks)
        decomposition.tails.length schema :=
    FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked
  have hpadding :
      g.ranks.foldr max 0 ≤ decomposition.schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity]
  have hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks :=
    RegularTerm.depthPrefix_paddedArguments_ground
      hterm hfiller depth
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent term :=
    RegularTerm.depthPrefix_compiled_unfoldingEquivalent
      hterm hfiller depth
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed hschemaSupported.1)
      hargumentsClosed
  obtain ⟨instanceTarget, hinstanceRun, hinstanceTargetEquivalent⟩ :=
    exists_runActions_of_unfoldingEquivalent hg
      hinstanceEquivalent hinstanceClosed
      (RegularTerm.referenceClosed_of_ground hterm) hrun
  obtain ⟨residual, hsymbolic, hresidualMatch⟩ :=
    runActions?_reflects_instantiation_of_noVariableBefore
      hg word ⟨_, hschemaSupported.1⟩ hargumentsClosed
      hinstanceRun
      (by simpa [schema, decomposition] using hnoVariable)
  have hresidualSupported :=
    hschemaSupported.residual hg hpadding hsymbolic
  have hsourceWitness :
      schema.HasPrefixWitness decomposition.tails.length :=
    FiniteHead.toRegularTerm_hasPrefixWitness hvalid
  have hresidualWitness :=
    hsourceWitness.runActions hg hpadding hschemaSupported.1 hsymbolic
  have hinitialSize :=
    RegularTerm.depthPrefix_schema_nodes_length_le hterm depth
  have hsize :=
    g.runActions?_nodes_length_le hg
      ⟨decomposition.schemaArity g.ranks, hschemaSupported.1⟩
      hinitialSize hsymbolic
  exact ⟨
    { residual := residual
      symbolic_run := by simpa [schema, decomposition] using hsymbolic
      instance_matches := by
        simpa [arguments, decomposition] using
          hresidualMatch.trans hinstanceTargetEquivalent
      supported := by simpa [decomposition] using hresidualSupported
      hasPrefixWitness := by
        simpa [schema, decomposition] using hresidualWitness
      size_le := by simpa [decomposition] using hsize }⟩

/-- A positive-depth fixed-tail residual follows from operational
fixed-base non-sinking alone. -/
public theorem exists_fixedTailResidual_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler target : RegularTerm}
    (hterm : term.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) (hdepth : 0 < depth)
    {word : List Action}
    (hrun : g.runActions? word term = some target)
    (hnever : g.NeverSinksFromBase term word) :
    Nonempty (FixedTailResidual g term filler depth word target) := by
  apply exists_fixedTailResidual_of_noVariableBefore
    hg hterm hfiller depth hrun
  exact depthPrefix_noVariableBefore_of_neverSinksFromBase
    hg hterm depth hdepth hnever

/-- A whole pivot family admits a fixed-tail presentation at any prescribed
positive depth when every concrete word is operationally non-sinking. -/
public theorem
    exists_fixedTailPivotPresentation_atDepth_of_neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (hbase : base.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) (hdepth : 0 < depth)
    (hruns : ∀ j, g.run? (labels j) base = some (pivots j))
    (hordinary : ∀ j, ∃ actions : List Action,
      labels j = actions.map Sum.inl)
    (hnever : ∀ j actions,
      labels j = actions.map Sum.inl →
        g.NeverSinksFromBase base actions) :
    ∃ presentation : FixedTailPivotPresentation
        g base filler labels pivots,
      presentation.depth = depth ∧
        ∀ j,
          g.NeverSinksFromBase base
            (presentation.actions j) := by
  classical
  choose actions hlabels using hordinary
  have hresidual :
      ∀ j, FixedTailResidual g base filler depth
        (actions j) (pivots j) := by
    intro j
    have hrunActions :
        g.runActions? (actions j) base = some (pivots j) := by
      simpa [runActions?, ← hlabels j] using hruns j
    exact Classical.choice
      (exists_fixedTailResidual_of_neverSinksFromBase
        hg hbase hfiller depth hdepth hrunActions
        (hnever j (actions j) (hlabels j)))
  let presentation : FixedTailPivotPresentation
      g base filler labels pivots :=
    { depth := depth
      base_ground := hbase
      filler_ground := hfiller
      actions := actions
      labels_eq := hlabels
      residual := hresidual }
  exact ⟨presentation, rfl, by
    intro j
    exact hnever j (presentation.actions j)
      (presentation.labels_eq j)⟩

namespace TracePath.StructuredPivotChain.PivotTrajectory

namespace MaximalProgressRebase

/-- The maximal operational rebase feeds the fixed-tail construction without
any semantic missing-depth premise. -/
public theorem exists_fixedTailPivotPresentation_atDepth
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ) (hdepth : 0 < depth) :
    ∃ presentation : FixedTailPivotPresentation g
        rebase.base filler rebase.labels
        (fun count =>
          trajectory.representatives (rebase.start + count)),
      presentation.depth = depth ∧
        ∀ count,
          g.NeverSinksFromBase rebase.base
            (presentation.actions count) := by
  apply exists_fixedTailPivotPresentation_atDepth_of_neverSinksFromBase
    hg rebase.base_ground hfiller depth hdepth
    rebase.labels_run rebase.exists_actions_labels
  intro count actions hlabels
  exact rebase.neverSinksFromBase count actions hlabels

end MaximalProgressRebase

end TracePath.StructuredPivotChain.PivotTrajectory

end EncodedFirstOrderGrammar

end DCFEquivalence
