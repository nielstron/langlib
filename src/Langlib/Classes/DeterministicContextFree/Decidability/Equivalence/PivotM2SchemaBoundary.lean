module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotM2Window
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteUnfoldingDepth
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteSchemaCompaction
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.NonSinkingReflection

@[expose]
public section

/-!
# Schema boundaries in the bounded pivot window

The pointed-subterm form of the `M₂` theorem is sufficient for the finite
neighbourhood argument, but the later schema recurrence also needs the exact
unfolding path followed by successive sinking steps.  This file retains that
path and factors it through a finite open schema.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath

namespace StructuredPivotChain

/-- The bounded-pivot argument with the exact accumulated descendant depth
retained.  Each sinking step contributes one edge to the returned
`SubtermAtDepth` witness. -/
public theorem edgePosition_exists_boundedPivot_of_descendant
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (hbound : 0 < bound)
    (j : ℕ)
    (position : trajectory.EdgePosition j)
    (source : RegularTerm)
    (hsourceGround : source.Ground g.ranks)
    (hequivalent : position.term.UnfoldingEquivalent source) :
    ∃ descent finalSource,
      source.SubtermAtDepth descent finalSource ∧
      finalSource.Ground g.ranks ∧
      ∃ labels reached,
        labels.length ≤ g.structuredPivotM2Bound bound ∧
        g.run? labels finalSource = some reached ∧
        RegularTerm.UnfoldingEquivalent
          (trajectory.toPivotTrajectory.representatives (j + 1))
          reached := by
  let edge := trajectory.toPivotTrajectory.edgeWords j
  have solve :
      ∀ remaining,
        ∀ (current : trajectory.EdgePosition j)
          (currentSource : RegularTerm),
          currentSource.Ground g.ranks →
          current.term.UnfoldingEquivalent currentSource →
          edge.length - current.offset = remaining →
          ∃ descent finalSource,
            currentSource.SubtermAtDepth descent finalSource ∧
            finalSource.Ground g.ranks ∧
            ∃ labels reached,
              labels.length ≤ g.structuredPivotM2Bound bound ∧
              g.run? labels finalSource = some reached ∧
              RegularTerm.UnfoldingEquivalent
                (trajectory.toPivotTrajectory.representatives (j + 1))
                reached := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
        intro current currentSource hcurrentSourceGround
          hcurrentEquivalent hremaining
        rcases trajectory.edgePosition_reachesPivot_or_sinks
            hbound j current with hpivot | hsinks
        · obtain ⟨labels, _hlabels, hlength, hrun⟩ := hpivot
          have hcurrentSourceClosed :
              currentSource.ReferenceClosed :=
            RegularTerm.referenceClosed_of_ground hcurrentSourceGround
          obtain ⟨reached, hreachedRun, hreachedEquivalent⟩ :=
            exists_run_of_unfoldingEquivalent hg
              hcurrentEquivalent.symm
              hcurrentSourceClosed
              (RegularTerm.referenceClosed_of_ground current.ground)
              hrun
          exact ⟨0, currentSource, by simp,
            hcurrentSourceGround, labels, reached,
            hlength, hreachedRun, hreachedEquivalent.symm⟩
        · obtain ⟨word, remainder, hedge, _hwordLength, hsinks⟩ :=
            hsinks
          obtain ⟨stem, suffix, target, hword, ⟨step⟩⟩ :=
            hsinks.exists_sinkingStep_prefix
          have hedgeSplit :
              edge.drop current.offset =
                stem ++ (suffix ++ remainder) := by
            rw [hedge, hword, List.append_assoc]
          have hstemTake :
              (edge.drop current.offset).take stem.length = stem := by
            rw [hedgeSplit]
            simp
          have hstemLength :
              stem.length ≤ (edge.drop current.offset).length := by
            rw [hedgeSplit]
            simp
          have hnextOffset :
              current.offset + stem.length ≤ edge.length := by
            have hcurrentOffset : current.offset ≤ edge.length := by
              simpa [edge] using current.offset_le
            rw [List.length_drop] at hstemLength
            omega
          let next : trajectory.EdgePosition j :=
            { offset := current.offset + stem.length
              offset_le := by simpa [edge] using hnextOffset
              term := target
              run := by
                have htake :
                    edge.take (current.offset + stem.length) =
                      edge.take current.offset ++ stem := by
                  rw [List.take_add, hstemTake]
                change
                  g.run? (edge.take (current.offset + stem.length))
                      (trajectory.toPivotTrajectory.representatives j) =
                    some target
                rw [htake, g.run?_append, current.run]
                exact step.run }
          obtain ⟨nestedSource, hnestedSource,
              hsubtermEquivalent⟩ :=
            hcurrentEquivalent.exists_subtermAtDepth step.subterm_at
          have hnextSourceGround : nestedSource.Ground g.ranks :=
            hcurrentSourceGround.subtermAtDepth hnestedSource
          have hnextEquivalent :
              next.term.UnfoldingEquivalent nestedSource :=
            step.target_matches.trans hsubtermEquivalent
          have hstemPositive : 0 < stem.length :=
            List.length_pos_iff.mpr step.word_nonempty
          have hnextRemaining :
              edge.length - next.offset < remaining := by
            change
              edge.length - (current.offset + stem.length) < remaining
            rw [← hremaining]
            omega
          obtain ⟨descent, finalSource, hfinalDescendant,
              hfinalGround, labels, reached, hlength,
              hfinalRun, hreached⟩ :=
            ih (edge.length - next.offset) hnextRemaining
              next nestedSource hnextSourceGround hnextEquivalent rfl
          exact ⟨1 + descent, finalSource,
            hnestedSource.trans hfinalDescendant,
            hfinalGround, labels, reached, hlength,
            hfinalRun, hreached⟩
  exact solve (edge.length - position.offset)
    position source hsourceGround hequivalent rfl

/-- A schema-side source and its bounded symbolic residual when the retained
descendant and the short action word do not cross a variable boundary. -/
public structure BoundedPivotAuxiliarySchema
    (g : EncodedFirstOrderGrammar Action)
    (schema : RegularTerm) (arguments : List RegularTerm)
    (arity width : ℕ) (target : RegularTerm)
    (schemaDepth actionBound : ℕ) where
  descent : ℕ
  source : ℕ
  source_descendant :
    schema.DescendantAt descent source
  actions : List Action
  actions_length_le : actions.length ≤ actionBound
  auxiliary : RegularTerm
  symbolic_run :
    g.runActions? actions (schema.withRoot source) = some auxiliary
  wellFormed : auxiliary.WellFormed g.ranks arity
  hasPrefixWitness : auxiliary.HasPrefixWitness width
  unfoldingDepthAtMost :
    auxiliary.UnfoldingDepthAtMost
      (g.residualUnfoldingDepthBound actionBound schemaDepth)
  instance_matches :
    (auxiliary.instantiate arguments).UnfoldingEquivalent target

/-- The retained descendant itself has crossed a schema variable.  The
factorization records the exact occurrence/remainder split, the selected
active argument, and the bounded concrete run from the final descendant. -/
public structure BoundedPivotDescendantVariableBoundary
    (g : EncodedFirstOrderGrammar Action)
    (schema : RegularTerm) (arguments : List RegularTerm)
    (width : ℕ) (target : RegularTerm) (actionBound : ℕ) where
  descent : ℕ
  finalIndex : ℕ
  occurrence : ℕ
  remaining : ℕ
  boundarySource : ℕ
  index : ℕ
  descent_eq : descent = occurrence + remaining
  boundary_descendant :
    schema.DescendantAt occurrence boundarySource
  boundary_node :
    schema.nodeAt? boundarySource = some (.inl index)
  index_lt : index < width
  argument : RegularTerm
  argument_at : arguments[index]? = some argument
  boundary_instance_matches :
    ((schema.withRoot boundarySource).instantiate arguments)
      |>.UnfoldingEquivalent argument
  instance_remainder :
    ((schema.withRoot boundarySource).instantiate arguments)
      |>.DescendantAt remaining finalIndex
  actions : List Action
  actions_length_le : actions.length ≤ actionBound
  reached : RegularTerm
  concrete_run :
    g.runActions? actions
      ((schema.instantiate arguments).withRoot finalIndex) =
        some reached
  target_matches : target.UnfoldingEquivalent reached

/-- The retained descendant remains on the schema side, but a proper prefix
of the bounded action word reaches an active variable.  Both halves of the
action word and the corresponding concrete runs are retained exactly. -/
public structure BoundedPivotActionVariableBoundary
    (g : EncodedFirstOrderGrammar Action)
    (schema : RegularTerm) (arguments : List RegularTerm)
    (width : ℕ) (target : RegularTerm) (actionBound : ℕ) where
  descent : ℕ
  source : ℕ
  source_descendant :
    schema.DescendantAt descent source
  actions : List Action
  actions_length_le : actions.length ≤ actionBound
  stem : List Action
  suffix : List Action
  actions_eq : actions = stem ++ suffix
  suffix_nonempty : suffix ≠ []
  residual : RegularTerm
  index : ℕ
  symbolic_prefix_run :
    g.runActions? stem (schema.withRoot source) = some residual
  residual_matches_variable :
    residual.UnfoldingEquivalent (RegularTerm.variableTerm index)
  index_lt : index < width
  argument : RegularTerm
  argument_at : arguments[index]? = some argument
  concreteBoundary : RegularTerm
  concrete_prefix_run :
    g.runActions? stem
      ((schema.withRoot source).instantiate arguments) =
        some concreteBoundary
  concreteBoundary_matches_argument :
    concreteBoundary.UnfoldingEquivalent argument
  reached : RegularTerm
  concrete_suffix_run :
    g.runActions? suffix concreteBoundary = some reached
  target_matches : target.UnfoldingEquivalent reached

/-- Factor one bounded run from an exact descendant of a finite-depth schema
instance.  Either it reflects to a uniformly depth-bounded auxiliary schema,
the descendant path has already entered an active argument, or an exact
proper action prefix reaches an active variable. -/
public theorem boundedPivotAuxiliary_or_variableBoundary
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {arity width schemaDepth actionBound : ℕ}
    {target : RegularTerm}
    (hschema : schema.WellFormed g.ranks arity)
    (hschemaWitness : schema.HasPrefixWitness width)
    (hschemaDepth :
      schema.UnfoldingDepthAtMost schemaDepth)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hargumentsLength : arguments.length = arity)
    (hwidth : width ≤ arguments.length)
    (hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks)
    {descent finalIndex : ℕ}
    (hdescendant :
      (schema.instantiate arguments).DescendantAt descent finalIndex)
    {labels : List (Label Action)} {reached : RegularTerm}
    (hlength : labels.length ≤ actionBound)
    (hrun :
      g.run? labels
        ((schema.instantiate arguments).withRoot finalIndex) =
          some reached)
    (htarget : target.UnfoldingEquivalent reached) :
    Nonempty (BoundedPivotAuxiliarySchema
        g schema arguments arity width target schemaDepth actionBound) ∨
      Nonempty (BoundedPivotDescendantVariableBoundary
        g schema arguments width target actionBound) ∨
      Nonempty (BoundedPivotActionVariableBoundary
        g schema arguments width target actionBound) := by
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hschemaClosed : schema.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed hschema
  have hinstanceGround :
      (schema.instantiate arguments).Ground g.ranks := by
    apply RegularTerm.instantiate_ground
    · simpa [hargumentsLength] using hschema
    · exact hargumentsGround
  have hfinalGround :
      ((schema.instantiate arguments).withRoot finalIndex)
        |>.Ground g.ranks :=
    hinstanceGround.withRoot_descendant hdescendant
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  obtain ⟨actions, hlabels⟩ :=
    hgroundSteps.exists_actions_of_ground_run hfinalGround hrun
  have hactionsLength : actions.length ≤ actionBound := by
    simpa [hlabels] using hlength
  have hrunActions :
      g.runActions? actions
        ((schema.instantiate arguments).withRoot finalIndex) =
          some reached := by
    simpa [runActions?, hlabels] using hrun
  obtain ⟨support, hsupport⟩ := hschemaWitness
  rcases RegularTerm.instantiate_descendant_factor_variable_or_schema
      hschemaClosed hdescendant with hvariable | hschemaSide
  · obtain ⟨occurrence, remaining, boundarySource, x,
        hdescent, hboundary, hboundaryNode, hremainder⟩ :=
      hvariable
    have hx : x < width :=
      hsupport.variable_lt_of_descendant
        hboundary hboundaryNode
    have hxArguments : x < arguments.length :=
      hx.trans_le hwidth
    let argument := arguments[x]
    have hargument :
        arguments[x]? = some argument :=
      List.getElem?_eq_getElem hxArguments
    have hboundaryRootNode :
        (schema.withRoot boundarySource).nodeAt?
            (schema.withRoot boundarySource).root =
          some (.inl x) := by
      simpa [RegularTerm.withRoot, RegularTerm.nodeAt?,
        RegularTerm.root, RegularTerm.nodes] using hboundaryNode
    have hboundaryArgument :
        ((schema.withRoot boundarySource).instantiate arguments)
          |>.UnfoldingEquivalent argument :=
      RegularTerm.instantiate_unfoldingEquivalent_argument
        hboundaryRootNode hargument
        (hargumentsClosed argument
          (List.mem_of_getElem? hargument))
    have hremainder' :
        ((schema.withRoot boundarySource).instantiate arguments)
          |>.DescendantAt remaining finalIndex := by
      simpa only [RegularTerm.instantiate_withRoot] using hremainder
    exact Or.inr (Or.inl ⟨
      { descent := descent
        finalIndex := finalIndex
        occurrence := occurrence
        remaining := remaining
        boundarySource := boundarySource
        index := x
        descent_eq := hdescent
        boundary_descendant := hboundary
        boundary_node := hboundaryNode
        index_lt := hx
        argument := argument
        argument_at := hargument
        boundary_instance_matches := hboundaryArgument
        instance_remainder := hremainder'
        actions := actions
        actions_length_le := hactionsLength
        reached := reached
        concrete_run := hrunActions
        target_matches := htarget }⟩)
  · obtain ⟨source, hsourceDescendant, hfinalIndex⟩ :=
      hschemaSide
    have hsourceMem : source ∈ support :=
      hsupport.node_mem_of_descendant hsourceDescendant
    have hsourceWellFormed :
        (schema.withRoot source).WellFormed g.ranks arity :=
      hschema.withRoot (hsupport.node_lt hsourceMem)
    have hsourceWitness :
        (schema.withRoot source).HasPrefixWitness width :=
      ⟨support, hsupport.withRoot hsourceMem⟩
    have hsourceDepth :
        (schema.withRoot source).UnfoldingDepthAtMost
          (schemaDepth - descent) :=
      hschemaDepth.withRoot_of_descendant hsourceDescendant
    have hsourceEq :
        (schema.instantiate arguments).withRoot finalIndex =
          (schema.withRoot source).instantiate arguments := by
      rw [hfinalIndex]
      exact schema.instantiate_withRoot arguments source
    have hconcreteRun :
        g.runActions? actions
            ((schema.withRoot source).instantiate arguments) =
          some reached := by
      simpa [hsourceEq] using hrunActions
    by_cases hnoVariable :
        g.NoVariableBefore (schema.withRoot source) actions
    · obtain ⟨auxiliary, hsymbolicRun, hauxiliaryInstance⟩ :=
        g.runActions?_reflects_instantiation_of_noVariableBefore
          hg actions ⟨arity, hsourceWellFormed⟩
          hargumentsClosed hconcreteRun hnoVariable
      have hauxiliaryWellFormed :
          auxiliary.WellFormed g.ranks arity :=
        g.runActions?_preserves_wellFormed_padded
          hg hpadding actions hsourceWellFormed hsymbolicRun
      have hauxiliaryWitness :
          auxiliary.HasPrefixWitness width :=
        hsourceWitness.runActions
          hg hpadding hsourceWellFormed hsymbolicRun
      have hauxiliaryDepthExact :
          auxiliary.UnfoldingDepthAtMost
            (g.residualUnfoldingDepthBound
              actions.length (schemaDepth - descent)) :=
        g.runActions?_preserves_unfoldingDepthAtMost
          hg ⟨arity, hsourceWellFormed⟩
          hsourceDepth hsymbolicRun
      have hdepthLe :
          g.residualUnfoldingDepthBound
              actions.length (schemaDepth - descent) ≤
            g.residualUnfoldingDepthBound
              actionBound schemaDepth := by
        rw [residualUnfoldingDepthBound_eq,
          residualUnfoldingDepthBound_eq]
        exact Nat.add_le_add
          (Nat.mul_le_mul_right g.rhsNodeBound hactionsLength)
          (Nat.sub_le schemaDepth descent)
      exact Or.inl ⟨
        { descent := descent
          source := source
          source_descendant := hsourceDescendant
          actions := actions
          actions_length_le := hactionsLength
          auxiliary := auxiliary
          symbolic_run := hsymbolicRun
          wellFormed := hauxiliaryWellFormed
          hasPrefixWitness := hauxiliaryWitness
          unfoldingDepthAtMost :=
            hauxiliaryDepthExact.mono hdepthLe
          instance_matches :=
            hauxiliaryInstance.trans htarget.symm }⟩
    · unfold NoVariableBefore at hnoVariable
      push_neg at hnoVariable
      obtain ⟨stem, suffix, hactions, hsuffix,
          residual, x, hstemRun, hresidualVariable⟩ :=
        hnoVariable
      have hresidualWitness :
          residual.HasPrefixWitness width :=
        hsourceWitness.runActions
          hg hpadding hsourceWellFormed hstemRun
      have hresidualRoot :
          residual.nodeAt? residual.root = some (.inl x) := by
        have hroot :
            residual.rootNode? = some (.inl x) :=
          rootNode?_variable_of_unfoldingEquivalent
            hresidualVariable.symm
            (RegularTerm.variableTerm_rootNode? x)
        simpa [RegularTerm.rootNode?] using hroot
      obtain ⟨residualSupport, hresidualSupport⟩ :=
        hresidualWitness
      have hx : x < width :=
        hresidualSupport.variable_lt_of_descendant
          (.root) hresidualRoot
      have hxArguments : x < arguments.length :=
        hx.trans_le hwidth
      let argument := arguments[x]
      have hargument :
          arguments[x]? = some argument :=
        List.getElem?_eq_getElem hxArguments
      obtain ⟨concreteBoundary, hconcretePrefix,
          hresidualConcrete⟩ :=
        g.runActions?_instantiate hg stem hsourceWellFormed
          hargumentsClosed hstemRun
      have hresidualArgument :
          (residual.instantiate arguments).UnfoldingEquivalent
            argument :=
        RegularTerm.instantiate_unfoldingEquivalent_argument
          hresidualRoot hargument
          (hargumentsClosed argument
            (List.mem_of_getElem? hargument))
      have hconcreteArgument :
          concreteBoundary.UnfoldingEquivalent argument :=
        hresidualConcrete.symm.trans hresidualArgument
      have hsuffixRun :
          g.runActions? suffix concreteBoundary = some reached := by
        have hsplit := hconcreteRun
        rw [hactions] at hsplit
        unfold runActions? at hsplit
        rw [List.map_append, g.run?_append] at hsplit
        have hprefix :
            g.run? (stem.map Sum.inl)
                ((schema.withRoot source).instantiate arguments) =
              some concreteBoundary := by
          simpa [runActions?] using hconcretePrefix
        rw [hprefix] at hsplit
        simpa [runActions?] using hsplit
      exact Or.inr (Or.inr ⟨
        { descent := descent
          source := source
          source_descendant := hsourceDescendant
          actions := actions
          actions_length_le := hactionsLength
          stem := stem
          suffix := suffix
          actions_eq := hactions
          suffix_nonempty := hsuffix
          residual := residual
          index := x
          symbolic_prefix_run := hstemRun
          residual_matches_variable := hresidualVariable
          index_lt := hx
          argument := argument
          argument_at := hargument
          concreteBoundary := concreteBoundary
          concrete_prefix_run := hconcretePrefix
          concreteBoundary_matches_argument := hconcreteArgument
          reached := reached
          concrete_suffix_run := hsuffixRun
          target_matches := htarget }⟩)

/-- Concrete structured-pivot form of the schema factorization.  Starting
from any edge position presented by one fixed finite-depth schema instance,
the next pivot has a uniformly bounded auxiliary schema unless the exact
descendant/action trace exposes an active variable boundary. -/
public theorem edgePosition_boundedPivotAuxiliary_or_variableBoundary
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (hbound : 0 < bound)
    (j : ℕ)
    (position : trajectory.EdgePosition j)
    {schema : RegularTerm} {arguments : List RegularTerm}
    {arity width schemaDepth : ℕ}
    (hschema : schema.WellFormed g.ranks arity)
    (hschemaWitness : schema.HasPrefixWitness width)
    (hschemaDepth :
      schema.UnfoldingDepthAtMost schemaDepth)
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hargumentsLength : arguments.length = arity)
    (hwidth : width ≤ arguments.length)
    (hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks)
    (hequivalent :
      position.term.UnfoldingEquivalent
        (schema.instantiate arguments)) :
    Nonempty (BoundedPivotAuxiliarySchema
        g schema arguments arity width
        (trajectory.toPivotTrajectory.representatives (j + 1))
        schemaDepth (g.structuredPivotM2Bound bound)) ∨
      Nonempty (BoundedPivotDescendantVariableBoundary
        g schema arguments width
        (trajectory.toPivotTrajectory.representatives (j + 1))
        (g.structuredPivotM2Bound bound)) ∨
      Nonempty (BoundedPivotActionVariableBoundary
        g schema arguments width
        (trajectory.toPivotTrajectory.representatives (j + 1))
        (g.structuredPivotM2Bound bound)) := by
  have hinstanceGround :
      (schema.instantiate arguments).Ground g.ranks := by
    apply RegularTerm.instantiate_ground
    · simpa [hargumentsLength] using hschema
    · exact hargumentsGround
  obtain ⟨descent, finalSource, hfinalSource,
      _hfinalGround, labels, reached,
      hlength, hrun, htarget⟩ :=
    edgePosition_exists_boundedPivot_of_descendant trajectory
      hbound j position (schema.instantiate arguments)
      hinstanceGround hequivalent
  obtain ⟨finalIndex, hdescendant, rfl⟩ :=
    hfinalSource
  exact boundedPivotAuxiliary_or_variableBoundary
    hg hschema hschemaWitness hschemaDepth hpadding
    hargumentsLength hwidth hargumentsGround
    hdescendant hlength hrun htarget

end StructuredPivotChain

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
