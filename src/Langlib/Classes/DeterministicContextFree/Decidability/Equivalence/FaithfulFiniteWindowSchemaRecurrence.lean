module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FaithfulSchemaArguments
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteSchemaCompaction
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailArgumentProtection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotM2Window
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaSinkingBoundaryExclusion

@[expose]
public section

/-!
# Faithful finite-window schema recurrence

The quantitative step in Proposition 49 follows one exact pivot edge through
a finite open schema.  At every current edge position, the `M₂` dichotomy
either says that the remaining edge is short, or supplies a short sinking
prefix.  In the latter case the sinking prefix descends to an immediate
schema child.  Because the common argument tuple is unfolding-faithful, the
symbolic residual reached by the same prefix is the same open child up to
unfolding equivalence.  Thus each sinking branch decreases semantic schema
depth, while the eventual short branch increases it by at most one
`B-Inc(M₂)` term.
-/

namespace DCFEquivalence

namespace RegularTerm

/-- Every unfolding descendant of a prefix-witnessed root belongs to the
chosen finite support. -/
public theorem PrefixWitness.node_mem_support
    {term : RegularTerm} {width : ℕ} {support : List ℕ}
    (hwitness : term.PrefixWitness width support)
    {depth index : ℕ} (hindex : term.DescendantAt depth index) :
    index ∈ support := by
  induction hindex with
  | root => exact hwitness.1
  | @child depth parent X children child hparent hnode hchild ih =>
      rcases hwitness.2 parent ih with hvariable | happlication
      · obtain ⟨x, hparentVariable, _hx⟩ := hvariable
        rw [hnode] at hparentVariable
        simp at hparentVariable
      · obtain ⟨Y, parentChildren, hparentNode,
          hchildrenSupport⟩ := happlication
        have happlications :
            (Y, parentChildren) = (X, children) :=
          Sum.inr.inj
            (Option.some.inj (hparentNode.symm.trans hnode))
        have hchildren :
            parentChildren = children :=
          congrArg Prod.snd happlications
        subst parentChildren
        exact hchildrenSupport child hchild

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The exact operational finite-window premise needed by the schema
recurrence.  It is intentionally independent of the structured-pivot
implementation: at every position of one fixed exact run, either the
remaining suffix is short or a short prefix sinks. -/
@[expose] public def BoundedReachOrSinkAlong
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (actions : List Action)
    (window : ℕ) : Prop :=
  ∀ consumed remaining current,
    actions = consumed ++ remaining →
    g.runActions? consumed source = some current →
    remaining.length ≤ window ∨
      ∃ sinking rest,
        remaining = sinking ++ rest ∧
          sinking.length ≤ window ∧
          g.SinksBy current (sinking.map Sum.inl)

namespace BoundedReachOrSinkAlong

/-- Enlarging the operational window preserves the reach-or-sink
dichotomy. -/
public theorem mono
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {actions : List Action}
    {small large : ℕ}
    (hwindow :
      g.BoundedReachOrSinkAlong source actions small)
    (hle : small ≤ large) :
    g.BoundedReachOrSinkAlong source actions large := by
  intro consumed remaining current hactions hrun
  rcases hwindow consumed remaining current hactions hrun with
    hshort | ⟨sinking, rest, hremaining, hlength, hsinks⟩
  · exact Or.inl (hshort.trans hle)
  · exact Or.inr ⟨sinking, rest, hremaining,
      hlength.trans hle, hsinks⟩

end BoundedReachOrSinkAlong

/-- The open successor produced by the finite-window recurrence.  Besides
the depth bound needed for finite compaction, it retains the same active
prefix witness and both the instantiated and open equivalences to the actual
next schema. -/
public structure FaithfulFiniteWindowSchemaSuccessor
    (g : EncodedFirstOrderGrammar Action)
    (arity width : ℕ) (arguments : List RegularTerm)
    (actualNext : RegularTerm) (depth : ℕ) where
  schema : RegularTerm
  wellFormed : schema.WellFormed g.ranks arity
  hasPrefixWitness : schema.HasPrefixWitness width
  unfoldingDepthAtMost : schema.UnfoldingDepthAtMost depth
  instance_equivalent :
    (schema.instantiate arguments).UnfoldingEquivalent
      (actualNext.instantiate arguments)
  equivalent_actual : schema.UnfoldingEquivalent actualNext

namespace FaithfulFiniteWindowSchemaSuccessor

/-- Enlarge only the advertised semantic-depth bound. -/
public def mono
    {g : EncodedFirstOrderGrammar Action}
    {arity width : ℕ} {arguments : List RegularTerm}
    {actualNext : RegularTerm} {small large : ℕ}
    (successor : FaithfulFiniteWindowSchemaSuccessor
      g arity width arguments actualNext small)
    (hle : small ≤ large) :
    FaithfulFiniteWindowSchemaSuccessor
      g arity width arguments actualNext large :=
  { successor with
    unfoldingDepthAtMost :=
      RegularTerm.UnfoldingDepthAtMost.mono
        successor.unfoldingDepthAtMost hle }

end FaithfulFiniteWindowSchemaSuccessor

omit [DecidableEq Action] in
/-- The semantic run-depth recurrence is monotone in its source-depth
argument. -/
public theorem residualUnfoldingDepthBound_mono_initial'
    (g : EncodedFirstOrderGrammar Action) (steps : ℕ)
    {initial initial' : ℕ} (hinitial : initial ≤ initial') :
    g.residualUnfoldingDepthBound steps initial ≤
      g.residualUnfoldingDepthBound steps initial' := by
  induction steps generalizing initial initial' with
  | zero => exact hinitial
  | succ steps ih =>
      simp only [residualUnfoldingDepthBound]
      exact ih (Nat.add_le_add_left hinitial g.rhsNodeBound)

omit [DecidableEq Action] in
/-- The semantic run-depth recurrence is monotone in the run length. -/
public theorem residualUnfoldingDepthBound_mono_steps'
    (g : EncodedFirstOrderGrammar Action)
    {steps steps' initial : ℕ} (hsteps : steps ≤ steps') :
    g.residualUnfoldingDepthBound steps initial ≤
      g.residualUnfoldingDepthBound steps' initial := by
  rw [residualUnfoldingDepthBound_eq,
    residualUnfoldingDepthBound_eq]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right g.rhsNodeBound hsteps) initial

/-- Proper-prefix variable exclusion restricts to every prefix of the
protected action word. -/
public theorem NoVariableBefore.of_prefix
    {g : EncodedFirstOrderGrammar Action}
    {schema : RegularTerm}
    {stemPrefix suffix : List Action}
    (hnoVariable :
      g.NoVariableBefore schema (stemPrefix ++ suffix)) :
    g.NoVariableBefore schema stemPrefix := by
  intro stem remainder hword hremainder target x htarget hvariable
  apply hnoVariable stem (remainder ++ suffix)
  · rw [hword, List.append_assoc]
  · exact (List.append_ne_nil_of_left_ne_nil hremainder) suffix
  · exact htarget
  · exact hvariable

/-- Factoring a symbolic run also factors the proper-prefix variable
exclusion needed by the recursive suffix. -/
public theorem NoVariableBefore.of_run_prefix
    {g : EncodedFirstOrderGrammar Action}
    {schema residual : RegularTerm}
    {stemPrefix suffix : List Action}
    (hnoVariable : g.NoVariableBefore schema (stemPrefix ++ suffix))
    (hrun : g.runActions? stemPrefix schema = some residual) :
    g.NoVariableBefore residual suffix := by
  intro stem remainder hword hremainder target x htarget hvariable
  apply hnoVariable (stemPrefix ++ stem) remainder
  · rw [hword, List.append_assoc]
  · exact hremainder
  · rw [runActions?, List.map_append, g.run?_append]
    rw [← runActions?, hrun]
    simpa [runActions?] using htarget
  · exact hvariable

/-- The short branch of the finite-window dichotomy: a bounded concrete run
reflects to a bounded open residual, and faithfulness identifies that
residual with the actual next schema. -/
public theorem
    exists_faithfulFiniteWindowSchemaSuccessor_of_boundedRun
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity width sourceDepth window : ℕ}
    {arguments : List RegularTerm}
    {current actualNext source target : RegularTerm}
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hfaithful : g.UnfoldingFaithfulArguments arity arguments)
    (hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks)
    (hcurrentWellFormed :
      current.WellFormed g.ranks arity)
    (hcurrentWitness : current.HasPrefixWitness width)
    (hcurrentDepth :
      current.UnfoldingDepthAtMost sourceDepth)
    (hactualWellFormed :
      actualNext.WellFormed g.ranks arity)
    (hsourceGround : source.Ground g.ranks)
    (hsourceCurrent :
      source.UnfoldingEquivalent
        (current.instantiate arguments))
    (htargetActual :
      target.UnfoldingEquivalent
        (actualNext.instantiate arguments))
    {actions : List Action}
    (hactionsLength : actions.length ≤ window)
    (hrun : g.runActions? actions source = some target)
    (hnoVariable : g.NoVariableBefore current actions) :
    Nonempty (FaithfulFiniteWindowSchemaSuccessor
      g arity width arguments actualNext
        (g.residualUnfoldingDepthBound window sourceDepth)) := by
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hcurrentInstanceGround :
      (current.instantiate arguments).Ground g.ranks := by
    apply RegularTerm.instantiate_ground
    · rw [hfaithful.1]
      exact hcurrentWellFormed
    · exact hargumentsGround
  obtain ⟨instanceTarget, hinstanceRun,
      hinstanceTarget⟩ :=
    exists_runActions_of_unfoldingEquivalent
      hg hsourceCurrent.symm
      (RegularTerm.referenceClosed_of_ground
        hcurrentInstanceGround)
      (RegularTerm.referenceClosed_of_ground hsourceGround)
      hrun
  obtain ⟨auxiliary, hauxiliaryRun,
      hauxiliaryInstance⟩ :=
    g.runActions?_reflects_instantiation_of_noVariableBefore
      hg actions ⟨arity, hcurrentWellFormed⟩
      hargumentsClosed hinstanceRun hnoVariable
  have hauxiliaryWellFormed :
      auxiliary.WellFormed g.ranks arity :=
    g.runActions?_preserves_wellFormed_padded
      hg hpadding actions hcurrentWellFormed hauxiliaryRun
  have hauxiliaryWitness :
      auxiliary.HasPrefixWitness width :=
    hcurrentWitness.runActions
      hg hpadding hcurrentWellFormed hauxiliaryRun
  have hauxiliaryDepth :
      auxiliary.UnfoldingDepthAtMost
        (g.residualUnfoldingDepthBound window sourceDepth) := by
    have hlocal : auxiliary.UnfoldingDepthAtMost
        (g.residualUnfoldingDepthBound
          actions.length sourceDepth) :=
      g.runActions?_preserves_unfoldingDepthAtMost
        hg ⟨arity, hcurrentWellFormed⟩
        hcurrentDepth hauxiliaryRun
    intro depth index hdescendant
    exact (hlocal hdescendant).trans
      (g.residualUnfoldingDepthBound_mono_steps'
        hactionsLength)
  have hauxiliaryActualInstance :
      (auxiliary.instantiate arguments).UnfoldingEquivalent
        (actualNext.instantiate arguments) :=
    hauxiliaryInstance.trans
      (hinstanceTarget.trans htargetActual)
  have hauxiliaryActual :
      auxiliary.UnfoldingEquivalent actualNext :=
    hfaithful.reflect hauxiliaryWellFormed
      hactualWellFormed hauxiliaryActualInstance
  exact ⟨
    { schema := auxiliary
      wellFormed := hauxiliaryWellFormed
      hasPrefixWitness := hauxiliaryWitness
      unfoldingDepthAtMost := hauxiliaryDepth
      instance_equivalent := hauxiliaryActualInstance
      equivalent_actual := hauxiliaryActual }⟩

/-- One schema-side descent selected by a sinking prefix.  The resulting
symbolic residual presents the exact concrete edge state after a nonempty
prefix, has one less unit of semantic unfolding depth available, and carries
the variable-exclusion invariant for the unconsumed suffix. -/
public structure FaithfulFiniteWindowSchemaDescent
    (g : EncodedFirstOrderGrammar Action)
    (arity width : ℕ) (arguments : List RegularTerm)
    (source current : RegularTerm) (sourceDepth : ℕ)
    (sinkingActions restActions : List Action) where
  stemActions : List Action
  sinkRemainderActions : List Action
  sinking_eq :
    sinkingActions = stemActions ++ sinkRemainderActions
  stem_nonempty : stemActions ≠ []
  sourceTarget : RegularTerm
  schema : RegularTerm
  child : ℕ
  child_descendant : current.DescendantAt 1 child
  source_run :
    g.runActions? stemActions source = some sourceTarget
  symbolic_run :
    g.runActions? stemActions current = some schema
  source_matches :
    sourceTarget.UnfoldingEquivalent
      (schema.instantiate arguments)
  wellFormed : schema.WellFormed g.ranks arity
  hasPrefixWitness : schema.HasPrefixWitness width
  unfoldingDepthAtMost :
    schema.UnfoldingDepthAtMost (sourceDepth - 1)
  sourceTarget_ground : sourceTarget.Ground g.ranks
  noVariableBefore :
    g.NoVariableBefore schema
      (sinkRemainderActions ++ restActions)

/-- The sinking branch of the finite-window dichotomy strictly descends the
open schema.  Faithfulness is used at the crucial point: the symbolic
residual and the selected child have equivalent instances, hence they are
equivalent open schemas and share the child's smaller unfolding-depth
bound. -/
public theorem exists_faithfulFiniteWindowSchemaDescent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity width sourceDepth : ℕ}
    {arguments : List RegularTerm}
    {current source : RegularTerm}
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hfaithful : g.UnfoldingFaithfulArguments arity arguments)
    (hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks)
    (hcurrentWellFormed :
      current.WellFormed g.ranks arity)
    (hcurrentWitness : current.HasPrefixWitness width)
    (hcurrentDepth :
      current.UnfoldingDepthAtMost sourceDepth)
    (hsourceGround : source.Ground g.ranks)
    (hsourceCurrent :
      source.UnfoldingEquivalent
        (current.instantiate arguments))
    {sinkingActions restActions : List Action}
    (hnoVariable :
      g.NoVariableBefore current
        (sinkingActions ++ restActions))
    (hsinks :
      g.SinksBy source (sinkingActions.map Sum.inl)) :
    Nonempty (FaithfulFiniteWindowSchemaDescent
      g arity width arguments source current sourceDepth
      sinkingActions restActions) := by
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hcurrentClosed :
      current.ReferenceClosed :=
    RegularTerm.referenceClosed_of_wellFormed
      hcurrentWellFormed
  have hcurrentInstanceGround :
      (current.instantiate arguments).Ground g.ranks := by
    apply RegularTerm.instantiate_ground
    · rw [hfaithful.1]
      exact hcurrentWellFormed
    · exact hargumentsGround
  obtain ⟨support, hsupport⟩ := hcurrentWitness
  obtain ⟨stemActions, sinkRemainderActions,
      sourceTarget, canonicalTarget, child,
      hsinking, hstemNonempty, hchild,
      hsourceRun, hcanonicalRun,
      hcanonicalSource, _hsourceChild,
      hcanonicalChild⟩ :=
    hsinks.exists_schemaChild_of_noVariableBefore
      hg hsupport hcurrentClosed
      hcurrentInstanceGround hsourceGround
      (RegularTerm.unfoldingEquivalent_refl _)
      hsourceCurrent hnoVariable
  let tailActions := sinkRemainderActions ++ restActions
  have hfullActions :
      sinkingActions ++ restActions =
        stemActions ++ tailActions := by
    simp [tailActions, hsinking, List.append_assoc]
  have hnoStem : g.NoVariableBefore current stemActions := by
    apply NoVariableBefore.of_prefix
      (suffix := tailActions)
    rw [← hfullActions]
    exact hnoVariable
  obtain ⟨residual, hsymbolicRun,
      hresidualCanonical⟩ :=
    g.runActions?_reflects_instantiation_of_noVariableBefore
      hg stemActions ⟨arity, hcurrentWellFormed⟩
      hargumentsClosed hcanonicalRun hnoStem
  have hresidualWellFormed :
      residual.WellFormed g.ranks arity :=
    g.runActions?_preserves_wellFormed_padded
      hg hpadding stemActions hcurrentWellFormed hsymbolicRun
  have hresidualWitness :
      residual.HasPrefixWitness width :=
    (show current.HasPrefixWitness width from
      ⟨support, hsupport⟩).runActions
      hg hpadding hcurrentWellFormed hsymbolicRun
  have hchildSupport : child ∈ support :=
    hsupport.node_mem_support hchild
  have hchildWellFormed :
      (current.withRoot child).WellFormed g.ranks arity :=
    RegularTerm.WellFormed.withRoot hcurrentWellFormed
      (hsupport.node_lt hchildSupport)
  have hresidualChildInstance :
      (residual.instantiate arguments).UnfoldingEquivalent
        ((current.withRoot child).instantiate arguments) :=
    hresidualCanonical.trans hcanonicalChild
  have hresidualChild :
      residual.UnfoldingEquivalent
        (current.withRoot child) :=
    hfaithful.reflect hresidualWellFormed
      hchildWellFormed hresidualChildInstance
  have hchildDepth :
      (current.withRoot child).UnfoldingDepthAtMost
        (sourceDepth - 1) :=
    hcurrentDepth.withRoot_of_descendant hchild
  have hresidualDepth :
      residual.UnfoldingDepthAtMost (sourceDepth - 1) :=
    hresidualChild.symm.unfoldingDepthAtMost hchildDepth
  have hsourceMatches :
      sourceTarget.UnfoldingEquivalent
        (residual.instantiate arguments) :=
    hcanonicalSource.symm.trans hresidualCanonical.symm
  have hsourceTargetGround : sourceTarget.Ground g.ranks :=
    let hgroundSteps : g.PreservesGroundSteps :=
      preservesGroundSteps_of_wellFormed hg
    hgroundSteps.ground_of_run hsourceGround hsourceRun
  have hnoTail : g.NoVariableBefore residual tailActions := by
    apply NoVariableBefore.of_run_prefix
      (hrun := hsymbolicRun)
    rw [← hfullActions]
    exact hnoVariable
  exact ⟨
    { stemActions := stemActions
      sinkRemainderActions := sinkRemainderActions
      sinking_eq := hsinking
      stem_nonempty := hstemNonempty
      sourceTarget := sourceTarget
      schema := residual
      child := child
      child_descendant := hchild
      source_run := hsourceRun
      symbolic_run := hsymbolicRun
      source_matches := hsourceMatches
      wellFormed := hresidualWellFormed
      hasPrefixWitness := hresidualWitness
      unfoldingDepthAtMost := hresidualDepth
      sourceTarget_ground := hsourceTargetGround
      noVariableBefore := by
        simpa [tailActions] using hnoTail }⟩

/-- The finite-window recurrence from an arbitrary position of the fixed
exact run.  Every sinking branch consumes a nonempty action prefix and
strictly descends the current finite schema.  Hence after at most
`sourceDepth` sinking branches the reach-or-sink dichotomy must take its
bounded-reach branch. -/
public theorem
    exists_faithfulFiniteWindowSchemaSuccessor_from_position
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity width sourceDepth window : ℕ}
    {arguments : List RegularTerm}
    {actualNext origin currentSource target current : RegularTerm}
    {actions consumed remaining : List Action}
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hfaithful : g.UnfoldingFaithfulArguments arity arguments)
    (hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks)
    (hactualWellFormed :
      actualNext.WellFormed g.ranks arity)
    (htargetActual :
      target.UnfoldingEquivalent
        (actualNext.instantiate arguments))
    (hcurrentWellFormed :
      current.WellFormed g.ranks arity)
    (hcurrentWitness : current.HasPrefixWitness width)
    (hcurrentDepth :
      current.UnfoldingDepthAtMost sourceDepth)
    (hcurrentSourceGround : currentSource.Ground g.ranks)
    (hcurrentSource :
      currentSource.UnfoldingEquivalent
        (current.instantiate arguments))
    (hwindow :
      g.BoundedReachOrSinkAlong origin actions window)
    (hactions :
      actions = consumed ++ remaining)
    (hprefixRun :
      g.runActions? consumed origin = some currentSource)
    (hremainingRun :
      g.runActions? remaining currentSource = some target)
    (hnoVariable :
      g.NoVariableBefore current remaining) :
    Nonempty (FaithfulFiniteWindowSchemaSuccessor
      g arity width arguments actualNext
        (g.residualUnfoldingDepthBound window sourceDepth)) := by
  induction sourceDepth generalizing
      current currentSource consumed remaining with
  | zero =>
      rcases hwindow consumed remaining currentSource
          hactions hprefixRun with
        hshort | ⟨sinkingActions, restActions,
          hremaining, _hsinkingLength, hsinks⟩
      · exact
          exists_faithfulFiniteWindowSchemaSuccessor_of_boundedRun
            hg hpadding hfaithful hargumentsGround
            hcurrentWellFormed hcurrentWitness hcurrentDepth
            hactualWellFormed hcurrentSourceGround
            hcurrentSource htargetActual hshort
            hremainingRun hnoVariable
      · have hnoSinking :
            g.NoVariableBefore current
              (sinkingActions ++ restActions) := by
          rw [← hremaining]
          exact hnoVariable
        obtain ⟨descent⟩ :=
          exists_faithfulFiniteWindowSchemaDescent
            hg hpadding hfaithful hargumentsGround
            hcurrentWellFormed hcurrentWitness hcurrentDepth
            hcurrentSourceGround hcurrentSource
            hnoSinking hsinks
        have himpossible : 1 ≤ 0 :=
          hcurrentDepth descent.child_descendant
        omega
  | succ sourceDepth ih =>
      rcases hwindow consumed remaining currentSource
          hactions hprefixRun with
        hshort | ⟨sinkingActions, restActions,
          hremaining, _hsinkingLength, hsinks⟩
      · exact
          exists_faithfulFiniteWindowSchemaSuccessor_of_boundedRun
            hg hpadding hfaithful hargumentsGround
            hcurrentWellFormed hcurrentWitness hcurrentDepth
            hactualWellFormed hcurrentSourceGround
            hcurrentSource htargetActual hshort
            hremainingRun hnoVariable
      · have hnoSinking :
            g.NoVariableBefore current
              (sinkingActions ++ restActions) := by
          rw [← hremaining]
          exact hnoVariable
        obtain ⟨descent⟩ :=
          exists_faithfulFiniteWindowSchemaDescent
            hg hpadding hfaithful hargumentsGround
            hcurrentWellFormed hcurrentWitness hcurrentDepth
            hcurrentSourceGround hcurrentSource
            hnoSinking hsinks
        let tailActions :=
          descent.sinkRemainderActions ++ restActions
        have hremainingFactor :
            remaining =
              descent.stemActions ++ tailActions := by
          calc
            remaining =
                sinkingActions ++ restActions := hremaining
            _ =
                (descent.stemActions ++
                    descent.sinkRemainderActions) ++
                  restActions := by rw [← descent.sinking_eq]
            _ =
                descent.stemActions ++ tailActions := by
              simp [tailActions, List.append_assoc]
        have hnextActions :
            actions =
              (consumed ++ descent.stemActions) ++
                tailActions := by
          calc
            actions = consumed ++ remaining := hactions
            _ =
                consumed ++
                  (descent.stemActions ++ tailActions) := by
              rw [hremainingFactor]
            _ =
                (consumed ++ descent.stemActions) ++
                  tailActions := by
              rw [List.append_assoc]
        have hnextPrefixRun :
            g.runActions?
                (consumed ++ descent.stemActions) origin =
              some descent.sourceTarget := by
          rw [runActions?, List.map_append, g.run?_append]
          rw [← runActions?, hprefixRun]
          simpa [runActions?] using descent.source_run
        have htailRun :
            g.runActions? tailActions descent.sourceTarget =
              some target := by
          rw [hremainingFactor, runActions?,
            List.map_append, g.run?_append] at hremainingRun
          rw [← runActions?, descent.source_run] at hremainingRun
          simpa [runActions?, tailActions] using hremainingRun
        have hdescentDepth :
            descent.schema.UnfoldingDepthAtMost sourceDepth := by
          intro depth index hdescendant
          have hle :=
            descent.unfoldingDepthAtMost hdescendant
          simpa using hle
        have hsuccessor :
            Nonempty (FaithfulFiniteWindowSchemaSuccessor
              g arity width arguments actualNext
                (g.residualUnfoldingDepthBound
                  window sourceDepth)) :=
          ih descent.wellFormed descent.hasPrefixWitness
            hdescentDepth descent.sourceTarget_ground
            descent.source_matches hnextActions
            hnextPrefixRun htailRun
            descent.noVariableBefore
        obtain ⟨successor⟩ := hsuccessor
        exact ⟨successor.mono
          (g.residualUnfoldingDepthBound_mono_initial'
            window (Nat.le_succ sourceDepth))⟩

/-- Starting at the beginning of an exact run gives the public
Proposition-49 finite-window successor bound. -/
public theorem exists_faithfulFiniteWindowSchemaSuccessor
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {arity width sourceDepth window : ℕ}
    {arguments : List RegularTerm}
    {current actualNext source target : RegularTerm}
    (hpadding : g.ranks.foldr max 0 ≤ arity)
    (hfaithful : g.UnfoldingFaithfulArguments arity arguments)
    (hargumentsGround :
      ∀ argument ∈ arguments, argument.Ground g.ranks)
    (hcurrentWellFormed :
      current.WellFormed g.ranks arity)
    (hcurrentWitness : current.HasPrefixWitness width)
    (hcurrentDepth :
      current.UnfoldingDepthAtMost sourceDepth)
    (hactualWellFormed :
      actualNext.WellFormed g.ranks arity)
    (hsourceGround : source.Ground g.ranks)
    (hsourceCurrent :
      source.UnfoldingEquivalent
        (current.instantiate arguments))
    (htargetActual :
      target.UnfoldingEquivalent
        (actualNext.instantiate arguments))
    {actions : List Action}
    (hrun : g.runActions? actions source = some target)
    (hwindow :
      g.BoundedReachOrSinkAlong source actions window)
    (hnoVariable : g.NoVariableBefore current actions) :
    Nonempty (FaithfulFiniteWindowSchemaSuccessor
      g arity width arguments actualNext
        (g.residualUnfoldingDepthBound window sourceDepth)) := by
  apply exists_faithfulFiniteWindowSchemaSuccessor_from_position
    hg hpadding hfaithful hargumentsGround
    hactualWellFormed htargetActual
    hcurrentWellFormed hcurrentWitness hcurrentDepth
    hsourceGround hsourceCurrent hwindow
    (consumed := []) (remaining := actions)
  · simp
  · simp [runActions?]
  · exact hrun
  · exact hnoVariable

end EncodedFirstOrderGrammar

end DCFEquivalence
