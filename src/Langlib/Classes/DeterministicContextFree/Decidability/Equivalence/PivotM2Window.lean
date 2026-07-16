module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotChain
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedRepeatPigeonhole
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailReflection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootNonSinkingReflection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedSinkingBoundary
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedRootSinking
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedRootSinkingBoundary
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotCutLocalization
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotStairAssembly
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedCoveragePigeonhole

@[expose]
public section

/-!
# Uniform sinking windows along the structured pivot path

The close/fallback policy retains more information than the simplified
`PivotEdge`: after the grammar-uniform close prefix, every complete
balancing-length window before the next pivot has no balancing opportunity
and therefore sinks.  This file rebuilds the concrete edge directly from the
retained policy so that the switched branch keeps its successor-row
reflection at intermediate path positions.

The resulting `WindowedPivotEdge` is the operational input to the global
`M₂` argument.  It leaves the existing lightweight edge API unchanged.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A shape-correct finite runtime graph admits some global variable bound.
Ground terms may retain unreachable variable nodes, so the bound is chosen
from all variable indices still present in the finite graph. -/
public theorem RegularTerm.Ground.exists_wellFormed
    {ranks : List ℕ} {term : RegularTerm}
    (hground : term.Ground ranks) :
    ∃ variableBound, term.WellFormed ranks variableBound := by
  let variableValue : RawNode → ℕ
    | .inl x => x + 1
    | .inr _ => 0
  let variableBound :=
    (term.nodes.map variableValue).foldr max 0
  refine ⟨variableBound, ?_⟩
  unfold RegularTerm.Ground at hground
  unfold RegularTerm.ShapeWellFormed
    RegularTerm.shapeWellFormedCode at hground
  unfold RegularTerm.WellFormed
    RegularTerm.wellFormedCode
  rw [Bool.and_eq_true] at hground ⊢
  refine ⟨hground.1.1, ?_⟩
  apply List.all_eq_true.mpr
  intro node hnode
  have hshape :=
    (List.all_eq_true.mp hground.1.2) node hnode
  cases node with
  | inl x =>
      have hxmem :
          x + 1 ∈ term.nodes.map variableValue :=
        List.mem_map.mpr ⟨.inl x, hnode, by
          simp [variableValue]⟩
      have hxle : x + 1 ≤ variableBound := by
        exact List.le_max_of_le hxmem (le_refl _)
      simp only [RegularTerm.nodeWellFormedCode]
      exact decide_eq_true (by omega)
  | inr application =>
      simpa [RegularTerm.nodeWellFormedCode,
        RegularTerm.nodeShapeWellFormedCode] using hshape

/-- The part of one pivot edge before the policy guarantees sinking
balancing-length windows. -/
@[expose] public def structuredPivotShortPrefixBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  bound + g.structuredPivotCloseBound bound

/-- Abstract `M₂` length for a chosen number of post-prefix sinking blocks. -/
@[expose] public def structuredPivotM2Window
    (g : EncodedFirstOrderGrammar Action)
    (bound depth : ℕ) : ℕ :=
  g.structuredPivotShortPrefixBound bound + depth * bound

/-- Grammar-uniform semantic depth of a residual produced by a prelude of at
most `short` actions over a depth-one source prefix. -/
@[expose] public def structuredPivotPreludeDepthBound
    (g : EncodedFirstOrderGrammar Action) (short : ℕ) : ℕ :=
  g.residualUnfoldingDepthBound short
    (FiniteHead.compiledDepthBound (g.ranks.foldr max 0) 1)

/-- One more sinking block than the prelude residual can contain. -/
@[expose] public def structuredPivotSinkDepth
    (g : EncodedFirstOrderGrammar Action) (short : ℕ) : ℕ :=
  g.structuredPivotPreludeDepthBound short + 1

/-- The concrete Proposition-49 `M₂` constant for structured pivot edges. -/
@[expose] public def structuredPivotM2Bound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  let short := g.structuredPivotShortPrefixBound bound
  g.structuredPivotM2Window bound (g.structuredPivotSinkDepth short)

omit [DecidableEq Action] in
/-- Closed form of the run-depth recurrence. -/
public theorem residualUnfoldingDepthBound_eq
    (g : EncodedFirstOrderGrammar Action) (steps initial : ℕ) :
    g.residualUnfoldingDepthBound steps initial =
      steps * g.rhsNodeBound + initial := by
  induction steps generalizing initial with
  | zero => simp [residualUnfoldingDepthBound]
  | succ steps ih =>
      simp [residualUnfoldingDepthBound, ih, Nat.succ_mul,
        Nat.add_assoc, Nat.add_comm]

namespace TracePath

/-- Absence of a left balancing segment makes the full left window
syntactically root-sink. -/
public theorem rootSinksLeft_of_noBalancingOpportunity
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hno : ¬path.HasLeftBalancingOpportunity bound start) :
    g.RootSinksBy (path.left start)
      (path.segmentWord start bound) := by
  by_contra hnotsinks
  apply hno
  refine ⟨path.leftBalancingSegment hinitial start bound ?_⟩
  intro initialSegment suffix hword _hsuffix hsinks
  apply hnotsinks
  rw [hword]
  exact hsinks.append suffix

/-- Absence of a right balancing segment makes the full right window
syntactically root-sink. -/
public theorem rootSinksRight_of_noBalancingOpportunity
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hno : ¬path.HasRightBalancingOpportunity bound start) :
    g.RootSinksBy (path.right start)
      (path.segmentWord start bound) := by
  by_contra hnotsinks
  apply hno
  refine ⟨path.rightBalancingSegment hinitial start bound ?_⟩
  intro initialSegment suffix hword _hsuffix hsinks
  apply hnotsinks
  rw [hword]
  exact hsinks.append suffix

/-- Dropping a prefix from an exact path segment gives the corresponding
later path segment. -/
public theorem segmentWord_drop
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start : ℕ) {skip total : ℕ} (hskip : skip ≤ total) :
    (path.segmentWord start total).drop skip =
      path.segmentWord (start + skip) (total - skip) := by
  have hsplit :=
    path.segmentWord_add start skip (total - skip)
  rw [Nat.add_sub_of_le hskip] at hsplit
  rw [hsplit, List.drop_append, path.segmentWord_length]
  simp

/-- A complete window cut from an exact path segment is again the exact
segment at the shifted path position. -/
public theorem take_drop_segmentWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start : ℕ) {skip window total : ℕ}
    (hfit : skip + window ≤ total) :
    ((path.segmentWord start total).drop skip).take window =
      path.segmentWord (start + skip) window := by
  rw [path.segmentWord_drop start (show skip ≤ total by omega)]
  exact path.take_segmentWord (start + skip) (by omega)

end TracePath

/-- Sinking is invariant under semantic equality of ground regular terms. -/
public theorem SinksBy.of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {left right : RegularTerm} {word : List (Label Action)}
    (hleft : left.Ground g.ranks)
    (hright : right.Ground g.ranks)
    (hequivalent : left.UnfoldingEquivalent right)
    (hsinks : g.SinksBy right word) :
    g.SinksBy left word := by
  obtain ⟨initialSegment, suffix, hword, hnonempty,
      rightSubterm, rightTarget, hrightSubterm,
      hrightRun, hrightTarget⟩ := hsinks
  obtain ⟨leftSubterm, hleftSubterm, hsubterms⟩ :=
    hequivalent.symm.exists_subtermAtDepth hrightSubterm
  obtain ⟨leftTarget, hleftRun, htargets⟩ :=
    exists_run_of_unfoldingEquivalent hg hequivalent
      (RegularTerm.referenceClosed_of_ground hleft)
      (RegularTerm.referenceClosed_of_ground hright)
      hrightRun
  exact ⟨initialSegment, suffix, hword, hnonempty,
    leftSubterm, leftTarget, hleftSubterm, hleftRun,
    htargets.trans (hrightTarget.trans hsubterms)⟩

/-- Repeated sinking is likewise invariant under semantic equality of ground
sources. -/
public theorem RepeatedlySinksBy.of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {left right : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hleft : left.Ground g.ranks)
    (hright : right.Ground g.ranks)
    (hequivalent : left.UnfoldingEquivalent right)
    (hsinks : g.RepeatedlySinksBy right word depth) :
    g.RepeatedlySinksBy left word depth := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  induction depth generalizing left right word with
  | zero => trivial
  | succ depth ih =>
      obtain ⟨stem, suffix, rightTarget, hword, ⟨rightStep⟩,
          hrest⟩ := hsinks
      obtain ⟨leftSubterm, hleftSubterm, hsubterms⟩ :=
        hequivalent.symm.exists_subtermAtDepth rightStep.subterm_at
      obtain ⟨leftTarget, hleftRun, htargets⟩ :=
        exists_run_of_unfoldingEquivalent hg hequivalent
          (RegularTerm.referenceClosed_of_ground hleft)
          (RegularTerm.referenceClosed_of_ground hright)
          rightStep.run
      have hleftTargetGround : leftTarget.Ground g.ranks :=
        hgroundSteps.ground_of_run hleft hleftRun
      have hrightTargetGround : rightTarget.Ground g.ranks :=
        hgroundSteps.ground_of_run hright rightStep.run
      refine ⟨stem, suffix, leftTarget, hword, ⟨
        { subterm := leftSubterm
          word_nonempty := rightStep.word_nonempty
          subterm_at := hleftSubterm
          run := hleftRun
          target_matches :=
            htargets.trans
              (rightStep.target_matches.trans hsubterms) }⟩, ?_⟩
      exact ih hleftTargetGround hrightTargetGround htargets hrest

/-- Repeated sinking selects one exact exposing prefix whose length is at
least the accumulated sinking depth. -/
public theorem RepeatedlySinksBy.exists_exposingPrefix
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsinks : g.RepeatedlySinksBy source word depth) :
    ∃ stem suffix,
      word = stem ++ suffix ∧
        depth ≤ stem.length ∧
        g.ExposesAtDepth source stem depth := by
  induction depth generalizing source word with
  | zero =>
      refine ⟨[], word, by simp, by simp, ?_⟩
      exact ⟨source, source, by simp, by simp,
        RegularTerm.unfoldingEquivalent_refl source⟩
  | succ depth ih =>
      obtain ⟨first, remainder, target, hword, ⟨step⟩,
          hrest⟩ := hsinks
      obtain ⟨second, suffix, hremainder, hlength,
          hexposes⟩ := ih hrest
      refine ⟨first ++ second, suffix, ?_, ?_, ?_⟩
      · rw [hword, hremainder, List.append_assoc]
      · have hfirst : 1 ≤ first.length :=
          List.length_pos_iff.mpr step.word_nonempty
        simp only [List.length_append]
        omega
      · simpa [Nat.add_comm] using
          (ExposesAtDepth.append_of_run step.subterm_at step.run
            step.target_matches hexposes)

/-- Any positive repeated root-sinking spine already root-sinks on its first
selected prefix. -/
public theorem RepeatedlyRootSinksBy.toRootSinksBy
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hpositive : 0 < depth)
    (hsinks : g.RepeatedlyRootSinksBy source word depth) :
    g.RootSinksBy source word := by
  cases depth with
  | zero => omega
  | succ depth =>
      cases hsinks with
      | succ hword step _rest =>
          rw [hword]
          exact step.rootSinks.append _

/-- If a concrete word does not sink from a ground term, its symbolic
execution over the depth-one prefix cannot reach a variable before the end.

Unlike `depthPrefix_noVariableBefore`, this statement does not reject a
semantic empty-word self-cycle.  The empty symbolic prefix is handled
structurally: a ground depth-one prefix has an application root, not a
variable root. -/
public theorem depthPrefix_one_noVariableBefore_of_not_sinksBy
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {term filler : RegularTerm}
    (hterm : term.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    {word : List Action}
    (hnotSinks : ¬g.SinksBy term (word.map Sum.inl)) :
    g.NoVariableBefore
      (term.depthPrefix 1).head.toRegularTerm word := by
  let decomposition := term.depthPrefix 1
  let schema := decomposition.head.toRegularTerm
  let arguments := decomposition.paddedArguments g.ranks filler
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid term 1
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hterm 1
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
      hterm hfiller 1
  have hargumentsClosed :
      ∀ argument ∈ arguments, argument.ReferenceClosed := by
    intro argument hargument
    exact RegularTerm.referenceClosed_of_ground
      (hargumentsGround argument hargument)
  have hinstanceEquivalent :
      (schema.instantiate arguments).UnfoldingEquivalent term :=
    RegularTerm.depthPrefix_compiled_unfoldingEquivalent
      hterm hfiller 1
  have hinstanceClosed :
      (schema.instantiate arguments).ReferenceClosed :=
    RegularTerm.instantiate_referenceClosed
      (RegularTerm.referenceClosed_of_wellFormed hschemaSupported.1)
      hargumentsClosed
  intro stem suffix hword hsuffix residual x
    hstemRun hresidualVariable
  have hresidualSupported :=
    hschemaSupported.residual hg hpadding hstemRun
  have hresidualRoot :
      residual.rootNode? = some (.inl x) :=
    rootNode?_variable_of_unfoldingEquivalent
      hresidualVariable.symm
      (RegularTerm.variableTerm_rootNode? x)
  by_cases hstemEmpty : stem = []
  · subst stem
    simp [runActions?] at hstemRun
    subst residual
    obtain ⟨X, children, hroot⟩ := hterm.exists_rootApplication
    let childPrefixes :=
      children.map fun child =>
        (term.withRoot child).depthPrefix 0
    have hdecomposition :
        decomposition = DepthPrefix.assemble X childPrefixes := by
      simpa [decomposition, childPrefixes] using
        RegularTerm.depthPrefix_succ_of_rootApplication hroot 0
    have hschema :
        schema =
          (FiniteHead.app X
            (DepthPrefix.collectHeads childPrefixes 0)).toRegularTerm := by
      simp [schema, hdecomposition, DepthPrefix.assemble]
    have hschemaApplication :=
      FiniteHead.toRegularTerm_app_rootApplication? X
        (DepthPrefix.collectHeads childPrefixes 0)
    have hschemaRoot :
        schema.rootNode? =
          some (.inr
            (X,
              ((List.range
                (DepthPrefix.collectHeads childPrefixes 0).length).map
                  (fun i => i + 1)).map
                ((RegularTerm.symbolTemplate X
                    (DepthPrefix.collectHeads childPrefixes 0).length)
                  |>.resolveRHSRef
                    ((DepthPrefix.collectHeads childPrefixes 0).map
                      FiniteHead.toRegularTerm)))) := by
      rw [hschema]
      exact RegularTerm.nodeAt?_root_of_rootApplication?
        hschemaApplication
    rw [hschemaRoot] at hresidualRoot
    simp at hresidualRoot
  · have hxTails : x < decomposition.tails.length :=
      hresidualSupported.variableIndex_lt_width_of_root hresidualRoot
    let tail := decomposition.tails[x]
    have htailGet : decomposition.tails[x]? = some tail :=
      List.getElem?_eq_getElem hxTails
    have hargumentGet : arguments[x]? = some tail := by
      unfold arguments DepthPrefix.paddedArguments
      rw [List.getElem?_append_left hxTails]
      exact htailGet
    have hresidualNode :
        residual.nodeAt? residual.root = some (.inl x) := by
      simpa [RegularTerm.rootNode?] using hresidualRoot
    have hresidualInstanceTail :
        (residual.instantiate arguments).UnfoldingEquivalent tail :=
      RegularTerm.instantiate_unfoldingEquivalent_argument
        hresidualNode hargumentGet
        (RegularTerm.referenceClosed_of_ground
          (hargumentsGround tail
            (List.mem_of_getElem? hargumentGet)))
    obtain ⟨instantiatedStem, hinstantiatedStemRun,
        hresidualInstantiation⟩ :=
      g.runActions?_instantiate hg stem hschemaSupported.1
        hargumentsClosed hstemRun
    obtain ⟨termStem, htermStemRun, htermStemEquivalent⟩ :=
      exists_runActions_of_unfoldingEquivalent hg
        hinstanceEquivalent.symm
        (RegularTerm.referenceClosed_of_ground hterm)
        hinstanceClosed hinstantiatedStemRun
    have htermStemTail :
        termStem.UnfoldingEquivalent tail :=
      htermStemEquivalent.trans
        (hresidualInstantiation.symm.trans hresidualInstanceTail)
    have htailSubterm :
        term.SubtermAtDepth 1 tail :=
      RegularTerm.depthPrefix_tails_subtermAtDepth
        hterm 1 tail (List.getElem_mem hxTails)
    apply hnotSinks
    refine ⟨stem.map Sum.inl, suffix.map Sum.inl, ?_, ?_, ?_⟩
    · simp [hword]
    · simpa using hstemEmpty
    · exact ⟨tail, termStem, htailSubterm,
        by simpa [runActions?] using htermStemRun,
        htermStemTail⟩

/-- A short prelude followed by more sinking blocks than its depth-one
symbolic residual can contain already makes the original source sink.

This is the formal `1 + B-Inc(short)` reflection used in the `M₂` argument. -/
public theorem sinksBy_append_of_shortPrelude_repeatedlySinks
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source intermediate : RegularTerm}
    (hsource : source.Ground g.ranks)
    (short : ℕ)
    {prelude sinkingWord : List (Label Action)}
    (hpreludeLength : prelude.length ≤ short)
    (hpreludeRun : g.run? prelude source = some intermediate)
    (hsinks :
      g.RepeatedlySinksBy intermediate sinkingWord
        (g.structuredPivotSinkDepth short)) :
    g.SinksBy source (prelude ++ sinkingWord) := by
  classical
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  obtain ⟨actions, hprelude⟩ :=
    hgroundSteps.exists_actions_of_ground_run hsource hpreludeRun
  subst prelude
  have hactionsLength : actions.length ≤ short := by
    simpa using hpreludeLength
  have hdepthPositive :
      1 ≤ g.structuredPivotSinkDepth short := by
    simp [structuredPivotSinkDepth]
  cases hactionsEmpty : actions with
  | nil =>
      subst actions
      simp at hpreludeRun
      subst intermediate
      simpa using
        (g.repeatedlySinksBy_one_iff source sinkingWord).mp
          (hsinks.mono hdepthPositive)
  | cons action actionsTail =>
      subst actions
      have hactionsNonempty : action :: actionsTail ≠ [] := by simp
      by_cases hsourceSinks :
          g.SinksBy source ((action :: actionsTail).map Sum.inl)
      · exact hsourceSinks.append sinkingWord
      · let filler := source
        let decomposition := source.depthPrefix 1
        let schema := decomposition.head.toRegularTerm
        let arguments :=
          decomposition.paddedArguments g.ranks filler
        have hvalid : decomposition.Valid :=
          RegularTerm.depthPrefix_valid source 1
        have hranked : decomposition.head.RankedBy g.ranks :=
          RegularTerm.depthPrefix_head_rankedBy hsource 1
        have hschemaSupported :
            RegularTerm.SupportedByPrefix g.ranks
              (decomposition.schemaArity g.ranks)
              decomposition.tails.length schema :=
          FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked
        have hpadding :
            g.ranks.foldr max 0 ≤
              decomposition.schemaArity g.ranks := by
          simp [DepthPrefix.schemaArity]
        have hargumentsGround :
            ∀ argument ∈ arguments, argument.Ground g.ranks :=
          RegularTerm.depthPrefix_paddedArguments_ground
            hsource hsource 1
        have hargumentsClosed :
            ∀ argument ∈ arguments, argument.ReferenceClosed := by
          intro argument hargument
          exact RegularTerm.referenceClosed_of_ground
            (hargumentsGround argument hargument)
        have hinstanceEquivalent :
            (schema.instantiate arguments).UnfoldingEquivalent source :=
          RegularTerm.depthPrefix_compiled_unfoldingEquivalent
            hsource hsource 1
        have hinstanceClosed :
            (schema.instantiate arguments).ReferenceClosed :=
          RegularTerm.instantiate_referenceClosed
            (RegularTerm.referenceClosed_of_wellFormed
              hschemaSupported.1)
            hargumentsClosed
        have hpreludeRunActions :
            g.runActions? (action :: actionsTail) source =
              some intermediate := by
          simpa only [runActions?] using hpreludeRun
        obtain ⟨instanceTarget, hinstanceRun,
            hinstanceTargetMatches⟩ :=
          exists_runActions_of_unfoldingEquivalent hg
            hinstanceEquivalent hinstanceClosed
            (RegularTerm.referenceClosed_of_ground hsource)
            hpreludeRunActions
        have hnoVariable :
            g.NoVariableBefore schema (action :: actionsTail) := by
          simpa [schema, decomposition, filler] using
            depthPrefix_one_noVariableBefore_of_not_sinksBy
              hg hsource hsource hsourceSinks
        obtain ⟨residual, hsymbolic, hresidualInstance⟩ :=
          runActions?_reflects_instantiation_of_noVariableBefore
            hg (action :: actionsTail)
            ⟨decomposition.schemaArity g.ranks,
              hschemaSupported.1⟩
            hargumentsClosed hinstanceRun hnoVariable
        have hresidualSupported :
            RegularTerm.SupportedByPrefix g.ranks
              (decomposition.schemaArity g.ranks)
              decomposition.tails.length residual :=
          hschemaSupported.residual hg hpadding hsymbolic
        have hsourceWitness :
            schema.HasPrefixWitness decomposition.tails.length :=
          FiniteHead.toRegularTerm_hasPrefixWitness hvalid
        have hresidualWitness :
            residual.HasPrefixWitness decomposition.tails.length := by
          exact hsourceWitness.runActions hg hpadding
            hschemaSupported.1 hsymbolic
        have hsourceDepth :
            schema.UnfoldingDepthAtMost
              decomposition.head.compiledNodeCount := by
          exact FiniteHead.toRegularTerm_unfoldingDepthAtMost hranked
        have hresidualDepthExact :
            residual.UnfoldingDepthAtMost
              (g.residualUnfoldingDepthBound
                (action :: actionsTail).length
                decomposition.head.compiledNodeCount) := by
          exact g.runActions?_preserves_unfoldingDepthAtMost
            hg ⟨decomposition.schemaArity g.ranks,
              hschemaSupported.1⟩
            hsourceDepth hsymbolic
        have hheadDepth :
            decomposition.head.depth ≤ 1 :=
          RegularTerm.depthPrefix_head_depth_le source 1
        have hheadSize :
            decomposition.head.compiledNodeCount ≤
              FiniteHead.compiledDepthBound
                (g.ranks.foldr max 0) 1 :=
          FiniteHead.compiledNodeCount_le_depthBound
            hranked hheadDepth
        have hresidualBound :
            g.residualUnfoldingDepthBound
                (action :: actionsTail).length
                decomposition.head.compiledNodeCount ≤
              g.structuredPivotPreludeDepthBound short := by
          rw [residualUnfoldingDepthBound_eq]
          unfold structuredPivotPreludeDepthBound
          rw [residualUnfoldingDepthBound_eq]
          exact Nat.add_le_add
            (Nat.mul_le_mul_right g.rhsNodeBound hactionsLength)
            hheadSize
        have hresidualDepth :
            residual.UnfoldingDepthAtMost
              (g.structuredPivotPreludeDepthBound short) :=
          hresidualDepthExact.mono hresidualBound
        have hargumentsLength :
            arguments.length =
              decomposition.schemaArity g.ranks := by
          simp [arguments]
        have hwidth :
            decomposition.tails.length ≤ arguments.length := by
          rw [hargumentsLength]
          exact hschemaSupported.2.1
        have hcanonicalGround :
            (residual.instantiate arguments).Ground g.ranks := by
          apply RegularTerm.instantiate_ground
          · simpa [hargumentsLength] using hresidualSupported.1
          · exact hargumentsGround
        have hintermediateGround : intermediate.Ground g.ranks :=
          hgroundSteps.ground_of_run hsource hpreludeRun
        have hcanonicalMatches :
            (residual.instantiate arguments).UnfoldingEquivalent
              intermediate :=
          hresidualInstance.trans hinstanceTargetMatches
        obtain ⟨hit⟩ :=
          g.exists_canonicalArgumentHit_of_repeatedlySinksBy_of_depthBound
            hg hresidualWitness hresidualDepth
            (RegularTerm.referenceClosed_of_wellFormed
              hresidualSupported.1)
            hwidth hargumentsGround hcanonicalGround
            hintermediateGround
            (RegularTerm.unfoldingEquivalent_refl _)
            hcanonicalMatches.symm
            (by simp [structuredPivotSinkDepth])
            hsinks
        let tail :=
          decomposition.tails.get ⟨hit.index, hit.index_lt⟩
        have htailGet :
            decomposition.tails[hit.index]? = some tail :=
          List.getElem?_eq_getElem hit.index_lt
        have hargumentGet :
            arguments[hit.index]? = some tail := by
          unfold arguments DepthPrefix.paddedArguments
          rw [List.getElem?_append_left hit.index_lt]
          exact htailGet
        have hargumentEq : hit.argument = tail :=
          Option.some.inj (hit.argument_at.symm.trans hargumentGet)
        have htailSubterm :
            source.SubtermAtDepth 1 tail :=
          RegularTerm.depthPrefix_tails_subtermAtDepth
            hsource 1 tail (List.getElem_mem hit.index_lt)
        obtain ⟨actualTarget, hactualRun, hactualMatches⟩ :=
          exists_run_of_unfoldingEquivalent hg
            hcanonicalMatches.symm
            (RegularTerm.referenceClosed_of_ground hintermediateGround)
            (RegularTerm.referenceClosed_of_ground hcanonicalGround)
            hit.run
        refine ⟨
          (action :: actionsTail).map Sum.inl ++ hit.initialSegment,
          hit.remainder, ?_, ?_, ?_⟩
        · calc
            (action :: actionsTail).map Sum.inl ++ sinkingWord =
                (action :: actionsTail).map Sum.inl ++
                  (hit.initialSegment ++ hit.remainder) :=
              congrArg
                ((action :: actionsTail).map Sum.inl ++ ·)
                hit.word_eq
            _ =
                ((action :: actionsTail).map Sum.inl ++
                  hit.initialSegment) ++ hit.remainder :=
              (List.append_assoc _ _ _).symm
        · simp
        · exact ⟨tail, actualTarget, htailSubterm, by
            rw [g.run?_append, hpreludeRun]
            exact hactualRun,
          hactualMatches.trans (hargumentEq ▸ hit.target_matches)⟩

/-- A short prelude followed by more exact root-sinking blocks than its
depth-one symbolic residual can contain already root-sinks from the original
source. -/
public theorem rootSinksBy_append_of_shortPrelude_repeatedlyRootSinks
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source intermediate : RegularTerm}
    (hsource : source.Ground g.ranks)
    (short : ℕ)
    {prelude sinkingWord : List (Label Action)}
    (hpreludeLength : prelude.length ≤ short)
    (hpreludeRun : g.run? prelude source = some intermediate)
    (hsinks :
      g.RepeatedlyRootSinksBy intermediate sinkingWord
        (g.structuredPivotSinkDepth short)) :
    g.RootSinksBy source (prelude ++ sinkingWord) := by
  classical
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  obtain ⟨actions, hprelude⟩ :=
    hgroundSteps.exists_actions_of_ground_run hsource hpreludeRun
  subst prelude
  have hactionsLength : actions.length ≤ short := by
    simpa using hpreludeLength
  have hdepthPositive :
      0 < g.structuredPivotSinkDepth short := by
    simp [structuredPivotSinkDepth]
  cases hactionsEmpty : actions with
  | nil =>
      subst actions
      simp at hpreludeRun
      subst intermediate
      simpa using hsinks.toRootSinksBy hdepthPositive
  | cons action actionsTail =>
      subst actions
      have hactionsNonempty : action :: actionsTail ≠ [] := by simp
      by_cases hsourceSinks :
          g.RootSinksBy source
            ((action :: actionsTail).map Sum.inl)
      · exact hsourceSinks.append sinkingWord
      · let decomposition := source.depthPrefix 1
        let schema := decomposition.head.toRegularTerm
        let arguments :=
          decomposition.paddedArguments g.ranks source
        have hvalid : decomposition.Valid :=
          RegularTerm.depthPrefix_valid source 1
        have hranked : decomposition.head.RankedBy g.ranks :=
          RegularTerm.depthPrefix_head_rankedBy hsource 1
        have hschemaSupported :
            RegularTerm.SupportedByPrefix g.ranks
              (decomposition.schemaArity g.ranks)
              decomposition.tails.length schema :=
          FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked
        have hpadding :
            g.ranks.foldr max 0 ≤
              decomposition.schemaArity g.ranks := by
          simp [DepthPrefix.schemaArity]
        have hargumentsGround :
            ∀ argument ∈ arguments, argument.Ground g.ranks :=
          RegularTerm.depthPrefix_paddedArguments_ground
            hsource hsource 1
        have hargumentsClosed :
            ∀ argument ∈ arguments, argument.ReferenceClosed := by
          intro argument hargument
          exact RegularTerm.referenceClosed_of_ground
            (hargumentsGround argument hargument)
        have hinstanceEquivalent :
            (schema.instantiate arguments).UnfoldingEquivalent source :=
          RegularTerm.depthPrefix_compiled_unfoldingEquivalent
            hsource hsource 1
        have hinstanceClosed :
            (schema.instantiate arguments).ReferenceClosed :=
          RegularTerm.instantiate_referenceClosed
            (RegularTerm.referenceClosed_of_wellFormed
              hschemaSupported.1)
            hargumentsClosed
        have hpreludeRunActions :
            g.runActions? (action :: actionsTail) source =
              some intermediate := by
          simpa only [runActions?] using hpreludeRun
        obtain ⟨instanceTarget, hinstanceRun,
            hinstanceTargetMatches⟩ :=
          exists_runActions_of_unfoldingEquivalent hg
            hinstanceEquivalent hinstanceClosed
            (RegularTerm.referenceClosed_of_ground hsource)
            hpreludeRunActions
        have hnoVariable :
            g.NoVariableBefore schema (action :: actionsTail) := by
          simpa [schema, decomposition] using
            depthPrefix_one_noVariableBefore_of_not_rootSinksBy
              hg hsource hsourceSinks
        obtain ⟨residual, hsymbolic, hresidualInstance⟩ :=
          runActions?_reflects_instantiation_of_noVariableBefore
            hg (action :: actionsTail)
            ⟨decomposition.schemaArity g.ranks,
              hschemaSupported.1⟩
            hargumentsClosed hinstanceRun hnoVariable
        have hresidualSupported :
            RegularTerm.SupportedByPrefix g.ranks
              (decomposition.schemaArity g.ranks)
              decomposition.tails.length residual :=
          hschemaSupported.residual hg hpadding hsymbolic
        have hsourceWitness :
            schema.HasPrefixWitness decomposition.tails.length :=
          FiniteHead.toRegularTerm_hasPrefixWitness hvalid
        have hresidualWitness :
            residual.HasPrefixWitness decomposition.tails.length := by
          exact hsourceWitness.runActions hg hpadding
            hschemaSupported.1 hsymbolic
        have hsourceDepth :
            schema.UnfoldingDepthAtMost
              decomposition.head.compiledNodeCount :=
          FiniteHead.toRegularTerm_unfoldingDepthAtMost hranked
        have hresidualDepthExact :
            residual.UnfoldingDepthAtMost
              (g.residualUnfoldingDepthBound
                (action :: actionsTail).length
                decomposition.head.compiledNodeCount) :=
          g.runActions?_preserves_unfoldingDepthAtMost
            hg ⟨decomposition.schemaArity g.ranks,
              hschemaSupported.1⟩
            hsourceDepth hsymbolic
        have hheadDepth :
            decomposition.head.depth ≤ 1 :=
          RegularTerm.depthPrefix_head_depth_le source 1
        have hheadSize :
            decomposition.head.compiledNodeCount ≤
              FiniteHead.compiledDepthBound
                (g.ranks.foldr max 0) 1 :=
          FiniteHead.compiledNodeCount_le_depthBound
            hranked hheadDepth
        have hresidualBound :
            g.residualUnfoldingDepthBound
                (action :: actionsTail).length
                decomposition.head.compiledNodeCount ≤
              g.structuredPivotPreludeDepthBound short := by
          rw [residualUnfoldingDepthBound_eq]
          unfold structuredPivotPreludeDepthBound
          rw [residualUnfoldingDepthBound_eq]
          exact Nat.add_le_add
            (Nat.mul_le_mul_right g.rhsNodeBound hactionsLength)
            hheadSize
        have hresidualDepth :
            residual.UnfoldingDepthAtMost
              (g.structuredPivotPreludeDepthBound short) :=
          hresidualDepthExact.mono hresidualBound
        have hargumentsLength :
            arguments.length =
              decomposition.schemaArity g.ranks := by
          simp [arguments]
        have hwidth :
            decomposition.tails.length ≤ arguments.length := by
          rw [hargumentsLength]
          exact hschemaSupported.2.1
        have hintermediateGround : intermediate.Ground g.ranks :=
          hgroundSteps.ground_of_run hsource hpreludeRun
        have hcanonicalMatches :
            (residual.instantiate arguments).UnfoldingEquivalent
              intermediate :=
          hresidualInstance.trans hinstanceTargetMatches
        obtain ⟨hit⟩ :=
          g.exists_schemaVariableHit_of_repeatedlyRootSinksBy_of_depthBound
            hg hresidualWitness hresidualDepth
            (RegularTerm.referenceClosed_of_wellFormed
              hresidualSupported.1)
            hwidth hintermediateGround hcanonicalMatches.symm
            (by simp [structuredPivotSinkDepth])
            hsinks
        obtain ⟨rootSymbol, children, hroot⟩ :=
          hsource.exists_rootApplication
        have hschemaTemplate :
            schema.UnfoldingEquivalent
              (RegularTerm.symbolTemplate
                rootSymbol children.length) := by
          simpa [schema, decomposition] using
            depthPrefix_one_head_unfoldingEquivalent_symbolTemplate
              hsource hroot
        have hhitRun :
            g.runActions?
                ((action :: actionsTail) ++ hit.actions)
                schema =
              some hit.target := by
          unfold runActions?
          rw [List.map_append, g.run?_append]
          change
            g.runActions? (action :: actionsTail) schema >>=
                g.runActions? hit.actions =
              some hit.target
          rw [hsymbolic]
          exact hit.run
        have hrank :
            g.ranks[rootSymbol]? = some children.length :=
          hsource.root_rank_arity hroot
        have htemplateWellFormed :
            (RegularTerm.symbolTemplate rootSymbol children.length)
              |>.WellFormed g.ranks children.length :=
          RegularTerm.symbolTemplate_wellFormed hrank
        obtain ⟨target, htargetRun, htargetHit⟩ :=
          exists_runActions_of_unfoldingEquivalent hg
            hschemaTemplate.symm
            (RegularTerm.referenceClosed_of_wellFormed
              htemplateWellFormed)
            (RegularTerm.referenceClosed_of_wellFormed
              hschemaSupported.1)
            hhitRun
        have htargetVariable :
            target.UnfoldingEquivalent
              (RegularTerm.variableTerm hit.index) :=
          htargetHit.trans hit.target_matches
        have htargetRoot :
            target.rootNode? = some (.inl hit.index) :=
          rootNode?_variable_of_unfoldingEquivalent
            htargetVariable.symm
            (RegularTerm.variableTerm_rootNode? hit.index)
        have hxChildren : hit.index < children.length := by
          have hx := hit.index_lt
          have htails :=
            RegularTerm.depthPrefix_one_tails_of_rootApplication
              hroot
          change hit.index < decomposition.tails.length at hx
          simpa [decomposition, htails] using hx
        let openStep :
            RootSinkingStep g rootSymbol children.length
              ((action :: actionsTail) ++ hit.actions) :=
          { child := ⟨hit.index, hxChildren⟩
            target := target
            actions_nonempty := by simp
            run := htargetRun
            target_root := htargetRoot }
        refine ⟨rootSymbol, children,
          (action :: actionsTail) ++ hit.actions,
          hit.remainder, hroot, ?_, ⟨openStep⟩⟩
        calc
          (action :: actionsTail).map Sum.inl ++ sinkingWord =
              (action :: actionsTail).map Sum.inl ++
                (hit.actions.map Sum.inl ++ hit.remainder) :=
            congrArg
              ((action :: actionsTail).map Sum.inl ++ ·)
              hit.word_eq
          _ =
              ((action :: actionsTail) ++ hit.actions).map
                  Sum.inl ++ hit.remainder := by
            simp [List.map_append, List.append_assoc]

end EncodedFirstOrderGrammar

namespace RegularTerm

/-- Semantically equal terms have pairwise semantically equal ordered
boundary tails at every finite unfolding depth. -/
public theorem depthPrefix_tails_forall₂
    {left right : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    (depth : ℕ) :
    List.Forall₂ RegularTerm.UnfoldingEquivalent
      (left.depthPrefix depth).tails
      (right.depthPrefix depth).tails := by
  induction depth generalizing left right with
  | zero =>
      simpa [RegularTerm.depthPrefix_zero] using
        List.Forall₂.cons hequivalent List.Forall₂.nil
  | succ depth ih =>
      cases hleftRoot : left.rootApplication? with
      | none =>
          have hrightRoot : right.rootApplication? = none := by
            cases hrightRoot : right.rootApplication? with
            | none => rfl
            | some application =>
                rcases application with ⟨X, rightChildren⟩
                obtain ⟨leftChildren, hleftSome, _hchildren⟩ :=
                  rootApplication?_of_unfoldingEquivalent
                    hequivalent.symm hrightRoot
                rw [hleftRoot] at hleftSome
                simp at hleftSome
          simp [RegularTerm.depthPrefix, hleftRoot, hrightRoot,
            hequivalent]
      | some application =>
          rcases application with ⟨X, leftChildren⟩
          obtain ⟨rightChildren, hrightRoot, hchildren⟩ :=
            rootApplication?_of_unfoldingEquivalent
              hequivalent hleftRoot
          rw [depthPrefix_succ_of_rootApplication hleftRoot,
            depthPrefix_succ_of_rootApplication hrightRoot]
          simp only [DepthPrefix.assemble_tails]
          simpa [List.flatMap_map, Function.comp_def] using
            (List.rel_flatMap hchildren
              (fun leftChild rightChild hchild =>
                ih
                  ((withRoot_unfoldingEquivalent_iff_bisimilarAt
                    left right leftChild rightChild).2 hchild)))

/-- Padding two equivalent depth prefixes preserves semantic agreement
through every genuine boundary-tail position. -/
public theorem depthPrefix_paddedArguments_equivalentThrough
    {ranks : List ℕ} {left right leftFiller rightFiller : RegularTerm}
    (hequivalent : left.UnfoldingEquivalent right)
    (depth : ℕ) :
    ArgumentsEquivalentThrough
      (left.depthPrefix depth).tails.length
      ((left.depthPrefix depth).paddedArguments ranks leftFiller)
      ((right.depthPrefix depth).paddedArguments ranks rightFiller) := by
  have htails :=
    depthPrefix_tails_forall₂ hequivalent depth
  have hlength :
      (left.depthPrefix depth).tails.length =
        (right.depthPrefix depth).tails.length :=
    htails.length_eq
  intro i hi
  have hiRight : i < (right.depthPrefix depth).tails.length := by
    omega
  let leftTail := (left.depthPrefix depth).tails.get ⟨i, hi⟩
  let rightTail :=
    (right.depthPrefix depth).tails.get ⟨i, hiRight⟩
  refine ⟨leftTail, rightTail, ?_, ?_, ?_⟩
  · unfold DepthPrefix.paddedArguments
    rw [List.getElem?_append_left hi]
    exact List.getElem?_eq_getElem hi
  · unfold DepthPrefix.paddedArguments
    rw [List.getElem?_append_left hiRight]
    exact List.getElem?_eq_getElem hiRight
  · exact (List.forall₂_iff_get.mp htails).2 i hi hiRight

/-- Pointing twice into one finite regular graph is the same as pointing
directly into the original graph. -/
public theorem mem_pointedSubterms_trans
    {base middle target : RegularTerm}
    (hmiddle : middle ∈ base.pointedSubterms)
    (htarget : target ∈ middle.pointedSubterms) :
    target ∈ base.pointedSubterms := by
  unfold RegularTerm.pointedSubterms at hmiddle htarget ⊢
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmiddle
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp htarget
  apply List.mem_map.mpr
  exact ⟨j, by simpa using hj, rfl⟩

/-- An exact unfolding subterm of a reference-closed graph is one of its
pointed presentations. -/
public theorem SubtermAtDepth.mem_pointedSubterms
    {term subterm : RegularTerm} {depth : ℕ}
    (hclosed : term.ReferenceClosed)
    (hsubterm : term.SubtermAtDepth depth subterm) :
    subterm ∈ term.pointedSubterms := by
  obtain ⟨i, hi, rfl⟩ := hsubterm
  apply term.withRoot_mem_pointedSubterms
  induction hi with
  | root => exact hclosed.1
  | @child depth parent X children child hparent hnode hchild ih =>
      exact hclosed.2 parent X children hnode child hchild

/-- Every pointed presentation of a reference-closed finite graph remains
reference closed. -/
public theorem referenceClosed_of_mem_pointedSubterms
    {base source : RegularTerm} (hbase : base.ReferenceClosed)
    (hsource : source ∈ base.pointedSubterms) :
    source.ReferenceClosed := by
  unfold RegularTerm.pointedSubterms at hsource
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hsource
  exact RegularTerm.withRoot_referenceClosed hbase (by simpa using hi)

end RegularTerm

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath

/-- A concrete pivot edge retaining the uniform sinking-window guarantee
which the lightweight `PivotEdge` deliberately forgets. -/
public structure StructuredPivotPolicyTransition.WindowedPivotEdge
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    {current : StructuredDerivedBalancingStep
      hg hground hinitial source bound}
    (transition : StructuredPivotPolicyTransition
      hg hground hinitial current) where
  toPivotEdge : transition.PivotEdge
  word_shape :
    0 < bound →
      (toPivotEdge.word =
          (source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord
              0 transition.policy.offset) ∨
        ∃ i : Fin current.structured.children.length,
          ∃ cut ≤ transition.policy.offset,
            toPivotEdge.word =
              (current.structured.family.row i).modifiedBridge
                current.continuationPath cut
                transition.policy.offset
  tail_windows_sink :
    0 < bound →
      ∀ skip,
        g.structuredPivotShortPrefixBound bound ≤ skip →
        skip + bound ≤ toPivotEdge.word.length →
        ∃ intermediate,
          g.run? (toPivotEdge.word.take skip)
              (SelectedBalancingSegment.pivot current.selected) =
            some intermediate ∧
          g.SinksBy intermediate
            ((toPivotEdge.word.drop skip).take bound)
  tail_windows_rootSink :
    0 < bound →
      ∀ skip,
        g.structuredPivotShortPrefixBound bound ≤ skip →
        skip + bound ≤ toPivotEdge.word.length →
        ∃ intermediate,
          g.run? (toPivotEdge.word.take skip)
              (SelectedBalancingSegment.pivot current.selected) =
            some intermediate ∧
          g.RootSinksBy intermediate
            ((toPivotEdge.word.drop skip).take bound)
  tail_repeatedly_root_sinks :
    0 < bound →
      ∀ depth skip,
        g.structuredPivotShortPrefixBound bound ≤ skip →
        skip + depth * bound ≤ toPivotEdge.word.length →
        ∃ intermediate,
          g.run? (toPivotEdge.word.take skip)
              (SelectedBalancingSegment.pivot current.selected) =
            some intermediate ∧
          g.RepeatedlyRootSinksBy intermediate
            ((toPivotEdge.word.drop skip).take (depth * bound))
            depth
  tail_repeatedly_sinks :
    0 < bound →
      ∀ depth skip,
        g.structuredPivotShortPrefixBound bound ≤ skip →
        skip + depth * bound ≤ toPivotEdge.word.length →
        ∃ intermediate,
          g.run? (toPivotEdge.word.take skip)
              (SelectedBalancingSegment.pivot current.selected) =
            some intermediate ∧
          g.RepeatedlySinksBy intermediate
            ((toPivotEdge.word.drop skip).take (depth * bound))
            depth

namespace StructuredDerivedBalancingStep

/-- On an unmodified fallback bridge, every complete window after the
grammar-uniform short prefix sinks on the pivot component. -/
public theorem direct_tail_windows_rootSink
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    {nextOffset : ℕ}
    (hno : ∀ earlier,
      current.closeBound ≤ earlier → earlier < nextOffset →
      ¬current.continuationPath.HasBalancingOpportunity bound earlier)
    (hbound : 0 < bound)
    (skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + bound ≤
        ((source.continuationPath hg hground hinitial).segmentWord
            current.offset bound ++
          current.continuationPath.segmentWord 0 nextOffset).length) :
    ∃ intermediate,
      g.run?
          (((source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord 0 nextOffset).take skip)
          (SelectedBalancingSegment.pivot current.selected) =
        some intermediate ∧
      g.RootSinksBy intermediate
        ((((source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord 0 nextOffset).drop skip)
          |>.take bound) := by
  let labels :=
    (source.continuationPath hg hground hinitial).segmentWord
      current.offset bound
  let continuation := current.continuationPath
  let position := skip - bound
  have hlabelsLength : labels.length = bound := by
    simp [labels]
  have hclose :
      current.closeBound ≤ g.structuredPivotCloseBound bound :=
    current.closeBound_le_structuredPivotCloseBound
  have hboundSkip : bound ≤ skip := by
    unfold structuredPivotShortPrefixBound at hshort
    omega
  have hpositionEq : bound + position = skip := by
    simp [position, Nat.add_sub_of_le hboundSkip]
  have hlength :
      (labels ++ continuation.segmentWord 0 nextOffset).length =
        bound + nextOffset := by
    simp [hlabelsLength, continuation]
  have hpositionFit : position + bound ≤ nextOffset := by
    have hfit' : skip + bound ≤ bound + nextOffset := by
      simpa [labels, continuation] using hfit
    omega
  have hpositionClose : current.closeBound ≤ position := by
    unfold structuredPivotShortPrefixBound at hshort
    omega
  have hpositionLt : position < nextOffset := by omega
  have hnoRight :
      ¬continuation.HasRightBalancingOpportunity bound position := by
    intro hopportunity
    exact hno position hpositionClose hpositionLt
      (hasBalancingOpportunity_of_hasRight hopportunity)
  have hsinks :
      g.RootSinksBy (continuation.right position)
        (continuation.segmentWord position bound) :=
    continuation.rootSinksRight_of_noBalancingOpportunity
      (current.target.derivation
        |>.pair_traceEquivalent_of_initial
          (guardedContextLaws_of_wellFormed hg) hinitial)
      position bound hnoRight
  have htake :
      (labels ++ continuation.segmentWord 0 nextOffset).take skip =
        labels ++ continuation.segmentWord 0 position := by
    rw [List.take_append]
    have htakeLabels : labels.take skip = labels :=
      (List.take_eq_self_iff labels).mpr (by
        simpa [hlabelsLength] using hboundSkip)
    rw [htakeLabels]
    have hsubtract : skip - labels.length = position := by
      simp [hlabelsLength, position]
    rw [hsubtract]
    exact congrArg (labels ++ ·)
      (continuation.take_segmentWord 0 hpositionLt.le)
  have hwindow :
      ((labels ++ continuation.segmentWord 0 nextOffset).drop skip).take
          bound =
        continuation.segmentWord position bound := by
    rw [List.drop_append]
    have hdropLabels : labels.drop skip = [] :=
      List.drop_eq_nil_iff.mpr (by
        simpa [hlabelsLength] using hboundSkip)
    rw [hdropLabels, List.nil_append]
    have hsubtract : skip - labels.length = position := by
      simp [hlabelsLength, position]
    rw [hsubtract]
    simpa using continuation.take_drop_segmentWord 0 hpositionFit
  refine ⟨continuation.right position, ?_, ?_⟩
  · rw [htake]
    exact current.pivot_run_to_continuation_right position
  · rw [hwindow]
    exact hsinks

/-- Semantic projection of the direct root-window witness. -/
public theorem direct_tail_windows_sink
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    {nextOffset : ℕ}
    (hno : ∀ earlier,
      current.closeBound ≤ earlier → earlier < nextOffset →
      ¬current.continuationPath.HasBalancingOpportunity bound earlier)
    (hbound : 0 < bound)
    (skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + bound ≤
        ((source.continuationPath hg hground hinitial).segmentWord
            current.offset bound ++
          current.continuationPath.segmentWord 0 nextOffset).length) :
    ∃ intermediate,
      g.run?
          (((source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord 0 nextOffset).take skip)
          (SelectedBalancingSegment.pivot current.selected) =
        some intermediate ∧
      g.SinksBy intermediate
        ((((source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord 0 nextOffset).drop skip)
          |>.take bound) := by
  obtain ⟨intermediate, hrun, hroot⟩ :=
    current.direct_tail_windows_rootSink
      hno hbound skip hshort hfit
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hintermediateGround : intermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run current.pivot_ground hrun
  exact ⟨intermediate, hrun,
    hroot.toSinksBy_of_ground hg hintermediateGround⟩

/-- Uniformly many consecutive post-prefix path windows retain an exact
root-syntactic sinking spine on an unmodified edge. -/
public theorem direct_tail_repeatedlyRootSinks
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    {nextOffset : ℕ}
    (hno : ∀ earlier,
      current.closeBound ≤ earlier → earlier < nextOffset →
      ¬current.continuationPath.HasBalancingOpportunity bound earlier)
    (hbound : 0 < bound)
    (depth skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + depth * bound ≤
        ((source.continuationPath hg hground hinitial).segmentWord
            current.offset bound ++
          current.continuationPath.segmentWord 0 nextOffset).length) :
    ∃ intermediate,
      g.run?
          (((source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord 0 nextOffset).take skip)
          (SelectedBalancingSegment.pivot current.selected) =
        some intermediate ∧
      g.RepeatedlyRootSinksBy intermediate
        ((((source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord 0 nextOffset).drop skip)
          |>.take (depth * bound))
        depth := by
  let labels :=
    (source.continuationPath hg hground hinitial).segmentWord
      current.offset bound
  let continuation := current.continuationPath
  let position := skip - bound
  have hlabelsLength : labels.length = bound := by
    simp [labels]
  have hclose :
      current.closeBound ≤ g.structuredPivotCloseBound bound :=
    current.closeBound_le_structuredPivotCloseBound
  have hboundSkip : bound ≤ skip := by
    unfold structuredPivotShortPrefixBound at hshort
    omega
  have hpositionFit : position + depth * bound ≤ nextOffset := by
    have hfit' : skip + depth * bound ≤ bound + nextOffset := by
      simpa [labels, continuation] using hfit
    simp only [position]
    omega
  have hpositionClose : current.closeBound ≤ position := by
    unfold structuredPivotShortPrefixBound at hshort
    simp only [position]
    omega
  have htake :
      (labels ++ continuation.segmentWord 0 nextOffset).take skip =
        labels ++ continuation.segmentWord 0 position := by
    rw [List.take_append]
    have htakeLabels : labels.take skip = labels :=
      (List.take_eq_self_iff labels).mpr (by
        simpa [hlabelsLength] using hboundSkip)
    rw [htakeLabels]
    have hsubtract : skip - labels.length = position := by
      simp [hlabelsLength, position]
    rw [hsubtract]
    have hpositionLe : position ≤ nextOffset := by omega
    exact congrArg (labels ++ ·)
      (continuation.take_segmentWord 0 hpositionLe)
  have hwindow :
      ((labels ++ continuation.segmentWord 0 nextOffset).drop skip).take
          (depth * bound) =
        continuation.segmentWord position (depth * bound) := by
    rw [List.drop_append]
    have hdropLabels : labels.drop skip = [] :=
      List.drop_eq_nil_iff.mpr (by
        simpa [hlabelsLength] using hboundSkip)
    rw [hdropLabels, List.nil_append]
    have hsubtract : skip - labels.length = position := by
      simp [hlabelsLength, position]
    rw [hsubtract]
    simpa using continuation.take_drop_segmentWord 0 hpositionFit
  refine ⟨continuation.right position, ?_, ?_⟩
  · rw [htake]
    exact current.pivot_run_to_continuation_right position
  · rw [hwindow]
    have hpositionPairGround :=
      continuation.residual_ground
        (preservesGroundSteps_of_wellFormed hg)
        (groundPairCode_of_pair_derivable current.target.derivation)
        position
    have hpositionGround :
        (continuation.right position).Ground g.ranks := by
      unfold groundPairCode at hpositionPairGround
      rw [Bool.and_eq_true] at hpositionPairGround
      exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
        hpositionPairGround.2
    apply continuation.repeatedlyRootSinksRight_of_noBalancingBefore
      hg
      (current.target.derivation
        |>.pair_traceEquivalent_of_initial
          (guardedContextLaws_of_wellFormed hg) hinitial)
      position bound depth
        (RegularTerm.Ground.exists_wellFormed hpositionGround) hbound
    intro later hlater
    have hlaterBefore : position + later < nextOffset := by
      have := hpositionFit
      omega
    exact fun hopportunity =>
      hno (position + later)
        (hpositionClose.trans (Nat.le_add_right _ _))
        hlaterBefore
        (hasBalancingOpportunity_of_hasRight hopportunity)

/-- Semantic projection of the direct repeated root-sinking spine. -/
public theorem direct_tail_repeatedlySinks
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    {nextOffset : ℕ}
    (hno : ∀ earlier,
      current.closeBound ≤ earlier → earlier < nextOffset →
      ¬current.continuationPath.HasBalancingOpportunity bound earlier)
    (hbound : 0 < bound)
    (depth skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + depth * bound ≤
        ((source.continuationPath hg hground hinitial).segmentWord
            current.offset bound ++
          current.continuationPath.segmentWord 0 nextOffset).length) :
    ∃ intermediate,
      g.run?
          (((source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord 0 nextOffset).take skip)
          (SelectedBalancingSegment.pivot current.selected) =
        some intermediate ∧
      g.RepeatedlySinksBy intermediate
        ((((source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord 0 nextOffset).drop skip)
          |>.take (depth * bound))
        depth := by
  obtain ⟨intermediate, hrun, hroot⟩ :=
    current.direct_tail_repeatedlyRootSinks
      hno hbound depth skip hshort hfit
  exact ⟨intermediate, hrun, hroot.toRepeatedlySinksBy⟩

/-- The switched bridge has the same tail-window property.  The retained row
reflection is what identifies every intermediate modified-word residual with
the active component of the continuation path. -/
public theorem switched_tail_windows_rootSink
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    (i : Fin current.structured.children.length)
    {cut nextOffset : ℕ}
    (hcut : cut ≤ current.closeBound)
    (hnext : current.closeBound ≤ nextOffset)
    (hmatch :
      (current.continuationPath.left cut).UnfoldingEquivalent
        (current.structured.family.row i).pivotTarget)
    (hno : ∀ earlier,
      current.closeBound ≤ earlier → earlier < nextOffset →
      ¬current.continuationPath.HasBalancingOpportunity bound earlier)
    (skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + bound ≤
        ((current.structured.family.row i).modifiedBridge
          current.continuationPath cut nextOffset).length) :
    ∃ intermediate,
      g.run?
          (((current.structured.family.row i).modifiedBridge
            current.continuationPath cut nextOffset).take skip)
          (SelectedBalancingSegment.pivot current.selected) =
        some intermediate ∧
      g.RootSinksBy intermediate
        ((((current.structured.family.row i).modifiedBridge
            current.continuationPath cut nextOffset).drop skip).take
          bound) := by
  let row := current.structured.family.row i
  let continuation := current.continuationPath
  let rowLabels : List (Label Action) := row.word.map Sum.inl
  let tailSkip := skip - rowLabels.length
  let position := cut + tailSkip
  have hrowLength : rowLabels.length < bound := by
    simpa [rowLabels, row] using row.word_length_lt
  have hrowSkip : rowLabels.length ≤ skip := by
    unfold structuredPivotShortPrefixBound at hshort
    omega
  have hcutNext : cut ≤ nextOffset := hcut.trans (hnext)
  have htailFit : tailSkip + bound ≤ nextOffset - cut := by
    have hlength :
        (row.modifiedBridge continuation cut nextOffset).length =
          rowLabels.length + (nextOffset - cut) := by
      simp [BalancingSegment.ExposedSuccessorResult.modifiedBridge,
        row, rowLabels, continuation]
    have hfit' :
        skip + bound ≤ rowLabels.length + (nextOffset - cut) := by
      change
        skip + bound ≤
          (row.modifiedBridge continuation cut nextOffset).length at hfit
      rw [hlength] at hfit
      exact hfit
    simp only [tailSkip]
    omega
  have hpositionFit : position + bound ≤ nextOffset := by
    simp only [position]
    omega
  have hpositionClose : current.closeBound ≤ position := by
    have hclose :
        current.closeBound ≤ g.structuredPivotCloseBound bound :=
      current.closeBound_le_structuredPivotCloseBound
    unfold structuredPivotShortPrefixBound at hshort
    simp only [position, tailSkip]
    omega
  have hpositionLt : position < nextOffset := by omega
  have hnoLeft :
      ¬continuation.HasLeftBalancingOpportunity bound position := by
    intro hopportunity
    exact hno position hpositionClose hpositionLt
      (hasBalancingOpportunity_of_hasLeft hopportunity)
  have hcontinuationEquivalent :
      g.TraceEquivalent current.resultLeft current.resultRight :=
    current.target.derivation
      |>.pair_traceEquivalent_of_initial
        (guardedContextLaws_of_wellFormed hg) hinitial
  have hsinksPath :
      g.RootSinksBy (continuation.left position)
        (continuation.segmentWord position bound) :=
    continuation.rootSinksLeft_of_noBalancingOpportunity
      hcontinuationEquivalent position bound hnoLeft
  have htailSkipFit : tailSkip ≤ nextOffset - cut := by omega
  have hpathRun :
      g.run? (continuation.segmentWord cut tailSkip)
          (continuation.left cut) =
        some (continuation.left position) := by
    simpa [position] using
      continuation.left_segment_run cut tailSkip
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hrowTargetGround : row.pivotTarget.Ground g.ranks := by
    exact hgroundSteps.ground_of_run
      current.pivot_ground
      (by simpa [row, rowLabels, runActions?] using row.pivot_run)
  have hcutPairGround :=
    continuation.residual_ground
      hgroundSteps
      (groundPairCode_of_pair_derivable current.target.derivation) cut
  have hcutGround : (continuation.left cut).Ground g.ranks := by
    unfold groundPairCode at hcutPairGround
    rw [Bool.and_eq_true] at hcutPairGround
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hcutPairGround.1
  obtain ⟨intermediate, hintermediateRun, hintermediateMatch⟩ :=
    exists_run_of_unfoldingEquivalent hg hmatch.symm
      (RegularTerm.referenceClosed_of_ground hrowTargetGround)
      (RegularTerm.referenceClosed_of_ground hcutGround)
      hpathRun
  have hintermediateGround : intermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run
      hrowTargetGround hintermediateRun
  have hpositionPairGround :=
    continuation.residual_ground
      hgroundSteps
      (groundPairCode_of_pair_derivable current.target.derivation) position
  have hpositionGround :
      (continuation.left position).Ground g.ranks := by
    unfold groundPairCode at hpositionPairGround
    rw [Bool.and_eq_true] at hpositionPairGround
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hpositionPairGround.1
  have hsinks :
      g.RootSinksBy intermediate
        (continuation.segmentWord position bound) :=
    hsinksPath.of_unfoldingEquivalent hintermediateMatch.symm
  have htake :
      (row.modifiedBridge continuation cut nextOffset).take skip =
        rowLabels ++ continuation.segmentWord cut tailSkip := by
    unfold BalancingSegment.ExposedSuccessorResult.modifiedBridge
    rw [List.take_append]
    have htakeRow : rowLabels.take skip = rowLabels :=
      (List.take_eq_self_iff rowLabels).mpr hrowSkip
    rw [htakeRow]
    have hsubtract : skip - rowLabels.length = tailSkip := by
      rfl
    rw [hsubtract]
    exact congrArg (rowLabels ++ ·)
      (continuation.take_segmentWord cut htailSkipFit)
  have hwindow :
      ((row.modifiedBridge continuation cut nextOffset).drop skip).take
          bound =
        continuation.segmentWord position bound := by
    unfold BalancingSegment.ExposedSuccessorResult.modifiedBridge
    rw [List.drop_append]
    have hdropRow : rowLabels.drop skip = [] :=
      List.drop_eq_nil_iff.mpr hrowSkip
    rw [hdropRow, List.nil_append]
    change
      ((continuation.segmentWord cut (nextOffset - cut)).drop
          tailSkip).take bound =
        continuation.segmentWord position bound
    simpa [position] using
      continuation.take_drop_segmentWord cut htailFit
  refine ⟨intermediate, ?_, ?_⟩
  · rw [htake, g.run?_append]
    have hpivotRun :
        g.run? rowLabels
            (SelectedBalancingSegment.pivot current.selected) =
          some row.pivotTarget := by
      simpa [row, rowLabels, runActions?] using row.pivot_run
    rw [hpivotRun]
    exact hintermediateRun
  · rw [hwindow]
    exact hsinks

/-- Semantic projection of the switched root-window witness. -/
public theorem switched_tail_windows_sink
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    (i : Fin current.structured.children.length)
    {cut nextOffset : ℕ}
    (hcut : cut ≤ current.closeBound)
    (hnext : current.closeBound ≤ nextOffset)
    (hmatch :
      (current.continuationPath.left cut).UnfoldingEquivalent
        (current.structured.family.row i).pivotTarget)
    (hno : ∀ earlier,
      current.closeBound ≤ earlier → earlier < nextOffset →
      ¬current.continuationPath.HasBalancingOpportunity bound earlier)
    (skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + bound ≤
        ((current.structured.family.row i).modifiedBridge
          current.continuationPath cut nextOffset).length) :
    ∃ intermediate,
      g.run?
          (((current.structured.family.row i).modifiedBridge
            current.continuationPath cut nextOffset).take skip)
          (SelectedBalancingSegment.pivot current.selected) =
        some intermediate ∧
      g.SinksBy intermediate
        ((((current.structured.family.row i).modifiedBridge
            current.continuationPath cut nextOffset).drop skip).take
          bound) := by
  obtain ⟨intermediate, hrun, hroot⟩ :=
    current.switched_tail_windows_rootSink
      i hcut hnext hmatch hno skip hshort hfit
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hintermediateGround : intermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run current.pivot_ground hrun
  exact ⟨intermediate, hrun,
    hroot.toSinksBy_of_ground hg hintermediateGround⟩

/-- Uniformly many consecutive post-prefix windows on a switched edge retain
an exact root-syntactic sinking spine. -/
public theorem switched_tail_repeatedlyRootSinks
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    (i : Fin current.structured.children.length)
    {cut nextOffset : ℕ}
    (hcut : cut ≤ current.closeBound)
    (hnext : current.closeBound ≤ nextOffset)
    (hmatch :
      (current.continuationPath.left cut).UnfoldingEquivalent
        (current.structured.family.row i).pivotTarget)
    (hno : ∀ earlier,
      current.closeBound ≤ earlier → earlier < nextOffset →
      ¬current.continuationPath.HasBalancingOpportunity bound earlier)
    (depth skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + depth * bound ≤
        ((current.structured.family.row i).modifiedBridge
          current.continuationPath cut nextOffset).length) :
    ∃ intermediate,
      g.run?
          (((current.structured.family.row i).modifiedBridge
            current.continuationPath cut nextOffset).take skip)
          (SelectedBalancingSegment.pivot current.selected) =
        some intermediate ∧
      g.RepeatedlyRootSinksBy intermediate
        ((((current.structured.family.row i).modifiedBridge
            current.continuationPath cut nextOffset).drop skip).take
          (depth * bound))
        depth := by
  let row := current.structured.family.row i
  let continuation := current.continuationPath
  let rowLabels : List (Label Action) := row.word.map Sum.inl
  let tailSkip := skip - rowLabels.length
  let position := cut + tailSkip
  have hrowLength : rowLabels.length < bound := by
    simpa [rowLabels, row] using row.word_length_lt
  have hbound : 0 < bound := by omega
  have hrowSkip : rowLabels.length ≤ skip := by
    unfold structuredPivotShortPrefixBound at hshort
    omega
  have hcutNext : cut ≤ nextOffset := hcut.trans hnext
  have htailFit :
      tailSkip + depth * bound ≤ nextOffset - cut := by
    have hlength :
        (row.modifiedBridge continuation cut nextOffset).length =
          rowLabels.length + (nextOffset - cut) := by
      simp [BalancingSegment.ExposedSuccessorResult.modifiedBridge,
        row, rowLabels, continuation]
    change
      skip + depth * bound ≤
        (row.modifiedBridge continuation cut nextOffset).length at hfit
    rw [hlength] at hfit
    simp only [tailSkip]
    omega
  have hpositionFit :
      position + depth * bound ≤ nextOffset := by
    simp only [position]
    omega
  have hpositionClose : current.closeBound ≤ position := by
    have hclose :
        current.closeBound ≤ g.structuredPivotCloseBound bound :=
      current.closeBound_le_structuredPivotCloseBound
    unfold structuredPivotShortPrefixBound at hshort
    simp only [position, tailSkip]
    omega
  have hpathRun :
      g.run? (continuation.segmentWord cut tailSkip)
          (continuation.left cut) =
        some (continuation.left position) := by
    simpa [position] using
      continuation.left_segment_run cut tailSkip
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hrowTargetGround : row.pivotTarget.Ground g.ranks := by
    exact hgroundSteps.ground_of_run current.pivot_ground
      (by simpa [row, rowLabels, runActions?] using row.pivot_run)
  have hcutPairGround :=
    continuation.residual_ground hgroundSteps
      (groundPairCode_of_pair_derivable current.target.derivation) cut
  have hcutGround : (continuation.left cut).Ground g.ranks := by
    unfold groundPairCode at hcutPairGround
    rw [Bool.and_eq_true] at hcutPairGround
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hcutPairGround.1
  obtain ⟨intermediate, hintermediateRun, hintermediateMatch⟩ :=
    exists_run_of_unfoldingEquivalent hg hmatch.symm
      (RegularTerm.referenceClosed_of_ground hrowTargetGround)
      (RegularTerm.referenceClosed_of_ground hcutGround)
      hpathRun
  have hintermediateGround : intermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run hrowTargetGround hintermediateRun
  have hpositionPairGround :=
    continuation.residual_ground hgroundSteps
      (groundPairCode_of_pair_derivable current.target.derivation) position
  have hpositionGround :
      (continuation.left position).Ground g.ranks := by
    unfold groundPairCode at hpositionPairGround
    rw [Bool.and_eq_true] at hpositionPairGround
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hpositionPairGround.1
  have hcontinuationEquivalent :
      g.TraceEquivalent current.resultLeft current.resultRight :=
    current.target.derivation
      |>.pair_traceEquivalent_of_initial
        (guardedContextLaws_of_wellFormed hg) hinitial
  have hsinksPath :
      g.RepeatedlyRootSinksBy
        (continuation.left position)
        (continuation.segmentWord position (depth * bound))
        depth := by
    apply continuation.repeatedlyRootSinksLeft_of_noBalancingBefore
      hg hcontinuationEquivalent position bound depth
      (RegularTerm.Ground.exists_wellFormed hpositionGround) hbound
    intro later hlater
    have hlaterBefore : position + later < nextOffset := by
      have := hpositionFit
      omega
    exact fun hopportunity =>
      hno (position + later)
        (hpositionClose.trans (Nat.le_add_right _ _))
        hlaterBefore
        (hasBalancingOpportunity_of_hasLeft hopportunity)
  have hsinks :
      g.RepeatedlyRootSinksBy intermediate
        (continuation.segmentWord position (depth * bound))
        depth :=
    hsinksPath.of_unfoldingEquivalent hg
      hintermediateGround hpositionGround hintermediateMatch
  have htake :
      (row.modifiedBridge continuation cut nextOffset).take skip =
        rowLabels ++ continuation.segmentWord cut tailSkip := by
    unfold BalancingSegment.ExposedSuccessorResult.modifiedBridge
    rw [List.take_append]
    have htakeRow : rowLabels.take skip = rowLabels :=
      (List.take_eq_self_iff rowLabels).mpr hrowSkip
    rw [htakeRow]
    change
      rowLabels ++
          (continuation.segmentWord cut (nextOffset - cut)).take
            tailSkip =
        rowLabels ++ continuation.segmentWord cut tailSkip
    have htailSkipLe : tailSkip ≤ nextOffset - cut := by omega
    exact congrArg (rowLabels ++ ·)
      (continuation.take_segmentWord cut htailSkipLe)
  have hwindow :
      ((row.modifiedBridge continuation cut nextOffset).drop skip).take
          (depth * bound) =
        continuation.segmentWord position (depth * bound) := by
    unfold BalancingSegment.ExposedSuccessorResult.modifiedBridge
    rw [List.drop_append]
    have hdropRow : rowLabels.drop skip = [] :=
      List.drop_eq_nil_iff.mpr hrowSkip
    rw [hdropRow, List.nil_append]
    change
      ((continuation.segmentWord cut (nextOffset - cut)).drop
          tailSkip).take (depth * bound) =
        continuation.segmentWord position (depth * bound)
    simpa [position] using
      continuation.take_drop_segmentWord cut htailFit
  refine ⟨intermediate, ?_, ?_⟩
  · rw [htake, g.run?_append]
    have hpivotRun :
        g.run? rowLabels
            (SelectedBalancingSegment.pivot current.selected) =
          some row.pivotTarget := by
      simpa [row, rowLabels, runActions?] using row.pivot_run
    rw [hpivotRun]
    exact hintermediateRun
  · rw [hwindow]
    exact hsinks

/-- Semantic projection of the switched repeated root-sinking spine. -/
public theorem switched_tail_repeatedlySinks
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    (i : Fin current.structured.children.length)
    {cut nextOffset : ℕ}
    (hcut : cut ≤ current.closeBound)
    (hnext : current.closeBound ≤ nextOffset)
    (hmatch :
      (current.continuationPath.left cut).UnfoldingEquivalent
        (current.structured.family.row i).pivotTarget)
    (hno : ∀ earlier,
      current.closeBound ≤ earlier → earlier < nextOffset →
      ¬current.continuationPath.HasBalancingOpportunity bound earlier)
    (depth skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + depth * bound ≤
        ((current.structured.family.row i).modifiedBridge
          current.continuationPath cut nextOffset).length) :
    ∃ intermediate,
      g.run?
          (((current.structured.family.row i).modifiedBridge
            current.continuationPath cut nextOffset).take skip)
          (SelectedBalancingSegment.pivot current.selected) =
        some intermediate ∧
      g.RepeatedlySinksBy intermediate
        ((((current.structured.family.row i).modifiedBridge
            current.continuationPath cut nextOffset).drop skip).take
          (depth * bound))
        depth := by
  obtain ⟨intermediate, hrun, hroot⟩ :=
    current.switched_tail_repeatedlyRootSinks
      i hcut hnext hmatch hno depth skip hshort hfit
  exact ⟨intermediate, hrun, hroot.toRepeatedlySinksBy⟩

end StructuredDerivedBalancingStep

namespace StructuredPivotPolicyTransition

/-- The segment selected by the policy is definitionally the segment used to
assemble the next structured state, after packaging the dependent offset. -/
public theorem next_pivot_eq_policy
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    {current : StructuredDerivedBalancingStep
      hg hground hinitial source bound}
    (transition : StructuredPivotPolicyTransition
      hg hground hinitial current) :
    SelectedBalancingSegment.pivot transition.next.selected =
      SelectedBalancingSegment.pivot transition.policy.selected := by
  let nextPackage :
      Σ offset, PathBalancingSegment current.continuationPath bound offset :=
    ⟨transition.next.offset, transition.next.selected⟩
  let policyPackage :
      Σ offset, PathBalancingSegment current.continuationPath bound offset :=
    ⟨transition.policy.offset, transition.policy.selected⟩
  have hpackages : nextPackage = policyPackage := by
    apply Sigma.ext transition.next_offset_eq
    exact transition.next_selected_eq
  exact congrArg
    (fun package => SelectedBalancingSegment.pivot package.2)
    hpackages

/-- Rebuild one policy edge without erasing the intermediate row reflection.
The resulting word is still no longer than the unmodified bridge, and now
also carries the grammar-uniform tail-window sinking property. -/
public theorem exists_windowedPivotEdge
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    {current : StructuredDerivedBalancingStep
      hg hground hinitial source bound}
    (transition : StructuredPivotPolicyTransition
      hg hground hinitial current) :
    Nonempty transition.WindowedPivotEdge := by
  classical
  by_cases hbound : 0 < bound
  · rcases transition.policy.closeLeft_or_afterClose with
      hcloseLeft | hafterClose
    · obtain ⟨hoffset, hside, _hminimal⟩ := hcloseLeft
      cases hselected : transition.policy.selected with
      | left nextSegment =>
          let word :=
            (source.continuationPath hg hground hinitial).segmentWord
                current.offset bound ++
              current.continuationPath.segmentWord
                0 transition.policy.offset
          have hrun :
              g.run? word
                  (SelectedBalancingSegment.pivot current.selected) =
                some (SelectedBalancingSegment.pivot
                  transition.policy.selected) := by
            simpa [word, hselected, SelectedBalancingSegment.pivot] using
              current.pivot_run_to_continuation_right
                transition.policy.offset
          let edge : transition.PivotEdge :=
            { word := word
              target :=
                SelectedBalancingSegment.pivot transition.policy.selected
              run := hrun
              target_matches := by
                rw [transition.next_pivot_eq_policy]
              length_le_unmodified := le_refl _ }
          refine ⟨
            { toPivotEdge := edge
              word_shape := fun _ =>
                Or.inl rfl
              tail_windows_sink := by
                intro _hbound skip hshort hfit
                have hedgeLength :
                    edge.word.length ≤
                      g.structuredPivotShortPrefixBound bound := by
                  unfold edge word structuredPivotShortPrefixBound
                  simp only [List.length_append,
                    TracePath.segmentWord_length]
                  exact Nat.add_le_add_left
                    (hoffset.trans
                      current.closeBound_le_structuredPivotCloseBound)
                    bound
                exact False.elim (by omega)
              tail_windows_rootSink := by
                intro _hbound skip hshort hfit
                have hedgeLength :
                    edge.word.length ≤
                      g.structuredPivotShortPrefixBound bound := by
                  unfold edge word structuredPivotShortPrefixBound
                  simp only [List.length_append,
                    TracePath.segmentWord_length]
                  exact Nat.add_le_add_left
                    (hoffset.trans
                      current.closeBound_le_structuredPivotCloseBound)
                    bound
                exact False.elim (by omega)
              tail_repeatedly_root_sinks := by
                intro _hbound depth skip hshort hfit
                have hedgeLength :
                    edge.word.length ≤
                      g.structuredPivotShortPrefixBound bound := by
                  unfold edge word structuredPivotShortPrefixBound
                  simp only [List.length_append,
                    TracePath.segmentWord_length]
                  exact Nat.add_le_add_left
                    (hoffset.trans
                      current.closeBound_le_structuredPivotCloseBound)
                    bound
                cases depth with
                | zero =>
                    have hskipLength : edge.word.length ≤ skip := by omega
                    refine ⟨edge.target, ?_, .zero _ _⟩
                    rw [(List.take_eq_self_iff edge.word).mpr hskipLength]
                    exact edge.run
                | succ depth =>
                    have hwindow :
                        skip + bound ≤ edge.word.length := by
                      exact (Nat.add_le_add_left
                        (Nat.le_mul_of_pos_left bound (by omega))
                        skip).trans hfit
                    exact False.elim (by omega)
              tail_repeatedly_sinks := by
                intro _hbound depth skip hshort hfit
                have hedgeLength :
                    edge.word.length ≤
                      g.structuredPivotShortPrefixBound bound := by
                  unfold edge word structuredPivotShortPrefixBound
                  simp only [List.length_append,
                    TracePath.segmentWord_length]
                  exact Nat.add_le_add_left
                    (hoffset.trans
                      current.closeBound_le_structuredPivotCloseBound)
                    bound
                cases depth with
                | zero =>
                    have hskipLength : edge.word.length ≤ skip := by omega
                    refine ⟨edge.target, ?_, trivial⟩
                    rw [(List.take_eq_self_iff edge.word).mpr hskipLength]
                    exact edge.run
                | succ depth =>
                    have hwindow :
                        skip + bound ≤ edge.word.length := by
                      exact (Nat.add_le_add_left
                        (Nat.le_mul_of_pos_left bound (by omega))
                        skip).trans hfit
                    exact False.elim (by omega) }⟩
      | right nextSegment =>
          simp [hselected, SelectedBalancingSegment.side] at hside
    · obtain ⟨hclose, hnoLeft, hgap⟩ := hafterClose
      have hcurrentEquivalent :
          g.TraceEquivalent current.resultLeft current.resultRight :=
        current.target.derivation
          |>.pair_traceEquivalent_of_initial
            (guardedContextLaws_of_wellFormed hg) hinitial
      obtain ⟨cut, hcut, i, hmatch⟩ :=
        current.structured.replacement
          |>.exists_row_match_of_noLeftBalancingBefore
            hg current.active_ground current.pivot_ground
            current.filler_ground current.structured.root_eq
            current.continuationPath hcurrentEquivalent
            bound current.switchDepth hbound
            (by simp [StructuredDerivedBalancingStep.switchDepth])
            (by
              intro offset hoffset
              exact hnoLeft offset (by
                have :
                    offset ≤ current.switchDepth * bound :=
                  Nat.le_of_lt hoffset
                simpa [StructuredDerivedBalancingStep.closeBound] using
                  this))
      cases hselected : transition.policy.selected with
      | left nextSegment =>
          let word :=
            (source.continuationPath hg hground hinitial).segmentWord
                current.offset bound ++
              current.continuationPath.segmentWord
                0 transition.policy.offset
          have hrun :
              g.run? word
                  (SelectedBalancingSegment.pivot current.selected) =
                some (SelectedBalancingSegment.pivot
                  transition.policy.selected) := by
            simpa [word, hselected, SelectedBalancingSegment.pivot] using
              current.pivot_run_to_continuation_right
                transition.policy.offset
          let edge : transition.PivotEdge :=
            { word := word
              target :=
                SelectedBalancingSegment.pivot transition.policy.selected
              run := hrun
              target_matches := by
                rw [transition.next_pivot_eq_policy]
              length_le_unmodified := le_refl _ }
          refine ⟨
            { toPivotEdge := edge
              word_shape := fun _ =>
                Or.inl rfl
              tail_windows_sink := by
                intro _hbound skip hshort hfit
                exact current.direct_tail_windows_sink
                  (fun earlier hearler hbefore =>
                    hgap earlier hearler hbefore)
                  hbound skip hshort
                  (by simpa [edge, word] using hfit)
              tail_windows_rootSink := by
                intro _hbound skip hshort hfit
                exact current.direct_tail_windows_rootSink
                  (fun earlier hearler hbefore =>
                    hgap earlier hearler hbefore)
                  hbound skip hshort
                  (by simpa [edge, word] using hfit)
              tail_repeatedly_root_sinks := by
                intro _hbound depth skip hshort hfit
                exact current.direct_tail_repeatedlyRootSinks
                  (fun earlier hearler hbefore =>
                    hgap earlier hearler hbefore)
                  hbound depth skip hshort
                  (by simpa [edge, word] using hfit)
              tail_repeatedly_sinks := by
                intro _hbound depth skip hshort hfit
                exact current.direct_tail_repeatedlySinks
                  (fun earlier hearler hbefore =>
                    hgap earlier hearler hbefore)
                  hbound depth skip hshort
                  (by simpa [edge, word] using hfit) }⟩
      | right nextSegment =>
          let row := current.structured.family.row i
          have hcutNext : cut ≤ transition.policy.offset :=
            hcut.trans hclose
          obtain ⟨reached, hrun, hreached⟩ :=
            row.exists_run_modifiedBridge
              hg current.pivot_ground current.continuationPath
              (groundPairCode_of_pair_derivable
                current.target.derivation)
              hcutNext hmatch
          let word :=
            row.modifiedBridge current.continuationPath cut
              transition.policy.offset
          have hpivot :
              SelectedBalancingSegment.pivot
                  transition.policy.selected =
                current.continuationPath.left
                  transition.policy.offset := by
            simp [hselected, SelectedBalancingSegment.pivot]
          let edge : transition.PivotEdge :=
            { word := word
              target := reached
              run := by simpa [word] using hrun
              target_matches := by
                rw [transition.next_pivot_eq_policy, hpivot]
                exact hreached
              length_le_unmodified := by
                exact Nat.le_of_lt
                  (row.modifiedBridge_length_lt
                    current.continuationPath hcutNext) }
          refine ⟨
            { toPivotEdge := edge
              word_shape := fun _ =>
                Or.inr ⟨i, cut, hcutNext, rfl⟩
              tail_windows_sink := by
                intro _hbound skip hshort hfit
                exact current.switched_tail_windows_sink i hcut hclose
                  hmatch
                  (fun earlier hearler hbefore =>
                    hgap earlier hearler hbefore)
                  skip hshort (by
                    simpa [edge, word, row] using hfit)
              tail_windows_rootSink := by
                intro _hbound skip hshort hfit
                exact current.switched_tail_windows_rootSink i hcut hclose
                  hmatch
                  (fun earlier hearler hbefore =>
                    hgap earlier hearler hbefore)
                  skip hshort (by
                    simpa [edge, word, row] using hfit)
              tail_repeatedly_root_sinks := by
                intro _hbound depth skip hshort hfit
                exact current.switched_tail_repeatedlyRootSinks
                  i hcut hclose hmatch
                  (fun earlier hearler hbefore =>
                    hgap earlier hearler hbefore)
                  depth skip hshort (by
                    simpa [edge, word, row] using hfit)
              tail_repeatedly_sinks := by
                intro _hbound depth skip hshort hfit
                exact current.switched_tail_repeatedlySinks i hcut hclose
                  hmatch
                  (fun earlier hearler hbefore =>
                    hgap earlier hearler hbefore)
                  depth skip hshort (by
                    simpa [edge, word, row] using hfit) }⟩
  · obtain ⟨edge⟩ := transition.exists_pivotEdge
    exact ⟨
      { toPivotEdge := edge
        word_shape := fun hpositive =>
          False.elim (hbound hpositive)
        tail_windows_sink := by
          intro hpositive
          exact False.elim (hbound hpositive)
        tail_windows_rootSink := by
          intro hpositive
          exact False.elim (hbound hpositive)
        tail_repeatedly_root_sinks := by
          intro hpositive
          exact False.elim (hbound hpositive)
        tail_repeatedly_sinks := by
          intro hpositive
          exact False.elim (hbound hpositive) }⟩

namespace WindowedPivotEdge

/-- A successor-exposing ordinary word cannot be empty: the source template
has an application root, whereas the exposed target has a variable root. -/
private theorem exposesSuccessor_word_nonempty
    {g : EncodedFirstOrderGrammar Action}
    {position : g.SuccessorPosition} {word : List Action}
    (hexposes : g.ExposesSuccessor position word) :
    word ≠ [] := by
  intro hnil
  subst word
  obtain ⟨target, hrun, htarget⟩ := hexposes
  simp [runActions?] at hrun
  subst target
  have hvariableRoot :
      (RegularTerm.symbolTemplate position.1
          (g.ranks.get position.1)).rootNode? =
        some (.inl position.2) :=
    rootNode?_variable_of_unfoldingEquivalent
      htarget.symm
      (RegularTerm.variableTerm_rootNode? position.2)
  have happlicationRoot :=
    RegularTerm.symbolTemplate_rootApplication?
      position.1 (g.ranks.get position.1)
  have happlicationRootNode :
      (RegularTerm.symbolTemplate position.1
          (g.ranks.get position.1)).rootNode? =
        some (.inr
          (position.1,
            (List.range (g.ranks.get position.1)).map
              (fun i => i + 1))) := by
    simpa [RegularTerm.rootNode?] using
      RegularTerm.nodeAt?_root_of_rootApplication?
        happlicationRoot
  rw [hvariableRoot] at happlicationRootNode
  simp at happlicationRootNode

/-- Every strong pivot edge makes genuine progress.  In the direct branch
its first path segment has the positive balancing length; in the switched
branch its first component is a nonempty successor-exposing word. -/
public theorem word_nonempty
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    {current : StructuredDerivedBalancingStep
      hg hground hinitial source bound}
    {transition : StructuredPivotPolicyTransition
      hg hground hinitial current}
    (edge : transition.WindowedPivotEdge)
    (hbound : 0 < bound) :
    edge.toPivotEdge.word ≠ [] := by
  rcases edge.word_shape hbound with hdirect | hswitched
  · rw [hdirect]
    apply List.append_ne_nil_of_left_ne_nil
    apply List.ne_nil_of_length_pos
    simpa using hbound
  · obtain ⟨i, cut, _hcut, hedge⟩ := hswitched
    rw [hedge]
    unfold BalancingSegment.ExposedSuccessorResult.modifiedBridge
    apply List.append_ne_nil_of_left_ne_nil
    intro hword
    have hrowWord : (current.structured.family.row i).word = [] := by
      simpa using hword
    obtain ⟨position, hexposes⟩ :=
      (current.structured.family.row i).word_exposes
    exact exposesSuccessor_word_nonempty hexposes hrowWord

/-- The tail-window guarantee transports to every ground representative of
the selected pivot, using the same concrete edge word. -/
public theorem tail_windows_rootSink_of_equivalent
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    {current : StructuredDerivedBalancingStep
      hg hground hinitial source bound}
    {transition : StructuredPivotPolicyTransition
      hg hground hinitial current}
    (edge : transition.WindowedPivotEdge)
    {representative : RegularTerm}
    (hrepresentative : representative.Ground g.ranks)
    (hmatches :
      representative.UnfoldingEquivalent
        (SelectedBalancingSegment.pivot current.selected))
    (hbound : 0 < bound)
    (skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit : skip + bound ≤ edge.toPivotEdge.word.length) :
    ∃ intermediate,
      g.run? (edge.toPivotEdge.word.take skip) representative =
        some intermediate ∧
      g.RootSinksBy intermediate
        ((edge.toPivotEdge.word.drop skip).take bound) := by
  obtain ⟨pivotIntermediate, hpivotRun, hpivotSinks⟩ :=
    edge.tail_windows_rootSink hbound skip hshort hfit
  obtain ⟨intermediate, hintermediateRun, hintermediateMatches⟩ :=
    exists_run_of_unfoldingEquivalent hg hmatches
      (RegularTerm.referenceClosed_of_ground hrepresentative)
      (RegularTerm.referenceClosed_of_ground current.pivot_ground)
      hpivotRun
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hintermediateGround : intermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run hrepresentative hintermediateRun
  have hpivotIntermediateGround : pivotIntermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run current.pivot_ground hpivotRun
  exact ⟨intermediate, hintermediateRun,
    hpivotSinks.of_unfoldingEquivalent
      hintermediateMatches.symm⟩

/-- Semantic projection of the transported root-window witness. -/
public theorem tail_windows_sink_of_equivalent
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    {current : StructuredDerivedBalancingStep
      hg hground hinitial source bound}
    {transition : StructuredPivotPolicyTransition
      hg hground hinitial current}
    (edge : transition.WindowedPivotEdge)
    {representative : RegularTerm}
    (hrepresentative : representative.Ground g.ranks)
    (hmatches :
      representative.UnfoldingEquivalent
        (SelectedBalancingSegment.pivot current.selected))
    (hbound : 0 < bound)
    (skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit : skip + bound ≤ edge.toPivotEdge.word.length) :
    ∃ intermediate,
      g.run? (edge.toPivotEdge.word.take skip) representative =
        some intermediate ∧
      g.SinksBy intermediate
        ((edge.toPivotEdge.word.drop skip).take bound) := by
  obtain ⟨intermediate, hrun, hroot⟩ :=
    edge.tail_windows_rootSink_of_equivalent
      hrepresentative hmatches hbound skip hshort hfit
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hintermediateGround : intermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run hrepresentative hrun
  exact ⟨intermediate, hrun,
    hroot.toSinksBy_of_ground hg hintermediateGround⟩

/-- The repeated root-sinking guarantee transports to every ground
representative of the selected pivot. -/
public theorem tail_repeatedly_root_sinks_of_equivalent
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    {current : StructuredDerivedBalancingStep
      hg hground hinitial source bound}
    {transition : StructuredPivotPolicyTransition
      hg hground hinitial current}
    (edge : transition.WindowedPivotEdge)
    {representative : RegularTerm}
    (hrepresentative : representative.Ground g.ranks)
    (hmatches :
      representative.UnfoldingEquivalent
        (SelectedBalancingSegment.pivot current.selected))
    (hbound : 0 < bound)
    (depth skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + depth * bound ≤ edge.toPivotEdge.word.length) :
    ∃ intermediate,
      g.run? (edge.toPivotEdge.word.take skip) representative =
        some intermediate ∧
      g.RepeatedlyRootSinksBy intermediate
        ((edge.toPivotEdge.word.drop skip).take (depth * bound))
        depth := by
  obtain ⟨pivotIntermediate, hpivotRun, hpivotSinks⟩ :=
    edge.tail_repeatedly_root_sinks
      hbound depth skip hshort hfit
  obtain ⟨intermediate, hintermediateRun, hintermediateMatches⟩ :=
    exists_run_of_unfoldingEquivalent hg hmatches
      (RegularTerm.referenceClosed_of_ground hrepresentative)
      (RegularTerm.referenceClosed_of_ground current.pivot_ground)
      hpivotRun
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hintermediateGround : intermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run hrepresentative hintermediateRun
  have hpivotIntermediateGround : pivotIntermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run current.pivot_ground hpivotRun
  exact ⟨intermediate, hintermediateRun,
    hpivotSinks.of_unfoldingEquivalent hg
      hintermediateGround hpivotIntermediateGround
      hintermediateMatches⟩

/-- The arbitrary-depth repeated-sinking guarantee also transports to every
ground representative. -/
public theorem tail_repeatedly_sinks_of_equivalent
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    {current : StructuredDerivedBalancingStep
      hg hground hinitial source bound}
    {transition : StructuredPivotPolicyTransition
      hg hground hinitial current}
    (edge : transition.WindowedPivotEdge)
    {representative : RegularTerm}
    (hrepresentative : representative.Ground g.ranks)
    (hmatches :
      representative.UnfoldingEquivalent
        (SelectedBalancingSegment.pivot current.selected))
    (hbound : 0 < bound)
    (depth skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + depth * bound ≤ edge.toPivotEdge.word.length) :
    ∃ intermediate,
      g.run? (edge.toPivotEdge.word.take skip) representative =
        some intermediate ∧
      g.RepeatedlySinksBy intermediate
        ((edge.toPivotEdge.word.drop skip).take (depth * bound))
        depth := by
  obtain ⟨pivotIntermediate, hpivotRun, hpivotSinks⟩ :=
    edge.tail_repeatedly_sinks hbound depth skip hshort hfit
  obtain ⟨intermediate, hintermediateRun, hintermediateMatches⟩ :=
    exists_run_of_unfoldingEquivalent hg hmatches
      (RegularTerm.referenceClosed_of_ground hrepresentative)
      (RegularTerm.referenceClosed_of_ground current.pivot_ground)
      hpivotRun
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hintermediateGround : intermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run hrepresentative hintermediateRun
  have hpivotIntermediateGround : pivotIntermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run current.pivot_ground hpivotRun
  exact ⟨intermediate, hintermediateRun,
    hpivotSinks.of_unfoldingEquivalent hg
      hintermediateGround hpivotIntermediateGround
      hintermediateMatches⟩

end WindowedPivotEdge

end StructuredPivotPolicyTransition

namespace StructuredPivotChain

/-- A fixed strong edge chosen at every structured chain index. -/
public noncomputable def chosenWindowedPivotEdge
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) :
    (chain.transitions j).WindowedPivotEdge :=
  Classical.choice
    (chain.transitions j).exists_windowedPivotEdge

/-- Transport a chosen strong edge to the representative reached by its
predecessor. -/
public noncomputable def nextWindowedPivotRepresentative
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) (current : chain.PivotRepresentativeAt j) :
    chain.PivotRepresentativeAt (j + 1) := by
  let edge := (chain.chosenWindowedPivotEdge j).toPivotEdge
  have hpivotGround : (chain.pivot j).Ground g.ranks :=
    (chain.states j).incoming.pivot_ground
  have htransport :=
    exists_run_of_unfoldingEquivalent hg current.equivalent
      (RegularTerm.referenceClosed_of_ground current.ground)
      (RegularTerm.referenceClosed_of_ground hpivotGround)
      edge.run
  let target := Classical.choose htransport
  have hrun := (Classical.choose_spec htransport).1
  have htarget := (Classical.choose_spec htransport).2
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact
    { term := target
      ground := hgroundSteps.ground_of_run current.ground hrun
      equivalent := by
        rw [← chain.transition_next_pivot_eq j]
        exact htarget.trans edge.target_matches }

/-- The transported strong edge executes exactly to its chosen successor
representative. -/
public theorem nextWindowedPivotRepresentative_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) (current : chain.PivotRepresentativeAt j) :
    g.run? (chain.chosenWindowedPivotEdge j).toPivotEdge.word
        current.term =
      some (chain.nextWindowedPivotRepresentative j current).term := by
  unfold nextWindowedPivotRepresentative
  exact (Classical.choose_spec
    (exists_run_of_unfoldingEquivalent hg current.equivalent
      (RegularTerm.referenceClosed_of_ground current.ground)
      (RegularTerm.referenceClosed_of_ground
        (chain.states j).incoming.pivot_ground)
      (chain.chosenWindowedPivotEdge j).toPivotEdge.run)).1

/-- Representatives generated by the strong edge choices. -/
public noncomputable def windowedPivotRepresentatives
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial) :
    ∀ j, chain.PivotRepresentativeAt j
  | 0 =>
      { term := chain.pivot 0
        ground := (chain.states 0).incoming.pivot_ground
        equivalent := RegularTerm.unfoldingEquivalent_refl _ }
  | j + 1 =>
      chain.nextWindowedPivotRepresentative j
        (chain.windowedPivotRepresentatives j)

/-- A pivot trajectory whose concrete edge choices retain the uniform
tail-window sinking theorem. -/
public structure WindowedPivotTrajectory
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hg : g.WellFormed)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (bound : ℕ)
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial) where
  toPivotTrajectory : chain.PivotTrajectory
  tail_windows_sink :
    0 < bound →
      ∀ j skip,
        g.structuredPivotShortPrefixBound bound ≤ skip →
        skip + bound ≤ (toPivotTrajectory.edgeWords j).length →
        ∃ intermediate,
          g.run? ((toPivotTrajectory.edgeWords j).take skip)
              (toPivotTrajectory.representatives j) =
            some intermediate ∧
          g.SinksBy intermediate
            (((toPivotTrajectory.edgeWords j).drop skip).take bound)
  tail_windows_rootSink :
    0 < bound →
      ∀ j skip,
        g.structuredPivotShortPrefixBound bound ≤ skip →
        skip + bound ≤ (toPivotTrajectory.edgeWords j).length →
        ∃ intermediate,
          g.run? ((toPivotTrajectory.edgeWords j).take skip)
              (toPivotTrajectory.representatives j) =
            some intermediate ∧
          g.RootSinksBy intermediate
            (((toPivotTrajectory.edgeWords j).drop skip).take bound)
  tail_repeatedly_root_sinks :
    0 < bound →
      ∀ j depth skip,
        g.structuredPivotShortPrefixBound bound ≤ skip →
        skip + depth * bound ≤
          (toPivotTrajectory.edgeWords j).length →
        ∃ intermediate,
          g.run? ((toPivotTrajectory.edgeWords j).take skip)
              (toPivotTrajectory.representatives j) =
            some intermediate ∧
          g.RepeatedlyRootSinksBy intermediate
            (((toPivotTrajectory.edgeWords j).drop skip).take
              (depth * bound))
            depth
  tail_repeatedly_sinks :
    0 < bound →
      ∀ j depth skip,
        g.structuredPivotShortPrefixBound bound ≤ skip →
        skip + depth * bound ≤
          (toPivotTrajectory.edgeWords j).length →
        ∃ intermediate,
          g.run? ((toPivotTrajectory.edgeWords j).take skip)
              (toPivotTrajectory.representatives j) =
            some intermediate ∧
          g.RepeatedlySinksBy intermediate
            (((toPivotTrajectory.edgeWords j).drop skip).take
              (depth * bound))
            depth

/-- Every structured chain admits a representative trajectory carrying the
strong edge theorem. -/
public noncomputable def toWindowedPivotTrajectory
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial) :
    WindowedPivotTrajectory hg hground hinitial bound chain := by
  let representatives :=
    fun j => (chain.windowedPivotRepresentatives j).term
  let edgeWords :=
    fun j => (chain.chosenWindowedPivotEdge j).toPivotEdge.word
  let trajectory : chain.PivotTrajectory :=
    { representatives := representatives
      representative_ground := fun j =>
        (chain.windowedPivotRepresentatives j).ground
      representative_matches := fun j =>
        (chain.windowedPivotRepresentatives j).equivalent
      edgeWords := edgeWords
      edge_run := by
        intro j
        change
          g.run? (chain.chosenWindowedPivotEdge j).toPivotEdge.word
              (chain.windowedPivotRepresentatives j).term =
            some (chain.windowedPivotRepresentatives (j + 1)).term
        rw [windowedPivotRepresentatives]
        exact chain.nextWindowedPivotRepresentative_run j
          (chain.windowedPivotRepresentatives j)
      edge_length_le := fun j =>
        (chain.chosenWindowedPivotEdge j)
          |>.toPivotEdge.length_le_unmodified }
  exact
    { toPivotTrajectory := trajectory
      tail_windows_sink := by
        intro hbound j skip hshort hfit
        exact (chain.chosenWindowedPivotEdge j)
          |>.tail_windows_sink_of_equivalent
            (chain.windowedPivotRepresentatives j).ground
            (chain.windowedPivotRepresentatives j).equivalent
            hbound skip hshort (by
              simpa [trajectory, edgeWords] using hfit)
      tail_windows_rootSink := by
        intro hbound j skip hshort hfit
        exact (chain.chosenWindowedPivotEdge j)
          |>.tail_windows_rootSink_of_equivalent
            (chain.windowedPivotRepresentatives j).ground
            (chain.windowedPivotRepresentatives j).equivalent
            hbound skip hshort (by
              simpa [trajectory, edgeWords] using hfit)
      tail_repeatedly_root_sinks := by
        intro hbound j depth skip hshort hfit
        exact (chain.chosenWindowedPivotEdge j)
          |>.tail_repeatedly_root_sinks_of_equivalent
            (chain.windowedPivotRepresentatives j).ground
            (chain.windowedPivotRepresentatives j).equivalent
            hbound depth skip hshort (by
              simpa [trajectory, edgeWords] using hfit)
      tail_repeatedly_sinks := by
        intro hbound j depth skip hshort hfit
        exact (chain.chosenWindowedPivotEdge j)
          |>.tail_repeatedly_sinks_of_equivalent
            (chain.windowedPivotRepresentatives j).ground
            (chain.windowedPivotRepresentatives j).equivalent
            hbound depth skip hshort (by
              simpa [trajectory, edgeWords] using hfit) }

namespace WindowedPivotTrajectory

/-- One concrete position inside a chosen pivot edge. -/
public structure EdgePosition
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
    (j : ℕ) where
  offset : ℕ
  offset_le :
    offset ≤ (trajectory.toPivotTrajectory.edgeWords j).length
  term : RegularTerm
  run :
    g.run? ((trajectory.toPivotTrajectory.edgeWords j).take offset)
        (trajectory.toPivotTrajectory.representatives j) =
      some term

namespace EdgePosition

/-- Every state reached inside a strong edge is ground. -/
public theorem ground
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
    {trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain}
    {j : ℕ} (position : trajectory.EdgePosition j) :
    position.term.Ground g.ranks := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact hgroundSteps.ground_of_run
    (trajectory.toPivotTrajectory.representative_ground j) position.run

end EdgePosition

/-- Starting anywhere inside an edge, an `M₂`-sized budget either reaches
the next pivot representative or contains, after a uniformly short prelude,
the requested number of consecutive sinking blocks.

This is the purely operational window lemma.  Turning the second branch into
`SinksBy position.term ...` is exactly the finite-prefix `B-Inc` reflection
step of Proposition 49. -/
public theorem edgePosition_reachesPivot_or_repeatedlyRootSinks
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
    (depth j : ℕ)
    (position : trajectory.EdgePosition j) :
    (∃ word,
        word =
          (trajectory.toPivotTrajectory.edgeWords j).drop
            position.offset ∧
        word.length ≤ g.structuredPivotM2Window bound depth ∧
        g.run? word position.term =
          some (trajectory.toPivotTrajectory.representatives (j + 1))) ∨
      ∃ prelude sinkingWord remainder intermediate,
        (trajectory.toPivotTrajectory.edgeWords j).drop position.offset =
          prelude ++ sinkingWord ++ remainder ∧
        prelude.length ≤ g.structuredPivotShortPrefixBound bound ∧
        g.run? prelude position.term = some intermediate ∧
        g.RepeatedlyRootSinksBy intermediate sinkingWord depth ∧
        sinkingWord.length = depth * bound := by
  let edge := trajectory.toPivotTrajectory.edgeWords j
  let short := g.structuredPivotShortPrefixBound bound
  let window := g.structuredPivotM2Window bound depth
  by_cases hpivot : edge.length - position.offset ≤ window
  · left
    refine ⟨edge.drop position.offset, rfl, ?_, ?_⟩
    · simpa [List.length_drop, edge, window] using hpivot
    · have hsplit :
          edge =
            edge.take position.offset ++ edge.drop position.offset :=
        (List.take_append_drop position.offset edge).symm
      have hedgeRun :=
        trajectory.toPivotTrajectory.edge_run j
      change
        g.run? edge (trajectory.toPivotTrajectory.representatives j) =
          some (trajectory.toPivotTrajectory.representatives (j + 1))
        at hedgeRun
      rw [hsplit, g.run?_append, position.run] at hedgeRun
      exact hedgeRun
  · right
    have hpivot' : window < edge.length - position.offset :=
      Nat.lt_of_not_ge hpivot
    let skip := max position.offset short
    let lead := skip - position.offset
    have hoffsetSkip : position.offset ≤ skip :=
      Nat.le_max_left _ _
    have hshortSkip : short ≤ skip :=
      Nat.le_max_right _ _
    have hskipEq : position.offset + lead = skip := by
      simp [lead, Nat.add_sub_of_le hoffsetSkip]
    have hleadShort : lead ≤ short := by
      simp only [lead, skip]
      omega
    have hfit :
        skip + depth * bound ≤ edge.length := by
      unfold window structuredPivotM2Window at hpivot'
      simp only [skip]
      omega
    obtain ⟨intermediate, hskipRun, hsinks⟩ :=
      trajectory.tail_repeatedly_root_sinks
        hbound j depth skip hshortSkip (by simpa [edge] using hfit)
    let prelude := (edge.drop position.offset).take lead
    let sinkingWord := (edge.drop skip).take (depth * bound)
    let remainder := (edge.drop skip).drop (depth * bound)
    have hpreludeRun :
        g.run? prelude position.term = some intermediate := by
      have htakeAdd :
          edge.take skip =
            edge.take position.offset ++ prelude := by
        rw [← hskipEq, List.take_add]
      rw [htakeAdd, g.run?_append, position.run] at hskipRun
      exact hskipRun
    have hdropSplit :
        edge.drop position.offset =
          prelude ++ edge.drop skip := by
      calc
        edge.drop position.offset =
            prelude ++ (edge.drop position.offset).drop lead := by
          simp [prelude]
        _ = prelude ++ edge.drop skip := by
          rw [List.drop_drop, hskipEq]
    have hsinkingSplit :
        edge.drop skip = sinkingWord ++ remainder := by
      exact (List.take_append_drop (depth * bound)
        (edge.drop skip)).symm
    refine ⟨prelude, sinkingWord, remainder, intermediate, ?_, ?_,
      hpreludeRun, ?_, ?_⟩
    · rw [hdropSplit, hsinkingSplit, List.append_assoc]
    · exact (List.length_take_le _ _).trans hleadShort
    · simpa [sinkingWord, edge] using hsinks
    · have hsinkingFit : depth * bound ≤ (edge.drop skip).length := by
        simp [List.length_drop]
        omega
      change ((edge.drop skip).take (depth * bound)).length =
        depth * bound
      rw [List.length_take, Nat.min_eq_left hsinkingFit]

/-- Semantic projection of the operational repeated root-sinking
dichotomy. -/
public theorem edgePosition_reachesPivot_or_repeatedlySinks
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
    (depth j : ℕ)
    (position : trajectory.EdgePosition j) :
    (∃ word,
        word =
          (trajectory.toPivotTrajectory.edgeWords j).drop
            position.offset ∧
        word.length ≤ g.structuredPivotM2Window bound depth ∧
        g.run? word position.term =
          some (trajectory.toPivotTrajectory.representatives (j + 1))) ∨
      ∃ prelude sinkingWord remainder intermediate,
        (trajectory.toPivotTrajectory.edgeWords j).drop position.offset =
          prelude ++ sinkingWord ++ remainder ∧
        prelude.length ≤ g.structuredPivotShortPrefixBound bound ∧
        g.run? prelude position.term = some intermediate ∧
        g.RepeatedlySinksBy intermediate sinkingWord depth ∧
        sinkingWord.length = depth * bound := by
  rcases trajectory.edgePosition_reachesPivot_or_repeatedlyRootSinks
      hbound depth j position with hpivot | hsinks
  · exact Or.inl hpivot
  · obtain ⟨prelude, sinkingWord, remainder, intermediate,
      hword, hpreludeLength, hpreludeRun, hroot,
      hsinkingLength⟩ := hsinks
    exact Or.inr ⟨prelude, sinkingWord, remainder, intermediate,
      hword, hpreludeLength, hpreludeRun,
      hroot.toRepeatedlySinksBy, hsinkingLength⟩

/-- Root-syntactic Proposition-49 window dichotomy: from every position
inside a pivot edge, a word of length at most the grammar-uniform `M₂`
either reaches the next pivot or root-sinks from the current term. -/
public theorem edgePosition_reachesPivot_or_rootSinks
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
    (position : trajectory.EdgePosition j) :
    (∃ word,
        word =
          (trajectory.toPivotTrajectory.edgeWords j).drop
            position.offset ∧
        word.length ≤ g.structuredPivotM2Bound bound ∧
        g.run? word position.term =
          some (trajectory.toPivotTrajectory.representatives (j + 1))) ∨
      ∃ word remainder,
        (trajectory.toPivotTrajectory.edgeWords j).drop position.offset =
          word ++ remainder ∧
        word.length ≤ g.structuredPivotM2Bound bound ∧
        g.RootSinksBy position.term word := by
  let short := g.structuredPivotShortPrefixBound bound
  let depth := g.structuredPivotSinkDepth short
  have hdichotomy :=
    trajectory.edgePosition_reachesPivot_or_repeatedlyRootSinks
      hbound depth j position
  rcases hdichotomy with hpivot | hsinks
  · left
    obtain ⟨word, hword, hlength, hrun⟩ := hpivot
    exact ⟨word, hword, by
      simpa [structuredPivotM2Bound, short, depth] using hlength,
      hrun⟩
  · right
    obtain ⟨prelude, sinkingWord, remainder, intermediate,
      hword, hpreludeLength, hpreludeRun, hrepeated,
      hsinkingLength⟩ := hsinks
    let word := prelude ++ sinkingWord
    refine ⟨word, remainder, ?_, ?_, ?_⟩
    · simpa [word, List.append_assoc] using hword
    · simp only [word, List.length_append]
      unfold structuredPivotM2Bound structuredPivotM2Window
      simp only [short, depth] at hpreludeLength hsinkingLength ⊢
      omega
    · exact rootSinksBy_append_of_shortPrelude_repeatedlyRootSinks
        hg position.ground short hpreludeLength hpreludeRun
        (by simpa [depth] using hrepeated)

/-- Concrete Proposition-49 window dichotomy: from every position inside a
pivot edge, a word of length at most the grammar-uniform `M₂` either reaches
the next pivot or makes the current term sink. -/
public theorem edgePosition_reachesPivot_or_sinks
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
    (position : trajectory.EdgePosition j) :
    (∃ word,
        word =
          (trajectory.toPivotTrajectory.edgeWords j).drop
            position.offset ∧
        word.length ≤ g.structuredPivotM2Bound bound ∧
        g.run? word position.term =
          some (trajectory.toPivotTrajectory.representatives (j + 1))) ∨
      ∃ word remainder,
        (trajectory.toPivotTrajectory.edgeWords j).drop position.offset =
          word ++ remainder ∧
        word.length ≤ g.structuredPivotM2Bound bound ∧
        g.SinksBy position.term word := by
  let short := g.structuredPivotShortPrefixBound bound
  let depth := g.structuredPivotSinkDepth short
  have hdichotomy :=
    trajectory.edgePosition_reachesPivot_or_repeatedlySinks
      hbound depth j position
  rcases hdichotomy with hpivot | hsinks
  · left
    obtain ⟨word, hword, hlength, hrun⟩ := hpivot
    exact ⟨word, hword, by
      simpa [structuredPivotM2Bound, short, depth] using hlength,
      hrun⟩
  · right
    obtain ⟨prelude, sinkingWord, remainder, intermediate,
      hword, hpreludeLength, hpreludeRun, hrepeated,
      hsinkingLength⟩ := hsinks
    let word := prelude ++ sinkingWord
    refine ⟨word, remainder, ?_, ?_, ?_⟩
    · simpa [word, List.append_assoc] using hword
    · simp only [word, List.length_append]
      unfold structuredPivotM2Bound structuredPivotM2Window
      simp only [short, depth] at hpreludeLength hsinkingLength ⊢
      omega
    · exact sinksBy_append_of_shortPrelude_repeatedlySinks
        hg position.ground short hpreludeLength hpreludeRun
        (by simpa [depth] using hrepeated)

/-- If no prefix of the actual remaining edge suffix sinks from the current
position, that suffix must reach the next pivot within `M₂`. -/
public theorem edgeRemaining_length_le_m2_of_noSinkingPrefix
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
    (hnoSinking : ∀ word remainder,
      (trajectory.toPivotTrajectory.edgeWords j).drop position.offset =
        word ++ remainder →
      ¬g.SinksBy position.term word) :
    ((trajectory.toPivotTrajectory.edgeWords j).drop position.offset).length ≤
      g.structuredPivotM2Bound bound := by
  rcases trajectory.edgePosition_reachesPivot_or_sinks
      hbound j position with hpivot | hsinks
  · obtain ⟨word, hword, hlength, _hrun⟩ := hpivot
    simpa [hword] using hlength
  · obtain ⟨word, remainder, hword, _hlength, hsink⟩ := hsinks
    exact False.elim ((hnoSinking word remainder hword) hsink)

/-- An exact exposing prefix of an accumulated pivot word can be located at
one concrete position inside a single edge.  The returned factorization keeps
the position of the cut, which is needed for cofinality arguments. -/
public theorem exists_pointedEdgePosition_of_exposesAt_prefixWord
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
    {count depth : ℕ}
    {first remainder : List (Label Action)}
    (hprefix :
      trajectory.toPivotTrajectory.prefixWord count =
        first ++ remainder)
    (hexposes :
      g.ExposesAtDepth
        (trajectory.toPivotTrajectory.representatives 0)
        first depth) :
    ∃ j, ∃ position : trajectory.EdgePosition j,
      ∃ source ∈
          (trajectory.toPivotTrajectory.representatives 0).pointedSubterms,
        source.Ground g.ranks ∧
          position.term.UnfoldingEquivalent source ∧
          first =
            trajectory.toPivotTrajectory.prefixWord j ++
              (trajectory.toPivotTrajectory.edgeWords j).take
                position.offset := by
  obtain ⟨subterm, target, hsubterm, hrun, htarget⟩ := hexposes
  obtain ⟨next, localizedRemainder, hlocalized, hshape⟩ :=
    trajectory.toPivotTrajectory.exists_endpoint_cut hprefix
  have hbaseClosed :
      (trajectory.toPivotTrajectory.representatives 0).ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground
      (trajectory.toPivotTrajectory.representative_ground 0)
  have hsource :
      subterm ∈
        (trajectory.toPivotTrajectory.representatives 0).pointedSubterms :=
    hsubterm.mem_pointedSubterms hbaseClosed
  have hsourceGround : subterm.Ground g.ranks :=
    (trajectory.toPivotTrajectory.representative_ground 0)
      |>.subtermAtDepth hsubterm
  rcases hshape with hfinished | hinside
  · subst localizedRemainder
    have hfirst :
        trajectory.toPivotTrajectory.prefixWord next = first := by
      simpa using hlocalized
    have hpivotRun :=
      trajectory.toPivotTrajectory.prefixWord_run next
    rw [hfirst] at hpivotRun
    have htargetEq :
        target =
          trajectory.toPivotTrajectory.representatives next :=
      Option.some.inj (hrun.symm.trans hpivotRun)
    subst target
    let position : trajectory.EdgePosition next :=
      { offset := 0
        offset_le := Nat.zero_le _
        term := trajectory.toPivotTrajectory.representatives next
        run := by simp }
    exact ⟨next, position, subterm, hsource, hsourceGround,
      htarget, by
        simpa [position] using hfirst.symm⟩
  · obtain ⟨j, offset, _hnext, hoffset, hfirst,
        _hremainder⟩ := hinside
    have hpositionRun :
        g.run?
            ((trajectory.toPivotTrajectory.edgeWords j).take offset)
            (trajectory.toPivotTrajectory.representatives j) =
          some target := by
      rw [hfirst, g.run?_append,
        trajectory.toPivotTrajectory.prefixWord_run] at hrun
      exact hrun
    let position : trajectory.EdgePosition j :=
      { offset := offset
        offset_le := hoffset
        term := target
        run := hpositionRun }
    exact ⟨j, position, subterm, hsource, hsourceGround,
      htarget, by
        simpa [position] using hfirst⟩

/-- An exposure witnessed by an accumulated pivot word can be located at one
concrete position inside a single edge.  Its reached state is, up to
unfolding, one of the finitely many pointed presentations of the initial
pivot representative. -/
public theorem exists_pointedEdgePosition_of_exposesBy_prefixWord
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
    {count depth : ℕ}
    (hexposes :
      g.ExposesBy (trajectory.toPivotTrajectory.representatives 0)
        (trajectory.toPivotTrajectory.prefixWord count) depth) :
    ∃ j, ∃ position : trajectory.EdgePosition j,
      ∃ source ∈
          (trajectory.toPivotTrajectory.representatives 0).pointedSubterms,
        source.Ground g.ranks ∧
          position.term.UnfoldingEquivalent source := by
  obtain ⟨first, remainder, hprefix, hexact⟩ := hexposes
  obtain ⟨j, position, source, hsource, hsourceGround, hequivalent,
      _hfirst⟩ :=
    trajectory.exists_pointedEdgePosition_of_exposesAt_prefixWord
      hprefix hexact
  exact ⟨j, position, source, hsource, hsourceGround, hequivalent⟩

/-- Starting from a state which presents a pointed subterm of one fixed
finite base, repeated sinking inside the current edge must eventually leave a
pointed subterm from which the next pivot is reachable within `M₂`.

The proof is a strong induction on the unconsumed edge length.  Every sinking
branch selects its exact nonempty exposing prefix, moves the edge position
forward by that prefix, and points one level further into the same base
graph. -/
public theorem edgePosition_exists_boundedPivot_of_pointed
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight base : RegularTerm}
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
    (hbase : base.Ground g.ranks)
    (j : ℕ)
    (position : trajectory.EdgePosition j)
    (source : RegularTerm)
    (hsource : source ∈ base.pointedSubterms)
    (hsourceGround : source.Ground g.ranks)
    (hequivalent : position.term.UnfoldingEquivalent source) :
    ∃ finalSource ∈ base.pointedSubterms,
      finalSource.Ground g.ranks ∧
      ∃ labels reached,
        labels.length ≤ g.structuredPivotM2Bound bound ∧
        g.run? labels finalSource = some reached ∧
        RegularTerm.UnfoldingEquivalent
          (trajectory.toPivotTrajectory.representatives (j + 1))
          reached := by
  let edge := trajectory.toPivotTrajectory.edgeWords j
  have hbaseClosed : base.ReferenceClosed :=
    RegularTerm.referenceClosed_of_ground hbase
  have solve :
      ∀ remaining,
        ∀ (current : trajectory.EdgePosition j)
          (currentSource : RegularTerm),
          currentSource ∈ base.pointedSubterms →
          currentSource.Ground g.ranks →
          current.term.UnfoldingEquivalent currentSource →
          edge.length - current.offset = remaining →
          ∃ finalSource ∈ base.pointedSubterms,
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
        intro current currentSource hcurrentSource hcurrentSourceGround
          hcurrentEquivalent hremaining
        rcases trajectory.edgePosition_reachesPivot_or_sinks
            hbound j current with hpivot | hsinks
        · obtain ⟨labels, _hlabels, hlength, hrun⟩ := hpivot
          have hcurrentSourceClosed :
              currentSource.ReferenceClosed :=
            RegularTerm.referenceClosed_of_mem_pointedSubterms
              hbaseClosed hcurrentSource
          obtain ⟨reached, hreachedRun, hreachedEquivalent⟩ :=
            exists_run_of_unfoldingEquivalent hg
              hcurrentEquivalent.symm
              hcurrentSourceClosed
              (RegularTerm.referenceClosed_of_ground current.ground)
              hrun
          exact ⟨currentSource, hcurrentSource, hcurrentSourceGround,
            labels, reached,
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
          have hcurrentSourceClosed :
              currentSource.ReferenceClosed :=
            RegularTerm.referenceClosed_of_mem_pointedSubterms
              hbaseClosed hcurrentSource
          have hnextNested :
              nestedSource ∈ currentSource.pointedSubterms :=
            hnestedSource.mem_pointedSubterms hcurrentSourceClosed
          have hnextSource :
              nestedSource ∈ base.pointedSubterms :=
            RegularTerm.mem_pointedSubterms_trans
              hcurrentSource hnextNested
          have hnextSourceGround : nestedSource.Ground g.ranks :=
            hcurrentSourceGround.subtermAtDepth hnestedSource
          have hnextEquivalent :
              next.term.UnfoldingEquivalent nestedSource :=
            step.target_matches.trans
              hsubtermEquivalent
          have hstemPositive : 0 < stem.length :=
            List.length_pos_iff.mpr step.word_nonempty
          have hnextRemaining :
              edge.length - next.offset < remaining := by
            change
              edge.length - (current.offset + stem.length) < remaining
            rw [← hremaining]
            omega
          exact ih (edge.length - next.offset) hnextRemaining
            next nestedSource hnextSource hnextSourceGround
              hnextEquivalent rfl
  exact solve (edge.length - position.offset)
    position source hsource hsourceGround hequivalent rfl

/-- Every exposure by an accumulated trajectory word yields some following
pivot in the fixed finite `M₂`-neighbourhood of the initial pivot graph. -/
public theorem exists_boundedPivot_of_exposesBy_prefixWord
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
    {count depth : ℕ}
    (hexposes :
      g.ExposesBy (trajectory.toPivotTrajectory.representatives 0)
        (trajectory.toPivotTrajectory.prefixWord count) depth) :
    ∃ j, ∃ source ∈
        (trajectory.toPivotTrajectory.representatives 0).pointedSubterms,
      source.Ground g.ranks ∧
      ∃ labels reached,
        labels.length ≤ g.structuredPivotM2Bound bound ∧
        g.run? labels source = some reached ∧
        RegularTerm.UnfoldingEquivalent
          (trajectory.toPivotTrajectory.representatives (j + 1))
          reached := by
  obtain ⟨j, position, source, hsource, hsourceGround,
      hequivalent⟩ :=
    trajectory.exists_pointedEdgePosition_of_exposesBy_prefixWord
      hexposes
  obtain ⟨finalSource, hfinalSource, hfinalSourceGround,
      labels, reached,
      hlength, hrun, hreached⟩ :=
    trajectory.edgePosition_exists_boundedPivot_of_pointed
      hbound
      (trajectory.toPivotTrajectory.representative_ground 0)
      j position source hsource hsourceGround hequivalent
  exact ⟨j, finalSource, hfinalSource, hfinalSourceGround,
    labels, reached,
    hlength, hrun, hreached⟩

/-- Unbounded progress-making exposure gives cofinally many pivots in one
fixed finite `M₂`-neighbourhood of the initial pivot graph.

The progress hypothesis is stated with `RepeatedlySinksBy`, so the exact
exposing prefix has length at least its depth.  Choosing that depth above the
length of every edge through `threshold` forces the localized exposure
position into a strictly later edge. -/
public theorem cofinally_boundedPivots_of_unboundedRepeatedSinking
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
    (hunbounded : ∀ depthBound,
      ∃ count depth,
        depthBound < depth ∧
        g.RepeatedlySinksBy
          (trajectory.toPivotTrajectory.representatives 0)
          (trajectory.toPivotTrajectory.prefixWord count)
          depth) :
    ∀ threshold, ∃ j,
      threshold < j ∧
      ∃ source ∈
          (trajectory.toPivotTrajectory.representatives 0).pointedSubterms,
        source.Ground g.ranks ∧
        ∃ labels reached,
          labels.length ≤ g.structuredPivotM2Bound bound ∧
          g.run? labels source = some reached ∧
          RegularTerm.UnfoldingEquivalent
            (trajectory.toPivotTrajectory.representatives (j + 1))
            reached := by
  intro threshold
  obtain ⟨count, depth, hdepth, hsinks⟩ :=
    hunbounded
      (trajectory.toPivotTrajectory.prefixWord
        (threshold + 1)).length
  obtain ⟨first, remainder, hprefix, hfirstLength, hexposes⟩ :=
    hsinks.exists_exposingPrefix
  obtain ⟨j, position, source, hsource, hsourceGround, hequivalent,
      hfirst⟩ :=
    trajectory.exists_pointedEdgePosition_of_exposesAt_prefixWord
      hprefix hexposes
  have hj : threshold < j := by
    by_contra hnot
    have hjle : j ≤ threshold := Nat.le_of_not_gt hnot
    have hfirstLeNext :
        first.length ≤
          (trajectory.toPivotTrajectory.prefixWord (j + 1)).length := by
      rw [hfirst, TracePath.StructuredPivotChain.PivotTrajectory.prefixWord]
      simp only [List.length_append]
      exact Nat.add_le_add_left
        (by
          simp only [List.length_take]
          exact Nat.min_le_right _ _)
        (trajectory.toPivotTrajectory.prefixWord j).length
    let gap := threshold + 1 - (j + 1)
    have hindex : j + 1 + gap = threshold + 1 := by
      simp only [gap]
      omega
    have hpref :=
      trajectory.toPivotTrajectory.prefixWord_add (j + 1) gap
    rw [hindex] at hpref
    have hprefixLengths := congrArg List.length hpref
    simp only [List.length_append] at hprefixLengths
    have hnextLe :
        (trajectory.toPivotTrajectory.prefixWord (j + 1)).length ≤
          (trajectory.toPivotTrajectory.prefixWord
            (threshold + 1)).length := by
      omega
    omega
  obtain ⟨finalSource, hfinalSource, hfinalSourceGround,
      labels, reached,
      hlength, hrun, hreached⟩ :=
    trajectory.edgePosition_exists_boundedPivot_of_pointed
      hbound
      (trajectory.toPivotTrajectory.representative_ground 0)
      j position source hsource hsourceGround hequivalent
  exact ⟨j, hj, finalSource, hfinalSource, hfinalSourceGround,
    labels, reached,
    hlength, hrun, hreached⟩

/-- The cofinal bounded-pivot theorem can be packaged as a strictly
increasing subsequence whose representatives all lie, up to unfolding, in
one fixed finite reachability list. -/
public theorem exists_pivotFiniteCover_of_unboundedRepeatedSinking
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
    (hunbounded : ∀ depthBound,
      ∃ count depth,
        depthBound < depth ∧
        g.RepeatedlySinksBy
          (trajectory.toPivotTrajectory.representatives 0)
          (trajectory.toPivotTrajectory.prefixWord count)
          depth) :
    ∃ indices : ℕ → ℕ,
      StrictMono indices ∧
      ∀ n, ∃ representative ∈
          g.reachableWithin (g.structuredPivotM2Bound bound)
            ((trajectory.toPivotTrajectory.representatives 0)
              |>.pointedSubterms),
        representative.Ground g.ranks ∧
          RegularTerm.UnfoldingEquivalent
            (trajectory.toPivotTrajectory.representatives (indices n))
            representative := by
  classical
  let cover :=
    g.reachableWithin (g.structuredPivotM2Bound bound)
      (trajectory.toPivotTrajectory.representatives 0).pointedSubterms
  have hcofinal : ∀ threshold, ∃ index,
      threshold < index ∧
        ∃ representative ∈ cover,
          representative.Ground g.ranks ∧
            RegularTerm.UnfoldingEquivalent
              (trajectory.toPivotTrajectory.representatives index)
              representative := by
    intro threshold
    obtain ⟨j, hj, source, hsource, hsourceGround,
        labels, reached,
        hlength, hrun, hreached⟩ :=
      trajectory.cofinally_boundedPivots_of_unboundedRepeatedSinking
        hbound hunbounded threshold
    have hrepresentative :
        reached ∈
          g.reachableWithin (g.structuredPivotM2Bound bound)
            ((trajectory.toPivotTrajectory.representatives 0)
              |>.pointedSubterms) :=
      mem_reachableWithin_of_run hsource hlength hrun
    let hgroundSteps : g.PreservesGroundSteps :=
      preservesGroundSteps_of_wellFormed hg
    have hrepresentativeGround : reached.Ground g.ranks :=
      hgroundSteps.ground_of_run hsourceGround hrun
    exact ⟨j + 1, hj.trans (Nat.lt_succ_self j),
      reached, by simpa [cover] using hrepresentative,
      hrepresentativeGround, hreached⟩
  let next : ℕ → ℕ :=
    fun threshold => Classical.choose (hcofinal threshold)
  have hnext : ∀ threshold,
      threshold < next threshold ∧
        ∃ representative ∈ cover,
          representative.Ground g.ranks ∧
            RegularTerm.UnfoldingEquivalent
              (trajectory.toPivotTrajectory.representatives
                (next threshold))
              representative :=
    fun threshold => Classical.choose_spec (hcofinal threshold)
  let indices : ℕ → ℕ :=
    fun n => Nat.rec (next 0)
      (fun _ previous => next previous) n
  have hindicesStep : ∀ n, indices n < indices (n + 1) := by
    intro n
    simpa [indices] using (hnext (indices n)).1
  refine ⟨indices, strictMono_nat_of_lt_succ hindicesStep, ?_⟩
  intro n
  cases n with
  | zero =>
      simpa [indices, cover] using (hnext 0).2
  | succ n =>
      simpa [indices, cover] using (hnext (indices n)).2

/-- Observation 46(1), in the form needed by the `M₂` branch: a strictly
increasing structured-pivot subsequence with representatives in one fixed
finite semantic cover forces a derived repeat.

For every finite representative we take its depth-`bound` prefix
presentation, reconstruct the corresponding Proposition-45 balancing result,
and widen it to one grammar-uniform arity and presentation bound.  The
resulting argument tuples range over the image of the supplied finite pivot
cover, so the existing finite-argument pigeonhole theorem applies. -/
public theorem hasDerivedRepeat_of_pivotFiniteCover
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain
      hg hground hinitial bound initial)
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (indices : ℕ → ℕ)
    (hindices : StrictMono indices)
    (pivotRepresentatives : ℕ → RegularTerm)
    (pivotCover : List RegularTerm)
    (hpivotMem : ∀ n, pivotRepresentatives n ∈ pivotCover)
    (hpivotGround : ∀ n,
      (pivotRepresentatives n).Ground g.ranks)
    (hpivotEquivalent : ∀ n,
      (trajectory.toPivotTrajectory.representatives (indices n))
        |>.UnfoldingEquivalent (pivotRepresentatives n)) :
    path.HasDerivedRepeat := by
  classical
  let filler := trajectory.toPivotTrajectory.representatives 0
  let targetArity := g.fixedTailArityBound bound
  let schemaBound :=
    FiniteHead.compiledDepthBound (g.ranks.foldr max 0) bound
  let targetBound :=
    g.fixedBalancingPresentationBound
      bound targetArity schemaBound
  let sourceArguments : ℕ → List RegularTerm :=
    fun n =>
      ((pivotRepresentatives n).depthPrefix bound)
        |>.paddedArguments g.ranks filler
  let arguments : ℕ → List RegularTerm :=
    fun n =>
      RegularTerm.padInactiveArguments
        (sourceArguments n) filler targetArity
  let argumentTupleOf : RegularTerm → List RegularTerm :=
    fun representative =>
      RegularTerm.padInactiveArguments
        ((representative.depthPrefix bound)
          |>.paddedArguments g.ranks filler)
        filler targetArity
  let argumentTuples : List (List RegularTerm) :=
    pivotCover.map argumentTupleOf
  let levels : ℕ → ℕ :=
    fun n => chain.levels (indices n)
  have hbound : 0 < bound :=
    (g.exposureBound_pos hnormal).trans_le hexposureBound
  have hlevels : StrictMono levels :=
    (chain.levels_strictMono hbound).comp hindices
  have hfiller : filler.Ground g.ranks :=
    trajectory.toPivotTrajectory.representative_ground 0
  have harguments : ∀ n, arguments n ∈ argumentTuples := by
    intro n
    apply List.mem_map.mpr
    exact ⟨pivotRepresentatives n, hpivotMem n, by
      simp [arguments, argumentTupleOf, sourceArguments]⟩
  apply path.hasDerivedRepeat_of_uniformBoundedWitnessedCoverages_finiteArguments
    levels hlevels targetBound targetArity arguments
      argumentTuples harguments
  intro n
  let index := indices n
  let state := chain.states index
  let step := state.incoming
  let segment := SelectedBalancingSegment.asSegment step.selected
  let representative := pivotRepresentatives n
  let decomposition := representative.depthPrefix bound
  let pivotSchema := decomposition.head.toRegularTerm
  let sourceArity := decomposition.schemaArity g.ranks
  let sourceWidth := decomposition.tails.length
  have hrepresentativeGround : representative.Ground g.ranks :=
    hpivotGround n
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid representative bound
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy
      hrepresentativeGround bound
  have hpivotSupported :
      RegularTerm.SupportedByPrefix g.ranks
        sourceArity sourceWidth pivotSchema :=
    FiniteHead.toRegularTerm_supportedByPrefix hvalid hranked
  have hpivotWitness :
      pivotSchema.HasPrefixWitness sourceWidth :=
    FiniteHead.toRegularTerm_hasPrefixWitness hvalid
  have hpadding :
      g.ranks.foldr max 0 ≤ sourceArity := by
    simp [sourceArity, DepthPrefix.schemaArity]
  have hpivotDepth :
      pivotSchema.ApplicationDepth bound := by
    exact FiniteHead.depthPrefix_schema_applicationDepth
      hrepresentativeGround bound
  have hsourceArgumentsLength :
      (sourceArguments n).length = sourceArity := by
    simp [sourceArguments, sourceArity, decomposition, representative]
  have hsourceArgumentsGround :
      ∀ argument ∈ sourceArguments n,
        argument.Ground g.ranks := by
    exact RegularTerm.depthPrefix_paddedArguments_ground
      hrepresentativeGround hfiller bound
  have hpivotInstance :
      (pivotSchema.instantiate (sourceArguments n))
        |>.UnfoldingEquivalent
          (SelectedBalancingSegment.pivot step.selected) := by
    have hprefix :
        (pivotSchema.instantiate (sourceArguments n))
          |>.UnfoldingEquivalent representative := by
      simpa [pivotSchema, sourceArguments, decomposition] using
        (RegularTerm.depthPrefix_compiled_unfoldingEquivalent
          hrepresentativeGround hfiller bound)
    have hrepresentative :
        representative.UnfoldingEquivalent
          (trajectory.toPivotTrajectory.representatives index) :=
      (hpivotEquivalent n).symm
    have hactual :
        (trajectory.toPivotTrajectory.representatives index)
          |>.UnfoldingEquivalent
            (SelectedBalancingSegment.pivot step.selected) := by
      simpa [index, state, step,
        TracePath.StructuredPivotChain.pivot] using
          trajectory.toPivotTrajectory.representative_matches index
    exact hprefix.trans (hrepresentative.trans hactual)
  have hpivotSchemaSize :
      pivotSchema.nodes.length ≤ schemaBound := by
    simpa [pivotSchema, schemaBound, decomposition] using
      (RegularTerm.depthPrefix_schema_nodes_length_le
        hrepresentativeGround bound)
  obtain ⟨X, children, hroot⟩ :=
    step.active_ground.exists_rootApplication
  obtain ⟨coverage⟩ :=
    segment.exists_schemaBoundedWitnessedBalancingResult
      hg hnormal hexposureBound
      step.active_ground step.pivot_ground hfiller
      step.outer_derivation step.active_traceEquivalent_pivot
      hpivotSupported hpivotWitness hpadding hpivotDepth
      hsourceArgumentsLength hsourceArgumentsGround hpivotInstance
      hpivotSchemaSize hroot
  have hsourceArity :
      sourceArity ≤ targetArity := by
    simpa [sourceArity, targetArity, decomposition,
      fixedTailArityBound, fixedTailWidthBound] using
        (RegularTerm.depthPrefix_schemaArity_le
          hrepresentativeGround bound)
  have hsourceWidth : sourceWidth ≤ targetArity :=
    hpivotSupported.2.1.trans hsourceArity
  have hcoverageArity :
      coverage.witnessed.coverage.schema.arity ≤ targetArity := by
    calc
      coverage.witnessed.coverage.schema.arity =
          coverage.witnessed.coverage.arguments.length :=
        coverage.witnessed.coverage.argument_count.symm
      _ = (sourceArguments n).length :=
        congrArg List.length coverage.arguments_eq
      _ = sourceArity := hsourceArgumentsLength
      _ ≤ targetArity := hsourceArity
  have hcoverageBound :
      g.fixedBalancingPresentationBound
          bound sourceArity schemaBound ≤ targetBound := by
    unfold targetBound
    unfold fixedBalancingPresentationBound
    exact max_le_max hsourceArity (le_refl _)
  let widened :=
    coverage.widen filler hfiller hsourceWidth hcoverageArity
      (le_refl targetArity) hcoverageBound
      (g.le_fixedBalancingPresentationBound_arity
        bound targetArity schemaBound)
  have hword :
      step.outerStem ++
          (state.source.continuationPath hg hground hinitial).segmentWord
            step.offset bound =
        path.word (chain.levels index) := by
    simpa [index, state, step, levels] using
      step.outerStem_append_labels
  exact ⟨by
    simpa [widened, arguments, sourceArguments, index, state, step,
      segment] using widened.castWord hword⟩

/-- The complete progress-making branch of Proposition 49: unbounded
repeated sinking along the accumulated pivot words forces a
certificate-derived repeat. -/
public theorem hasDerivedRepeat_of_unboundedRepeatedSinking
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain
      hg hground hinitial bound initial)
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (hunbounded : ∀ depthBound,
      ∃ count depth,
        depthBound < depth ∧
        g.RepeatedlySinksBy
          (trajectory.toPivotTrajectory.representatives 0)
          (trajectory.toPivotTrajectory.prefixWord count)
          depth) :
    path.HasDerivedRepeat := by
  classical
  have hbound : 0 < bound :=
    (g.exposureBound_pos hnormal).trans_le hexposureBound
  obtain ⟨indices, hindices, hcover⟩ :=
    trajectory.exists_pivotFiniteCover_of_unboundedRepeatedSinking
      hbound hunbounded
  let pivotCover :=
    g.reachableWithin (g.structuredPivotM2Bound bound)
      (trajectory.toPivotTrajectory.representatives 0).pointedSubterms
  have hcovered : ∀ n, ∃ representative,
      representative ∈ pivotCover ∧
        representative.Ground g.ranks ∧
        RegularTerm.UnfoldingEquivalent
          (trajectory.toPivotTrajectory.representatives (indices n))
          representative := by
    intro n
    simpa [pivotCover] using hcover n
  choose pivotRepresentatives hpivotMem hpivotGround
    hpivotEquivalent using hcovered
  exact trajectory.hasDerivedRepeat_of_pivotFiniteCover
    hg hnormal hground hinitial hexposureBound chain
    indices hindices pivotRepresentatives pivotCover
    hpivotMem hpivotGround hpivotEquivalent

/-- The accumulated pivot path has one finite upper bound on the number of
progress-making sinking steps witnessed by any of its prefixes. -/
@[expose] public def HasBoundedRepeatedSinkingDepths
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
      hg hground hinitial bound chain) : Prop :=
  ∃ depthBound, ∀ count depth,
    g.RepeatedlySinksBy
        (trajectory.toPivotTrajectory.representatives 0)
        (trajectory.toPivotTrajectory.prefixWord count)
        depth →
      depth ≤ depthBound

/-- Absence of a derived repeat therefore bounds all progress-making
exposure depths. -/
public theorem hasBoundedRepeatedSinkingDepths_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain
      hg hground hinitial bound initial)
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (hnoRepeat : ¬path.HasDerivedRepeat) :
    trajectory.HasBoundedRepeatedSinkingDepths := by
  by_contra hnotBounded
  apply hnoRepeat
  apply trajectory.hasDerivedRepeat_of_unboundedRepeatedSinking
    hg hnormal hground hinitial hexposureBound chain
  unfold HasBoundedRepeatedSinkingDepths at hnotBounded
  push_neg at hnotBounded
  intro depthBound
  obtain ⟨count, depth, hsinks, hdepth⟩ :=
    hnotBounded depthBound
  exact ⟨count, depth, hdepth, hsinks⟩

/-- Exact remaining bridge between the semantic exposure predicate used by
`MaximalExposureRebase` and the progress-making predicate controlled by the
`M₂` argument.

This is deliberately a named obligation: `ExposesBy` permits a target merely
semantically equal to an arbitrarily deep occurrence, including empty-word
self-similarity of a cyclic regular term, whereas `RepeatedlySinksBy`
requires a nonempty input prefix at every increase of depth. -/
@[expose] public def SemanticExposureHasProgressWitness
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
      hg hground hinitial bound chain) : Prop :=
  ∀ count depth,
    g.ExposesBy
        (trajectory.toPivotTrajectory.representatives 0)
        (trajectory.toPivotTrajectory.prefixWord count)
        depth →
      ∃ progressCount progressDepth,
        depth ≤ progressDepth ∧
        g.RepeatedlySinksBy
          (trajectory.toPivotTrajectory.representatives 0)
          (trajectory.toPivotTrajectory.prefixWord progressCount)
          progressDepth

/-- Under the explicit semantic-to-progress reflection obligation, the
progress bound is exactly the exposure bound required by maximal rebasing. -/
public theorem hasBoundedExposureDepths_of_boundedRepeatedSinking
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
    (hreflection : trajectory.SemanticExposureHasProgressWitness)
    (hbounded : trajectory.HasBoundedRepeatedSinkingDepths) :
    trajectory.toPivotTrajectory.HasBoundedExposureDepths := by
  obtain ⟨depthBound, hdepthBound⟩ := hbounded
  exact ⟨depthBound, by
    intro depth hexposes
    obtain ⟨count, hexposes⟩ := hexposes
    obtain ⟨progressCount, progressDepth, hdepth, hprogress⟩ :=
      hreflection count depth hexposes
    exact hdepth.trans
      (hdepthBound progressCount progressDepth hprogress)⟩

/-- Consequently, no derived repeat implies the maximal-rebase exposure
premise as soon as the semantic-to-progress reflection obligation is
discharged. -/
public theorem hasBoundedExposureDepths_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain
      hg hground hinitial bound initial)
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    (hreflection : trajectory.SemanticExposureHasProgressWitness) :
    trajectory.toPivotTrajectory.HasBoundedExposureDepths :=
  trajectory.hasBoundedExposureDepths_of_boundedRepeatedSinking
    hreflection
    (trajectory.hasBoundedRepeatedSinkingDepths_of_noDerivedRepeat
      hg hnormal hground hinitial hexposureBound chain hnoRepeat)

end WindowedPivotTrajectory

end StructuredPivotChain

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
