module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotSwitchReachability
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedSinkingBoundary

@[expose]
public section

/-!
# Balancing results with retained construction data

The public Proposition-45 coverage intentionally forgets the intermediate
successor family.  Proposition 49 later needs that family again: a sufficiently
deep exposure of the active result must cross one of the concrete replacement
targets obtained from the previous pivot.

This file retains the coherent construction data before it is erased by the
coverage interface.  In particular, `ConcreteActiveReplacement` records the
actual certificate-derived active term together with its semantic equality to
the active residual instantiated by the ordered successor targets.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace BalancingSegment.ActivePrefixResidual

variable {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
  {active pivot : RegularTerm} {labels : List (Label Action)}
  {segment : BalancingSegment g bound active pivot labels}
  {filler : RegularTerm}

/-- A grammar- and run-uniform semantic unfolding-depth bound for the active
symbolic residual. -/
@[expose] public def unfoldingDepthBound
    (activeResult : segment.ActivePrefixResidual filler) : ℕ :=
  g.residualUnfoldingDepthBound activeResult.actions.length
    (active.depthPrefix 1).head.compiledNodeCount

/-- The active residual produced by finite-prefix execution satisfies its
explicit semantic unfolding-depth bound. -/
public theorem residual_unfoldingDepthAtMost
    (activeResult : segment.ActivePrefixResidual filler)
    (hg : g.WellFormed)
    (hactive : active.Ground g.ranks) :
    activeResult.residual.UnfoldingDepthAtMost
      activeResult.unfoldingDepthBound := by
  let decomposition := active.depthPrefix 1
  have hvalid : decomposition.Valid :=
    RegularTerm.depthPrefix_valid active 1
  have hranked : decomposition.head.RankedBy g.ranks :=
    RegularTerm.depthPrefix_head_rankedBy hactive 1
  have hsourceWellFormed :
      decomposition.head.toRegularTerm.WellFormed g.ranks
        (decomposition.schemaArity g.ranks) :=
    decomposition.head_wellFormed_schemaArity hvalid hranked
  have hsourceDepth :
      decomposition.head.toRegularTerm.UnfoldingDepthAtMost
        decomposition.head.compiledNodeCount :=
    FiniteHead.toRegularTerm_unfoldingDepthAtMost hranked
  change activeResult.residual.UnfoldingDepthAtMost
    (g.residualUnfoldingDepthBound activeResult.actions.length
      decomposition.head.compiledNodeCount)
  exact g.runActions?_preserves_unfoldingDepthAtMost
    hg ⟨_, hsourceWellFormed⟩
    (fun {depth index} hdescendant =>
      hsourceDepth (depth := depth) (index := index) hdescendant)
    activeResult.symbolic_run

end BalancingSegment.ActivePrefixResidual

namespace BalancingSegment.ExposedSuccessorFamily

variable {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
  {active pivot : RegularTerm} {labels : List (Label Action)}
  {segment : BalancingSegment g bound active pivot labels}
  {initialLeft initialRight : RegularTerm}
  {stem : List (Label Action)} {filler : RegularTerm}
  {children : List ℕ}

/-- The concrete argument tuple installed into the active symbolic residual:
one target reached from the old pivot for each active successor, followed by
the same filler padding used by Proposition 45. -/
@[expose] public noncomputable def concreteActiveArguments
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children) : List RegularTerm :=
  family.pivotTargets ++
    List.replicate
      ((active.depthPrefix 1).schemaArity g.ranks - children.length)
      filler

/-- The certificate-derived active component before the schema-coverage
packaging step, retaining its exact semantic presentation by the ordered
successor targets. -/
public structure ConcreteActiveReplacement
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (activeResult : segment.ActivePrefixResidual filler) where
  result : RegularTerm
  derivation :
    CertificateDerivable g initialLeft initialRight []
      (.pair (stem ++ activeResult.actions.map Sum.inl)
        result segment.pivotTarget)
  instance_matches :
    result.UnfoldingEquivalent
      (activeResult.residual.instantiate
        family.concreteActiveArguments)

/-- The argument tuple retained by a concrete replacement has exactly the
active depth-one schema arity. -/
public theorem concreteActiveArguments_length
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hroot : active.rootApplication? = some (X, children)) :
    family.concreteActiveArguments.length =
      (active.depthPrefix 1).schemaArity g.ranks := by
  have htails :=
    RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
  have hchildrenArity :
      children.length ≤
        (active.depthPrefix 1).schemaArity g.ranks := by
    simp [DepthPrefix.schemaArity, htails]
  simp [concreteActiveArguments, family.pivotTargets_length]
  omega

/-- Every retained concrete active argument is ground. -/
public theorem concreteActiveArguments_ground
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hg : g.WellFormed)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks) :
    ∀ argument ∈ family.concreteActiveArguments,
      argument.Ground g.ranks := by
  intro argument hargument
  simp only [concreteActiveArguments, List.mem_append,
    List.mem_replicate] at hargument
  rcases hargument with htarget | ⟨_hcount, rfl⟩
  · exact family.pivotTargets_ground hg hpivot argument htarget
  · exact hfiller

/-- Proposition 45's argument-prefix replacement, factored before any schema
coverage data is discarded. -/
public theorem exists_concreteActiveReplacement
    (family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children)
    (hg : g.WellFormed)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot)
    (activeResult : segment.ActivePrefixResidual filler) :
    Nonempty (family.ConcreteActiveReplacement activeResult) := by
  classical
  let activeArguments :=
    (active.depthPrefix 1).paddedArguments g.ranks filler
  have hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hactiveRun :
      g.runActions? activeResult.actions active =
        some segment.active_target := by
    simpa [runActions?, activeResult.labels_eq] using segment.active_run
  have hpivotRun :
      g.runActions? activeResult.actions pivot =
        some segment.pivotTarget := by
    simpa [runActions?, activeResult.labels_eq] using segment.pivot_run
  have hsegmentDerivation :
      CertificateDerivable g initialLeft initialRight []
        (.pair (stem ++ activeResult.actions.map Sum.inl)
          segment.active_target segment.pivotTarget) :=
    houter.follow_runActions hgroundSteps hequivalent
      hactiveRun hpivotRun
  have hactiveArgumentsGround :
      ∀ argument ∈ activeArguments, argument.Ground g.ranks :=
    RegularTerm.depthPrefix_paddedArguments_ground
      hactive hfiller 1
  have hreplacementsGround :
      ∀ replacement ∈ family.pivotTargets,
        replacement.Ground g.ranks :=
    family.pivotTargets_ground hg hpivot
  have hreplacementLength :
      family.pivotTargets.length ≤ activeArguments.length := by
    rw [family.pivotTargets_length]
    have htails :=
      RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
    have hchildrenArity :
        children.length ≤
          (active.depthPrefix 1).schemaArity g.ranks := by
      simp [DepthPrefix.schemaArity, htails]
    simpa [activeArguments] using hchildrenArity
  let childIndex : Fin family.pivotTargets.length → Fin children.length :=
    fun i => ⟨i.val, by simpa using i.isLt⟩
  let shorterWord : Fin family.pivotTargets.length →
      List (Label Action) :=
    fun i => stem ++ (family.row (childIndex i)).word.map Sum.inl
  let shorterLeft : Fin family.pivotTargets.length → RegularTerm :=
    fun i => (family.row (childIndex i)).activeTarget
  let shorterRight : Fin family.pivotTargets.length → RegularTerm :=
    fun i => (family.row (childIndex i)).pivotTarget
  have hactiveSchemaWellFormed :
      activeResult.residual.WellFormed g.ranks activeArguments.length := by
    simpa [activeArguments] using activeResult.supported.1
  obtain ⟨result, hresultDerivation, hresultMatch⟩ :=
    hsegmentDerivation.replaceArgumentPrefixFin
      hactiveSchemaWellFormed hactiveArgumentsGround
      hreplacementsGround hreplacementLength
      activeResult.instance_matches.symm
      shorterWord shorterLeft shorterRight
      (fun i => (family.row (childIndex i)).shorter_derivation)
      (fun i => by
        simp only [shorterWord, List.length_append, List.length_map]
        have hshort :=
          (family.row (childIndex i)).word_length_lt
        have houterLength := activeResult.actions_length
        omega)
      (fun i => by
        let index := childIndex i
        have hiChildren : i.val < children.length := index.isLt
        have htails :=
          RegularTerm.depthPrefix_one_tails_of_rootApplication hroot
        have hiArguments : i.val < activeArguments.length :=
          i.isLt.trans_le hreplacementLength
        have hargumentGet :
            activeArguments[i.val]? =
              some (active.withRoot children[i.val]) := by
          unfold activeArguments DepthPrefix.paddedArguments
          rw [List.getElem?_append_left (by
            simpa [htails] using hiChildren)]
          simp [htails, List.getElem?_eq_getElem hiChildren]
        have hargumentEq :
            activeArguments[i.val] =
              active.withRoot children[i.val] :=
          Option.some.inj
            ((List.getElem?_eq_getElem hiArguments).symm.trans
              hargumentGet)
        rw [hargumentEq]
        simpa [index, childIndex] using
          (family.row index).active_matches)
      (fun i => by
        let index := childIndex i
        rw [family.pivotTargets_getElem index])
  exact ⟨
    { result := result
      derivation := hresultDerivation
      instance_matches := by
        simpa [concreteActiveArguments, activeArguments,
          family.replaceArgumentPrefix_activeArguments hroot] using
            hresultMatch }⟩

namespace ConcreteActiveReplacement

/-- The retained concrete active component is ground because it occurs in a
certificate-derived pair. -/
public theorem result_ground
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult) :
    replacement.result.Ground g.ranks := by
  have hpair := groundPairCode_of_pair_derivable replacement.derivation
  unfold groundPairCode at hpair
  rw [Bool.and_eq_true] at hpair
  exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpair.1

/-- The canonical active instance retained by the construction is reference
closed. -/
public theorem canonical_referenceClosed
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (_replacement : family.ConcreteActiveReplacement activeResult)
    (hg : g.WellFormed)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks) :
    (activeResult.residual.instantiate
      family.concreteActiveArguments).ReferenceClosed := by
  apply RegularTerm.instantiate_referenceClosed
    (RegularTerm.referenceClosed_of_wellFormed
      activeResult.supported.1)
  intro argument hargument
  exact RegularTerm.referenceClosed_of_ground
    (family.concreteActiveArguments_ground
      hg hpivot hfiller argument hargument)

/-- Transport a canonical successor-row hit back to the actual
certificate-derived active component and identify it with the corresponding
path residual.  This is the representation-sensitive bridge needed after the
pure finite-context boundary argument. -/
public theorem path_left_matches_row_of_canonical_run
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (hg : g.WellFormed)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (path : TracePath g replacement.result segment.pivotTarget)
    (cut : ℕ) (i : Fin children.length)
    {canonicalTarget : RegularTerm}
    (hcanonicalRun :
      g.run? (path.segmentWord 0 cut)
        (activeResult.residual.instantiate
          family.concreteActiveArguments) =
        some canonicalTarget)
    (htarget :
      canonicalTarget.UnfoldingEquivalent
        (family.row i).pivotTarget) :
    (path.left cut).UnfoldingEquivalent
      (family.row i).pivotTarget := by
  obtain ⟨actualTarget, hactualRun, hactualMatches⟩ :=
    exists_run_of_unfoldingEquivalent hg
      replacement.instance_matches
      (RegularTerm.referenceClosed_of_ground replacement.result_ground)
      (replacement.canonical_referenceClosed
        hg hpivot hfiller)
      hcanonicalRun
  have hpathRun := path.left_segment_run 0 cut
  have hpathRun' :
      g.run? (path.segmentWord 0 cut) replacement.result =
        some (path.left cut) := by
    simpa [path.starts_left] using hpathRun
  have hactualEq : actualTarget = path.left cut := by
    apply Option.some.inj
    exact hactualRun.symm.trans hpathRun'
  subst actualTarget
  exact hactualMatches.trans htarget

/-- A prefix of `word` reaches, in the canonical active instance, one of the
ordered successor targets installed by Proposition 45. -/
public structure CanonicalSuccessorHitBy
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (word : List (Label Action)) where
  initialSegment : List (Label Action)
  remainder : List (Label Action)
  word_eq : word = initialSegment ++ remainder
  index : Fin children.length
  target : RegularTerm
  run :
    g.run? initialSegment
      (activeResult.residual.instantiate
        family.concreteActiveArguments) = some target
  target_matches :
    target.UnfoldingEquivalent (family.row index).pivotTarget

/-- Repeated sinking from the concrete replacement crosses one of the
ordered successor arguments in the retained canonical presentation. -/
@[expose] public def RepeatedSinkingReflects
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (depth : ℕ) : Prop :=
  ∀ word,
    g.RepeatedlySinksBy replacement.result word depth →
      Nonempty (replacement.CanonicalSuccessorHitBy word)

/-- A sinking spine deeper than a semantic bound for the active schema must
cross one of the concrete successor targets installed at its variables. -/
public theorem repeatedSinkingReflects_of_depthBound
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (hg : g.WellFormed)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    {schemaBound depth : ℕ}
    (hdepth :
      activeResult.residual.UnfoldingDepthAtMost schemaBound)
    (hdeep : schemaBound < depth) :
    replacement.RepeatedSinkingReflects depth := by
  intro word hsinks
  have hargumentsGround :
      ∀ argument ∈ family.concreteActiveArguments,
        argument.Ground g.ranks :=
    family.concreteActiveArguments_ground
      hg hpivot hfiller
  have hargumentsLength :
    family.concreteActiveArguments.length =
        (active.depthPrefix 1).schemaArity g.ranks :=
    family.concreteActiveArguments_length hroot
  have hschemaWellFormed :
      activeResult.residual.WellFormed g.ranks
        family.concreteActiveArguments.length := by
    rw [hargumentsLength]
    exact activeResult.supported.1
  have hcanonicalGround :
      (activeResult.residual.instantiate
        family.concreteActiveArguments).Ground g.ranks :=
    RegularTerm.instantiate_ground
      hschemaWellFormed hargumentsGround
  have hwidth :
      children.length ≤ family.concreteActiveArguments.length := by
    simp [BalancingSegment.ExposedSuccessorFamily.concreteActiveArguments,
      family.pivotTargets_length]
  obtain ⟨hit⟩ :=
    g.exists_canonicalArgumentHit_of_repeatedlySinksBy_of_depthBound
      hg
      (family.activeResidual_hasPrefixWitness
        hg hactive hroot activeResult)
      hdepth
      (RegularTerm.referenceClosed_of_wellFormed
        activeResult.supported.1)
      hwidth hargumentsGround hcanonicalGround
      replacement.result_ground
      (RegularTerm.unfoldingEquivalent_refl _)
      replacement.instance_matches hdeep hsinks
  let index : Fin children.length :=
    ⟨hit.index, hit.index_lt⟩
  have htargetBound :
      hit.index < family.pivotTargets.length := by
    simpa [family.pivotTargets_length] using hit.index_lt
  have htargetAt :
      family.concreteActiveArguments[hit.index]? =
        some (family.row index).pivotTarget := by
    unfold BalancingSegment.ExposedSuccessorFamily.concreteActiveArguments
    rw [List.getElem?_append_left htargetBound,
      List.getElem?_eq_getElem htargetBound,
      family.pivotTargets_getElem index]
  have hargumentEq :
      hit.argument = (family.row index).pivotTarget :=
    Option.some.inj (hit.argument_at.symm.trans htargetAt)
  exact ⟨
    { initialSegment := hit.initialSegment
      remainder := hit.remainder
      word_eq := hit.word_eq
      index := index
      target := hit.target
      run := hit.run
      target_matches := by
        rw [← hargumentEq]
        exact hit.target_matches }⟩

/-- The explicit run-derived bound discharges the semantic-depth premise
without requiring executable finiteness of the residual graph. -/
public theorem repeatedSinkingReflects_of_activeResidualBound
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (hg : g.WellFormed)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    {depth : ℕ}
    (hdeep : activeResult.unfoldingDepthBound < depth) :
    replacement.RepeatedSinkingReflects depth := by
  exact replacement.repeatedSinkingReflects_of_depthBound
    hg hactive hpivot hfiller hroot
    (activeResult.residual_unfoldingDepthAtMost hg hactive)
    hdeep

/-- Executable finiteness supplies the semantic depth bound used by repeated
sinking reflection. -/
public theorem repeatedSinkingReflects_of_unfoldsFinite
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (hg : g.WellFormed)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (hfinite : activeResult.residual.UnfoldsFinite)
    {depth : ℕ}
    (hdeep : activeResult.residual.nodes.length < depth) :
    replacement.RepeatedSinkingReflects depth := by
  exact replacement.repeatedSinkingReflects_of_depthBound
    hg hactive hpivot hfiller hroot
    hfinite.unfoldingDepthAtMost_nodes hdeep

/-- The exact finite-context boundary property missing from the current
regular-graph API.  A depth-`depth` exposure of the concrete active
replacement has an earlier canonical prefix which reaches one of the
successor targets.

For Proposition 49, `depth` is `1 + B-Inc(bound)`.  Proving this predicate
uniformly requires finiteness/height elimination for symbolic residuals and
substitution-boundary factorization. -/
@[expose] public def DeepExposureReflects
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (depth : ℕ) : Prop :=
  ∀ word,
    g.ExposesBy replacement.result word depth →
      Nonempty (replacement.CanonicalSuccessorHitBy word)

/-- Once the finite-context boundary property is available, every deep path
exposure yields exactly the row/cut semantic match consumed by
`nextPivotBridge`. -/
public theorem exists_row_match_of_deepExposure
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (hg : g.WellFormed)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth limit : ℕ)
    (hreflection : replacement.DeepExposureReflects depth)
    (path : TracePath g replacement.result segment.pivotTarget)
    (hexposure :
      g.ExposesBy replacement.result
        (path.segmentWord 0 limit) depth) :
    ∃ cut, cut ≤ limit ∧
      ∃ i : Fin children.length,
        (path.left cut).UnfoldingEquivalent
          (family.row i).pivotTarget := by
  obtain ⟨hit⟩ :=
    hreflection (path.segmentWord 0 limit) hexposure
  have hcut : hit.initialSegment.length ≤ limit := by
    have hlength := congrArg List.length hit.word_eq
    simp [path.segmentWord_length] at hlength
    omega
  have hprefix :
      hit.initialSegment =
        path.segmentWord 0 hit.initialSegment.length := by
    have htake :=
      congrArg (List.take hit.initialSegment.length) hit.word_eq
    rw [path.take_segmentWord 0 hcut] at htake
    simpa using htake.symm
  refine ⟨hit.initialSegment.length, hcut, hit.index, ?_⟩
  apply replacement.path_left_matches_row_of_canonical_run
    hg hpivot hfiller path
      hit.initialSegment.length hit.index
  · have hrun := hit.run
    rw [hprefix] at hrun
    exact hrun
  · exact hit.target_matches

/-- A reflected repeated-sinking spine yields exactly the row/cut semantic
match consumed by `nextPivotBridge`. -/
public theorem exists_row_match_of_repeatedSinking
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (hg : g.WellFormed)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth limit : ℕ)
    (hreflection : replacement.RepeatedSinkingReflects depth)
    (path : TracePath g replacement.result segment.pivotTarget)
    (hsinks :
      g.RepeatedlySinksBy replacement.result
        (path.segmentWord 0 limit) depth) :
    ∃ cut, cut ≤ limit ∧
      ∃ i : Fin children.length,
        (path.left cut).UnfoldingEquivalent
          (family.row i).pivotTarget := by
  obtain ⟨hit⟩ :=
    hreflection (path.segmentWord 0 limit) hsinks
  have hcut : hit.initialSegment.length ≤ limit := by
    have hlength := congrArg List.length hit.word_eq
    simp [path.segmentWord_length] at hlength
    omega
  have hprefix :
      hit.initialSegment =
        path.segmentWord 0 hit.initialSegment.length := by
    have htake :=
      congrArg (List.take hit.initialSegment.length) hit.word_eq
    rw [path.take_segmentWord 0 hcut] at htake
    simpa using htake.symm
  refine ⟨hit.initialSegment.length, hcut, hit.index, ?_⟩
  apply replacement.path_left_matches_row_of_canonical_run
    hg hpivot hfiller path
      hit.initialSegment.length hit.index
  · have hrun := hit.run
    rw [hprefix] at hrun
    exact hrun
  · exact hit.target_matches

/-- The no-close-left branch supplies a repeated-sinking spine which must
cross an active successor once it is deeper than the finite residual schema. -/
public theorem exists_row_match_of_noLeftBalancingBefore
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (hg : g.WellFormed)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (path : TracePath g replacement.result segment.pivotTarget)
    (hinitial :
      g.TraceEquivalent replacement.result segment.pivotTarget)
    (bound depth : ℕ)
    (hbound : 0 < bound)
    (hdeep : activeResult.unfoldingDepthBound < depth)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasLeftBalancingOpportunity bound offset) :
    ∃ cut, cut ≤ depth * bound ∧
      ∃ i : Fin children.length,
        (path.left cut).UnfoldingEquivalent
          (family.row i).pivotTarget := by
  apply replacement.exists_row_match_of_repeatedSinking
    hg hpivot hfiller depth (depth * bound)
    (replacement.repeatedSinkingReflects_of_activeResidualBound
      hg hactive hpivot hfiller hroot hdeep)
    path
  simpa only [path.starts_left] using
    (path.repeatedlySinksLeft_of_noBalancingBefore
      hg
      (groundPairCode_of_pair_derivable replacement.derivation)
      hinitial 0 bound depth hbound (by
        intro offset hoffset
        simpa using hno offset hoffset))

/-- Conditional close/no-close pivot bridge in the exact form used by
Proposition 49.  The close-window argument and word surgery are fully
discharged; `hreflection` is the sole remaining finite-context lemma.

The same-side branch follows the old pivot directly.  In the switch branch,
the old balancing word and a prefix of length at most `depth * bound` are
replaced by one strictly shorter exposed-successor word. -/
public theorem nextPivotBridge_of_noLeftBalancingBefore
    {family : segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children}
    {activeResult : segment.ActivePrefixResidual filler}
    (replacement : family.ConcreteActiveReplacement activeResult)
    (hg : g.WellFormed)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (hroot : active.rootApplication? = some (X, children))
    (path : TracePath g replacement.result segment.pivotTarget)
    (hinitial :
      g.TraceEquivalent replacement.result segment.pivotTarget)
    (bound depth : ℕ)
    (hbound : 0 < bound)
    (hdeep : activeResult.unfoldingDepthBound < depth)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasLeftBalancingOpportunity bound offset)
    {nextLevel : ℕ} (hclose : depth * bound ≤ nextLevel)
    (selected : PathBalancingSegment path bound nextLevel) :
    (path.HasLeftBalancingOpportunity bound nextLevel ∧
        g.run? (labels ++ path.segmentWord 0 nextLevel) pivot =
          some (path.right nextLevel)) ∨
      (path.HasRightBalancingOpportunity bound nextLevel ∧
        ∃ i : Fin children.length,
          ∃ cut ≤ depth * bound,
            ∃ reached,
              g.run?
                  ((family.row i).modifiedBridge
                    path cut nextLevel)
                  pivot = some reached ∧
              reached.UnfoldingEquivalent (path.left nextLevel) ∧
              ((family.row i).modifiedBridge
                    path cut nextLevel).length <
                (labels ++ path.segmentWord 0 nextLevel).length) := by
  obtain ⟨cut, hcutClose, i, hmatch⟩ :=
    replacement.exists_row_match_of_noLeftBalancingBefore
      hg hactive hpivot hfiller hroot path hinitial
      bound depth hbound hdeep hno
  have hcutNext : cut ≤ nextLevel :=
    hcutClose.trans hclose
  have hresultGround :
      g.groundPairCode replacement.result segment.pivotTarget = true :=
    groundPairCode_of_pair_derivable replacement.derivation
  cases selected with
  | left next =>
      refine Or.inl ⟨⟨next⟩, ?_⟩
      rw [g.run?_append, segment.pivot_run]
      have hright :
          g.run? (path.segmentWord 0 nextLevel)
              segment.pivotTarget =
            some (path.right nextLevel) := by
        simpa only [path.starts_right, Nat.zero_add] using
          path.right_segment_run 0 nextLevel
      simpa using hright
  | right next =>
      obtain ⟨reached, hrun, hreached⟩ :=
        (family.row i).exists_run_modifiedBridge
          hg hpivot path hresultGround hcutNext hmatch
      exact Or.inr
        ⟨⟨next⟩, i, cut, hcutClose, reached,
          hrun, hreached,
          (family.row i).modifiedBridge_length_lt
            path hcutNext⟩

end ConcreteActiveReplacement

end BalancingSegment.ExposedSuccessorFamily

/-- All coherent local choices used to build one balancing result, retained
before the public coverage layer forgets them. -/
public structure BalancingSegment.StructuredBalancingResult
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    {initialLeft initialRight : RegularTerm}
    (stem : List (Label Action)) (filler : RegularTerm) where
  rootSymbol : ℕ
  children : List ℕ
  root_eq :
    active.rootApplication? = some (rootSymbol, children)
  activeResult : segment.ActivePrefixResidual filler
  pivotResult :
    segment.PivotPrefixResidual filler activeResult
  family :
    segment.ExposedSuccessorFamily
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler children
  replacement :
    family.ConcreteActiveReplacement activeResult

/-- Normal-form Proposition-45 construction with every successor row and the
concrete active replacement retained coherently. -/
public theorem BalancingSegment.exists_structuredBalancingResult
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ} (hexposureBound : g.exposureBound hnormal ≤ bound)
    {active pivot : RegularTerm} {labels : List (Label Action)}
    (segment : BalancingSegment g bound active pivot labels)
    (hactive : active.Ground g.ranks)
    (hpivot : pivot.Ground g.ranks)
    {filler : RegularTerm} (hfiller : filler.Ground g.ranks)
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)}
    (houter : CertificateDerivable g initialLeft initialRight []
      (.pair stem active pivot))
    (hequivalent : g.TraceEquivalent active pivot) :
    Nonempty (segment.StructuredBalancingResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler) := by
  obtain ⟨X, children, hroot⟩ := hactive.exists_rootApplication
  obtain ⟨activeResult⟩ :=
    segment.exists_activePrefixResidual hg hactive hfiller
  obtain ⟨pivotResult⟩ :=
    segment.exists_pivotPrefixResidual hg hpivot hfiller activeResult
  obtain ⟨family⟩ :=
    segment.exists_exposedSuccessorFamily hg hnormal hexposureBound
      hactive hpivot hfiller houter hequivalent hroot
  obtain ⟨replacement⟩ :=
    family.exists_concreteActiveReplacement
      hg hactive hpivot hfiller hroot houter hequivalent activeResult
  exact ⟨
    { rootSymbol := X
      children := children
      root_eq := hroot
      activeResult := activeResult
      pivotResult := pivotResult
      family := family
      replacement := replacement }⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
