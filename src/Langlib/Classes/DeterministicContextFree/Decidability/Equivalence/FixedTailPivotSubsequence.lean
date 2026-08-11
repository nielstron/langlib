module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailReflection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.OrientedBalancingSubsequence

@[expose]
public section

/-!
# Fixed tails along an oriented pivot subsequence

Once all retained balancing opportunities have one orientation, their pivots
lie on one ordinary residual stream.  This file isolates the remaining
maximal-depth premise: some unfolding depth of the first pivot is never
exposed along the retained stream.  The least such depth is the cutoff after
the maximal initial interval of exposed depths.

At that cutoff every retained pivot is represented by a symbolic residual
over one and the same padded tuple of depth-prefix tails.  The construction is
independent of the later balancing-result assembly.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A family of finite words eventually exposes a fixed unfolding depth. -/
@[expose] public def EverExposesDepth
    (g : EncodedFirstOrderGrammar Action)
    (base : RegularTerm)
    (labels : ℕ → List (Label Action))
    (depth : ℕ) : Prop :=
  ∃ j, g.ExposesBy base (labels j) depth

/-- At least one unfolding depth is absent from all words in the family. -/
@[expose] public def HasMissingExposureDepth
    (g : EncodedFirstOrderGrammar Action)
    (base : RegularTerm)
    (labels : ℕ → List (Label Action)) : Prop :=
  ∃ depth, ¬g.EverExposesDepth base labels depth

/-- The least missing depth cuts off a maximal initial interval of depths
which are all exposed.  No monotonicity assumption on later depths is hidden
in this presentation. -/
public structure InitialExposureCutoff
    (g : EncodedFirstOrderGrammar Action)
    (base : RegularTerm)
    (labels : ℕ → List (Label Action)) where
  depth : ℕ
  positive : 0 < depth
  exposes_below :
    ∀ smaller, smaller < depth →
      g.EverExposesDepth base labels smaller
  missing :
    ¬g.EverExposesDepth base labels depth

/-- Well-ordering turns any missing depth into the least missing depth. -/
public theorem exists_initialExposureCutoff
    {g : EncodedFirstOrderGrammar Action}
    {base : RegularTerm}
    {labels : ℕ → List (Label Action)}
    (hmissing : g.HasMissingExposureDepth base labels) :
    Nonempty (g.InitialExposureCutoff base labels) := by
  classical
  let depth := Nat.find hmissing
  have hdepthMissing :
      ¬g.EverExposesDepth base labels depth :=
    Nat.find_spec hmissing
  have hdepthPositive : 0 < depth := by
    by_contra hnot
    have hzero : depth = 0 := by omega
    apply hdepthMissing
    rw [hzero]
    exact ⟨0, g.exposesBy_zero base (labels 0)⟩
  have hbelow :
      ∀ smaller, smaller < depth →
        g.EverExposesDepth base labels smaller := by
    intro smaller hsmaller
    by_contra hnot
    exact (Nat.find_min hmissing hsmaller) hnot
  exact ⟨
    { depth := depth
      positive := hdepthPositive
      exposes_below := hbelow
      missing := hdepthMissing }⟩

/-- An infinite family of concrete pivots, all presented by residual schemas
over one fixed depth-prefix argument tuple. -/
public structure FixedTailPivotPresentation
    (g : EncodedFirstOrderGrammar Action)
    (base filler : RegularTerm)
    (labels : ℕ → List (Label Action))
    (pivots : ℕ → RegularTerm) where
  /-- The depth at which the common tail tuple is cut. -/
  depth : ℕ
  base_ground : base.Ground g.ranks
  filler_ground : filler.Ground g.ranks
  actions : ℕ → List Action
  labels_eq : ∀ j, labels j = (actions j).map Sum.inl
  residual :
    ∀ j, FixedTailResidual g base filler depth
      (actions j) (pivots j)

namespace FixedTailPivotPresentation

/-- The common genuine boundary width. -/
@[expose] public def width
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots) : ℕ :=
  (base.depthPrefix presentation.depth).tails.length

/-- The common padded arity. -/
@[expose] public def arity
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots) : ℕ :=
  (base.depthPrefix presentation.depth).schemaArity g.ranks

/-- The one fixed tuple used by every residual schema. -/
@[expose] public def arguments
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots) :
    List RegularTerm :=
  (base.depthPrefix presentation.depth)
    |>.paddedArguments g.ranks filler

/-- The residual schema representing the `j`th pivot. -/
@[expose] public def schema
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (j : ℕ) : RegularTerm :=
  (presentation.residual j).residual

@[simp] public theorem arguments_length
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots) :
    presentation.arguments.length = presentation.arity := by
  simp [arguments, arity]

public theorem arguments_ground
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots) :
    ∀ argument ∈ presentation.arguments,
      argument.Ground g.ranks := by
  exact RegularTerm.depthPrefix_paddedArguments_ground
    presentation.base_ground presentation.filler_ground
    presentation.depth

public theorem schema_instance_matches
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (j : ℕ) :
    ((presentation.schema j).instantiate presentation.arguments)
      |>.UnfoldingEquivalent (pivots j) := by
  exact (presentation.residual j).instance_matches

public theorem schema_supported
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (j : ℕ) :
    RegularTerm.SupportedByPrefix g.ranks
      presentation.arity presentation.width
      (presentation.schema j) := by
  exact (presentation.residual j).supported

public theorem schema_hasPrefixWitness
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (j : ℕ) :
    (presentation.schema j).HasPrefixWitness
      presentation.width := by
  exact (presentation.residual j).hasPrefixWitness

public theorem schema_size_le
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (j : ℕ) :
    (presentation.schema j).nodes.length ≤
      g.residualNodeBound (presentation.actions j).length
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) presentation.depth) := by
  exact (presentation.residual j).size_le

end FixedTailPivotPresentation

/-- Generic fixed-tail extraction from ordinary runs and one missing exposure
depth. -/
public theorem exists_fixedTailPivotPresentation_of_missingDepth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (hbase : base.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (hruns : ∀ j, g.run? (labels j) base = some (pivots j))
    (hordinary : ∀ j, ∃ actions : List Action,
      labels j = actions.map Sum.inl)
    (hmissing : g.HasMissingExposureDepth base labels) :
    Nonempty (FixedTailPivotPresentation
      g base filler labels pivots) := by
  classical
  let cutoff :=
    Classical.choice (exists_initialExposureCutoff hmissing)
  choose actions hlabels using hordinary
  have hresidual :
      ∀ j, FixedTailResidual g base filler cutoff.depth
        (actions j) (pivots j) := by
    intro j
    have hrunActions :
        g.runActions? (actions j) base = some (pivots j) := by
      simpa [runActions?, ← hlabels j] using hruns j
    have hnotExposes :
        ¬g.ExposesBy base ((actions j).map Sum.inl)
          cutoff.depth := by
      simpa [← hlabels j] using
        (show ¬g.ExposesBy base (labels j) cutoff.depth from
          fun hexposes => cutoff.missing ⟨j, hexposes⟩)
    exact Classical.choice
      (exists_fixedTailResidual hg hbase hfiller
        cutoff.depth hrunActions
        (noDepthExposureBefore_of_not_exposesBy hnotExposes))
  exact ⟨
    { depth := cutoff.depth
      base_ground := hbase
      filler_ground := hfiller
      actions := actions
      labels_eq := hlabels
      residual := hresidual }⟩

/-- Generic fixed-tail extraction at an explicitly selected depth.  The
least-missing cutoff is retained only as useful metadata; it need not equal the
presentation depth.  This is the form used after Proposition 49 rebases the
pivot path at its deepest exposed subterm and chooses depth `M₀`. -/
public theorem exists_fixedTailPivotPresentation_atDepth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (hbase : base.Ground g.ranks)
    (hfiller : filler.Ground g.ranks)
    (depth : ℕ)
    (hruns : ∀ j, g.run? (labels j) base = some (pivots j))
    (hordinary : ∀ j, ∃ actions : List Action,
      labels j = actions.map Sum.inl)
    (hnotExposes : ∀ j,
      ¬g.ExposesBy base (labels j) depth) :
    ∃ presentation : FixedTailPivotPresentation
        g base filler labels pivots,
      presentation.depth = depth := by
  classical
  choose actions hlabels using hordinary
  have hresidual :
      ∀ j, FixedTailResidual g base filler depth
        (actions j) (pivots j) := by
    intro j
    have hrunActions :
        g.runActions? (actions j) base = some (pivots j) := by
      simpa [runActions?, ← hlabels j] using hruns j
    have hnotExposes' :
        ¬g.ExposesBy base ((actions j).map Sum.inl) depth := by
      simpa [← hlabels j] using hnotExposes j
    exact Classical.choice
      (exists_fixedTailResidual hg hbase hfiller depth hrunActions
        (noDepthExposureBefore_of_not_exposesBy hnotExposes'))
  exact ⟨
    { depth := depth
      base_ground := hbase
      filler_ground := hfiller
      actions := actions
      labels_eq := hlabels
      residual := hresidual }, rfl⟩

namespace LeftBalancingSubsequence

/-- The word from the first retained left-balancing pivot to the `j`th one. -/
@[expose] public noncomputable def bridgeLabels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : LeftBalancingSubsequence sequence)
    (j : ℕ) : List (Label Action) :=
  path.segmentWord (subsequence.levels 0)
    (subsequence.levels j - subsequence.levels 0)

/-- The maximal-initial-depth premise for the retained right-side pivot
stream. -/
@[expose] public def HasMissingPivotExposureDepth
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : LeftBalancingSubsequence sequence) : Prop :=
  g.HasMissingExposureDepth (subsequence.pivot 0)
    subsequence.bridgeLabels

/-- Every left-balancing pivot is presented over one fixed tail tuple once
the retained pivot stream has a missing exposure depth. -/
public theorem exists_fixedTailPivotPresentation
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : LeftBalancingSubsequence sequence)
    (hgroundSteps : g.PreservesGroundSteps)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hfiller : filler.Ground g.ranks)
    (hmissing : subsequence.HasMissingPivotExposureDepth) :
    Nonempty (FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot) := by
  have hpivotGround :
      (subsequence.pivot 0).Ground g.ranks := by
    have hpair := path.residual_ground hgroundSteps hground
      (subsequence.levels 0)
    unfold groundPairCode at hpair
    rw [Bool.and_eq_true] at hpair
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpair.2
  apply exists_fixedTailPivotPresentation_of_missingDepth
    hg hpivotGround hfiller
  · intro j
    exact subsequence.pivot_run (i := 0) (j := j) (Nat.zero_le j)
  · intro j
    exact path.exists_actions_segmentWord hgroundSteps hground
      (subsequence.levels 0)
      (subsequence.levels j - subsequence.levels 0)
  · exact hmissing

end LeftBalancingSubsequence

namespace RightBalancingSubsequence

/-- The word from the first retained right-balancing pivot to the `j`th one. -/
@[expose] public noncomputable def bridgeLabels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : RightBalancingSubsequence sequence)
    (j : ℕ) : List (Label Action) :=
  path.segmentWord (subsequence.levels 0)
    (subsequence.levels j - subsequence.levels 0)

/-- The maximal-initial-depth premise for the retained left-side pivot
stream. -/
@[expose] public def HasMissingPivotExposureDepth
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : RightBalancingSubsequence sequence) : Prop :=
  g.HasMissingExposureDepth (subsequence.pivot 0)
    subsequence.bridgeLabels

/-- Every right-balancing pivot is presented over one fixed tail tuple once
the retained pivot stream has a missing exposure depth. -/
public theorem exists_fixedTailPivotPresentation
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight} {bound : ℕ}
    {sequence : BalancingOpportunitySequence path bound}
    (subsequence : RightBalancingSubsequence sequence)
    (hgroundSteps : g.PreservesGroundSteps)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hfiller : filler.Ground g.ranks)
    (hmissing : subsequence.HasMissingPivotExposureDepth) :
    Nonempty (FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot) := by
  have hpivotGround :
      (subsequence.pivot 0).Ground g.ranks := by
    have hpair := path.residual_ground hgroundSteps hground
      (subsequence.levels 0)
    unfold groundPairCode at hpair
    rw [Bool.and_eq_true] at hpair
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpair.1
  apply exists_fixedTailPivotPresentation_of_missingDepth
    hg hpivotGround hfiller
  · intro j
    exact subsequence.pivot_run (i := 0) (j := j) (Nat.zero_le j)
  · intro j
    exact path.exists_actions_segmentWord hgroundSteps hground
      (subsequence.levels 0)
      (subsequence.levels j - subsequence.levels 0)
  · exact hmissing

end RightBalancingSubsequence

end EncodedFirstOrderGrammar

end DCFEquivalence
