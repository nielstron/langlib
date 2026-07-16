module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotContextDepth
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SchemaBalancingBoundedCoverage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.WitnessedBalancingStairAssembly

@[expose]
public section

/-!
# Fixed-tail balancing stair assembly

This file completes the structural part of Proposition 49 after a retained
pivot stream has been presented over one fixed tuple.  The only additional
local facts needed by the fixed-argument Proposition-45 constructor are:

* every retained pivot schema protects the whole balancing-word depth; and
* its graph size is bounded by the chosen growth function.

Both orientations are handled explicitly.  Groundness, residual
equivalence, the outer certificate row, the active root application, the
fixed argument count, and argument groundness are all discharged from the
path and the fixed-tail presentation.

The remaining global Proposition-49 step is therefore precise: construct
these protected, uniformly bounded presentations with a grammar-uniform
width and growth function.  The raw least-missing-depth presentation in
`FixedTailPivotSubsequence` alone does not provide those quantitative facts.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace FixedTailPivotPresentation

/-- The common padded arity always includes the grammar's maximum rank. -/
public theorem rankMax_le_arity
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots) :
    g.ranks.foldr max 0 ≤ presentation.arity := by
  simp [arity, DepthPrefix.schemaArity]

/-- The canonical path-local schema bound supplied by fixed-tail
reflection.  Making it explicit separates the already-proved local size
estimate from the still-missing grammar-uniform growth estimate. -/
@[expose] public def schemaGrowth
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (j : ℕ) : ℕ :=
    g.residualNodeBound (presentation.actions j).length
    (FiniteHead.compiledDepthBound
      (g.ranks.foldr max 0) presentation.depth)

/-- Fixed-tail reflection supplies its canonical path-local size bound
without any further premise. -/
public theorem schema_nodes_length_le_schemaGrowth
    {g : EncodedFirstOrderGrammar Action}
    {base filler : RegularTerm}
    {labels : ℕ → List (Label Action)}
    {pivots : ℕ → RegularTerm}
    (presentation :
      FixedTailPivotPresentation g base filler labels pivots)
    (j : ℕ) :
    (presentation.schema j).nodes.length ≤ presentation.schemaGrowth j :=
  presentation.schema_size_le j

end FixedTailPivotPresentation

namespace LeftBalancingSubsequence

/-- A fixed-tail presentation of the retained right-side pivots, with
protected balancing depth and a pointwise schema-size bound, produces a
witnessed regular active stair on the original path. -/
public def toWitnessedRegularActiveStairSequence_of_fixedTail
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : LeftBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (schemaGrowth : ℕ → ℕ)
    (hdepth : presentation.ProtectsDepth segmentBound)
    (hsize : ∀ j,
      (presentation.schema j).nodes.length ≤ schemaGrowth j) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      presentation.width
      (fun j => g.fixedBalancingPresentationBound segmentBound
        presentation.arity (schemaGrowth j))
      path := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  let levels : ℕ → ℕ :=
    fun j => subsequence.levels j + segmentBound
  refine
    { arguments := presentation.arguments
      levels := levels
      levels_strictMono := ?_
      covered := ?_ }
  · intro i j hij
    exact Nat.add_lt_add_right
      (subsequence.levels_strictMono hij) segmentBound
  · intro j
    let start := subsequence.levels j
    let segment := subsequence.segment j
    have hpairGround :=
      path.residual_ground hgroundSteps hground start
    unfold groundPairCode at hpairGround
    rw [Bool.and_eq_true] at hpairGround
    have hactive : (path.left start).Ground g.ranks :=
      (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpairGround.1
    have hpivot : (path.right start).Ground g.ranks :=
      (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpairGround.2
    have houter :=
      path.pair_derivable hgroundSteps hground hinitial start
    have hequivalent :=
      path.residual_traceEquivalent hinitial start
    obtain ⟨X, children, hroot⟩ := hactive.exists_rootApplication
    obtain ⟨coverage⟩ :=
      segment.exists_schemaBoundedWitnessedBalancingResult
        hg hnormal hexposureBound hactive hpivot hfiller
        houter hequivalent
        (presentation.schema_supported j)
        (presentation.schema_hasPrefixWitness j)
        presentation.rankMax_le_arity
        (hdepth j)
        presentation.arguments_length
        presentation.arguments_ground
        (presentation.schema_instance_matches j)
        (hsize j)
        hroot
    have hword :
        path.word start ++ path.segmentWord start segmentBound =
          path.word (start + segmentBound) := by
      exact (path.word_add start segmentBound).symm
    exact ⟨coverage.castWord (by
      simpa [segment, start, levels] using hword)⟩

/-- Using fixed-tail reflection's canonical local graph bound leaves only
the protected-depth premise in the path-local stair assembly. -/
public def
    toWitnessedRegularActiveStairSequence_of_fixedTail_canonicalGrowth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : LeftBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (hdepth : presentation.ProtectsDepth segmentBound) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      presentation.width
      (fun j => g.fixedBalancingPresentationBound segmentBound
        presentation.arity (presentation.schemaGrowth j))
      path :=
  subsequence.toWitnessedRegularActiveStairSequence_of_fixedTail
    hg hnormal hexposureBound hground hinitial hfiller presentation
    presentation.schemaGrowth hdepth
    presentation.schema_nodes_length_le_schemaGrowth

end LeftBalancingSubsequence

namespace RightBalancingSubsequence

/-- Symmetric fixed-tail stair assembly for retained left-side pivots. -/
public def toWitnessedRegularActiveStairSequence_of_fixedTail
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : RightBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (schemaGrowth : ℕ → ℕ)
    (hdepth : presentation.ProtectsDepth segmentBound)
    (hsize : ∀ j,
      (presentation.schema j).nodes.length ≤ schemaGrowth j) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      presentation.width
      (fun j => g.fixedBalancingPresentationBound segmentBound
        presentation.arity (schemaGrowth j))
      path := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  let levels : ℕ → ℕ :=
    fun j => subsequence.levels j + segmentBound
  refine
    { arguments := presentation.arguments
      levels := levels
      levels_strictMono := ?_
      covered := ?_ }
  · intro i j hij
    exact Nat.add_lt_add_right
      (subsequence.levels_strictMono hij) segmentBound
  · intro j
    let start := subsequence.levels j
    let segment := subsequence.segment j
    have hpairGround :=
      path.residual_ground hgroundSteps hground start
    unfold groundPairCode at hpairGround
    rw [Bool.and_eq_true] at hpairGround
    have hactive : (path.right start).Ground g.ranks :=
      (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpairGround.2
    have hpivot : (path.left start).Ground g.ranks :=
      (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpairGround.1
    have houter :=
      CertificateDerivable.symmetry
        (path.pair_derivable hgroundSteps hground hinitial start)
    have hequivalent :=
      (path.residual_traceEquivalent hinitial start).symm
    obtain ⟨X, children, hroot⟩ := hactive.exists_rootApplication
    obtain ⟨coverage⟩ :=
      segment.exists_schemaBoundedWitnessedBalancingResult
        hg hnormal hexposureBound hactive hpivot hfiller
        houter hequivalent
        (presentation.schema_supported j)
        (presentation.schema_hasPrefixWitness j)
        presentation.rankMax_le_arity
        (hdepth j)
        presentation.arguments_length
        presentation.arguments_ground
        (presentation.schema_instance_matches j)
        (hsize j)
        hroot
    have hword :
        path.word start ++ path.segmentWord start segmentBound =
          path.word (start + segmentBound) := by
      exact (path.word_add start segmentBound).symm
    exact ⟨coverage.castWord (by
      simpa [segment, start, levels] using hword)⟩

/-- Symmetric canonical-growth assembly. -/
public def
    toWitnessedRegularActiveStairSequence_of_fixedTail_canonicalGrowth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {segmentBound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ segmentBound)
    {sequence : BalancingOpportunitySequence path segmentBound}
    (subsequence : RightBalancingSubsequence sequence)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hfiller : filler.Ground g.ranks)
    (presentation : FixedTailPivotPresentation g
      (subsequence.pivot 0) filler subsequence.bridgeLabels
      subsequence.pivot)
    (hdepth : presentation.ProtectsDepth segmentBound) :
    WitnessedRegularActiveStairSequence g initialLeft initialRight
      presentation.width
      (fun j => g.fixedBalancingPresentationBound segmentBound
        presentation.arity (presentation.schemaGrowth j))
      path :=
  subsequence.toWitnessedRegularActiveStairSequence_of_fixedTail
    hg hnormal hexposureBound hground hinitial hfiller presentation
    presentation.schemaGrowth hdepth
    presentation.schema_nodes_length_le_schemaGrowth

end RightBalancingSubsequence

end EncodedFirstOrderGrammar

end DCFEquivalence
