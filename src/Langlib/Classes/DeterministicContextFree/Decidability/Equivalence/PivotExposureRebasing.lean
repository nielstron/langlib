module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotChain
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailPivotSubsequence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedSemanticReachability
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.NonSinkingApplicationDepth

@[expose]
public section

/-!
# Rebasing a pivot trajectory at a maximal exposed depth

The second half of the Proposition-49 `M₂` dichotomy starts once the
exposure depths of the concrete pivot path are known to be bounded.  This
file isolates that order-theoretic and operational step.

There is then a genuinely maximal exposed depth.  Choosing an exact exposing
prefix at that depth and rebasing the remaining pivot trajectory at its
target gives one fixed ground base from which no remaining pivot word can
expose any positive depth.  In particular no prefix sinks from that base.

The complementary, unbounded-exposure branch is the part that uses the
`M₂` window lemma to force a derived repeat; it is intentionally separate.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath.StructuredPivotChain.PivotTrajectory

/-- Concatenation of `count` pivot-edge words beginning at `start`. -/
@[expose] public def edgeSegment
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory)
    (start : ℕ) : ℕ → List (Label Action)
  | 0 => []
  | count + 1 =>
      trajectory.edgeSegment start count ++
        trajectory.edgeWords (start + count)

/-- Accumulated pivot words split at every pivot index. -/
public theorem prefixWord_add
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory)
    (start count : ℕ) :
    trajectory.prefixWord (start + count) =
      trajectory.prefixWord start ++ trajectory.edgeSegment start count := by
  induction count with
  | zero => simp [edgeSegment]
  | succ count ih =>
      rw [Nat.add_succ, prefixWord, edgeSegment, ih]
      simp [List.append_assoc]

/-- An edge segment executes exactly between its endpoint representatives. -/
public theorem edgeSegment_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory)
    (start count : ℕ) :
    g.run? (trajectory.edgeSegment start count)
        (trajectory.representatives start) =
      some (trajectory.representatives (start + count)) := by
  induction count with
  | zero => simp [edgeSegment]
  | succ count ih =>
      rw [edgeSegment, g.run?_append, ih]
      simpa [Nat.add_assoc] using trajectory.edge_run (start + count)

/-- The pivot path exposes depths only below one finite upper bound. -/
@[expose] public def HasBoundedExposureDepths
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory) : Prop :=
  ∃ depthBound, ∀ depth,
    g.EverExposesDepth (trajectory.representatives 0)
        trajectory.prefixWord depth →
      depth ≤ depthBound

/-- A depth which is exposed by the pivot path and dominates every other
exposed depth. -/
public structure MaximalExposure
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory) where
  depth : ℕ
  exposed :
    g.EverExposesDepth (trajectory.representatives 0)
      trajectory.prefixWord depth
  maximal : ∀ other,
    g.EverExposesDepth (trajectory.representatives 0)
        trajectory.prefixWord other →
      other ≤ depth

/-- A bounded nonempty set of natural exposure depths has a maximum.  The
set is nonempty because depth zero is exposed by the empty prefix. -/
public theorem exists_maximalExposure
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory)
    (hbounded : trajectory.HasBoundedExposureDepths) :
    Nonempty trajectory.MaximalExposure := by
  classical
  let upper : ℕ := Nat.find hbounded
  have hupper : ∀ depth,
      g.EverExposesDepth (trajectory.representatives 0)
          trajectory.prefixWord depth →
        depth ≤ upper :=
    Nat.find_spec hbounded
  have hupperExposed :
      g.EverExposesDepth (trajectory.representatives 0)
        trajectory.prefixWord upper := by
    by_cases hzero : upper = 0
    · refine ⟨0, ?_⟩
      simpa [hzero] using
        (g.exposesBy_zero (trajectory.representatives 0)
          (trajectory.prefixWord 0))
    · by_contra hnotExposed
      have hpredUpper : ∀ depth,
          g.EverExposesDepth (trajectory.representatives 0)
              trajectory.prefixWord depth →
            depth ≤ upper - 1 := by
        intro depth hexposed
        have hle := hupper depth hexposed
        have hne : depth ≠ upper := by
          intro heq
          subst depth
          exact hnotExposed hexposed
        omega
      have hminimal := Nat.find_min hbounded
        (show upper - 1 < Nat.find hbounded by
          simpa [upper] using (show upper - 1 < upper by omega))
      exact hminimal hpredUpper
  exact ⟨
    { depth := upper
      exposed := hupperExposed
      maximal := hupper }⟩

/-- Concrete suffix data obtained by cutting the pivot trajectory at one
exact maximal-depth exposing prefix. -/
public structure MaximalExposureRebase
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory) where
  maximalExposure : trajectory.MaximalExposure
  start : ℕ
  first : List (Label Action)
  remainder : List (Label Action)
  prefix_eq : trajectory.prefixWord start = first ++ remainder
  subterm : RegularTerm
  base : RegularTerm
  subterm_at :
    (trajectory.representatives 0).SubtermAtDepth
      maximalExposure.depth subterm
  first_run : g.run? first (trajectory.representatives 0) = some base
  base_matches : base.UnfoldingEquivalent subterm

namespace MaximalExposureRebase

/-- Word from the rebased target to the `count`th retained pivot. -/
@[expose] public def labels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
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
    (rebase : trajectory.MaximalExposureRebase)
    (count : ℕ) : List (Label Action) :=
  rebase.remainder ++ trajectory.edgeSegment rebase.start count

/-- The original accumulated pivot word factors through the rebased word. -/
public theorem prefixWord_start_add
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
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
    (rebase : trajectory.MaximalExposureRebase)
    (count : ℕ) :
    trajectory.prefixWord (rebase.start + count) =
      rebase.first ++ rebase.labels count := by
  rw [trajectory.prefixWord_add, rebase.prefix_eq]
  simp [labels, List.append_assoc]

/-- Every rebased word executes exactly to its retained pivot. -/
public theorem labels_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
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
    (rebase : trajectory.MaximalExposureRebase)
    (count : ℕ) :
    g.run? (rebase.labels count) rebase.base =
      some (trajectory.representatives (rebase.start + count)) := by
  have hfull := trajectory.prefixWord_run (rebase.start + count)
  rw [rebase.prefixWord_start_add, g.run?_append,
    rebase.first_run] at hfull
  exact hfull

/-- The rebased base is ground. -/
public theorem base_ground
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
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
    (rebase : trajectory.MaximalExposureRebase) :
    rebase.base.Ground g.ranks := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact hgroundSteps.ground_of_run
    (trajectory.representative_ground 0) rebase.first_run

/-- Every rebased word consists only of ordinary grammar actions. -/
public theorem exists_actions_labels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
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
    (rebase : trajectory.MaximalExposureRebase)
    (count : ℕ) :
    ∃ actions : List Action,
      rebase.labels count = actions.map Sum.inl := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact hgroundSteps.exists_actions_of_ground_run
    rebase.base_ground (rebase.labels_run count)

/-- Maximality rules out every positive-depth exposure after rebasing. -/
public theorem not_exposes_positive
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
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
    (rebase : trajectory.MaximalExposureRebase)
    (count depth : ℕ) (hdepth : 0 < depth) :
    ¬g.ExposesBy rebase.base (rebase.labels count) depth := by
  intro hexposes
  obtain ⟨initialSegment, suffix, hlabels, hexact⟩ := hexposes
  have hcombined : g.ExposesAtDepth
      (trajectory.representatives 0)
      (rebase.first ++ initialSegment)
      (rebase.maximalExposure.depth + depth) :=
    ExposesAtDepth.append_of_run rebase.subterm_at
      rebase.first_run rebase.base_matches hexact
  have hever : g.EverExposesDepth
      (trajectory.representatives 0) trajectory.prefixWord
      (rebase.maximalExposure.depth + depth) := by
    refine ⟨rebase.start + count, ?_⟩
    refine ⟨rebase.first ++ initialSegment, suffix, ?_, hcombined⟩
    rw [rebase.prefixWord_start_add, hlabels, List.append_assoc]
  have hle := rebase.maximalExposure.maximal _ hever
  omega

/-- No prefix of any rebased ordinary word sinks from the fixed base. -/
public theorem neverSinksFromBase
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
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
    (rebase : trajectory.MaximalExposureRebase)
    (count : ℕ) (actions : List Action)
    (hlabels : rebase.labels count = actions.map Sum.inl) :
    g.NeverSinksFromBase rebase.base actions := by
  intro stem suffix hword hsinks
  apply rebase.not_exposes_positive count 1 (by omega)
  obtain ⟨initialSegment, remainder, hsinkWord,
      _hnonempty, hexact⟩ := hsinks
  refine ⟨initialSegment,
    remainder ++ suffix.map Sum.inl, ?_, hexact⟩
  calc
    rebase.labels count = actions.map Sum.inl := hlabels
    _ = stem.map Sum.inl ++ suffix.map Sum.inl := by
      rw [hword, List.map_append]
    _ = (initialSegment ++ remainder) ++ suffix.map Sum.inl := by
      rw [hsinkWord]
    _ = initialSegment ++ (remainder ++ suffix.map Sum.inl) :=
      List.append_assoc _ _ _

/-- At any prescribed positive depth, the rebased pivots admit one fixed-tail
presentation whose ordinary words never sink from the common base. -/
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
    (rebase : trajectory.MaximalExposureRebase)
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
  obtain ⟨presentation, hpresentationDepth⟩ :=
    DCFEquivalence.EncodedFirstOrderGrammar.exists_fixedTailPivotPresentation_atDepth
      (g := g) hg rebase.base_ground hfiller depth
        rebase.labels_run rebase.exists_actions_labels
        (fun count => rebase.not_exposes_positive count depth hdepth)
  refine ⟨presentation, hpresentationDepth, ?_⟩
  intro count
  exact rebase.neverSinksFromBase count
    (presentation.actions count) (presentation.labels_eq count)

end MaximalExposureRebase

/-- Choosing witnesses from a maximal exposed depth produces the concrete
rebasing package. -/
public theorem exists_maximalExposureRebase
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory)
    (hbounded : trajectory.HasBoundedExposureDepths) :
    Nonempty trajectory.MaximalExposureRebase := by
  let maximal := Classical.choice
    (trajectory.exists_maximalExposure hbounded)
  let start := Classical.choose maximal.exposed
  have hexposes := Classical.choose_spec maximal.exposed
  let first := Classical.choose hexposes
  have hfirst := Classical.choose_spec hexposes
  let remainder := Classical.choose hfirst
  have hremainder := Classical.choose_spec hfirst
  have hprefix := hremainder.1
  have hexact := hremainder.2
  let subterm := Classical.choose hexact
  have hsubtermChoice := Classical.choose_spec hexact
  let base := Classical.choose hsubtermChoice
  have hbaseChoice := Classical.choose_spec hsubtermChoice
  have hsubterm := hbaseChoice.1
  have hrun := hbaseChoice.2.1
  have hmatches := hbaseChoice.2.2
  exact ⟨
    { maximalExposure := maximal
      start := start
      first := first
      remainder := remainder
      prefix_eq := hprefix
      subterm := subterm
      base := base
      subterm_at := hsubterm
      first_run := hrun
      base_matches := hmatches }⟩

end TracePath.StructuredPivotChain.PivotTrajectory

end EncodedFirstOrderGrammar

end DCFEquivalence
