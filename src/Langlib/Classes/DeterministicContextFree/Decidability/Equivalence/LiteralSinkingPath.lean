module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotM2Window

@[expose]
public section

/-!
# Literal subterm paths behind repeated sinking

`RepeatedlySinksBy` follows the concrete graph reached by each sinking
prefix.  That graph is only unfolding-equivalent to the selected subterm:
root rewriting can leave unreachable graph nodes behind, so equality of graph
codes would be too strong.

The relation below normalizes after every sinking prefix to the *literal*
subterm selected in the current canonical source.  Consequently its recursive
spine is an honest syntactic path through nested `SubtermAtDepth 1`
occurrences, while each concrete run endpoint is still recorded by the
corresponding `SinkingStep`.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Repeated sinking whose recursive sources are the literal subterms selected
by the preceding step.

The concrete endpoint of `step` need not have the same graph code as
`step.subterm`; `SinkingStep.target_matches` is the exact semantic bridge
between those two presentations. -/
public inductive LiteralRepeatedlySinksBy
    (g : EncodedFirstOrderGrammar Action) :
    RegularTerm → List (Label Action) → ℕ → Prop
  | zero (source word) :
      LiteralRepeatedlySinksBy g source word 0
  | succ {source word stem suffix target depth}
      (word_eq : word = stem ++ suffix)
      (step : SinkingStep g source stem target)
      (rest :
        LiteralRepeatedlySinksBy g step.subterm suffix depth) :
      LiteralRepeatedlySinksBy g source word (depth + 1)

@[simp] public theorem literalRepeatedlySinksBy_zero
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List (Label Action)) :
    g.LiteralRepeatedlySinksBy source word 0 :=
  .zero source word

/-- A repeated-sinking witness from a ground source can be normalized after
each step to the literal selected subterm. -/
public theorem RepeatedlySinksBy.toLiteral
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsource : source.Ground g.ranks)
    (hsinks : g.RepeatedlySinksBy source word depth) :
    g.LiteralRepeatedlySinksBy source word depth := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  induction depth generalizing source word with
  | zero =>
      exact .zero source word
  | succ depth ih =>
      obtain ⟨stem, suffix, target, hword, ⟨step⟩, hrest⟩ :=
        hsinks
      have htargetGround : target.Ground g.ranks :=
        hgroundSteps.ground_of_run hsource step.run
      have hsubtermGround : step.subterm.Ground g.ranks := by
        obtain ⟨index, hdescendant, hsubterm⟩ := step.subterm_at
        rw [hsubterm]
        exact hsource.withRoot_descendant hdescendant
      have hrestFromLiteral :
          g.RepeatedlySinksBy step.subterm suffix depth :=
        RepeatedlySinksBy.of_unfoldingEquivalent hg
          hsubtermGround htargetGround step.target_matches.symm hrest
      exact .succ hword step
        (ih hsubtermGround hrestFromLiteral)

/-- The canonical endpoint of a literal sinking path is a literal subterm at
exactly the accumulated depth of its original source. -/
public theorem LiteralRepeatedlySinksBy.exists_subtermAtDepth
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsinks : g.LiteralRepeatedlySinksBy source word depth) :
    ∃ target, source.SubtermAtDepth depth target := by
  induction hsinks with
  | zero source _word =>
      exact ⟨source, by simp⟩
  | succ _word_eq step _rest ih =>
      obtain ⟨target, htarget⟩ := ih
      exact ⟨target, by
        simpa [Nat.add_comm] using
          RegularTerm.SubtermAtDepth.trans step.subterm_at htarget⟩

/-- Literal normalization does not change the progress lower bound: every
syntactic descent consumes at least one input label. -/
public theorem LiteralRepeatedlySinksBy.depth_le_length
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsinks : g.LiteralRepeatedlySinksBy source word depth) :
    depth ≤ word.length := by
  induction hsinks with
  | zero => omega
  | succ hword step _rest ih =>
      have hstem : 1 ≤ _ :=
        List.length_pos_iff.mpr step.word_nonempty
      rw [hword, List.length_append]
      omega

/-- Repeated sinking with the per-step root-sinking budget retained.

This is the information present in the `noBalancingBefore` construction but
forgotten by `RepeatedlySinksBy`: every selected nonempty sinking prefix has
length at most `bound`. -/
public inductive BoundedRepeatedlySinksBy
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) :
    RegularTerm → List (Label Action) → ℕ → Prop
  | zero (source word) :
      BoundedRepeatedlySinksBy g bound source word 0
  | succ {source word stem suffix target depth}
      (word_eq : word = stem ++ suffix)
      (step : SinkingStep g source stem target)
      (step_length_le : stem.length ≤ bound)
      (rest :
        BoundedRepeatedlySinksBy g bound target suffix depth) :
      BoundedRepeatedlySinksBy g bound source word (depth + 1)

@[simp] public theorem boundedRepeatedlySinksBy_zero
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ)
    (source : RegularTerm) (word : List (Label Action)) :
    g.BoundedRepeatedlySinksBy bound source word 0 :=
  .zero source word

/-- Appending unused labels preserves every retained sinking-prefix bound. -/
public theorem BoundedRepeatedlySinksBy.append
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} {source : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hsinks : g.BoundedRepeatedlySinksBy
      bound source word depth)
    (suffix : List (Label Action)) :
    g.BoundedRepeatedlySinksBy
      bound source (word ++ suffix) depth := by
  induction depth generalizing source word with
  | zero =>
      exact .zero source (word ++ suffix)
  | succ depth ih =>
      cases hsinks with
      | succ hword step hstepLength hrest =>
          refine .succ ?_ step hstepLength (ih hrest)
          rw [hword, List.append_assoc]

/-- Forgetting the per-step bounds recovers ordinary repeated sinking. -/
public theorem BoundedRepeatedlySinksBy.toRepeatedlySinksBy
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} {source : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hsinks : g.BoundedRepeatedlySinksBy
      bound source word depth) :
    g.RepeatedlySinksBy source word depth := by
  induction hsinks with
  | zero => trivial
  | succ hword step _hstepLength _rest ih =>
      exact ⟨_, _, _, hword, ⟨step⟩, ih⟩

/-- Forgetting the open root computations preserves every selected
per-step length bound. -/
public theorem BoundedRepeatedlyRootSinksBy.toBoundedRepeatedlySinksBy
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} {source : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hsinks : g.BoundedRepeatedlyRootSinksBy
      bound source word depth) :
    g.BoundedRepeatedlySinksBy bound source word depth := by
  induction hsinks with
  | zero =>
      exact .zero _ _
  | succ hword step hstepLength _rest ih =>
      exact .succ hword step.semantic hstepLength ih

/-- Bounded repeated sinking is invariant under semantic equality of ground
sources, without changing any selected prefix or its length bound. -/
public theorem BoundedRepeatedlySinksBy.of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} {left right : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hleft : left.Ground g.ranks)
    (hright : right.Ground g.ranks)
    (hequivalent : left.UnfoldingEquivalent right)
    (hsinks : g.BoundedRepeatedlySinksBy
      bound right word depth) :
    g.BoundedRepeatedlySinksBy bound left word depth := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  induction depth generalizing left right word with
  | zero =>
      exact .zero left word
  | succ depth ih =>
      cases hsinks with
      | @succ source word stem suffix target depth
          hword rightStep hstepLength hrest =>
          obtain ⟨leftSubterm, hleftSubterm, hsubterms⟩ :=
            hequivalent.symm.exists_subtermAtDepth
              rightStep.subterm_at
          obtain ⟨leftTarget, hleftRun, htargets⟩ :=
            exists_run_of_unfoldingEquivalent hg hequivalent
              (RegularTerm.referenceClosed_of_ground hleft)
              (RegularTerm.referenceClosed_of_ground hright)
              rightStep.run
          have hleftTargetGround : leftTarget.Ground g.ranks :=
            hgroundSteps.ground_of_run hleft hleftRun
          have hrightTargetGround :
              target.Ground g.ranks :=
            hgroundSteps.ground_of_run hright rightStep.run
          let leftStep : SinkingStep g left _ leftTarget :=
            { subterm := leftSubterm
              word_nonempty := rightStep.word_nonempty
              subterm_at := hleftSubterm
              run := hleftRun
              target_matches :=
                htargets.trans
                  (rightStep.target_matches.trans hsubterms) }
          exact .succ hword leftStep hstepLength
            (ih hleftTargetGround hrightTargetGround htargets hrest)

/-- The bounded relation with recursive sources normalized to literal selected
subterms. -/
public inductive BoundedLiteralRepeatedlySinksBy
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) :
    RegularTerm → List (Label Action) → ℕ → Prop
  | zero (source word) :
      BoundedLiteralRepeatedlySinksBy g bound source word 0
  | succ {source word stem suffix target depth}
      (word_eq : word = stem ++ suffix)
      (step : SinkingStep g source stem target)
      (step_length_le : stem.length ≤ bound)
      (rest :
        BoundedLiteralRepeatedlySinksBy
          g bound step.subterm suffix depth) :
      BoundedLiteralRepeatedlySinksBy
        g bound source word (depth + 1)

@[simp] public theorem boundedLiteralRepeatedlySinksBy_zero
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ)
    (source : RegularTerm) (word : List (Label Action)) :
    g.BoundedLiteralRepeatedlySinksBy bound source word 0 :=
  .zero source word

/-- Normalize a bounded concrete sinking spine to its literal selected
subterms. -/
public theorem BoundedRepeatedlySinksBy.toLiteral
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} {source : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hsource : source.Ground g.ranks)
    (hsinks : g.BoundedRepeatedlySinksBy
      bound source word depth) :
    g.BoundedLiteralRepeatedlySinksBy
      bound source word depth := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  induction depth generalizing source word with
  | zero =>
      exact .zero source word
  | succ depth ih =>
      cases hsinks with
      | @succ source word stem suffix target depth
          hword step hstepLength hrest =>
          have htargetGround : target.Ground g.ranks :=
            hgroundSteps.ground_of_run hsource step.run
          have hsubtermGround : step.subterm.Ground g.ranks := by
            obtain ⟨index, hdescendant, hsubterm⟩ :=
              step.subterm_at
            rw [hsubterm]
            exact hsource.withRoot_descendant hdescendant
          have hrestFromLiteral :
              g.BoundedRepeatedlySinksBy
                bound step.subterm _ depth :=
            hrest.of_unfoldingEquivalent hg
              hsubtermGround htargetGround
              step.target_matches.symm
          exact .succ hword step hstepLength
            (ih hsubtermGround hrestFromLiteral)

/-- Forgetting the retained budgets recovers the unbounded literal path. -/
public theorem BoundedLiteralRepeatedlySinksBy.toLiteralRepeatedlySinksBy
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} {source : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hsinks : g.BoundedLiteralRepeatedlySinksBy
      bound source word depth) :
    g.LiteralRepeatedlySinksBy source word depth := by
  induction hsinks with
  | zero =>
      exact .zero _ _
  | succ hword step _hstepLength _rest ih =>
      exact .succ hword step ih

/-- A fixed-window sinking region together with its canonical literal
subterm path.

`windows_sink` retains the actual `window`-sized follow-up paths.  The
separate `literal_path` records the nested literal subterms selected while
those paths are consumed.  Keeping both components is important: one
follow-up window may contain more than one root-sinking event. -/
public structure FixedWindowLiteralSinkingPath
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List (Label Action))
    (window depth : ℕ) : Prop where
  word_length : word.length = depth * window
  windows_sink :
    ∀ k, k < depth →
      ∃ intermediate,
        g.run? (word.take (k * window)) source =
            some intermediate ∧
          g.SinksBy intermediate
            ((word.drop (k * window)).take window)
  literal_path :
    g.LiteralRepeatedlySinksBy source word depth

/-- Every indexed follow-up word in a fixed-window path has exactly the
declared window length. -/
public theorem FixedWindowLiteralSinkingPath.window_length
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {window depth : ℕ}
    (path : g.FixedWindowLiteralSinkingPath
      source word window depth)
    {k : ℕ} (hk : k < depth) :
    ((word.drop (k * window)).take window).length = window := by
  have hfit : k * window + window ≤ word.length := by
    rw [path.word_length, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right window (Nat.succ_le_of_lt hk)
  simp only [List.length_take, List.length_drop]
  exact Nat.min_eq_left
    (Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hfit))

namespace TracePath

/-- The left `noBalancingBefore` construction with its per-step
`offset ≤ bound` facts retained. -/
public theorem boundedRepeatedlySinksLeft_of_noBalancingBefore
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hg : g.WellFormed)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound depth : ℕ)
    (hsource : ∃ variableBound,
      (path.left start).WellFormed g.ranks variableBound)
    (hbound : 0 < bound)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasLeftBalancingOpportunity bound (start + offset)) :
    g.BoundedRepeatedlySinksBy bound
      (path.left start)
      (path.segmentWord start (depth * bound))
      depth := by
  exact
    (path.boundedRepeatedlyRootSinksLeft_of_noBalancingBefore
      hg hinitial start bound depth hsource hbound hno)
      |>.toBoundedRepeatedlySinksBy

/-- Symmetric bounded `noBalancingBefore` construction for the right side. -/
public theorem boundedRepeatedlySinksRight_of_noBalancingBefore
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hg : g.WellFormed)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound depth : ℕ)
    (hsource : ∃ variableBound,
      (path.right start).WellFormed g.ranks variableBound)
    (hbound : 0 < bound)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasRightBalancingOpportunity bound (start + offset)) :
    g.BoundedRepeatedlySinksBy bound
      (path.right start)
      (path.segmentWord start (depth * bound))
      depth := by
  exact
    (path.boundedRepeatedlyRootSinksRight_of_noBalancingBefore
      hg hinitial start bound depth hsource hbound hno)
      |>.toBoundedRepeatedlySinksBy

/-- Literal-subterm corollary of the bounded left no-balancing
construction. -/
public theorem boundedLiteralRepeatedlySinksLeft_of_noBalancingBefore
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hg : g.WellFormed)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound depth : ℕ)
    (hsource : (path.left start).Ground g.ranks)
    (hbound : 0 < bound)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasLeftBalancingOpportunity bound (start + offset)) :
    g.BoundedLiteralRepeatedlySinksBy bound
      (path.left start)
      (path.segmentWord start (depth * bound))
      depth :=
  (path.boundedRepeatedlySinksLeft_of_noBalancingBefore
    hg hinitial start bound depth
      (RegularTerm.Ground.exists_wellFormed hsource) hbound hno)
    |>.toLiteral hg hsource

/-- Literal-subterm corollary of the bounded right no-balancing
construction. -/
public theorem boundedLiteralRepeatedlySinksRight_of_noBalancingBefore
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hg : g.WellFormed)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound depth : ℕ)
    (hsource : (path.right start).Ground g.ranks)
    (hbound : 0 < bound)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasRightBalancingOpportunity bound (start + offset)) :
    g.BoundedLiteralRepeatedlySinksBy bound
      (path.right start)
      (path.segmentWord start (depth * bound))
      depth :=
  (path.boundedRepeatedlySinksRight_of_noBalancingBefore
    hg hinitial start bound depth
      (RegularTerm.Ground.exists_wellFormed hsource) hbound hno)
    |>.toLiteral hg hsource

namespace StructuredPivotChain

namespace WindowedPivotTrajectory

/-- The post-prefix part of a structured pivot edge has the exact form used
by the special-pivot argument: a sequence of fixed-length sinking paths, plus
an honest nested path through literal subterms. -/
public theorem tail_fixedWindowLiteralSinkingPath
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
    (j depth skip : ℕ)
    (hshort :
      g.structuredPivotShortPrefixBound bound ≤ skip)
    (hfit :
      skip + depth * bound ≤
        (trajectory.toPivotTrajectory.edgeWords j).length) :
    ∃ intermediate,
      g.run? ((trajectory.toPivotTrajectory.edgeWords j).take skip)
          (trajectory.toPivotTrajectory.representatives j) =
        some intermediate ∧
      g.FixedWindowLiteralSinkingPath intermediate
        (((trajectory.toPivotTrajectory.edgeWords j).drop skip).take
          (depth * bound))
        bound depth := by
  let edge := trajectory.toPivotTrajectory.edgeWords j
  obtain ⟨intermediate, hskipRun, hsinks⟩ :=
    trajectory.tail_repeatedly_sinks
      hbound j depth skip hshort (by simpa [edge] using hfit)
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hintermediateGround : intermediate.Ground g.ranks :=
    hgroundSteps.ground_of_run
      (trajectory.toPivotTrajectory.representative_ground j)
      hskipRun
  refine ⟨intermediate, hskipRun, ?_⟩
  refine
    { word_length := ?_
      windows_sink := ?_
      literal_path := hsinks.toLiteral hg hintermediateGround }
  · have hsliceFit :
        depth * bound ≤ (edge.drop skip).length := by
      rw [List.length_drop]
      exact Nat.le_sub_of_add_le
        (by simpa [edge, Nat.add_comm] using hfit)
    rw [List.length_take, Nat.min_eq_left hsliceFit]
  · intro k hk
    let offset := k * bound
    have hoffsetLe : offset ≤ depth * bound := by
      exact Nat.mul_le_mul_right bound (Nat.le_of_lt hk)
    have hnextLe : offset + bound ≤ depth * bound := by
      change k * bound + bound ≤ depth * bound
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right bound (Nat.succ_le_of_lt hk)
    have hglobalFit :
        skip + offset + bound ≤ edge.length := by
      calc
        skip + offset + bound = skip + (offset + bound) := by
          omega
        _ ≤ skip + depth * bound :=
          Nat.add_le_add_left hnextLe skip
        _ ≤ edge.length := by simpa [edge] using hfit
    obtain ⟨windowState, hwindowRun, hwindowSink⟩ :=
      trajectory.tail_windows_sink
        hbound j (skip + offset)
          (hshort.trans (Nat.le_add_right skip offset))
          (by simpa [edge, Nat.add_assoc] using hglobalFit)
    have hprefix :
        edge.take (skip + offset) =
          edge.take skip ++
            (((edge.drop skip).take (depth * bound)).take offset) := by
      rw [List.take_add, List.take_take,
        Nat.min_eq_left hoffsetLe]
    have hlocalRun :
        g.run?
            (((edge.drop skip).take (depth * bound)).take offset)
            intermediate =
          some windowState := by
      rw [hprefix, g.run?_append, hskipRun] at hwindowRun
      exact hwindowRun
    have hwindowWord :
        ((((edge.drop skip).take (depth * bound)).drop offset).take
            bound) =
          (edge.drop (skip + offset)).take bound := by
      have hboundLe : bound ≤ depth * bound - offset :=
        Nat.le_sub_of_add_le
          (by simpa [Nat.add_comm] using hnextLe)
      simp only [List.drop_take, List.take_take]
      simp only [Nat.min_eq_left hboundLe]
      rw [List.drop_drop]
    refine ⟨windowState, ?_, ?_⟩
    · simpa [edge, offset] using hlocalRun
    · simpa [edge, offset, hwindowWord] using hwindowSink

/-- Exact syntactic form of the structured-edge `M₂` dichotomy.

The second branch consists of a uniformly bounded starting prefix followed by
`depth` fixed-length sinking paths.  Its `literal_path` field names the
literal nested subterms visited while those paths are consumed. -/
public theorem edgePosition_reachesPivot_or_fixedWindowLiteralSinkingPath
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
        g.FixedWindowLiteralSinkingPath
          intermediate sinkingWord bound depth := by
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
    obtain ⟨intermediate, hskipRun, hfixed⟩ :=
      trajectory.tail_fixedWindowLiteralSinkingPath
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
      hpreludeRun, ?_⟩
    · rw [hdropSplit, hsinkingSplit, List.append_assoc]
    · exact (List.length_take_le _ _).trans hleadShort
    · simpa [sinkingWord, edge] using hfixed

end WindowedPivotTrajectory

end StructuredPivotChain

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
