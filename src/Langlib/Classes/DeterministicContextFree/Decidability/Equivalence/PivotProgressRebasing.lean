module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotM2Window

@[expose]
public section

/-!
# Rebasing at a maximal progress-making sinking depth

Semantic exposure is too coarse on cyclic regular terms: the empty word can
be semantically equal to occurrences at arbitrarily large unfolding depths.
This file instead maximizes the operational `RepeatedlySinksBy` predicate.
Its exact endpoint is a concrete fixed base, and maximality directly says
that no retained trajectory prefix can sink from that base.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- An exact repeated-sinking run records the final reached representative
and consumes precisely the displayed word. -/
public inductive ExactRepeatedSinkingRun
    (g : EncodedFirstOrderGrammar Action) :
    RegularTerm → List (Label Action) → ℕ → RegularTerm → Prop
  | nil (source : RegularTerm) :
      ExactRepeatedSinkingRun g source [] 0 source
  | cons
      {source middle target : RegularTerm}
      {first rest : List (Label Action)} {depth : ℕ}
      (step : SinkingStep g source first middle)
      (tail : ExactRepeatedSinkingRun g middle rest depth target) :
      ExactRepeatedSinkingRun g source
        (first ++ rest) (depth + 1) target

namespace ExactRepeatedSinkingRun

/-- The concatenated exact sinking blocks execute to the recorded endpoint. -/
public theorem run
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (chain : ExactRepeatedSinkingRun g source word depth target) :
    g.run? word source = some target := by
  induction chain with
  | nil => rfl
  | cons step tail ih =>
      rw [g.run?_append, step.run]
      exact ih

/-- An exact chain remains a repeated-sinking witness after appending unused
input. -/
public theorem repeatedlySinksBy_append
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (chain : ExactRepeatedSinkingRun g source word depth target)
    (suffix : List (Label Action)) :
    g.RepeatedlySinksBy source (word ++ suffix) depth := by
  induction chain with
  | nil => trivial
  | @cons source middle target first rest depth step tail ih =>
      refine ⟨first, rest ++ suffix, middle, ?_, ⟨step⟩, ih⟩
      simp [List.append_assoc]

/-- Append one exact sinking step at the final endpoint. -/
public theorem append_step
    {g : EncodedFirstOrderGrammar Action}
    {source middle target : RegularTerm}
    {word stepWord : List (Label Action)} {depth : ℕ}
    (chain : ExactRepeatedSinkingRun g source word depth middle)
    (step : SinkingStep g middle stepWord target) :
    ExactRepeatedSinkingRun g source
      (word ++ stepWord) (depth + 1) target := by
  induction chain with
  | nil =>
      simpa using ExactRepeatedSinkingRun.cons step
        (ExactRepeatedSinkingRun.nil target)
  | @cons source firstMiddle middle first rest priorDepth
      firstStep tail ih =>
      simpa [List.append_assoc] using
        ExactRepeatedSinkingRun.cons firstStep (ih step)

/-- A sinking prefix after the endpoint extends the exact chain by one
progress-making depth. -/
public theorem repeatedlySinksBy_succ_of_sinksBy
    {g : EncodedFirstOrderGrammar Action}
    {source base : RegularTerm}
    {consumed tail : List (Label Action)} {depth : ℕ}
    (chain : ExactRepeatedSinkingRun g source consumed depth base)
    (hsinks : g.SinksBy base tail) :
    g.RepeatedlySinksBy source (consumed ++ tail) (depth + 1) := by
  obtain ⟨stem, remainder, target, htail, ⟨step⟩⟩ :=
    hsinks.exists_sinkingStep_prefix
  have extended := chain.append_step step
  have hrepeated := extended.repeatedlySinksBy_append remainder
  simpa [htail, List.append_assoc] using hrepeated

end ExactRepeatedSinkingRun

/-- Every repeated-sinking witness has an exact consumed prefix, endpoint,
and unused remainder. -/
public theorem RepeatedlySinksBy.exists_exactPrefix
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsinks : g.RepeatedlySinksBy source word depth) :
    ∃ consumed remainder target,
      word = consumed ++ remainder ∧
        ExactRepeatedSinkingRun g source consumed depth target := by
  induction depth generalizing source word with
  | zero =>
      exact ⟨[], word, source, by simp,
        ExactRepeatedSinkingRun.nil source⟩
  | succ depth ih =>
      obtain ⟨first, suffix, middle, hword, ⟨step⟩, hrest⟩ :=
        hsinks
      obtain ⟨consumed, remainder, target, hsuffix, hchain⟩ :=
        ih hrest
      refine ⟨first ++ consumed, remainder, target, ?_,
        ExactRepeatedSinkingRun.cons step hchain⟩
      rw [hword, hsuffix, List.append_assoc]

namespace TracePath.StructuredPivotChain

namespace PivotTrajectory

/-- A repeated-sinking depth attained on the accumulated pivot path and
dominating every other attained depth. -/
public structure MaximalRepeatedSinkingDepth
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
    (trajectory : chain.PivotTrajectory) where
  depth : ℕ
  witnessed :
    ∃ count,
      g.RepeatedlySinksBy
        (trajectory.representatives 0)
        (trajectory.prefixWord count) depth
  maximal : ∀ other,
    (∃ count,
      g.RepeatedlySinksBy
        (trajectory.representatives 0)
        (trajectory.prefixWord count) other) →
      other ≤ depth

/-- Bounded repeated-sinking depths have an attained maximum. -/
public theorem exists_maximalRepeatedSinkingDepth
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
    (trajectory : chain.PivotTrajectory)
    (hbounded :
      ∃ depthBound, ∀ count depth,
        g.RepeatedlySinksBy
            (trajectory.representatives 0)
            (trajectory.prefixWord count)
            depth →
          depth ≤ depthBound) :
    Nonempty trajectory.MaximalRepeatedSinkingDepth := by
  classical
  let upper : ℕ := Nat.find hbounded
  have hupper : ∀ count depth,
      g.RepeatedlySinksBy
          (trajectory.representatives 0)
          (trajectory.prefixWord count)
          depth →
        depth ≤ upper :=
    Nat.find_spec hbounded
  have hupperWitnessed :
      ∃ count,
        g.RepeatedlySinksBy
          (trajectory.representatives 0)
          (trajectory.prefixWord count)
          upper := by
    by_cases hzero : upper = 0
    · exact ⟨0, by simp [hzero, prefixWord]⟩
    · by_contra hnotWitnessed
      have hpredUpper : ∀ count depth,
          g.RepeatedlySinksBy
              (trajectory.representatives 0)
              (trajectory.prefixWord count)
              depth →
            depth ≤ upper - 1 := by
        intro count depth hsinks
        have hle := hupper count depth hsinks
        have hne : depth ≠ upper := by
          intro heq
          subst depth
          exact hnotWitnessed ⟨count, hsinks⟩
        omega
      have hminimal := Nat.find_min hbounded
        (show upper - 1 < Nat.find hbounded by
          simpa [upper] using (show upper - 1 < upper by omega))
      exact hminimal hpredUpper
  exact ⟨
    { depth := upper
      witnessed := hupperWitnessed
      maximal := by
        rintro other ⟨count, hsinks⟩
        exact hupper count other hsinks }⟩

/-- Concrete suffix data obtained by cutting an exact maximal repeated-
sinking prefix at its operational endpoint. -/
public structure MaximalProgressRebase
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
    (trajectory : chain.PivotTrajectory) where
  maximalDepth : trajectory.MaximalRepeatedSinkingDepth
  start : ℕ
  consumed : List (Label Action)
  remainder : List (Label Action)
  prefix_eq :
    trajectory.prefixWord start = consumed ++ remainder
  base : RegularTerm
  exactRun :
    ExactRepeatedSinkingRun g
      (trajectory.representatives 0)
      consumed maximalDepth.depth base

namespace MaximalProgressRebase

/-- Word from the operational rebase target to a retained pivot. -/
@[expose] public def labels
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
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (count : ℕ) : List (Label Action) :=
  rebase.remainder ++ trajectory.edgeSegment rebase.start count

/-- Original accumulated words factor through the operational rebase. -/
public theorem prefixWord_start_add
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
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (count : ℕ) :
    trajectory.prefixWord (rebase.start + count) =
      rebase.consumed ++ rebase.labels count := by
  rw [trajectory.prefixWord_add, rebase.prefix_eq]
  simp [labels, List.append_assoc]

public theorem consumed_run
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
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase) :
    g.run? rebase.consumed (trajectory.representatives 0) =
      some rebase.base :=
  rebase.exactRun.run

/-- Every rebased word executes to its retained pivot. -/
public theorem labels_run
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
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (count : ℕ) :
    g.run? (rebase.labels count) rebase.base =
      some (trajectory.representatives (rebase.start + count)) := by
  have hfull := trajectory.prefixWord_run (rebase.start + count)
  rw [rebase.prefixWord_start_add, g.run?_append,
    rebase.consumed_run] at hfull
  exact hfull

public theorem base_ground
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
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase) :
    rebase.base.Ground g.ranks := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact hgroundSteps.ground_of_run
    (trajectory.representative_ground 0) rebase.consumed_run

public theorem exists_actions_labels
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
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (count : ℕ) :
    ∃ actions : List Action,
      rebase.labels count = actions.map Sum.inl := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact hgroundSteps.exists_actions_of_ground_run
    rebase.base_ground (rebase.labels_run count)

/-- Maximal operational depth rules out every sinking prefix after rebasing. -/
public theorem neverSinksFromBase
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
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (count : ℕ) (actions : List Action)
    (hlabels : rebase.labels count = actions.map Sum.inl) :
    g.NeverSinksFromBase rebase.base actions := by
  intro stem suffix hword hsinks
  have hsinksFull :
      g.SinksBy rebase.base (rebase.labels count) := by
    rw [hlabels, hword, List.map_append]
    exact hsinks.append (suffix.map Sum.inl)
  have hprogress :
      g.RepeatedlySinksBy
        (trajectory.representatives 0)
        (trajectory.prefixWord (rebase.start + count))
        (rebase.maximalDepth.depth + 1) := by
    rw [rebase.prefixWord_start_add]
    exact rebase.exactRun.repeatedlySinksBy_succ_of_sinksBy hsinksFull
  have hle := rebase.maximalDepth.maximal
    (rebase.maximalDepth.depth + 1)
    ⟨rebase.start + count, hprogress⟩
  omega

end MaximalProgressRebase

/-- Choose a concrete operational rebase at the attained maximal sinking
depth. -/
public theorem exists_maximalProgressRebase
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
    (trajectory : chain.PivotTrajectory)
    (hbounded :
      ∃ depthBound, ∀ count depth,
        g.RepeatedlySinksBy
            (trajectory.representatives 0)
            (trajectory.prefixWord count)
            depth →
          depth ≤ depthBound) :
    Nonempty trajectory.MaximalProgressRebase := by
  let maximal := Classical.choice
    (trajectory.exists_maximalRepeatedSinkingDepth hbounded)
  let start := Classical.choose maximal.witnessed
  have hsinks := Classical.choose_spec maximal.witnessed
  obtain ⟨consumed, remainder, base, hprefix, hexact⟩ :=
    hsinks.exists_exactPrefix
  exact ⟨
    { maximalDepth := maximal
      start := start
      consumed := consumed
      remainder := remainder
      prefix_eq := hprefix
      base := base
      exactRun := hexact }⟩

end PivotTrajectory

namespace WindowedPivotTrajectory

/-- Absence of a derived repeat supplies the bounded-progress premise and
therefore an operational maximal rebase on the canonical windowed
trajectory. -/
public theorem exists_maximalProgressRebase_of_noDerivedRepeat
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
    Nonempty trajectory.toPivotTrajectory.MaximalProgressRebase := by
  apply trajectory.toPivotTrajectory.exists_maximalProgressRebase
  exact trajectory.hasBoundedRepeatedSinkingDepths_of_noDerivedRepeat
    hg hnormal hground hinitial hexposureBound chain hnoRepeat

end WindowedPivotTrajectory

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
