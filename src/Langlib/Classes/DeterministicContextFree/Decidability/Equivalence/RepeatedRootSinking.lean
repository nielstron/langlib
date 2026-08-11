module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotSwitchReachability
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedSinking
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootSinking

@[expose]
public section

/-!
# Repeated syntactic root sinking

`RepeatedlySinksBy` retains semantic immediate-subterm exposure.  The special
pivot argument needs the stronger fact that every selected prefix is induced
by an open run from a root template to one of its literal parameters.

This file keeps that root-syntactic witness at every recursive step.  The
semantic `SinkingStep` stored beside it is obtained only by replaying the open
root witness, so erasing this relation to `RepeatedlySinksBy` is one-way and
does not assert a false semantic-to-syntactic converse.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- One exact concrete sinking prefix together with the open root computation
that induces its *entire* word.

The root symbol, source children, and open step are fields rather than a
bare `RootSinksBy` proposition.  Consequently there cannot be an unrecorded
shorter root prefix followed by an internal suffix. -/
public structure RootSinkingRunStep
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List (Label Action))
    (target : RegularTerm) where
  rootSymbol : ℕ
  children : List ℕ
  actions : List Action
  source_root :
    source.rootApplication? = some (rootSymbol, children)
  actions_eq : word = actions.map Sum.inl
  open_step :
    RootSinkingStep g rootSymbol children.length actions
  semantic : SinkingStep g source word target

/-- An exact run step is in particular a source-attached root-sinking
witness, with no internal unused suffix. -/
public theorem RootSinkingRunStep.rootSinks
    {g : EncodedFirstOrderGrammar Action}
    {source target : RegularTerm} {word : List (Label Action)}
    (step : RootSinkingRunStep g source word target) :
    g.RootSinksBy source word :=
  ⟨step.rootSymbol, step.children, step.actions, [],
    step.source_root, step.actions_eq.trans (by simp),
    ⟨step.open_step⟩⟩

/-- Extract the exact open root prefix from a possibly longer
`RootSinksBy` word and replay it as a concrete semantic sinking step. -/
public theorem RootSinksBy.exists_rootSinkingRunStep_prefix
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source : RegularTerm} {word : List (Label Action)}
    (hsource : ∃ variableBound,
      source.WellFormed g.ranks variableBound)
    (hsinks : g.RootSinksBy source word) :
    ∃ stem suffix target,
      word = stem ++ suffix ∧
        Nonempty (RootSinkingRunStep
          g source stem target) := by
  obtain ⟨rootSymbol, children, actions, suffix,
      hroot, hword, ⟨openStep⟩⟩ := hsinks
  obtain ⟨target, child, _hchildMem, hchild,
      hrun, htarget⟩ :=
    openStep.replay hg (Classical.choose_spec hsource) hroot
  let stem : List (Label Action) := actions.map Sum.inl
  have hsemantic : SinkingStep g source stem target :=
    { subterm := source.withRoot child
      word_nonempty := by
        simpa [stem] using openStep.actions_nonempty
      subterm_at := ⟨child, hchild, rfl⟩
      run := by simpa [stem, runActions?] using hrun
      target_matches := htarget }
  exact ⟨stem, suffix, target, by simpa [stem] using hword,
    ⟨
      { rootSymbol := rootSymbol
        children := children
        actions := actions
        source_root := hroot
        actions_eq := by simp [stem]
        open_step := openStep
        semantic := hsemantic }⟩⟩

/-- `depth` consecutive exact root-syntactic sinking prefixes. -/
public inductive RepeatedlyRootSinksBy
    (g : EncodedFirstOrderGrammar Action) :
    RegularTerm → List (Label Action) → ℕ → Prop
  | zero (source word) :
      RepeatedlyRootSinksBy g source word 0
  | succ {source word stem suffix target depth}
      (word_eq : word = stem ++ suffix)
      (step : RootSinkingRunStep g source stem target)
      (rest : RepeatedlyRootSinksBy g target suffix depth) :
      RepeatedlyRootSinksBy g source word (depth + 1)

/-- Repeated root sinking with each selected prefix bounded by `bound`. -/
public inductive BoundedRepeatedlyRootSinksBy
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) :
    RegularTerm → List (Label Action) → ℕ → Prop
  | zero (source word) :
      BoundedRepeatedlyRootSinksBy g bound source word 0
  | succ {source word stem suffix target depth}
      (word_eq : word = stem ++ suffix)
      (step : RootSinkingRunStep g source stem target)
      (step_length_le : stem.length ≤ bound)
      (rest :
        BoundedRepeatedlyRootSinksBy
          g bound target suffix depth) :
      BoundedRepeatedlyRootSinksBy
        g bound source word (depth + 1)

@[simp] public theorem repeatedlyRootSinksBy_zero
    (g : EncodedFirstOrderGrammar Action)
    (source : RegularTerm) (word : List (Label Action)) :
    g.RepeatedlyRootSinksBy source word 0 :=
  .zero source word

@[simp] public theorem boundedRepeatedlyRootSinksBy_zero
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ)
    (source : RegularTerm) (word : List (Label Action)) :
    g.BoundedRepeatedlyRootSinksBy bound source word 0 :=
  .zero source word

/-- Appending unused labels preserves a repeated root-sinking spine. -/
public theorem RepeatedlyRootSinksBy.append
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsinks : g.RepeatedlyRootSinksBy source word depth)
    (suffix : List (Label Action)) :
    g.RepeatedlyRootSinksBy source (word ++ suffix) depth := by
  induction depth generalizing source word with
  | zero =>
      exact .zero source (word ++ suffix)
  | succ depth ih =>
      cases hsinks with
      | succ hword step hrest =>
          refine .succ ?_ step (ih hrest)
          rw [hword, List.append_assoc]

/-- Appending unused labels also preserves every per-step bound. -/
public theorem BoundedRepeatedlyRootSinksBy.append
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} {source : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hsinks : g.BoundedRepeatedlyRootSinksBy
      bound source word depth)
    (suffix : List (Label Action)) :
    g.BoundedRepeatedlyRootSinksBy
      bound source (word ++ suffix) depth := by
  induction depth generalizing source word with
  | zero =>
      exact .zero source (word ++ suffix)
  | succ depth ih =>
      cases hsinks with
      | succ hword step hstepLength hrest =>
          refine .succ ?_ step hstepLength (ih hrest)
          rw [hword, List.append_assoc]

/-- Erase only the numerical per-step bounds. -/
public theorem BoundedRepeatedlyRootSinksBy.toRepeatedlyRootSinksBy
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} {source : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hsinks : g.BoundedRepeatedlyRootSinksBy
      bound source word depth) :
    g.RepeatedlyRootSinksBy source word depth := by
  induction hsinks with
  | zero =>
      exact .zero _ _
  | succ hword step _hstepLength _hrest ih =>
      exact .succ hword step ih

/-- Forgetting the open root computations gives ordinary repeated semantic
sinking.  The only erased field is the replay witness retained by each
`RootSinkingRunStep`. -/
public theorem RepeatedlyRootSinksBy.toRepeatedlySinksBy
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hsinks : g.RepeatedlyRootSinksBy source word depth) :
    g.RepeatedlySinksBy source word depth := by
  induction hsinks with
  | zero => trivial
  | succ hword step _hrest ih =>
      exact ⟨_, _, _, hword, ⟨step.semantic⟩, ih⟩

/-- Bounded root sinking forgets to the existing semantic recurrence. -/
public theorem BoundedRepeatedlyRootSinksBy.toRepeatedlySinksBy
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ} {source : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hsinks : g.BoundedRepeatedlyRootSinksBy
      bound source word depth) :
    g.RepeatedlySinksBy source word depth :=
  hsinks.toRepeatedlyRootSinksBy.toRepeatedlySinksBy

/-- Replay one exact root-sinking step on an unfolding-equivalent ground
source.  The entire retained action word is replayed, and determinism aligns
its endpoint with the ordinary run transported from the original source. -/
public theorem RootSinkingRunStep.of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {left right rightTarget : RegularTerm}
    {word : List (Label Action)}
    (hleft : left.Ground g.ranks)
    (hright : right.Ground g.ranks)
    (hequivalent : left.UnfoldingEquivalent right)
    (step : RootSinkingRunStep g right word rightTarget) :
    ∃ leftTarget,
      Nonempty (RootSinkingRunStep
        g left word leftTarget) ∧
      leftTarget.UnfoldingEquivalent rightTarget := by
  obtain ⟨leftChildren, hleftRoot, hchildren⟩ :=
    RegularTerm.rootApplication?_of_unfoldingEquivalent
      hequivalent.symm step.source_root
  have hopen :
      RootSinkingStep g step.rootSymbol
        leftChildren.length step.actions := by
    simpa [hchildren.length_eq] using step.open_step
  obtain ⟨leftTarget, child, _hchildMem, hchild,
      hleftRunActions, hleftTarget⟩ :=
    hopen.replay_ground hg hleft hleftRoot
  have hrightRunActions :
      g.runActions? step.actions right = some rightTarget := by
    simpa [runActions?, step.actions_eq] using step.semantic.run
  obtain ⟨transportedTarget, htransportedRun,
      htransportedTarget⟩ :=
    exists_runActions_of_unfoldingEquivalent hg hequivalent
      (RegularTerm.referenceClosed_of_ground hleft)
      (RegularTerm.referenceClosed_of_ground hright)
      hrightRunActions
  have htransportedEq : transportedTarget = leftTarget :=
    Option.some.inj
      (htransportedRun.symm.trans hleftRunActions)
  subst transportedTarget
  let leftStep : RootSinkingRunStep g left word leftTarget :=
    { rootSymbol := step.rootSymbol
      children := leftChildren
      actions := step.actions
      source_root := hleftRoot
      actions_eq := step.actions_eq
      open_step := hopen
      semantic :=
        { subterm := left.withRoot child
          word_nonempty := by
            simpa [step.actions_eq] using hopen.actions_nonempty
          subterm_at := ⟨child, hchild, rfl⟩
          run := by
            simpa [runActions?, step.actions_eq] using
              hleftRunActions
          target_matches := hleftTarget } }
  exact ⟨leftTarget, ⟨leftStep⟩, htransportedTarget⟩

/-- Repeated exact root sinking is invariant under equality of ground
regular-tree unfoldings. -/
public theorem RepeatedlyRootSinksBy.of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {left right : RegularTerm} {word : List (Label Action)}
    {depth : ℕ}
    (hleft : left.Ground g.ranks)
    (hright : right.Ground g.ranks)
    (hequivalent : left.UnfoldingEquivalent right)
    (hsinks : g.RepeatedlyRootSinksBy right word depth) :
    g.RepeatedlyRootSinksBy left word depth := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  induction depth generalizing left right word with
  | zero =>
      exact .zero left word
  | succ depth ih =>
      cases hsinks with
      | @succ source word stem suffix rightTarget depth
          hword rightStep hrest =>
          obtain ⟨leftTarget, ⟨leftStep⟩, htargets⟩ :=
            rightStep.of_unfoldingEquivalent
              hg hleft hright hequivalent
          have hleftTargetGround :
              leftTarget.Ground g.ranks :=
            hgroundSteps.ground_of_run
              hleft leftStep.semantic.run
          have hrightTargetGround :
              rightTarget.Ground g.ranks := by
            exact hgroundSteps.ground_of_run
              hright rightStep.semantic.run
          exact .succ hword leftStep
            (ih hleftTargetGround hrightTargetGround
              htargets hrest)

/-- The bounded recurrence transports in the same way and keeps every
selected prefix-length bound unchanged. -/
public theorem BoundedRepeatedlyRootSinksBy.of_unfoldingEquivalent
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ} {left right : RegularTerm}
    {word : List (Label Action)} {depth : ℕ}
    (hleft : left.Ground g.ranks)
    (hright : right.Ground g.ranks)
    (hequivalent : left.UnfoldingEquivalent right)
    (hsinks :
      g.BoundedRepeatedlyRootSinksBy
        bound right word depth) :
    g.BoundedRepeatedlyRootSinksBy
      bound left word depth := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  induction depth generalizing left right word with
  | zero =>
      exact .zero left word
  | succ depth ih =>
      cases hsinks with
      | @succ source word stem suffix rightTarget depth
          hword rightStep hstepLength hrest =>
          obtain ⟨leftTarget, ⟨leftStep⟩, htargets⟩ :=
            rightStep.of_unfoldingEquivalent
              hg hleft hright hequivalent
          have hleftTargetGround :
              leftTarget.Ground g.ranks :=
            hgroundSteps.ground_of_run
              hleft leftStep.semantic.run
          have hrightTargetGround :
              rightTarget.Ground g.ranks := by
            exact hgroundSteps.ground_of_run
              hright rightStep.semantic.run
          exact .succ hword leftStep hstepLength
            (ih hleftTargetGround hrightTargetGround
              htargets hrest)

/-- Ordinary runs preserve the existence of some finite variable bound. -/
private theorem runActions?_someWellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {source target : RegularTerm} {actions : List Action}
    (hsource : ∃ variableBound,
      source.WellFormed g.ranks variableBound)
    (hrun : g.runActions? actions source = some target) :
    ∃ variableBound, target.WellFormed g.ranks variableBound := by
  induction actions generalizing source with
  | nil =>
      simp [runActions?] at hrun
      subst target
      exact hsource
  | cons action actions ih =>
      cases hstep : g.step? (.inl action) source with
      | none =>
          simp [runActions?, hstep] at hrun
      | some next =>
          have htail :
              g.runActions? actions next = some target := by
            simpa [runActions?, hstep] using hrun
          exact ih
            (stepAction_some_wellFormed hg hsource hstep)
            htail

namespace TracePath

/-- The left `noBalancingBefore` construction with the exact open root
witness and its per-step prefix bound retained. -/
public theorem boundedRepeatedlyRootSinksLeft_of_noBalancingBefore
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
    g.BoundedRepeatedlyRootSinksBy bound
      (path.left start)
      (path.segmentWord start (depth * bound))
      depth := by
  induction depth generalizing start with
  | zero =>
      exact .zero _ _
  | succ depth ih =>
      have hnoStart :
          ¬path.HasLeftBalancingOpportunity bound start := by
        simpa using hno 0 (by
          have : 0 < (depth + 1) * bound :=
            Nat.mul_pos (by omega) hbound
          omega)
      obtain ⟨rootOffset, _hrootPositive, hrootBound, hrootSinks⟩ :=
        path.exists_left_rootSinkingPrefix_of_noBalancing
          hinitial start bound hnoStart
      obtain ⟨stem, _inside, target, hrootWord, ⟨step⟩⟩ :=
        hrootSinks.exists_rootSinkingRunStep_prefix hg hsource
      have hstemRootOffset : stem.length ≤ rootOffset := by
        have hlength := congrArg List.length hrootWord
        simp only [path.segmentWord_length, List.length_append]
          at hlength
        omega
      have hstemBound : stem.length ≤ bound :=
        hstemRootOffset.trans hrootBound
      have hstem :
          stem = path.segmentWord start stem.length := by
        have htake := congrArg (List.take stem.length) hrootWord
        rw [path.take_segmentWord start hstemRootOffset] at htake
        simpa using htake.symm
      rw [hstem] at step
      have hpathRun :=
        path.left_segment_run start stem.length
      have htarget :
          target = path.left (start + stem.length) :=
        Option.some.inj (step.semantic.run.symm.trans hpathRun)
      subst target
      have hoffsetTotal :
          stem.length ≤ (depth + 1) * bound :=
        hstemBound.trans
          (Nat.le_mul_of_pos_left bound (by omega))
      have hremaining :
          depth * bound ≤
            (depth + 1) * bound - stem.length := by
        apply Nat.le_sub_of_add_le
        calc
          depth * bound + stem.length ≤ depth * bound + bound :=
            Nat.add_le_add_left hstemBound _
          _ = (depth + 1) * bound := by
            simp [Nat.add_mul, Nat.add_comm]
      have hnoTail : ∀ later, later < depth * bound →
          ¬path.HasLeftBalancingOpportunity bound
            (start + stem.length + later) := by
        intro later hlater
        have hsum :
            stem.length + later < (depth + 1) * bound := by
          rw [show (depth + 1) * bound =
              depth * bound + bound by
            simp [Nat.add_mul, Nat.add_comm]]
          omega
        simpa [Nat.add_assoc] using
          hno (stem.length + later) hsum
      have hrunActions :
          g.runActions? step.actions (path.left start) =
            some (path.left (start + stem.length)) := by
        simpa [runActions?, step.actions_eq] using hpathRun
      have hnextWellFormed :
          ∃ variableBound,
            (path.left (start + stem.length))
              |>.WellFormed g.ranks variableBound :=
        runActions?_someWellFormed hg hsource hrunActions
      have htail :=
        ih (start := start + stem.length)
          hnextWellFormed hnoTail
      let extra :=
        path.segmentWord
          (start + stem.length + depth * bound)
          ((depth + 1) * bound - stem.length -
            depth * bound)
      have htailFull :
          g.BoundedRepeatedlyRootSinksBy bound
            (path.left (start + stem.length))
            (path.segmentWord (start + stem.length)
              ((depth + 1) * bound - stem.length))
            depth := by
        have happended := htail.append extra
        rw [← path.segmentWord_add] at happended
        simpa [extra, Nat.add_sub_of_le hremaining] using happended
      refine .succ ?_ step (by simpa using hstemBound) htailFull
      simpa [Nat.add_sub_of_le hoffsetTotal] using
        path.segmentWord_add start stem.length
          ((depth + 1) * bound - stem.length)

/-- Symmetric bounded root-syntactic construction for the right side. -/
public theorem boundedRepeatedlyRootSinksRight_of_noBalancingBefore
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
    g.BoundedRepeatedlyRootSinksBy bound
      (path.right start)
      (path.segmentWord start (depth * bound))
      depth := by
  induction depth generalizing start with
  | zero =>
      exact .zero _ _
  | succ depth ih =>
      have hnoStart :
          ¬path.HasRightBalancingOpportunity bound start := by
        simpa using hno 0 (by
          have : 0 < (depth + 1) * bound :=
            Nat.mul_pos (by omega) hbound
          omega)
      obtain ⟨rootOffset, _hrootPositive, hrootBound, hrootSinks⟩ :=
        path.exists_right_rootSinkingPrefix_of_noBalancing
          hinitial start bound hnoStart
      obtain ⟨stem, _inside, target, hrootWord, ⟨step⟩⟩ :=
        hrootSinks.exists_rootSinkingRunStep_prefix hg hsource
      have hstemRootOffset : stem.length ≤ rootOffset := by
        have hlength := congrArg List.length hrootWord
        simp only [path.segmentWord_length, List.length_append]
          at hlength
        omega
      have hstemBound : stem.length ≤ bound :=
        hstemRootOffset.trans hrootBound
      have hstem :
          stem = path.segmentWord start stem.length := by
        have htake := congrArg (List.take stem.length) hrootWord
        rw [path.take_segmentWord start hstemRootOffset] at htake
        simpa using htake.symm
      rw [hstem] at step
      have hpathRun :=
        path.right_segment_run start stem.length
      have htarget :
          target = path.right (start + stem.length) :=
        Option.some.inj (step.semantic.run.symm.trans hpathRun)
      subst target
      have hoffsetTotal :
          stem.length ≤ (depth + 1) * bound :=
        hstemBound.trans
          (Nat.le_mul_of_pos_left bound (by omega))
      have hremaining :
          depth * bound ≤
            (depth + 1) * bound - stem.length := by
        apply Nat.le_sub_of_add_le
        calc
          depth * bound + stem.length ≤ depth * bound + bound :=
            Nat.add_le_add_left hstemBound _
          _ = (depth + 1) * bound := by
            simp [Nat.add_mul, Nat.add_comm]
      have hnoTail : ∀ later, later < depth * bound →
          ¬path.HasRightBalancingOpportunity bound
            (start + stem.length + later) := by
        intro later hlater
        have hsum :
            stem.length + later < (depth + 1) * bound := by
          rw [show (depth + 1) * bound =
              depth * bound + bound by
            simp [Nat.add_mul, Nat.add_comm]]
          omega
        simpa [Nat.add_assoc] using
          hno (stem.length + later) hsum
      have hrunActions :
          g.runActions? step.actions (path.right start) =
            some (path.right (start + stem.length)) := by
        simpa [runActions?, step.actions_eq] using hpathRun
      have hnextWellFormed :
          ∃ variableBound,
            (path.right (start + stem.length))
              |>.WellFormed g.ranks variableBound :=
        runActions?_someWellFormed hg hsource hrunActions
      have htail :=
        ih (start := start + stem.length)
          hnextWellFormed hnoTail
      let extra :=
        path.segmentWord
          (start + stem.length + depth * bound)
          ((depth + 1) * bound - stem.length -
            depth * bound)
      have htailFull :
          g.BoundedRepeatedlyRootSinksBy bound
            (path.right (start + stem.length))
            (path.segmentWord (start + stem.length)
              ((depth + 1) * bound - stem.length))
            depth := by
        have happended := htail.append extra
        rw [← path.segmentWord_add] at happended
        simpa [extra, Nat.add_sub_of_le hremaining] using happended
      refine .succ ?_ step (by simpa using hstemBound) htailFull
      simpa [Nat.add_sub_of_le hoffsetTotal] using
        path.segmentWord_add start stem.length
          ((depth + 1) * bound - stem.length)

/-- Unbounded left corollary. -/
public theorem repeatedlyRootSinksLeft_of_noBalancingBefore
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
    g.RepeatedlyRootSinksBy
      (path.left start)
      (path.segmentWord start (depth * bound))
      depth :=
  (path.boundedRepeatedlyRootSinksLeft_of_noBalancingBefore
    hg hinitial start bound depth hsource hbound hno)
    |>.toRepeatedlyRootSinksBy

/-- Unbounded right corollary. -/
public theorem repeatedlyRootSinksRight_of_noBalancingBefore
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
    g.RepeatedlyRootSinksBy
      (path.right start)
      (path.segmentWord start (depth * bound))
      depth :=
  (path.boundedRepeatedlyRootSinksRight_of_noBalancingBefore
    hg hinitial start bound depth hsource hbound hno)
    |>.toRepeatedlyRootSinksBy

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
