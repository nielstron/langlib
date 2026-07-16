module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingResultCoverage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingOpportunitySequence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RepeatedSinking
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootSinking

@[expose]
public section

/-!
# Close balancing opportunities and pivot-switch reachability

This file isolates the operational core of the side-switch paragraph in
Jančar's Proposition 49.

If one fixed side has no balancing opportunity throughout `depth * bound`
successive path positions, that side sinks `depth` times and therefore exposes
a subterm at depth `depth`.  This is the formal form of the paper's
`M₁ = depth * M₀` argument.

The second part packages the word replacement used when the exposed active
subterm is one of the successor rows recorded by a balancing result.  The
original pivot then reaches the switched pivot by replacing the old balancing
word and an active prefix with the strictly shorter exposing word of that
successor row.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath

/-- A left-oriented balancing opportunity at one path position. -/
@[expose] public def HasLeftBalancingOpportunity
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (bound start : ℕ) : Prop :=
  Nonempty (BalancingSegment g bound
    (path.left start) (path.right start)
    (path.segmentWord start bound))

/-- A right-oriented balancing opportunity at one path position. -/
@[expose] public def HasRightBalancingOpportunity
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (bound start : ℕ) : Prop :=
  Nonempty (BalancingSegment g bound
    (path.right start) (path.left start)
    (path.segmentWord start bound))

/-- A left opportunity is an unoriented balancing opportunity. -/
public theorem hasBalancingOpportunity_of_hasLeft
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {bound start : ℕ}
    (hopportunity : path.HasLeftBalancingOpportunity bound start) :
    path.HasBalancingOpportunity bound start := by
  obtain ⟨segment⟩ := hopportunity
  exact ⟨.left segment⟩

/-- A right opportunity is an unoriented balancing opportunity. -/
public theorem hasBalancingOpportunity_of_hasRight
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {bound start : ℕ}
    (hopportunity : path.HasRightBalancingOpportunity bound start) :
    path.HasBalancingOpportunity bound start := by
  obtain ⟨segment⟩ := hopportunity
  exact ⟨.right segment⟩

/-- If the left window is not balancing, a nonempty exact path prefix makes
one syntactic root-sinking step. -/
public theorem exists_left_rootSinkingPrefix_of_noBalancing
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hno : ¬path.HasLeftBalancingOpportunity bound start) :
    ∃ offset, 0 < offset ∧ offset ≤ bound ∧
      g.RootSinksBy
        (path.left start)
        (path.segmentWord start offset) := by
  classical
  have hsinks :
      g.RootSinksBy (path.left start)
        (path.segmentWord start bound) := by
    by_contra hnot
    apply hno
    refine ⟨path.leftBalancingSegment hinitial start bound ?_⟩
    intro initialSegment suffix hword hsuffix hsink
    apply hnot
    rw [hword]
    exact hsink.append suffix
  obtain ⟨rootSymbol, children, actions, suffix,
      hroot, hwindow, hstep⟩ := hsinks
  have hoffset : actions.length ≤ bound := by
    have hlength := congrArg List.length hwindow
    simp [path.segmentWord_length] at hlength
    omega
  have hstem :
      actions.map Sum.inl =
        path.segmentWord start actions.length := by
    have htake := congrArg
      (List.take
        (actions.map (Sum.inl : Action → Label Action)).length)
      hwindow
    rw [path.take_segmentWord start (by simpa using hoffset)] at htake
    simpa using htake.symm
  obtain ⟨step⟩ := hstep
  refine ⟨actions.length,
    List.length_pos_iff.mpr step.actions_nonempty,
    hoffset, ?_⟩
  exact ⟨rootSymbol, children, actions, [], hroot,
    by simpa [hstem], ⟨step⟩⟩

/-- Symmetric exact root-sinking prefix extraction for a non-balancing right
window. -/
public theorem exists_right_rootSinkingPrefix_of_noBalancing
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hno : ¬path.HasRightBalancingOpportunity bound start) :
    ∃ offset, 0 < offset ∧ offset ≤ bound ∧
      g.RootSinksBy
        (path.right start)
        (path.segmentWord start offset) := by
  classical
  have hsinks :
      g.RootSinksBy (path.right start)
        (path.segmentWord start bound) := by
    by_contra hnot
    apply hno
    refine ⟨path.rightBalancingSegment hinitial start bound ?_⟩
    intro initialSegment suffix hword hsuffix hsink
    apply hnot
    rw [hword]
    exact hsink.append suffix
  obtain ⟨rootSymbol, children, actions, suffix,
      hroot, hwindow, hstep⟩ := hsinks
  have hoffset : actions.length ≤ bound := by
    have hlength := congrArg List.length hwindow
    simp [path.segmentWord_length] at hlength
    omega
  have hstem :
      actions.map Sum.inl =
        path.segmentWord start actions.length := by
    have htake := congrArg
      (List.take
        (actions.map (Sum.inl : Action → Label Action)).length)
      hwindow
    rw [path.take_segmentWord start (by simpa using hoffset)] at htake
    simpa using htake.symm
  obtain ⟨step⟩ := hstep
  refine ⟨actions.length,
    List.length_pos_iff.mpr step.actions_nonempty,
    hoffset, ?_⟩
  exact ⟨rootSymbol, children, actions, [], hroot,
    by simpa [hstem], ⟨step⟩⟩

/-- Compatibility projection of the syntactic left root-sinking prefix to
the older semantic `SinkingStep` interface. -/
public theorem exists_left_sinkingStep_of_noBalancing
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hno : ¬path.HasLeftBalancingOpportunity bound start) :
    ∃ offset, 0 < offset ∧ offset ≤ bound ∧
      Nonempty (SinkingStep g
        (path.left start)
        (path.segmentWord start offset)
        (path.left (start + offset))) := by
  obtain ⟨rootOffset, _hrootPositive, hrootBound, hrootSinks⟩ :=
    path.exists_left_rootSinkingPrefix_of_noBalancing
      hinitial start bound hno
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hpairGround :=
    path.residual_ground hgroundSteps hground start
  have hsourceGround : (path.left start).Ground g.ranks := by
    unfold groundPairCode at hpairGround
    rw [Bool.and_eq_true] at hpairGround
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hpairGround.1
  have hsinks :
      g.SinksBy (path.left start)
        (path.segmentWord start rootOffset) :=
    hrootSinks.toSinksBy_of_ground hg hsourceGround
  obtain ⟨stem, suffix, target, hword, ⟨step⟩⟩ :=
    hsinks.exists_sinkingStep_prefix
  have hoffset : stem.length ≤ bound := by
    have hlength := congrArg List.length hword
    simp [path.segmentWord_length] at hlength
    omega
  have hstem :
      stem = path.segmentWord start stem.length := by
    have htake := congrArg (List.take stem.length) hword
    rw [path.take_segmentWord start
      (show stem.length ≤ rootOffset by
        have hlength := congrArg List.length hword
        simp [path.segmentWord_length] at hlength
        omega)] at htake
    simpa using htake.symm
  have hstepRun := step.run
  have hpathRun :=
    path.left_segment_run start stem.length
  rw [hstem] at hstepRun
  have htarget :
      target = path.left (start + stem.length) :=
    Option.some.inj (hstepRun.symm.trans hpathRun)
  subst target
  exact ⟨stem.length,
    List.length_pos_iff.mpr step.word_nonempty,
    hoffset, ⟨
      { subterm := step.subterm
        word_nonempty := by
          rw [← hstem]
          exact step.word_nonempty
        subterm_at := step.subterm_at
        run := hpathRun
        target_matches := step.target_matches }⟩⟩

/-- Compatibility projection of the syntactic right root-sinking prefix to
the older semantic `SinkingStep` interface. -/
public theorem exists_right_sinkingStep_of_noBalancing
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hno : ¬path.HasRightBalancingOpportunity bound start) :
    ∃ offset, 0 < offset ∧ offset ≤ bound ∧
      Nonempty (SinkingStep g
        (path.right start)
        (path.segmentWord start offset)
        (path.right (start + offset))) := by
  obtain ⟨rootOffset, _hrootPositive, hrootBound, hrootSinks⟩ :=
    path.exists_right_rootSinkingPrefix_of_noBalancing
      hinitial start bound hno
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hpairGround :=
    path.residual_ground hgroundSteps hground start
  have hsourceGround : (path.right start).Ground g.ranks := by
    unfold groundPairCode at hpairGround
    rw [Bool.and_eq_true] at hpairGround
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hpairGround.2
  have hsinks :
      g.SinksBy (path.right start)
        (path.segmentWord start rootOffset) :=
    hrootSinks.toSinksBy_of_ground hg hsourceGround
  obtain ⟨stem, suffix, target, hword, ⟨step⟩⟩ :=
    hsinks.exists_sinkingStep_prefix
  have hoffset : stem.length ≤ bound := by
    have hlength := congrArg List.length hword
    simp [path.segmentWord_length] at hlength
    omega
  have hstem :
      stem = path.segmentWord start stem.length := by
    have htake := congrArg (List.take stem.length) hword
    rw [path.take_segmentWord start
      (show stem.length ≤ rootOffset by
        have hlength := congrArg List.length hword
        simp [path.segmentWord_length] at hlength
        omega)] at htake
    simpa using htake.symm
  have hstepRun := step.run
  have hpathRun :=
    path.right_segment_run start stem.length
  rw [hstem] at hstepRun
  have htarget :
      target = path.right (start + stem.length) :=
    Option.some.inj (hstepRun.symm.trans hpathRun)
  subst target
  exact ⟨stem.length,
    List.length_pos_iff.mpr step.word_nonempty,
    hoffset, ⟨
      { subterm := step.subterm
        word_nonempty := by
          rw [← hstem]
          exact step.word_nonempty
        subterm_at := step.subterm_at
        run := hpathRun
        target_matches := step.target_matches }⟩⟩

/-- Absence of left balancing opportunities throughout a close window of
length `depth * bound` forces `depth` consecutive sinking steps. -/
public theorem repeatedlySinksLeft_of_noBalancingBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound depth : ℕ)
    (hbound : 0 < bound)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasLeftBalancingOpportunity bound (start + offset)) :
    g.RepeatedlySinksBy
      (path.left start)
      (path.segmentWord start (depth * bound))
      depth := by
  induction depth generalizing start with
  | zero => trivial
  | succ depth ih =>
      have hnoStart :
          ¬path.HasLeftBalancingOpportunity bound start := by
        simpa using hno 0 (by
          have : 0 < (depth + 1) * bound := Nat.mul_pos (by omega) hbound
          omega)
      obtain ⟨offset, hpositive, hoffsetBound, ⟨step⟩⟩ :=
        path.exists_left_sinkingStep_of_noBalancing
          hg hground hinitial start bound hnoStart
      have hoffsetTotal : offset ≤ (depth + 1) * bound := by
        exact hoffsetBound.trans
          (Nat.le_mul_of_pos_left bound (by omega))
      have hremaining : depth * bound ≤ (depth + 1) * bound - offset := by
        apply Nat.le_sub_of_add_le
        calc
          depth * bound + offset ≤ depth * bound + bound :=
            Nat.add_le_add_left hoffsetBound _
          _ = (depth + 1) * bound := by
            simp [Nat.add_mul, Nat.add_comm]
      have hnoTail : ∀ later, later < depth * bound →
          ¬path.HasLeftBalancingOpportunity bound
            (start + offset + later) := by
        intro later hlater
        have hsum : offset + later < (depth + 1) * bound := by
          rw [show (depth + 1) * bound =
              depth * bound + bound by
            simp [Nat.add_mul, Nat.add_comm]]
          omega
        simpa [Nat.add_assoc] using hno (offset + later) hsum
      have htail :=
        ih (start := start + offset) hnoTail
      let extra :=
        path.segmentWord (start + offset + depth * bound)
          ((depth + 1) * bound - offset - depth * bound)
      have htailFull :
          g.RepeatedlySinksBy
            (path.left (start + offset))
            (path.segmentWord (start + offset)
              ((depth + 1) * bound - offset))
            depth := by
        have happended := htail.append extra
        rw [← path.segmentWord_add] at happended
        simpa [extra, Nat.add_sub_of_le hremaining] using happended
      refine ⟨path.segmentWord start offset,
        path.segmentWord (start + offset)
          ((depth + 1) * bound - offset),
        path.left (start + offset), ?_, ⟨step⟩, htailFull⟩
      simpa [Nat.add_sub_of_le hoffsetTotal] using
        path.segmentWord_add start offset
          ((depth + 1) * bound - offset)

/-- Symmetric repeated-sinking theorem for the right side. -/
public theorem repeatedlySinksRight_of_noBalancingBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound depth : ℕ)
    (hbound : 0 < bound)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasRightBalancingOpportunity bound (start + offset)) :
    g.RepeatedlySinksBy
      (path.right start)
      (path.segmentWord start (depth * bound))
      depth := by
  induction depth generalizing start with
  | zero => trivial
  | succ depth ih =>
      have hnoStart :
          ¬path.HasRightBalancingOpportunity bound start := by
        simpa using hno 0 (by
          have : 0 < (depth + 1) * bound := Nat.mul_pos (by omega) hbound
          omega)
      obtain ⟨offset, hpositive, hoffsetBound, ⟨step⟩⟩ :=
        path.exists_right_sinkingStep_of_noBalancing
          hg hground hinitial start bound hnoStart
      have hoffsetTotal : offset ≤ (depth + 1) * bound := by
        exact hoffsetBound.trans
          (Nat.le_mul_of_pos_left bound (by omega))
      have hremaining : depth * bound ≤ (depth + 1) * bound - offset := by
        apply Nat.le_sub_of_add_le
        calc
          depth * bound + offset ≤ depth * bound + bound :=
            Nat.add_le_add_left hoffsetBound _
          _ = (depth + 1) * bound := by
            simp [Nat.add_mul, Nat.add_comm]
      have hnoTail : ∀ later, later < depth * bound →
          ¬path.HasRightBalancingOpportunity bound
            (start + offset + later) := by
        intro later hlater
        have hsum : offset + later < (depth + 1) * bound := by
          rw [show (depth + 1) * bound =
              depth * bound + bound by
            simp [Nat.add_mul, Nat.add_comm]]
          omega
        simpa [Nat.add_assoc] using hno (offset + later) hsum
      have htail :=
        ih (start := start + offset) hnoTail
      let extra :=
        path.segmentWord (start + offset + depth * bound)
          ((depth + 1) * bound - offset - depth * bound)
      have htailFull :
          g.RepeatedlySinksBy
            (path.right (start + offset))
            (path.segmentWord (start + offset)
              ((depth + 1) * bound - offset))
            depth := by
        have happended := htail.append extra
        rw [← path.segmentWord_add] at happended
        simpa [extra, Nat.add_sub_of_le hremaining] using happended
      refine ⟨path.segmentWord start offset,
        path.segmentWord (start + offset)
          ((depth + 1) * bound - offset),
        path.right (start + offset), ?_, ⟨step⟩, htailFull⟩
      simpa [Nat.add_sub_of_le hoffsetTotal] using
        path.segmentWord_add start offset
          ((depth + 1) * bound - offset)

/-- The close-window conclusion used in Proposition 49: the active left
result exposes the requested depth. -/
public theorem exposesLeftDepth_of_noBalancingBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound depth : ℕ)
    (hbound : 0 < bound)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasLeftBalancingOpportunity bound (start + offset)) :
    g.ExposesBy
      (path.left start)
      (path.segmentWord start (depth * bound))
      depth :=
  (path.repeatedlySinksLeft_of_noBalancingBefore
    hg hground hinitial start bound depth hbound hno).exposesBy

/-- Symmetric close-window depth exposure on the right. -/
public theorem exposesRightDepth_of_noBalancingBefore
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound depth : ℕ)
    (hbound : 0 < bound)
    (hno : ∀ offset, offset < depth * bound →
      ¬path.HasRightBalancingOpportunity bound (start + offset)) :
    g.ExposesBy
      (path.right start)
      (path.segmentWord start (depth * bound))
      depth :=
  (path.repeatedlySinksRight_of_noBalancingBefore
    hg hground hinitial start bound depth hbound hno).exposesBy

end TracePath

namespace BalancingSegment.ExposedSuccessorResult

/-- The modified bridge used on a pivot-side switch.  The original balancing
word and an active prefix are replaced by this row's shorter exposing word;
the untouched suffix from the reflected point is retained. -/
@[expose] public noncomputable def modifiedBridge
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)} {filler : RegularTerm} {child : ℕ}
    (row : segment.ExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler child)
    {resultLeft resultRight : RegularTerm}
    (path : TracePath g resultLeft resultRight)
    (cut targetLevel : ℕ) : List (Label Action) :=
  row.word.map Sum.inl ++
    path.segmentWord cut (targetLevel - cut)

/-- The modified switch word is strictly shorter than the unmodified bridge
whenever the reflected point occurs no later than the target level. -/
public theorem modifiedBridge_length_lt
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)} {filler : RegularTerm} {child : ℕ}
    (row : segment.ExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler child)
    {resultLeft resultRight : RegularTerm}
    (path : TracePath g resultLeft resultRight)
    {cut targetLevel : ℕ} (hcut : cut ≤ targetLevel) :
    (row.modifiedBridge path cut targetLevel).length <
      (labels ++ path.segmentWord 0 targetLevel).length := by
  have hrow := row.word_length_lt
  simp [modifiedBridge, path.segmentWord_length,
    segment.word_length]
  omega

/-- Observation 46(4), once supplied as a semantic match with one successor
row, gives the exact modified-word reachability used by the switch case. -/
public theorem exists_run_modifiedBridge
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label Action)} {filler : RegularTerm} {child : ℕ}
    (row : segment.ExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler child)
    (hpivot : pivot.Ground g.ranks)
    {resultLeft resultRight : RegularTerm}
    (path : TracePath g resultLeft resultRight)
    (hresultGround : g.groundPairCode resultLeft resultRight = true)
    {cut targetLevel : ℕ} (hcut : cut ≤ targetLevel)
    (hreflect :
      (path.left cut).UnfoldingEquivalent row.pivotTarget) :
    ∃ reached,
      g.run? (row.modifiedBridge path cut targetLevel) pivot =
        some reached ∧
      reached.UnfoldingEquivalent (path.left targetLevel) := by
  have hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hrowGround : row.pivotTarget.Ground g.ranks := by
    exact hgroundSteps.ground_of_run hpivot
      (by simpa [runActions?] using row.pivot_run)
  have hcutGround :
      (path.left cut).Ground g.ranks := by
    have hpair := path.residual_ground hgroundSteps hresultGround cut
    unfold groundPairCode at hpair
    rw [Bool.and_eq_true] at hpair
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpair.1
  obtain ⟨reached, hrun, hreached⟩ :=
    exists_run_of_unfoldingEquivalent hg hreflect.symm
      (RegularTerm.referenceClosed_of_ground hrowGround)
      (RegularTerm.referenceClosed_of_ground hcutGround)
      (path.left_segment_run cut (targetLevel - cut))
  refine ⟨reached, ?_, ?_⟩
  · unfold modifiedBridge
    rw [g.run?_append]
    rw [show g.run? (row.word.map Sum.inl) pivot =
        some row.pivotTarget by
      simpa [runActions?] using row.pivot_run]
    exact hrun
  · simpa [Nat.add_sub_of_le hcut] using hreached

end BalancingSegment.ExposedSuccessorResult

namespace BalancingSegment.WitnessedBalancingResult

/-- The unmodified bridge keeps following the old pivot component of a
balancing result. -/
public theorem pivot_run_to_right
    {g : EncodedFirstOrderGrammar Action}
    {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {initialLeft initialRight : RegularTerm} {word : List (Label Action)}
    (result : segment.WitnessedBalancingResult
      initialLeft initialRight word)
    (path : TracePath g
      result.witnessed.coverage.left
      result.witnessed.coverage.right)
    (targetLevel : ℕ) :
    g.run? (labels ++ path.segmentWord 0 targetLevel) pivot =
      some (path.right targetLevel) := by
  rw [g.run?_append, segment.pivot_run]
  have hstart :
      path.right 0 = segment.pivotTarget := by
    rw [path.starts_right, result.pivot_eq]
  rw [← hstart]
  simpa using path.right_segment_run 0 targetLevel

/-- At the next selected opportunity, either the old pivot follows the
unmodified bridge to the next left-oriented pivot, or the selected
right-oriented pivot is reached by the strictly shorter modified bridge.

The sole switch-specific premise is `hreflect`: this is exactly the
Observation 46(4) interface saying that a reached active residual agrees with
one of the exposed-successor targets obtained from the previous pivot. -/
public theorem nextPivotBridge
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {bound : ℕ}
    {active pivot : RegularTerm} {labels : List (Label Action)}
    {segment : BalancingSegment g bound active pivot labels}
    {initialLeft initialRight : RegularTerm} {word : List (Label Action)}
    (result : segment.WitnessedBalancingResult
      initialLeft initialRight word)
    (hpivot : pivot.Ground g.ranks)
    (path : TracePath g
      result.witnessed.coverage.left
      result.witnessed.coverage.right)
    {outerLeft outerRight : RegularTerm}
    {stem : List (Label Action)} {filler : RegularTerm} {child : ℕ}
    (row : segment.ExposedSuccessorResult
      (initialLeft := outerLeft) (initialRight := outerRight)
      stem filler child)
    {cut targetLevel : ℕ} (hcut : cut ≤ targetLevel)
    (hreflect :
      (path.left cut).UnfoldingEquivalent row.pivotTarget)
    (selected : PathBalancingSegment path bound targetLevel) :
    (path.HasLeftBalancingOpportunity bound targetLevel ∧
        g.run? (labels ++ path.segmentWord 0 targetLevel) pivot =
          some (path.right targetLevel)) ∨
      (path.HasRightBalancingOpportunity bound targetLevel ∧
        ∃ reached,
          g.run? (row.modifiedBridge path cut targetLevel) pivot =
            some reached ∧
          reached.UnfoldingEquivalent (path.left targetLevel) ∧
          (row.modifiedBridge path cut targetLevel).length <
            (labels ++ path.segmentWord 0 targetLevel).length) := by
  have hresultGround :
      g.groundPairCode
        result.witnessed.coverage.left
        result.witnessed.coverage.right = true :=
    groundPairCode_of_pair_derivable
      result.witnessed.coverage.derivation
  cases selected with
  | left next =>
      exact Or.inl
        ⟨⟨next⟩, result.pivot_run_to_right path targetLevel⟩
  | right next =>
      obtain ⟨reached, hrun, hreached⟩ :=
        row.exists_run_modifiedBridge hg hpivot path
          hresultGround hcut hreflect
      exact Or.inr
        ⟨⟨next⟩, reached, hrun, hreached,
          row.modifiedBridge_length_lt path hcut⟩

end BalancingSegment.WitnessedBalancingResult

end EncodedFirstOrderGrammar

end DCFEquivalence
