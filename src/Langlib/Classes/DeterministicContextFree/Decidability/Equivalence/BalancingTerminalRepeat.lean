module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingOpportunitySequence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CertificateRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootSinking

@[expose]
public section

/-!
# The terminal branch of the balancing-window dichotomy

Every sinking witness consumes at least one label.  Thus a window which does
not yield a balancing segment yields a genuinely later pointed return.  By
iterating these returns, the two residual streams remain in finite bounded
families, and hence the trace path repeats.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The suffix of a common trace path beginning at `threshold`. -/
noncomputable def TracePath.drop
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (threshold : ℕ) :
    TracePath g (path.left threshold) (path.right threshold) where
  word n := path.segmentWord threshold n
  left n := path.left (threshold + n)
  right n := path.right (threshold + n)
  starts_word := by simp [segmentWord]
  starts_left := by simp
  starts_right := by simp
  step n := by
    refine ⟨path.nextLabel (threshold + n), ?_, ?_, ?_⟩
    · simp [segmentWord]
    · simpa [Nat.add_assoc] using
        (path.nextLabel_spec (threshold + n)).2.1
    · simpa [Nat.add_assoc] using
        (path.nextLabel_spec (threshold + n)).2.2

@[simp] public theorem TracePath.drop_left
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (threshold n : ℕ) :
    (path.drop threshold).left n = path.left (threshold + n) := rfl

@[simp] public theorem TracePath.drop_right
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (threshold n : ℕ) :
    (path.drop threshold).right n = path.right (threshold + n) := rfl

@[simp] public theorem TracePath.drop_nextLabel
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (threshold n : ℕ) :
    (path.drop threshold).nextLabel n =
      path.nextLabel (threshold + n) := by
  have hword := ((path.drop threshold).nextLabel_spec n).1
  change path.segmentWord threshold (n + 1) =
    path.segmentWord threshold n ++
      [(path.drop threshold).nextLabel n] at hword
  simp only [segmentWord] at hword
  have hsingleton : [(path.drop threshold).nextLabel n] =
      [path.nextLabel (threshold + n)] := by
    have h : path.nextLabel (threshold + n) =
        (path.drop threshold).nextLabel n := by
      simpa [Nat.add_assoc] using hword
    simpa using h.symm
  simpa using hsingleton

@[simp] public theorem TracePath.drop_segmentWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (threshold start length : ℕ) :
    (path.drop threshold).segmentWord start length =
      path.segmentWord (threshold + start) length := by
  induction length with
  | zero => simp [segmentWord]
  | succ length ih =>
      simp only [segmentWord]
      rw [ih]
      simp [Nat.add_assoc]

private theorem TracePath.exists_left_positive_pointed_return_of_sinks
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight base : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start windowLength : ℕ)
    (hbaseClosed : base.ReferenceClosed)
    (hbase : (path.left start).UnfoldingEquivalent base)
    (hsinks : g.SinksBy (path.left start)
      (path.segmentWord start windowLength)) :
    ∃ offset, 0 < offset ∧ offset ≤ windowLength ∧
      ∃ representative ∈ base.pointedSubterms,
        (path.left (start + offset)).UnfoldingEquivalent
          representative := by
  obtain ⟨initialSegment, suffix, hwindow, hnonempty, hexact⟩ := hsinks
  have hpositive : 0 < initialSegment.length :=
    List.length_pos_iff.mpr hnonempty
  obtain ⟨subterm, target, hsubterm, hrun, htarget⟩ := hexact
  have hoffset : initialSegment.length ≤ windowLength := by
    have hlength := congrArg List.length hwindow
    simp [path.segmentWord_length] at hlength
    omega
  have hinitialSegment :
      initialSegment =
        path.segmentWord start initialSegment.length := by
    have htake := congrArg (List.take initialSegment.length) hwindow
    rw [path.take_segmentWord start hoffset] at htake
    simpa using htake.symm
  have hpathRun :=
    path.left_segment_run start initialSegment.length
  rw [hinitialSegment] at hrun
  have htargetEq : target = path.left (start + initialSegment.length) :=
    Option.some.inj (hrun.symm.trans hpathRun)
  subst target
  obtain ⟨baseSubterm, hbaseSubterm, hsubtermBase⟩ :=
    hbase.exists_subtermAtDepth_one hsubterm
  obtain ⟨representative, hrepresentative, hbaseRepresentative⟩ :=
    RegularTerm.exists_mem_pointedSubterms_of_subtermAtDepth
      hbaseClosed hbaseSubterm
  exact ⟨initialSegment.length, hpositive, hoffset, representative,
    hrepresentative,
    htarget.trans (hsubtermBase.trans hbaseRepresentative)⟩

private theorem TracePath.exists_right_positive_pointed_return_of_sinks
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight base : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start windowLength : ℕ)
    (hbaseClosed : base.ReferenceClosed)
    (hbase : (path.right start).UnfoldingEquivalent base)
    (hsinks : g.SinksBy (path.right start)
      (path.segmentWord start windowLength)) :
    ∃ offset, 0 < offset ∧ offset ≤ windowLength ∧
      ∃ representative ∈ base.pointedSubterms,
        (path.right (start + offset)).UnfoldingEquivalent
          representative := by
  obtain ⟨initialSegment, suffix, hwindow, hnonempty, hexact⟩ := hsinks
  have hpositive : 0 < initialSegment.length :=
    List.length_pos_iff.mpr hnonempty
  obtain ⟨subterm, target, hsubterm, hrun, htarget⟩ := hexact
  have hoffset : initialSegment.length ≤ windowLength := by
    have hlength := congrArg List.length hwindow
    simp [path.segmentWord_length] at hlength
    omega
  have hinitialSegment :
      initialSegment =
        path.segmentWord start initialSegment.length := by
    have htake := congrArg (List.take initialSegment.length) hwindow
    rw [path.take_segmentWord start hoffset] at htake
    simpa using htake.symm
  have hpathRun :=
    path.right_segment_run start initialSegment.length
  rw [hinitialSegment] at hrun
  have htargetEq : target = path.right (start + initialSegment.length) :=
    Option.some.inj (hrun.symm.trans hpathRun)
  subst target
  obtain ⟨baseSubterm, hbaseSubterm, hsubtermBase⟩ :=
    hbase.exists_subtermAtDepth_one hsubterm
  obtain ⟨representative, hrepresentative, hbaseRepresentative⟩ :=
    RegularTerm.exists_mem_pointedSubterms_of_subtermAtDepth
      hbaseClosed hbaseSubterm
  exact ⟨initialSegment.length, hpositive, hoffset, representative,
    hrepresentative,
    htarget.trans (hsubtermBase.trans hbaseRepresentative)⟩

/-- The left window dichotomy has a genuinely later pointed return. -/
public theorem TracePath.leftBalancingSegment_or_positivePointedReturn
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight base : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hsource : (path.left start).Ground g.ranks)
    (hbaseClosed : base.ReferenceClosed)
    (hbase : (path.left start).UnfoldingEquivalent base) :
    Nonempty (BalancingSegment g bound
        (path.left start) (path.right start)
        (path.segmentWord start bound)) ∨
      ∃ offset, 0 < offset ∧ offset ≤ bound ∧
        ∃ representative ∈ base.pointedSubterms,
          (path.left (start + offset)).UnfoldingEquivalent
            representative := by
  classical
  let noEarlySink : Prop :=
    ∀ initialSegment suffix,
      path.segmentWord start bound = initialSegment ++ suffix →
      suffix ≠ [] →
      ¬g.RootSinksBy (path.left start) initialSegment
  by_cases hno : noEarlySink
  · exact Or.inl ⟨path.leftBalancingSegment hinitial start bound hno⟩
  · right
    unfold noEarlySink at hno
    push_neg at hno
    obtain ⟨initialSegment, suffix, hwindow, _hsuffix, hsinks⟩ := hno
    have hfullRoot : g.RootSinksBy (path.left start)
        (path.segmentWord start bound) := by
      rw [hwindow]
      exact hsinks.append suffix
    have hfull : g.SinksBy (path.left start)
        (path.segmentWord start bound) :=
      hfullRoot.toSinksBy_of_ground hg hsource
    exact path.exists_left_positive_pointed_return_of_sinks start bound
      hbaseClosed hbase hfull

/-- The right window dichotomy has a genuinely later pointed return. -/
public theorem TracePath.rightBalancingSegment_or_positivePointedReturn
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight base : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hsource : (path.right start).Ground g.ranks)
    (hbaseClosed : base.ReferenceClosed)
    (hbase : (path.right start).UnfoldingEquivalent base) :
    Nonempty (BalancingSegment g bound
        (path.right start) (path.left start)
        (path.segmentWord start bound)) ∨
      ∃ offset, 0 < offset ∧ offset ≤ bound ∧
        ∃ representative ∈ base.pointedSubterms,
          (path.right (start + offset)).UnfoldingEquivalent
            representative := by
  classical
  let noEarlySink : Prop :=
    ∀ initialSegment suffix,
      path.segmentWord start bound = initialSegment ++ suffix →
      suffix ≠ [] →
      ¬g.RootSinksBy (path.right start) initialSegment
  by_cases hno : noEarlySink
  · exact Or.inl ⟨path.rightBalancingSegment hinitial start bound hno⟩
  · right
    unfold noEarlySink at hno
    push_neg at hno
    obtain ⟨initialSegment, suffix, hwindow, _hsuffix, hsinks⟩ := hno
    have hfullRoot : g.RootSinksBy (path.right start)
        (path.segmentWord start bound) := by
      rw [hwindow]
      exact hsinks.append suffix
    have hfull : g.SinksBy (path.right start)
        (path.segmentWord start bound) :=
      hfullRoot.toSinksBy_of_ground hg hsource
    exact path.exists_right_positive_pointed_return_of_sinks start bound
      hbaseClosed hbase hfull

private theorem RegularTerm.mem_pointedSubterms_trans
    {base middle target : RegularTerm}
    (hmiddle : middle ∈ base.pointedSubterms)
    (htarget : target ∈ middle.pointedSubterms) :
    target ∈ base.pointedSubterms := by
  unfold RegularTerm.pointedSubterms at hmiddle htarget ⊢
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmiddle
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp htarget
  apply List.mem_map.mpr
  exact ⟨j, by simpa using hj, rfl⟩

private theorem RegularTerm.referenceClosed_of_mem_pointedSubterms
    {base source : RegularTerm} (hbase : base.ReferenceClosed)
    (hsource : source ∈ base.pointedSubterms) :
    source.ReferenceClosed := by
  unfold RegularTerm.pointedSubterms at hsource
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hsource
  exact RegularTerm.withRoot_referenceClosed hbase (by simpa using hi)

private theorem TracePath.left_bounded_pointed_reachability_of_noBalancing
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (bound : ℕ)
    (hnoOpportunity : ∀ start,
      ¬path.HasBalancingOpportunity bound start) :
    ∀ n,
      ∃ source ∈ (path.left 0).pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (path.left n).UnfoldingEquivalent reached := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hleftGround : ∀ n, (path.left n).Ground g.ranks := by
    intro n
    have hpair := path.residual_ground hgroundSteps hground n
    unfold groundPairCode at hpair
    rw [Bool.and_eq_true] at hpair
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpair.1
  have hleftClosed : ∀ n, (path.left n).ReferenceClosed :=
    fun n => RegularTerm.referenceClosed_of_ground (hleftGround n)
  let base := path.left 0
  have hbaseClosed : base.ReferenceClosed := hleftClosed 0
  have reachFrom : ∀ gap start source,
      source ∈ base.pointedSubterms →
      (path.left start).UnfoldingEquivalent source →
      ∃ finalSource ∈ base.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels finalSource = some reached ∧
          (path.left (start + gap)).UnfoldingEquivalent reached := by
    intro gap
    induction gap using Nat.strong_induction_on with
    | h gap ih =>
        intro start source hsource hequivalent
        by_cases hshort : gap < bound
        · let labels := path.segmentWord start gap
          have hsourceClosed :=
            RegularTerm.referenceClosed_of_mem_pointedSubterms
              hbaseClosed hsource
          obtain ⟨reached, hrun, hreached⟩ :=
            exists_run_of_unfoldingEquivalent hg hequivalent.symm
              hsourceClosed (hleftClosed start)
              (path.left_segment_run start gap)
          exact ⟨source, hsource, labels, reached,
            by simpa [labels] using Nat.le_of_lt hshort,
            hrun, hreached.symm⟩
        · have hnobalancing : ¬Nonempty (BalancingSegment g bound
              (path.left start) (path.right start)
              (path.segmentWord start bound)) := by
            intro hsegment
            apply hnoOpportunity start
            obtain ⟨segment⟩ := hsegment
            exact ⟨PathBalancingSegment.left segment⟩
          have hsourceClosed :=
            RegularTerm.referenceClosed_of_mem_pointedSubterms
              hbaseClosed hsource
          rcases path.leftBalancingSegment_or_positivePointedReturn
              hg hinitial start bound (hleftGround start)
              hsourceClosed hequivalent with
            hsegment | hreturn
          · exact False.elim (hnobalancing hsegment)
          · obtain ⟨offset, hpositive, hoffsetBound,
                nextSource, hnextNested, hnextEquivalent⟩ := hreturn
            have hboundGap : bound ≤ gap := Nat.le_of_not_gt hshort
            have hoffsetGap : offset ≤ gap :=
              hoffsetBound.trans hboundGap
            have hnextSource : nextSource ∈ base.pointedSubterms :=
              RegularTerm.mem_pointedSubterms_trans hsource hnextNested
            have hremaining : gap - offset < gap := by omega
            have hresult := ih (gap - offset) hremaining
              (start + offset) nextSource hnextSource hnextEquivalent
            simpa [Nat.add_assoc, Nat.add_sub_of_le hoffsetGap] using hresult
  intro n
  obtain ⟨source, hsource, hequivalent⟩ :=
    RegularTerm.exists_mem_pointedSubterms_of_subtermAtDepth
      hbaseClosed (show base.SubtermAtDepth 0 base by simp)
  simpa [base] using reachFrom n 0 source hsource hequivalent

private theorem TracePath.right_bounded_pointed_reachability_of_noBalancing
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (bound : ℕ)
    (hnoOpportunity : ∀ start,
      ¬path.HasBalancingOpportunity bound start) :
    ∀ n,
      ∃ source ∈ (path.right 0).pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels source = some reached ∧
          (path.right n).UnfoldingEquivalent reached := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  have hrightGround : ∀ n, (path.right n).Ground g.ranks := by
    intro n
    have hpair := path.residual_ground hgroundSteps hground n
    unfold groundPairCode at hpair
    rw [Bool.and_eq_true] at hpair
    exact (RegularTerm.groundCode_eq_true_iff g.ranks _).mp hpair.2
  have hrightClosed : ∀ n, (path.right n).ReferenceClosed :=
    fun n => RegularTerm.referenceClosed_of_ground (hrightGround n)
  let base := path.right 0
  have hbaseClosed : base.ReferenceClosed := hrightClosed 0
  have reachFrom : ∀ gap start source,
      source ∈ base.pointedSubterms →
      (path.right start).UnfoldingEquivalent source →
      ∃ finalSource ∈ base.pointedSubterms,
        ∃ labels reached,
          labels.length ≤ bound ∧
          g.run? labels finalSource = some reached ∧
          (path.right (start + gap)).UnfoldingEquivalent reached := by
    intro gap
    induction gap using Nat.strong_induction_on with
    | h gap ih =>
        intro start source hsource hequivalent
        by_cases hshort : gap < bound
        · let labels := path.segmentWord start gap
          have hsourceClosed :=
            RegularTerm.referenceClosed_of_mem_pointedSubterms
              hbaseClosed hsource
          obtain ⟨reached, hrun, hreached⟩ :=
            exists_run_of_unfoldingEquivalent hg hequivalent.symm
              hsourceClosed (hrightClosed start)
              (path.right_segment_run start gap)
          exact ⟨source, hsource, labels, reached,
            by simpa [labels] using Nat.le_of_lt hshort,
            hrun, hreached.symm⟩
        · have hnobalancing : ¬Nonempty (BalancingSegment g bound
              (path.right start) (path.left start)
              (path.segmentWord start bound)) := by
            intro hsegment
            apply hnoOpportunity start
            obtain ⟨segment⟩ := hsegment
            exact ⟨PathBalancingSegment.right segment⟩
          have hsourceClosed :=
            RegularTerm.referenceClosed_of_mem_pointedSubterms
              hbaseClosed hsource
          rcases path.rightBalancingSegment_or_positivePointedReturn
              hg hinitial start bound (hrightGround start)
              hsourceClosed hequivalent with
            hsegment | hreturn
          · exact False.elim (hnobalancing hsegment)
          · obtain ⟨offset, hpositive, hoffsetBound,
                nextSource, hnextNested, hnextEquivalent⟩ := hreturn
            have hboundGap : bound ≤ gap := Nat.le_of_not_gt hshort
            have hoffsetGap : offset ≤ gap :=
              hoffsetBound.trans hboundGap
            have hnextSource : nextSource ∈ base.pointedSubterms :=
              RegularTerm.mem_pointedSubterms_trans hsource hnextNested
            have hremaining : gap - offset < gap := by omega
            have hresult := ih (gap - offset) hremaining
              (start + offset) nextSource hnextSource hnextEquivalent
            simpa [Nat.add_assoc, Nat.add_sub_of_le hoffsetGap] using hresult
  intro n
  obtain ⟨source, hsource, hequivalent⟩ :=
    RegularTerm.exists_mem_pointedSubterms_of_subtermAtDepth
      hbaseClosed (show base.SubtermAtDepth 0 base by simp)
  simpa [base] using reachFrom n 0 source hsource hequivalent

/-- If no window is balanceable anywhere, both residual streams are uniformly
reachable from finite pointed bases.  Bounded pointed reachability therefore
forces a repeated pair. -/
public theorem TracePath.hasRepeat_of_noBalancingOpportunity
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (bound : ℕ)
    (hnoOpportunity : ∀ start,
      ¬path.HasBalancingOpportunity bound start) :
    path.HasRepeat := by
  apply path.hasRepeat_of_bounded_pointed_reachability bound
  · exact path.left_bounded_pointed_reachability_of_noBalancing
      hg hground hinitial bound hnoOpportunity
  · exact path.right_bounded_pointed_reachability_of_noBalancing
      hg hground hinitial bound hnoOpportunity

/-- Proposition 48's terminal branch: eventual absence of balancing
opportunities forces a repeat. -/
public theorem TracePath.hasRepeat_of_eventually_noBalancingOpportunity
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (bound threshold : ℕ)
    (hnoOpportunity : ∀ start, threshold ≤ start →
      ¬path.HasBalancingOpportunity bound start) :
    path.HasRepeat := by
  let suffix := path.drop threshold
  have hgroundSteps : g.PreservesGroundSteps := by
    intro label source target hsource hstep
    exact preservesGroundSteps_of_wellFormed hg hsource hstep
  have hsuffixGround : g.groundPairCode
      (path.left threshold) (path.right threshold) = true :=
    path.residual_ground hgroundSteps hground threshold
  have hsuffixEquivalent : g.TraceEquivalent
      (path.left threshold) (path.right threshold) :=
    path.residual_traceEquivalent hinitial threshold
  have hsuffixNoOpportunity : ∀ start,
      ¬suffix.HasBalancingOpportunity bound start := by
    intro start hopportunity
    apply hnoOpportunity (threshold + start) (by omega)
    obtain ⟨segment⟩ := hopportunity
    cases segment with
    | left segment =>
        exact ⟨PathBalancingSegment.left (by
          simpa [suffix] using segment)⟩
    | right segment =>
        exact ⟨PathBalancingSegment.right (by
          simpa [suffix] using segment)⟩
  obtain ⟨i, j, hij, hleft, hright⟩ :=
    suffix.hasRepeat_of_noBalancingOpportunity
      hg hsuffixGround hsuffixEquivalent bound
        hsuffixNoOpportunity
  exact ⟨threshold + i, threshold + j, by omega,
    by simpa [suffix] using hleft,
    by simpa [suffix] using hright⟩

/-- The terminal theorem discharges the abstract terminal premise of the
cofinal-opportunity construction. -/
public theorem TracePath.exists_balancingOpportunitySequence_of_noRepeat_wellFormed
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {bound : ℕ} (hbound : 0 < bound)
    (hnoRepeat : ¬path.HasRepeat) :
    Nonempty (BalancingOpportunitySequence path bound) := by
  apply path.exists_balancingOpportunitySequence_of_noRepeat
    hbound hnoRepeat
  intro threshold hnoOpportunity
  exact path.hasRepeat_of_eventually_noBalancingOpportunity
    hg hground hinitial bound threshold hnoOpportunity

end EncodedFirstOrderGrammar

end DCFEquivalence
