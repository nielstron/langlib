module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BoundedSemanticReachability

@[expose]
public section

/-!
# Finite returns forced by sinking path windows

If a residual sinks during a finite common path window, some prefix of that
window exposes an immediate subterm of the residual.  Semantic equality with a
fixed finite base graph therefore places the reached residual, up to unfolding,
among the finitely many pointed subgraphs of that base.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A sinking left path window returns, up to unfolding, to a pointed subterm
of any fixed semantic representative of its starting residual. -/
public theorem TracePath.exists_left_pointed_return_of_sinks
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight base : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start windowLength : ℕ)
    (hbaseClosed : base.ReferenceClosed)
    (hbase : (path.left start).UnfoldingEquivalent base)
    (hsinks : g.SinksBy (path.left start)
      (path.segmentWord start windowLength)) :
    ∃ offset ≤ windowLength,
      ∃ representative ∈ base.pointedSubterms,
        (path.left (start + offset)).UnfoldingEquivalent representative := by
  obtain ⟨initialSegment, suffix, hwindow, _hnonempty,
      subterm, target, hsubterm, hrun, htarget⟩ := hsinks
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
  exact ⟨initialSegment.length, hoffset, representative,
    hrepresentative,
    htarget.trans (hsubtermBase.trans hbaseRepresentative)⟩

/-- A sinking right path window returns, up to unfolding, to a pointed subterm
of any fixed semantic representative of its starting residual. -/
public theorem TracePath.exists_right_pointed_return_of_sinks
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight base : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start windowLength : ℕ)
    (hbaseClosed : base.ReferenceClosed)
    (hbase : (path.right start).UnfoldingEquivalent base)
    (hsinks : g.SinksBy (path.right start)
      (path.segmentWord start windowLength)) :
    ∃ offset ≤ windowLength,
      ∃ representative ∈ base.pointedSubterms,
        (path.right (start + offset)).UnfoldingEquivalent representative := by
  obtain ⟨initialSegment, suffix, hwindow, _hnonempty,
      subterm, target, hsubterm, hrun, htarget⟩ := hsinks
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
  exact ⟨initialSegment.length, hoffset, representative,
    hrepresentative,
    htarget.trans (hsubtermBase.trans hbaseRepresentative)⟩

end EncodedFirstOrderGrammar

end DCFEquivalence
