module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.SinkReturns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootSinking

@[expose]
public section

/-!
# One-window balancing dichotomies

Along a common trace path, a fixed-length window either avoids sinking on all
proper prefixes and is therefore a balancing segment, or a proper prefix
sinks.  In the latter case the full window sinks as well, forcing a return to
one of the finitely many pointed subgraphs of any fixed semantic base.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Every left path window is either a left balancing segment or contains a
semantic return to a pointed subterm of the supplied base. -/
public theorem TracePath.leftBalancingSegment_or_pointedReturn
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
      ∃ offset ≤ bound,
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
    exact path.exists_left_pointed_return_of_sinks start bound
      hbaseClosed hbase hfull

/-- Every right path window is either a right balancing segment or contains a
semantic return to a pointed subterm of the supplied base. -/
public theorem TracePath.rightBalancingSegment_or_pointedReturn
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
      ∃ offset ≤ bound,
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
    exact path.exists_right_pointed_return_of_sinks start bound
      hbaseClosed hbase hfull

end EncodedFirstOrderGrammar

end DCFEquivalence
