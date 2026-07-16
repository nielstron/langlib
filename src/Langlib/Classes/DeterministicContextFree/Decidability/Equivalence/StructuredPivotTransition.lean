module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotSelectionPolicy
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredBalancingResult

@[expose]
public section

/-!
# One bounded structured pivot transition

This file retains the full Proposition-45 construction at a selected
balancing opportunity and packages one Proposition-49 close/fallback
transition.  It deliberately stops after one step: no infinite iteration or
global stair construction is performed here.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath

namespace SelectedBalancingSegment

/-- The active input of an oriented path balancing segment. -/
@[expose] public def active
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {bound start : ℕ}
    (selected : PathBalancingSegment path bound start) : RegularTerm :=
  match selected with
  | .left _ => path.left start
  | .right _ => path.right start

/-- Forget only the orientation wrapper while preserving its dependent active
and pivot inputs. -/
@[expose] public def asSegment
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {bound start : ℕ}
    (selected : PathBalancingSegment path bound start) :
    BalancingSegment g bound
      (SelectedBalancingSegment.active selected)
      (SelectedBalancingSegment.pivot selected)
      (path.segmentWord start bound) := by
  cases selected with
  | left segment => exact segment
  | right segment => exact segment

/-- The retained structured Proposition-45 result belonging to one exact
oriented path segment. -/
@[expose] public def StructuredResult
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {bound start : ℕ}
    (selected : PathBalancingSegment path bound start)
    {outerLeft outerRight : RegularTerm}
    (stem : List (Label Action)) (filler : RegularTerm) : Type :=
  (SelectedBalancingSegment.asSegment selected)
    |>.StructuredBalancingResult
    (initialLeft := outerLeft) (initialRight := outerRight)
    stem filler

end SelectedBalancingSegment

/-- One selected balancing step retaining the exact structured result before
the coverage interface erases its successor family. -/
public structure StructuredDerivedBalancingStep
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hg : g.WellFormed)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {start : ℕ}
    (source : path.DerivedPairAt start)
    (bound : ℕ) where
  offset : ℕ
  selected :
    PathBalancingSegment
      (source.continuationPath hg hground hinitial) bound offset
  filler : RegularTerm
  active_ground :
    (SelectedBalancingSegment.active selected).Ground g.ranks
  pivot_ground :
    (SelectedBalancingSegment.pivot selected).Ground g.ranks
  filler_ground : filler.Ground g.ranks
  structured :
    SelectedBalancingSegment.StructuredResult
      (outerLeft := initialLeft) (outerRight := initialRight)
      selected (path.word (start + offset)) filler

namespace StructuredDerivedBalancingStep

/-- Absolute endpoint of the retained balancing segment. -/
@[expose] public def endLevel
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) : ℕ :=
  start + step.offset + bound

/-- The concrete left result retained by the structured construction. -/
@[expose] public def resultLeft
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) : RegularTerm :=
  step.structured.replacement.result

/-- The normalized pivot result retained on the right. -/
@[expose] public noncomputable def resultRight
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) : RegularTerm :=
  (SelectedBalancingSegment.asSegment step.selected).pivotTarget

/-- The structured result is a derived pair at the exact absolute endpoint. -/
public noncomputable def target
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) :
    path.DerivedPairAt step.endLevel := by
  let continuation :=
    source.continuationPath hg hground hinitial
  have hword :
      path.word (start + step.offset) ++
          continuation.segmentWord step.offset bound =
        path.word (start + step.offset + bound) := by
    rw [source.continuationPath_segmentWord
      hg hground hinitial step.offset bound]
    exact (path.word_add (start + step.offset) bound).symm
  have hderivation := step.structured.replacement.derivation
  rw [← step.structured.activeResult.labels_eq, hword] at hderivation
  exact
    { left := step.resultLeft
      right := step.resultRight
      derivation := hderivation }

/-- Canonical continuation from the concrete structured result. -/
public noncomputable def continuationPath
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) :
    TracePath g step.resultLeft step.resultRight :=
  step.target.continuationPath hg hground hinitial

/-- The semantic depth used for the close-window search. -/
@[expose] public noncomputable def switchDepth
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) : ℕ :=
  step.structured.activeResult.unfoldingDepthBound + 1

/-- The bounded close-left search window. -/
@[expose] public noncomputable def closeBound
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound) : ℕ :=
  step.switchDepth * bound

end StructuredDerivedBalancingStep

/-- Assemble the full retained Proposition-45 construction at an externally
selected oriented balancing segment. -/
public theorem DerivedPairAt.exists_structuredBalancingStep_of_selected
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {start bound offset : ℕ}
    (source : path.DerivedPairAt start)
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (selected :
      PathBalancingSegment
        (source.continuationPath hg hground hinitial) bound offset) :
    ∃ step : StructuredDerivedBalancingStep
        hg hground hinitial source bound,
      step.offset = offset ∧
        SelectedBalancingSegment.side step.selected =
          SelectedBalancingSegment.side selected ∧
        HEq step.selected selected := by
  classical
  let continuation :=
    source.continuationPath hg hground hinitial
  have laws := guardedContextLaws_of_wellFormed hg
  let current :=
    (source.continuationAt hg hground hinitial offset).target
  have hcurrentGround :=
    groundPairCode_of_pair_derivable current.derivation
  unfold groundPairCode at hcurrentGround
  rw [Bool.and_eq_true] at hcurrentGround
  have hleftGround : current.left.Ground g.ranks :=
    (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hcurrentGround.1
  have hrightGround : current.right.Ground g.ranks :=
    (RegularTerm.groundCode_eq_true_iff g.ranks _).mp
      hcurrentGround.2
  have hcurrentEquivalent :=
    current.derivation.pair_traceEquivalent_of_initial laws hinitial
  have houter :
      CertificateDerivable g initialLeft initialRight []
        (.pair (path.word (start + offset))
          current.left current.right) := by
    simpa [current] using current.derivation
  cases selected with
  | left segment =>
      obtain ⟨structured⟩ :=
        segment.exists_structuredBalancingResult
          hg hnormal hexposureBound
          hleftGround hrightGround hleftGround
          houter hcurrentEquivalent
      let step : StructuredDerivedBalancingStep
          hg hground hinitial source bound :=
        { offset := offset
          selected := .left segment
          filler := current.left
          active_ground := by
            simpa [SelectedBalancingSegment.active,
              continuation, current] using hleftGround
          pivot_ground := by
            simpa [SelectedBalancingSegment.pivot,
              continuation, current] using hrightGround
          filler_ground := hleftGround
          structured := by
            simpa [SelectedBalancingSegment.StructuredResult,
              SelectedBalancingSegment.asSegment,
              continuation, current] using structured }
      exact ⟨step, rfl, rfl, HEq.rfl⟩
  | right segment =>
      obtain ⟨structured⟩ :=
        segment.exists_structuredBalancingResult
          hg hnormal hexposureBound
          hrightGround hleftGround hrightGround
          (.symmetry houter) hcurrentEquivalent.symm
      let step : StructuredDerivedBalancingStep
          hg hground hinitial source bound :=
        { offset := offset
          selected := .right segment
          filler := current.right
          active_ground := by
            simpa [SelectedBalancingSegment.active,
              continuation, current] using hrightGround
          pivot_ground := by
            simpa [SelectedBalancingSegment.pivot,
              continuation, current] using hleftGround
          filler_ground := hrightGround
          structured := by
            simpa [SelectedBalancingSegment.StructuredResult,
              SelectedBalancingSegment.asSegment,
              continuation, current] using structured }
      exact ⟨step, rfl, rfl, HEq.rfl⟩

/-- A structured balancing step viewed as the current recursive state.  Its
current pair is the normalized target of the retained segment. -/
public structure StructuredDerivedBalancingState
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hg : g.WellFormed)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (bound : ℕ) where
  start : ℕ
  source : path.DerivedPairAt start
  incoming :
    StructuredDerivedBalancingStep
      hg hground hinitial source bound

namespace StructuredDerivedBalancingState

/-- Absolute level of the state's normalized current pair. -/
@[expose] public noncomputable def level
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    (state : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound) : ℕ :=
  state.incoming.endLevel

/-- The normalized pair from which the next policy search starts. -/
public noncomputable def pair
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    (state : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound) :
    path.DerivedPairAt state.level :=
  state.incoming.target

end StructuredDerivedBalancingState

namespace StructuredDerivedBalancingStep

/-- The current input pivot follows the unmodified current balancing word and
then the right side of its normalized continuation. -/
public theorem pivot_run_to_continuation_right
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    (nextOffset : ℕ) :
    g.run?
        ((source.continuationPath hg hground hinitial).segmentWord
            current.offset bound ++
          current.continuationPath.segmentWord 0 nextOffset)
        (SelectedBalancingSegment.pivot current.selected) =
      some (current.continuationPath.right nextOffset) := by
  rw [g.run?_append,
    (SelectedBalancingSegment.asSegment current.selected).pivot_run]
  have hrun :=
    current.continuationPath.right_segment_run 0 nextOffset
  have hstart :
      current.continuationPath.right 0 =
        (SelectedBalancingSegment.asSegment
          current.selected).pivotTarget := by
    simpa [continuationPath, target, resultRight] using
      current.continuationPath.starts_right
  rw [← hstart]
  simpa using hrun

/-- A bridge from the current segment's input pivot to the input pivot of an
aligned next selected segment.  The switched branch retains the exact shorter
modified word and its successor-row witness. -/
public structure PivotBridgeTo
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    {nextOffset : ℕ}
    (nextSelected :
      PathBalancingSegment current.continuationPath
        bound nextOffset) where
  direct_or_switched :
    (SelectedBalancingSegment.side nextSelected =
        BalancingSide.left ∧
      g.run?
          ((source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord 0 nextOffset)
          (SelectedBalancingSegment.pivot current.selected) =
        some (SelectedBalancingSegment.pivot nextSelected)) ∨
    (SelectedBalancingSegment.side nextSelected =
        BalancingSide.right ∧
      ∃ i : Fin current.structured.children.length,
        ∃ cut ≤ current.closeBound,
          ∃ reached,
            g.run?
                ((current.structured.family.row i).modifiedBridge
                  current.continuationPath cut nextOffset)
                (SelectedBalancingSegment.pivot current.selected) =
              some reached ∧
            reached.UnfoldingEquivalent
              (SelectedBalancingSegment.pivot nextSelected) ∧
            ((current.structured.family.row i).modifiedBridge
                  current.continuationPath cut nextOffset).length <
              ((source.continuationPath hg hground hinitial).segmentWord
                    current.offset bound ++
                current.continuationPath.segmentWord
                  0 nextOffset).length)

end StructuredDerivedBalancingStep

/-- One bounded policy transition, retaining the close/fallback metadata, an
aligned next structured segment, and the corresponding pivot bridge. -/
public structure StructuredPivotPolicyTransition
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hg : g.WellFormed)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound) where
  policy :
    PivotSelectionPolicy current.continuationPath
      bound current.closeBound
  next :
    StructuredDerivedBalancingStep
      hg hground hinitial current.target bound
  next_offset_eq : next.offset = policy.offset
  next_selected_eq : HEq next.selected policy.selected
  bridge : current.PivotBridgeTo policy.selected

namespace StructuredPivotPolicyTransition

/-- The structured state reached after one bounded policy transition. -/
public noncomputable def nextState
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    {current : StructuredDerivedBalancingStep
      hg hground hinitial source bound}
    (transition : StructuredPivotPolicyTransition
      hg hground hinitial current) :
    StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound :=
  { start := current.endLevel
    source := current.target
    incoming := transition.next }

end StructuredPivotPolicyTransition

namespace StructuredDerivedBalancingStep

/-- One paper-faithful close/fallback transition from a retained structured
segment.  The next structured segment is aligned to the bridge branch at the
policy-selected offset; in the fallback case this may replace the original
orientation by another available orientation at the same offset. -/
public theorem exists_policyTransition_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} {hg : g.WellFormed}
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (current : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    (hexposureBound : g.exposureBound hnormal ≤ bound) :
    Nonempty (StructuredPivotPolicyTransition
      hg hground hinitial current) := by
  classical
  have hbound : 0 < bound :=
    (g.exposureBound_pos hnormal).trans_le hexposureBound
  have laws := guardedContextLaws_of_wellFormed hg
  have hcurrentEquivalent :
      g.TraceEquivalent current.resultLeft current.resultRight :=
    current.target.derivation
      |>.pair_traceEquivalent_of_initial laws hinitial
  obtain ⟨originalPolicy⟩ :=
    current.target.exists_pivotSelectionPolicy_of_noDerivedRepeat
      hg hground hinitial hnoRepeat current.closeBound
  rcases originalPolicy.closeLeft_or_afterClose with
    hcloseLeft | hafterClose
  · obtain ⟨hoffsetClose, hside, hminimal⟩ := hcloseLeft
    cases hselected : originalPolicy.selected with
    | left nextSegment =>
        obtain ⟨next, hnextOffset, _hnextSide, hnextSelected⟩ :=
          current.target.exists_structuredBalancingStep_of_selected
            hg hnormal hground hinitial hexposureBound
            (.left nextSegment)
        refine ⟨
          { policy := originalPolicy
            next := next
            next_offset_eq := hnextOffset
            next_selected_eq := ?_
            bridge :=
              { direct_or_switched := .inl
                  ⟨hside,
                    ?_⟩ } }⟩
        · simpa [hselected] using hnextSelected
        · have hrun :=
            current.pivot_run_to_continuation_right
              originalPolicy.offset
          simpa [SelectedBalancingSegment.pivot, hselected] using hrun
    | right nextSegment =>
        simp [SelectedBalancingSegment.side, hselected] at hside
  · obtain ⟨hclose, hnoLeft, hgap⟩ := hafterClose
    have hbridge :=
      current.structured.replacement
        |>.nextPivotBridge_of_noLeftBalancingBefore
          hg current.active_ground current.pivot_ground
          current.filler_ground current.structured.root_eq
          current.continuationPath hcurrentEquivalent
          bound current.switchDepth hbound
          (by simp [switchDepth])
          (by
            intro offset hoffset
            exact hnoLeft offset
              (Nat.le_of_lt (by
                simpa [closeBound] using hoffset)))
          (by simpa [closeBound] using hclose)
          originalPolicy.selected
    rcases hbridge with hdirect | hswitch
    · obtain ⟨⟨nextSegment⟩, hrun⟩ := hdirect
      let alignedPolicy :
          PivotSelectionPolicy current.continuationPath
            bound current.closeBound :=
        { offset := originalPolicy.offset
          selected := .left nextSegment
          closeLeft_or_afterClose := .inr
            ⟨hclose, hnoLeft, hgap⟩ }
      obtain ⟨next, hnextOffset, _hnextSide, hnextSelected⟩ :=
        current.target.exists_structuredBalancingStep_of_selected
          hg hnormal hground hinitial hexposureBound
          alignedPolicy.selected
      refine ⟨
        { policy := alignedPolicy
          next := next
          next_offset_eq := hnextOffset
          next_selected_eq := hnextSelected
          bridge :=
            { direct_or_switched := .inl
                ⟨by
                  simp [alignedPolicy,
                    SelectedBalancingSegment.side],
                  ?_⟩ } }⟩
      simpa [alignedPolicy, SelectedBalancingSegment.pivot] using hrun
    · obtain ⟨⟨nextSegment⟩, i, cut, hcut, reached,
          hrun, hreached, hshorter⟩ := hswitch
      let alignedPolicy :
          PivotSelectionPolicy current.continuationPath
            bound current.closeBound :=
        { offset := originalPolicy.offset
          selected := .right nextSegment
          closeLeft_or_afterClose := .inr
            ⟨hclose, hnoLeft, hgap⟩ }
      obtain ⟨next, hnextOffset, _hnextSide, hnextSelected⟩ :=
        current.target.exists_structuredBalancingStep_of_selected
          hg hnormal hground hinitial hexposureBound
          alignedPolicy.selected
      refine ⟨
        { policy := alignedPolicy
          next := next
          next_offset_eq := hnextOffset
          next_selected_eq := hnextSelected
          bridge :=
            { direct_or_switched := .inr
                ⟨by
                  simp [alignedPolicy,
                    SelectedBalancingSegment.side],
                  i, cut, ?_, reached, ?_, ?_, ?_⟩ } }⟩
      · simpa [closeBound] using hcut
      · exact hrun
      · simpa [alignedPolicy,
          SelectedBalancingSegment.pivot] using hreached
      · exact hshorter

end StructuredDerivedBalancingStep

/-- State-level entry point for one bounded structured policy transition. -/
public theorem StructuredDerivedBalancingState.exists_policyTransition_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} {hg : g.WellFormed}
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {bound : ℕ}
    (state : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound)
    (hexposureBound : g.exposureBound hnormal ≤ bound) :
    Nonempty (StructuredPivotPolicyTransition
      hg hground hinitial state.incoming) :=
  state.incoming.exists_policyTransition_of_noDerivedRepeat
    hnormal hnoRepeat hexposureBound

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
