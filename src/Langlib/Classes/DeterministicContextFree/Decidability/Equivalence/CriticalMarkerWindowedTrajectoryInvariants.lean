module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerNormalForm
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerStructuredPivotInvariants
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedFixedTailPresentation
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerTerminalCoverage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotM2Window
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.PivotProgressM2Bound

@[expose]
public section

/-!
# Marker-freeness of canonical windowed pivot trajectories

The strong pivot edge used by the operational `M₂` theorem retains whether
its word is the direct path bridge or a switched bridge.  Direct bridge
components are exact factors of the next marker-free absolute endpoint.
Switched bridges replace the first component by a genuine successor-exposing
word; in a critical-marker extension every such word consists only of
injected original actions.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Every successor-exposing row selected in a critical-marker extension has
a marker-free ordinary-label word. -/
public theorem
    BalancingSegment.ExposedSuccessorResult.word_noCriticalMarkerActions
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count bound : ℕ}
    {active pivot : RegularTerm}
    {labels : List (Label (Action ⊕ ℕ))}
    {segment : BalancingSegment (g.withCriticalMarkers count)
      bound active pivot labels}
    {initialLeft initialRight : RegularTerm}
    {stem : List (Label (Action ⊕ ℕ))}
    {filler : RegularTerm} {child : ℕ}
    (row : segment.ExposedSuccessorResult
      (initialLeft := initialLeft) (initialRight := initialRight)
      stem filler child) :
    NoCriticalMarkerActions (row.word.map Sum.inl) := by
  obtain ⟨position, hexposes⟩ := row.word_exposes
  obtain ⟨originalActions, hword⟩ :=
    g.withCriticalMarkers_exposesSuccessor_exists_originalActions
      hg position hexposes
  intro marker hmarker
  rw [hword, List.map_map] at hmarker
  simp [Function.comp_def] at hmarker

namespace TracePath.StructuredPivotChain

/-- The concrete word of a canonical strong pivot edge is marker-free when
the next absolute selected endpoint is marker-free. -/
public theorem windowedPivotEdge_noCriticalMarkerActions
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (hbound : 0 < bound) (j : ℕ)
    (edge : (chain.transitions j).WindowedPivotEdge)
    (hendpoint : NoCriticalMarkerActions
      (path.word (chain.levels (j + 1)))) :
    NoCriticalMarkerActions edge.toPivotEdge.word := by
  let extended := g.withCriticalMarkers count
  let hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  let state := chain.states j
  let current := state.incoming
  let transition := chain.transitions j
  have hnextLevel :
      chain.levels (j + 1) =
        current.endLevel + transition.policy.offset + bound := by
    rw [StructuredPivotChain.levels, chain.advances j]
    simp [StructuredPivotPolicyTransition.nextState,
      StructuredDerivedBalancingState.level,
      StructuredDerivedBalancingStep.endLevel,
      transition.next_offset_eq, state, current, transition]
  rcases edge.word_shape hbound with hdirect | hswitched
  · rw [hdirect]
    apply NoCriticalMarkerActions.append
    · have hfit :
          state.start + current.offset + bound ≤
            chain.levels (j + 1) := by
        calc
          state.start + current.offset + bound =
              current.endLevel := by
            rfl
          _ ≤ chain.levels (j + 1) := by
            rw [hnextLevel]
            omega
      have hsegment :=
        path.segmentWord_noCriticalMarkerActions_of_endpoint
          hfit hendpoint
      simpa [state, current,
        state.source.continuationPath_segmentWord
          hgExtended hground hinitial] using hsegment
    · have hfit :
          current.endLevel + transition.policy.offset ≤
            chain.levels (j + 1) := by
        rw [hnextLevel]
        omega
      have hsegment :=
        path.segmentWord_noCriticalMarkerActions_of_endpoint
          hfit hendpoint
      simpa [StructuredDerivedBalancingStep.continuationPath,
        current.target.continuationPath_segmentWord
          hgExtended hground hinitial,
        state, current, transition] using hsegment
  · obtain ⟨i, cut, hcut, hedge⟩ := hswitched
    rw [hedge]
    unfold BalancingSegment.ExposedSuccessorResult.modifiedBridge
    apply NoCriticalMarkerActions.append
    · exact
        (current.structured.family.row i)
          |>.word_noCriticalMarkerActions hg
    · have hfit :
          current.endLevel + cut +
              (transition.policy.offset - cut) ≤
            chain.levels (j + 1) := by
        have hcut' : cut ≤ transition.policy.offset := by
          simpa [transition] using hcut
        rw [hnextLevel]
        omega
      have hsegment :=
        path.segmentWord_noCriticalMarkerActions_of_endpoint
          hfit hendpoint
      simpa [StructuredDerivedBalancingStep.continuationPath,
        current.target.continuationPath_segmentWord
          hgExtended hground hinitial,
        state, current, transition] using hsegment

namespace PivotTrajectory

/-- Pointwise marker-free pivot edges give marker-free accumulated pivot
prefixes. -/
public theorem prefixWord_noCriticalMarkerActions
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : (g.withCriticalMarkers count).WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory)
    (hedges : ∀ j,
      NoCriticalMarkerActions (trajectory.edgeWords j)) :
    ∀ j,
      NoCriticalMarkerActions (trajectory.prefixWord j) := by
  intro j
  induction j with
  | zero =>
      intro marker
      simp [prefixWord]
  | succ j ih =>
      rw [prefixWord]
      exact ih.append (hedges j)

namespace MaximalProgressRebase

/-- The suffix retained by an operational rebase is marker-free whenever
all underlying pivot edges are marker-free. -/
public theorem labels_noCriticalMarkerActions
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : (g.withCriticalMarkers count).WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (hedges : ∀ j,
      NoCriticalMarkerActions (trajectory.edgeWords j))
    (j : ℕ) :
    NoCriticalMarkerActions (rebase.labels j) := by
  have hprefix :=
    trajectory.prefixWord_noCriticalMarkerActions
      hedges (rebase.start + j)
  rw [rebase.prefixWord_start_add] at hprefix
  exact hprefix.right_of_append

/-- Hence every rebased ordinary-action word is a double injection of an
original action word. -/
public theorem exists_originalActions_labels
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : (g.withCriticalMarkers count).WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      hg hground hinitial bound initial}
    {trajectory : chain.PivotTrajectory}
    (rebase : trajectory.MaximalProgressRebase)
    (hedges : ∀ j,
      NoCriticalMarkerActions (trajectory.edgeWords j))
    (j : ℕ) :
    ∃ originalActions : List Action,
      rebase.labels j =
        (originalActions.map Sum.inl).map Sum.inl := by
  obtain ⟨extendedActions, hlabels⟩ :=
    rebase.exists_actions_labels j
  have hactionsNoMarker :
      NoCriticalMarkerActions
        (extendedActions.map Sum.inl) := by
    rw [← hlabels]
    exact rebase.labels_noCriticalMarkerActions hedges j
  obtain ⟨originalActions, hactions⟩ :=
    exists_originalActions_of_noCriticalMarkerActions
      hactionsNoMarker
  exact ⟨originalActions, by rw [hlabels, hactions]⟩

end MaximalProgressRebase

end PivotTrajectory

/-- The canonical strong trajectory has marker-free edges whenever every
selected absolute endpoint is marker-free. -/
public theorem toWindowedPivotTrajectory_edgeWords_noCriticalMarkerActions
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (hbound : 0 < bound)
    (hendpoint : ∀ j,
      NoCriticalMarkerActions (path.word (chain.levels j))) :
    ∀ j, NoCriticalMarkerActions
      ((chain.toWindowedPivotTrajectory).toPivotTrajectory.edgeWords j) := by
  intro j
  change NoCriticalMarkerActions
    (chain.chosenWindowedPivotEdge j).toPivotEdge.word
  exact chain.windowedPivotEdge_noCriticalMarkerActions
    hg hbound j (chain.chosenWindowedPivotEdge j)
    (hendpoint (j + 1))

namespace WindowedPivotTrajectory

namespace MaximalProgressRebase

/-- On the marker-free endpoint branch, the canonical operational rebase
admits a guarded critical-prefix presentation at exactly any prescribed
positive depth. -/
public theorem
    exists_criticalGuardedFixedTailPivotPresentation_atDepth
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    (rebase :
      (chain.toWindowedPivotTrajectory).toPivotTrajectory
        |>.MaximalProgressRebase)
    (hbound : 0 < bound)
    (hendpoint : ∀ j,
      NoCriticalMarkerActions (path.word (chain.levels j)))
    (hfiller : filler.Ground
      (g.withCriticalMarkers count).ranks)
    (depth : ℕ) (hdepth : 0 < depth) :
    ∃ presentation : CriticalGuardedFixedTailPivotPresentation
        g count rebase.base filler rebase.labels
        (fun j =>
          (chain.toWindowedPivotTrajectory).toPivotTrajectory
            |>.representatives (rebase.start + j)),
      presentation.depth = depth := by
  let trajectory :=
    (chain.toWindowedPivotTrajectory).toPivotTrajectory
  have hedges : ∀ j,
      NoCriticalMarkerActions (trajectory.edgeWords j) := by
    simpa [trajectory] using
      chain.toWindowedPivotTrajectory_edgeWords_noCriticalMarkerActions
        hg hbound hendpoint
  apply
    _root_.DCFEquivalence.EncodedFirstOrderGrammar.exists_criticalGuardedFixedTailPivotPresentation_atDepth
      hg rebase.base_ground hfiller depth hdepth
      rebase.labels_run
      (fun j => rebase.exists_originalActions_labels hedges j)
  intro j originalActions hlabels
  exact rebase.neverSinksFromBase
    j (originalActions.map Sum.inl) hlabels

end MaximalProgressRebase

end WindowedPivotTrajectory

/-- The complete marker-free operational package for one structured chain:
the canonical strong trajectory, a localized maximal-progress rebase, and a
guarded critical-prefix presentation at the balancing depth. -/
public structure MarkerFreeGuardedProgressPresentation
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial) where
  rebase :
    (chain.toWindowedPivotTrajectory).toPivotTrajectory
      |>.MaximalProgressRebase
  presentation : CriticalGuardedFixedTailPivotPresentation
    g count rebase.base filler rebase.labels
    (fun j =>
      (chain.toWindowedPivotTrajectory).toPivotTrajectory
        |>.representatives (rebase.start + j))
  depth_eq : presentation.depth = bound
  labels_zero_length_le :
    (rebase.labels 0).length ≤
      (g.withCriticalMarkers count).structuredPivotM2Bound bound
  endpoint_noMarkerActions : ∀ j,
    NoCriticalMarkerActions (path.word (chain.levels j))

/-- Every no-repeat structured chain either has already taken a fresh marker
step, yielding the uniform terminal coverage, or admits the complete
marker-free guarded maximal-progress presentation. -/
public theorem
    eventuallyMarkerStableOpenSound_or_exists_markerFreeGuardedProgressPresentation
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    {count : ℕ}
    (hnormal : (g.withCriticalMarkers count).ExposingNormalForm)
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    {bound : ℕ}
    (hexposureBound :
      (g.withCriticalMarkers count).exposureBound hnormal ≤ bound)
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    (hfiller : filler.Ground
      (g.withCriticalMarkers count).ranks) :
    EventuallyMarkerStableOpenSound g count
        initialLeft initialRight
        g.criticalMarkerTerminalBound path ∨
      Nonempty (MarkerFreeGuardedProgressPresentation
        (hg := hg) (filler := filler) chain) := by
  let extended := g.withCriticalMarkers count
  let hgExtended : extended.WellFormed :=
    g.withCriticalMarkers_wellFormed hg count
  have hbound : 0 < bound :=
    (extended.exposureBound_pos hnormal).trans_le hexposureBound
  rcases chain.endpointMarkerActionDichotomy
      (hg := hg) 0 with
      hnoMarker | ⟨j, marker, hmarker⟩
  · have hendpoint : ∀ j,
        NoCriticalMarkerActions
          (path.word (chain.levels j)) := by
      intro j
      simpa using hnoMarker j
    let trajectory := chain.toWindowedPivotTrajectory
    obtain ⟨rebase, hlabelsZero⟩ :=
      trajectory
        |>.exists_maximalProgressRebase_labels_zero_length_le_of_noDerivedRepeat
          hgExtended hnormal hground hinitial
          hexposureBound chain hnoRepeat
    obtain ⟨presentation, hpresentationDepth⟩ :=
      _root_.DCFEquivalence.EncodedFirstOrderGrammar.TracePath.StructuredPivotChain.WindowedPivotTrajectory.MaximalProgressRebase.exists_criticalGuardedFixedTailPivotPresentation_atDepth
        hg rebase hbound hendpoint hfiller bound hbound
    exact Or.inr ⟨
      { rebase := rebase
        presentation := presentation
        depth_eq := hpresentationDepth
        labels_zero_length_le := by
          simpa [trajectory] using hlabelsZero
        endpoint_noMarkerActions := hendpoint }⟩
  · exact Or.inl
      (path.eventuallyMarkerStableOpenSound_of_markerAction_mem
        hg hground hinitial hmarker)

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
