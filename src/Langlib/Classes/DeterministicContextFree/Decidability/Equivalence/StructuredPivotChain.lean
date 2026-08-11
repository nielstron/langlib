module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotTransition
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FiniteHeadPrefixes

@[expose]
public section

/-!
# Iterating structured pivot-policy transitions

`StructuredPivotTransition` proves the paper-faithful close/switch argument
for one retained balancing result.  This module performs the dependent choice
needed to iterate that construction, and records the numerical fact that the
apparently step-dependent close window is bounded by one grammar-wide
constant.

The final `PivotEdge` interface forgets the internal successor-row index while
retaining an actual run from the current pivot to a representative of the next
pivot.  Switched edges may end only up to unfolding equivalence, which is the
right invariant for later run transport.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Grammar-uniform upper bound for the finite active residual occurring in
one structured balancing step of length `bound`. -/
@[expose] public def structuredPivotSwitchDepthBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  g.residualUnfoldingDepthBound bound
      (FiniteHead.compiledDepthBound (g.ranks.foldr max 0) 1) + 1

/-- Grammar-uniform upper bound for the close-left search window. -/
@[expose] public def structuredPivotCloseBound
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  g.structuredPivotSwitchDepthBound bound * bound

namespace TracePath

namespace StructuredDerivedBalancingStep

omit [DecidableEq Action] in
private theorem residualUnfoldingDepthBound_mono_initial
    (g : EncodedFirstOrderGrammar Action)
    {steps initial initial' : ℕ} (hinitial : initial ≤ initial') :
    g.residualUnfoldingDepthBound steps initial ≤
      g.residualUnfoldingDepthBound steps initial' := by
  induction steps generalizing initial initial' with
  | zero => simpa [residualUnfoldingDepthBound] using hinitial
  | succ steps ih =>
      simp only [residualUnfoldingDepthBound]
      exact ih (Nat.add_le_add_left hinitial g.rhsNodeBound)

/-- Every structured step uses at most the grammar-wide switch depth. -/
public theorem switchDepth_le_structuredPivotSwitchDepthBound
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
    step.switchDepth ≤ g.structuredPivotSwitchDepthBound bound := by
  unfold switchDepth structuredPivotSwitchDepthBound
  have hactions : step.structured.activeResult.actions.length = bound :=
    step.structured.activeResult.actions_length
  unfold BalancingSegment.ActivePrefixResidual.unfoldingDepthBound
  rw [hactions]
  apply Nat.add_le_add_right
  apply residualUnfoldingDepthBound_mono_initial
  exact FiniteHead.compiledNodeCount_le_depthBound
    (RegularTerm.depthPrefix_head_rankedBy
      step.active_ground 1)
    (RegularTerm.depthPrefix_head_depth_le _ 1)

/-- Consequently every dynamic close window is below one grammar-wide
window. -/
public theorem closeBound_le_structuredPivotCloseBound
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
    step.closeBound ≤ g.structuredPivotCloseBound bound := by
  unfold closeBound structuredPivotCloseBound
  exact Nat.mul_le_mul_right bound
    step.switchDepth_le_structuredPivotSwitchDepthBound

/-- A positive balancing length makes a structured step advance strictly
beyond its source level. -/
public theorem source_lt_endLevel
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : StructuredDerivedBalancingStep
      hg hground hinitial source bound)
    (hbound : 0 < bound) :
    start < step.endLevel := by
  unfold endLevel
  omega

end StructuredDerivedBalancingStep

/-- An infinite sequence of retained structured balancing results, with each
successor selected by the close-left/fallback policy of Proposition 49. -/
public structure StructuredPivotChain
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hg : g.WellFormed)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (bound : ℕ)
    (initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound) where
  states : ℕ → StructuredDerivedBalancingState
    (path := path) hg hground hinitial bound
  transitions : ∀ j, StructuredPivotPolicyTransition
    hg hground hinitial (states j).incoming
  starts : states 0 = initial
  advances : ∀ j,
    states (j + 1) = (transitions j).nextState

namespace StructuredPivotChain

/-- Absolute endpoint level of the retained balancing result at index `j`. -/
@[expose] public noncomputable def levels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) : ℕ :=
  (chain.states j).level

/-- The certificate-derived pair attached to a chain level. -/
public noncomputable def pairs
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) : path.DerivedPairAt (chain.levels j) :=
  (chain.states j).pair

/-- Input pivot of the selected balancing segment at index `j`. -/
@[expose] public noncomputable def pivot
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) : RegularTerm :=
  SelectedBalancingSegment.pivot (chain.states j).incoming.selected

/-- Every chain step advances to a strictly later absolute prefix. -/
public theorem levels_lt_next
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (hbound : 0 < bound) (j : ℕ) :
    chain.levels j < chain.levels (j + 1) := by
  rw [levels, levels, chain.advances j]
  exact (chain.transitions j).next.source_lt_endLevel hbound

/-- Chain endpoint levels form a strict subsequence of the original trace. -/
public theorem levels_strictMono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (hbound : 0 < bound) :
    StrictMono chain.levels := by
  apply strictMono_nat_of_lt_succ
  exact chain.levels_lt_next hbound

/-- The next segment retained by a transition is exactly the incoming segment
of the next chain state. -/
public theorem transition_next_pivot_eq
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) :
    SelectedBalancingSegment.pivot (chain.transitions j).next.selected =
      chain.pivot (j + 1) := by
  rw [pivot, chain.advances j]
  rfl

/-- The unmodified path word against which the selected pivot bridge is
compared. -/
@[expose] public noncomputable def unmodifiedBridgeWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) : List (Label Action) :=
  let state := chain.states j
  let current := state.incoming
  (state.source.continuationPath hg hground hinitial).segmentWord
      current.offset bound ++
    current.continuationPath.segmentWord
      0 (chain.transitions j).policy.offset

end StructuredPivotChain

private noncomputable def chooseStructuredPivotTransition
    {g : EncodedFirstOrderGrammar Action} {hg : g.WellFormed}
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (state : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound) :
    StructuredPivotPolicyTransition
      hg hground hinitial state.incoming :=
  Classical.choice
    (state.exists_policyTransition_of_noDerivedRepeat
      hnormal hnoRepeat hexposureBound)

private noncomputable def structuredPivotStates
    {g : EncodedFirstOrderGrammar Action} {hg : g.WellFormed}
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound) :
    ℕ → StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound
  | 0 => initial
  | j + 1 =>
      (chooseStructuredPivotTransition hnormal hnoRepeat
        hexposureBound
        (structuredPivotStates hnormal hnoRepeat
          hexposureBound initial j)).nextState

/-- Dependent choice iterates the one-step structured policy theorem. -/
public theorem exists_structuredPivotChain_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} {hg : g.WellFormed}
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound) :
    Nonempty (StructuredPivotChain
      hg hground hinitial bound initial) := by
  let states := structuredPivotStates hnormal hnoRepeat
    hexposureBound initial
  exact ⟨
    { states := states
      transitions := fun j =>
        chooseStructuredPivotTransition hnormal hnoRepeat
          hexposureBound (states j)
      starts := rfl
      advances := fun j => rfl }⟩

/-- The first structured state may be selected from any certificate-derived
source pair. -/
public theorem DerivedPairAt.exists_initialStructuredBalancingState
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {start bound : ℕ}
    (source : path.DerivedPairAt start)
    (hexposureBound : g.exposureBound hnormal ≤ bound) :
    Nonempty (StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound) := by
  obtain ⟨selection⟩ :=
    source.exists_pivotSelectionPolicy_of_noDerivedRepeat
      hg hground hinitial hnoRepeat 0
  obtain ⟨step, _hoffset, _hside, _hselected⟩ :=
    source.exists_structuredBalancingStep_of_selected
      hg hnormal hground hinitial hexposureBound selection.selected
  exact ⟨{ start := start, source := source, incoming := step }⟩

/-- A simplified executable edge between consecutive selected pivots. -/
public structure StructuredPivotPolicyTransition.PivotEdge
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
      hg hground hinitial current) where
  word : List (Label Action)
  target : RegularTerm
  run : g.run? word
      (SelectedBalancingSegment.pivot current.selected) = some target
  target_matches : target.UnfoldingEquivalent
      (SelectedBalancingSegment.pivot transition.next.selected)
  length_le_unmodified :
    word.length ≤
      ((source.continuationPath hg hground hinitial).segmentWord
          current.offset bound ++
        current.continuationPath.segmentWord
          0 transition.policy.offset).length

namespace StructuredPivotPolicyTransition

/-- Forget the internal direct/switch branch while retaining one concrete
pivot run and its length comparison with the unmodified path word. -/
public theorem exists_pivotEdge
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
    Nonempty transition.PivotEdge := by
  classical
  let nextPackage :
      Σ offset, PathBalancingSegment current.continuationPath bound offset :=
    ⟨transition.next.offset, transition.next.selected⟩
  let policyPackage :
      Σ offset, PathBalancingSegment current.continuationPath bound offset :=
    ⟨transition.policy.offset, transition.policy.selected⟩
  have hpackages : nextPackage = policyPackage := by
    apply Sigma.ext transition.next_offset_eq
    exact transition.next_selected_eq
  have hselected :
      SelectedBalancingSegment.pivot transition.next.selected =
        SelectedBalancingSegment.pivot transition.policy.selected := by
    exact congrArg
      (fun package => SelectedBalancingSegment.pivot package.2)
      hpackages
  rcases transition.bridge.direct_or_switched with hdirect | hswitch
  · obtain ⟨_hside, hrun⟩ := hdirect
    exact ⟨
      { word :=
          (source.continuationPath hg hground hinitial).segmentWord
              current.offset bound ++
            current.continuationPath.segmentWord
              0 transition.policy.offset
        target := SelectedBalancingSegment.pivot transition.policy.selected
        run := hrun
        target_matches := by
          rw [hselected]
        length_le_unmodified := le_refl _ }⟩
  · obtain ⟨_hside, i, cut, _hcut, reached,
        hrun, hreached, hshort⟩ := hswitch
    exact ⟨
      { word :=
          (current.structured.family.row i).modifiedBridge
            current.continuationPath cut transition.policy.offset
        target := reached
        run := hrun
        target_matches := by
          rw [hselected]
          exact hreached
        length_le_unmodified := Nat.le_of_lt hshort }⟩

end StructuredPivotPolicyTransition

namespace StructuredPivotChain

public noncomputable def chosenPivotEdge
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) : (chain.transitions j).PivotEdge :=
  Classical.choice (chain.transitions j).exists_pivotEdge

/-- One actual representative of a selected pivot, retained with groundness
and semantic equality to the chain's chosen presentation. -/
public structure PivotRepresentativeAt
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) where
  term : RegularTerm
  ground : term.Ground g.ranks
  equivalent : term.UnfoldingEquivalent (chain.pivot j)

public noncomputable def nextPivotRepresentative
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) (current : chain.PivotRepresentativeAt j) :
    chain.PivotRepresentativeAt (j + 1) := by
  let edge := chosenPivotEdge chain j
  have hpivotGround : (chain.pivot j).Ground g.ranks := by
    exact (chain.states j).incoming.pivot_ground
  have htransport :=
    exists_run_of_unfoldingEquivalent hg current.equivalent
      (RegularTerm.referenceClosed_of_ground current.ground)
      (RegularTerm.referenceClosed_of_ground hpivotGround)
      edge.run
  let target := Classical.choose htransport
  have hrun := (Classical.choose_spec htransport).1
  have htarget := (Classical.choose_spec htransport).2
  have hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact
    { term := target
      ground := hgroundSteps.ground_of_run current.ground hrun
      equivalent := by
        rw [← chain.transition_next_pivot_eq j]
        exact htarget.trans edge.target_matches }

/-- The chosen representative successor is reached by the chosen concrete
edge word. -/
public theorem nextPivotRepresentative_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial)
    (j : ℕ) (current : chain.PivotRepresentativeAt j) :
    g.run? (chain.chosenPivotEdge j).word current.term =
      some (chain.nextPivotRepresentative j current).term := by
  unfold nextPivotRepresentative
  exact (Classical.choose_spec
    (exists_run_of_unfoldingEquivalent hg current.equivalent
      (RegularTerm.referenceClosed_of_ground current.ground)
      (RegularTerm.referenceClosed_of_ground
        (chain.states j).incoming.pivot_ground)
      (chain.chosenPivotEdge j).run)).1

public noncomputable def pivotRepresentatives
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial) :
    ∀ j, chain.PivotRepresentativeAt j
  | 0 =>
      { term := chain.pivot 0
        ground := (chain.states 0).incoming.pivot_ground
        equivalent := RegularTerm.unfoldingEquivalent_refl _ }
  | j + 1 =>
      nextPivotRepresentative chain j (pivotRepresentatives chain j)

/-- The concrete pivot trajectory obtained by transporting every selected
bridge to the representative reached by its predecessor. -/
public structure PivotTrajectory
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial) where
  representatives : ℕ → RegularTerm
  representative_ground : ∀ j,
    (representatives j).Ground g.ranks
  representative_matches : ∀ j,
    (representatives j).UnfoldingEquivalent (chain.pivot j)
  edgeWords : ℕ → List (Label Action)
  edge_run : ∀ j,
    g.run? (edgeWords j) (representatives j) =
      some (representatives (j + 1))
  edge_length_le : ∀ j,
    (edgeWords j).length ≤ (chain.unmodifiedBridgeWord j).length

/-- Every structured pivot chain admits an exact executable representative
trajectory. -/
public noncomputable def toPivotTrajectory
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    (chain : StructuredPivotChain hg hground hinitial bound initial) :
    chain.PivotTrajectory := by
  let representatives := fun j => (pivotRepresentatives chain j).term
  let edgeWords := fun j => (chosenPivotEdge chain j).word
  refine
    { representatives := representatives
      representative_ground := fun j =>
        (pivotRepresentatives chain j).ground
      representative_matches := fun j =>
        (pivotRepresentatives chain j).equivalent
      edgeWords := edgeWords
      edge_run := ?_
      edge_length_le := ?_ }
  · intro j
    change g.run? (chosenPivotEdge chain j).word
        (pivotRepresentatives chain j).term =
      some (pivotRepresentatives chain (j + 1)).term
    rw [pivotRepresentatives]
    exact chain.nextPivotRepresentative_run j
      (pivotRepresentatives chain j)
  · intro j
    exact (chosenPivotEdge chain j).length_le_unmodified

namespace PivotTrajectory

/-- Concatenation of the first `j` concrete pivot edges. -/
@[expose] public def prefixWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory) : ℕ → List (Label Action)
  | 0 => []
  | j + 1 => trajectory.prefixWord j ++ trajectory.edgeWords j

/-- The accumulated pivot word executes exactly from the first representative
to the representative at index `j`. -/
public theorem prefixWord_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory) (j : ℕ) :
    g.run? (trajectory.prefixWord j) (trajectory.representatives 0) =
      some (trajectory.representatives j) := by
  induction j with
  | zero => simp [prefixWord]
  | succ j ih =>
      rw [prefixWord, g.run?_append, ih]
      exact trajectory.edge_run j

/-- Every accumulated concrete pivot word consists only of ordinary grammar
actions. -/
public theorem exists_actions_prefixWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory) (j : ℕ) :
    ∃ actions : List Action,
      trajectory.prefixWord j = actions.map Sum.inl := by
  let hgroundSteps : g.PreservesGroundSteps :=
    preservesGroundSteps_of_wellFormed hg
  exact hgroundSteps.exists_actions_of_ground_run
    (trajectory.representative_ground 0)
    (trajectory.prefixWord_run j)

/-- Pointwise edge-length bounds accumulate by the corresponding primitive
recursive sum. -/
public theorem prefixWord_length_le_sum
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory)
    (edgeBound : ℕ → ℕ)
    (hedge : ∀ j, (trajectory.edgeWords j).length ≤ edgeBound j) :
    ∀ j, (trajectory.prefixWord j).length ≤
      ((List.range j).map edgeBound).sum := by
  intro j
  induction j with
  | zero => simp [prefixWord.eq_def]
  | succ j ih =>
      rw [prefixWord.eq_def, List.length_append]
      simpa [List.range_succ, List.map_append, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using Nat.add_le_add ih (hedge j)

/-- A constant edge bound gives the linear accumulated action budget used by
the fixed-tail schema envelope. -/
public theorem prefixWord_length_le_mul
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound edgeBound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain hg hground hinitial bound initial}
    (trajectory : chain.PivotTrajectory)
    (hedge : ∀ j, (trajectory.edgeWords j).length ≤ edgeBound)
    (j : ℕ) :
    (trajectory.prefixWord j).length ≤ j * edgeBound := by
  have hsum := trajectory.prefixWord_length_le_sum
    (fun _ => edgeBound) hedge j
  simpa using hsum

end PivotTrajectory

end StructuredPivotChain

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
