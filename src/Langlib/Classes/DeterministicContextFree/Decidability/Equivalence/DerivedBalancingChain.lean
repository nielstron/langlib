module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingResultCoverage
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.BalancingTerminalRepeat
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DerivedPairContinuation

@[expose]
public section

/-!
# Recursive balancing over certificate-derived path states

A balancing result is generally not the raw residual pair of the fixed trace.
The next balancing search must therefore start from that derived result and
continue along the same remaining trace.  `DerivedPairContinuation` supplies
the canonical continuation path, while absence of a derived repeat excludes a
raw repeat on every such continuation.  Proposition 48 can then select a
balancing opportunity again.

This file packages one recursive step and an infinite choice sequence of such
steps.  Each step records its local left/right orientation and its witnessed
balancing result at the exact absolute path word.  Results are canonically
ordered as `(active-result, pivot-result)`, even when the selected segment was
right-oriented.  Thus the retained pivot is always the right component of the
next derived state: a following left segment keeps that pivot stream, while a
following right segment is precisely a pivot-side switch.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Reindex an unbounded witnessed coverage along equality of its word. -/
public def WitnessedActiveSchemaCoverage.castWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {word word' : List (Label Action)}
    (coverage : WitnessedActiveSchemaCoverage g initialLeft initialRight
      width word)
    (hword : word = word') :
    WitnessedActiveSchemaCoverage g initialLeft initialRight
      width word' := by
  subst word'
  exact coverage

/-- Reindexing only changes the word index, not the covered endpoint pair. -/
public theorem WitnessedActiveSchemaCoverage.castWord_coverage_right
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {width : ℕ} {word word' : List (Label Action)}
    (coverage : WitnessedActiveSchemaCoverage g initialLeft initialRight
      width word)
    (hword : word = word') :
    (coverage.castWord hword).coverage.right =
      coverage.coverage.right := by
  subst word'
  rfl

namespace TracePath

/-- The side on which a balancing segment is active in the current local
ordering.  Since every result is normalized to put its pivot second, `.left`
after the first step means “retain the current pivot”, and `.right` means
“switch the pivot”. -/
public inductive BalancingSide
  | left
  | right
  deriving DecidableEq

namespace SelectedBalancingSegment

/-- Orientation of a selected balancing segment. -/
@[expose] public def side
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {bound start : ℕ}
    (selected : PathBalancingSegment path bound start) : BalancingSide :=
  match selected with
  | .left _ => BalancingSide.left
  | .right _ => BalancingSide.right

/-- The pivot component of a selected balancing segment. -/
@[expose] public def pivot
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {bound start : ℕ}
    (selected : PathBalancingSegment path bound start) : RegularTerm :=
  match selected with
  | .left _ => path.right start
  | .right _ => path.left start

end SelectedBalancingSegment

/-- One recursively selected balancing step from a certificate-derived pair.
The selected segment lives on that pair's continuation path; the result is
reindexed to the corresponding absolute word of the original path.  Both
orientations store the result in canonical `(active-result, pivot-result)`
order, so `result.coverage.right` is always the retained pivot endpoint. -/
public structure DerivedBalancingStep
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
  resultWidth : ℕ
  result :
    WitnessedActiveSchemaCoverage g initialLeft initialRight
      resultWidth (path.word (start + offset + bound))
  pivot_run_to_result :
    g.run?
        ((source.continuationPath hg hground hinitial)
          |>.segmentWord offset bound)
        (SelectedBalancingSegment.pivot selected) =
      some result.coverage.right

namespace DerivedBalancingStep

/-- Absolute prefix level reached by a recursive balancing step. -/
@[expose] public def endLevel
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : DerivedBalancingStep hg hground hinitial source bound) : ℕ :=
  start + step.offset + bound

/-- Forget the balancing presentation but retain its certificate-derived
result as the next recursive state. -/
public def target
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : DerivedBalancingStep hg hground hinitial source bound) :
    path.DerivedPairAt step.endLevel :=
  { left := step.result.coverage.left
    right := step.result.coverage.right
    derivation := step.result.coverage.derivation }

/-- Positive balancing length makes every recursive step advance strictly. -/
public theorem start_lt_endLevel
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : DerivedBalancingStep hg hground hinitial source bound)
    (hbound : 0 < bound) :
    start < step.endLevel := by
  unfold endLevel
  omega

end DerivedBalancingStep

/-- Assemble Proposition 45 at any externally selected oriented balancing
segment on the continuation from a certificate-derived state.  Selection
policy is deliberately left to the caller, which is needed when Proposition
49 chooses nearby opportunities of one fixed orientation. -/
public theorem DerivedPairAt.exists_balancingStep_of_selected
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
    ∃ step : DerivedBalancingStep hg hground hinitial source bound,
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
  have hword :
      path.word (start + offset) ++
          continuation.segmentWord offset bound =
        path.word (start + offset + bound) := by
    rw [source.continuationPath_segmentWord
      hg hground hinitial offset bound]
    exact (path.word_add (start + offset) bound).symm
  cases selected with
  | left segment =>
      obtain ⟨X, children, hroot⟩ :=
        hleftGround.exists_rootApplication
      obtain ⟨result⟩ :=
        segment.exists_concreteWitnessedBalancingResult
          hg hnormal hexposureBound
          hleftGround hrightGround hleftGround
          current.derivation hcurrentEquivalent hroot
      have hresultWord :
          path.word (start + offset) ++
              continuation.segmentWord offset bound =
            path.word (start + offset + bound) := by
        simpa [continuation, current] using hword
      let casted := result.witnessed.castWord hresultWord
      let step :
          DerivedBalancingStep hg hground hinitial source bound :=
        { offset := offset
          selected := .left segment
          resultWidth :=
            (current.right.depthPrefix bound).tails.length
          result := casted
          pivot_run_to_result := by
            rw [show casted.coverage.right =
                segment.pivotTarget by
              calc
                casted.coverage.right =
                    result.witnessed.coverage.right := by
                  exact
                    result.witnessed.castWord_coverage_right
                      hresultWord
                _ = segment.pivotTarget := result.pivot_eq]
            simpa [SelectedBalancingSegment.pivot,
              continuation, current] using
                segment.pivot_run }
      exact ⟨step, rfl, rfl, HEq.rfl⟩
  | right segment =>
      obtain ⟨X, children, hroot⟩ :=
        hrightGround.exists_rootApplication
      obtain ⟨result⟩ :=
        segment.exists_concreteWitnessedBalancingResult
          hg hnormal hexposureBound
          hrightGround hleftGround hrightGround
          (.symmetry current.derivation)
          hcurrentEquivalent.symm hroot
      have hresultWord :
          path.word (start + offset) ++
              continuation.segmentWord offset bound =
            path.word (start + offset + bound) := by
        simpa [continuation, current] using hword
      let casted := result.witnessed.castWord hresultWord
      let step :
          DerivedBalancingStep hg hground hinitial source bound :=
        { offset := offset
          selected := .right segment
          resultWidth :=
            (current.left.depthPrefix bound).tails.length
          result := casted
          pivot_run_to_result := by
            rw [show casted.coverage.right =
                segment.pivotTarget by
              calc
                casted.coverage.right =
                    result.witnessed.coverage.right := by
                  exact
                    result.witnessed.castWord_coverage_right
                      hresultWord
                _ = segment.pivotTarget := result.pivot_eq]
            simpa [SelectedBalancingSegment.pivot,
              continuation, current] using
                segment.pivot_run }
      exact ⟨step, rfl, rfl, HEq.rfl⟩

/-- Under absence of a derived repeat, every derived state admits another
normal-form balancing step along the fixed trace.  This corollary chooses the
least available offset, but `exists_balancingStep_of_selected` permits the
orientation-sensitive selections required by Proposition 49. -/
public theorem DerivedPairAt.exists_balancingStep_of_noDerivedRepeat
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
    Nonempty
      (DerivedBalancingStep hg hground hinitial source bound) := by
  classical
  let continuation :=
    source.continuationPath hg hground hinitial
  have hsourceGround :=
    groundPairCode_of_pair_derivable source.derivation
  have laws := guardedContextLaws_of_wellFormed hg
  have hsourceEquivalent :=
    source.derivation.pair_traceEquivalent_of_initial laws hinitial
  have hbound : 0 < bound :=
    (g.exposureBound_pos hnormal).trans_le hexposureBound
  have hnoRawRepeat : ¬continuation.HasRepeat :=
    source.continuationPath_hasNoRepeat
      hg hground hinitial hnoRepeat
  obtain ⟨sequence⟩ :=
    continuation.exists_balancingOpportunitySequence_of_noRepeat_wellFormed
      hg hsourceGround hsourceEquivalent hbound hnoRawRepeat
  have hexists : ∃ offset,
      continuation.HasBalancingOpportunity bound offset :=
    ⟨sequence.starts 0, sequence.selected 0⟩
  let offset := Nat.find hexists
  obtain ⟨selected⟩ := Nat.find_spec hexists
  obtain ⟨step, _hoffset, _hside, _hselected⟩ :=
    source.exists_balancingStep_of_selected
      hg hnormal hground hinitial hexposureBound selected
  exact ⟨step⟩

/-- A dependent package of one absolute path level and a pair derived there. -/
public structure DerivedBalancingState
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) where
  level : ℕ
  pair : path.DerivedPairAt level

/-- The derived state reached by a balancing step. -/
public def DerivedBalancingStep.nextState
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {start bound : ℕ}
    {source : path.DerivedPairAt start}
    (step : DerivedBalancingStep hg hground hinitial source bound) :
    DerivedBalancingState path :=
  { level := step.endLevel
    pair := step.target }

/-- An infinite recursively balanced path records one selected, oriented
balancing step from each certificate-derived state. -/
public structure DerivedBalancingChain
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hg : g.WellFormed)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (bound : ℕ)
    (initial : DerivedBalancingState path) where
  states : ℕ → DerivedBalancingState path
  steps : ∀ j,
    DerivedBalancingStep hg hground hinitial (states j).pair bound
  starts : states 0 = initial
  advances : ∀ j, states (j + 1) = (steps j).nextState

namespace DerivedBalancingChain

/-- Absolute prefix levels selected by the recursive chain. -/
@[expose] public def levels
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : DerivedBalancingState path}
    (chain : DerivedBalancingChain hg hground hinitial bound initial)
    (j : ℕ) : ℕ :=
  (chain.states j).level

/-- Every recursive step advances to a strictly later absolute prefix. -/
public theorem levels_lt_next
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : DerivedBalancingState path}
    (chain : DerivedBalancingChain hg hground hinitial bound initial)
    (hbound : 0 < bound)
    (j : ℕ) :
    chain.levels j < chain.levels (j + 1) := by
  rw [levels, levels, chain.advances j]
  exact (chain.steps j).start_lt_endLevel hbound

/-- Recursive balancing levels form a strict subsequence of the fixed trace. -/
public theorem levels_strictMono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : DerivedBalancingState path}
    (chain : DerivedBalancingChain hg hground hinitial bound initial)
    (hbound : 0 < bound) :
    StrictMono chain.levels := by
  apply strictMono_nat_of_lt_succ
  exact chain.levels_lt_next hbound

end DerivedBalancingChain

private noncomputable def chooseDerivedBalancingStep
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (state : DerivedBalancingState path) :
    DerivedBalancingStep hg hground hinitial state.pair bound :=
  Classical.choice
    (state.pair.exists_balancingStep_of_noDerivedRepeat
      hg hnormal hground hinitial hnoRepeat hexposureBound)

private noncomputable def derivedBalancingStates
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (initial : DerivedBalancingState path) :
    ℕ → DerivedBalancingState path
  | 0 => initial
  | j + 1 =>
      (chooseDerivedBalancingStep hg hnormal hground hinitial
        hnoRepeat hexposureBound
        (derivedBalancingStates hg hnormal hground hinitial
          hnoRepeat hexposureBound initial j)).nextState

/-- Classical dependent choice iterates the one-step closure into an infinite
recursively balanced chain whenever the original fixed path has no derived
repeat. -/
public theorem exists_derivedBalancingChain_of_noDerivedRepeat
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    (hground : g.groundPairCode initialLeft initialRight = true)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (hnoRepeat : ¬path.HasDerivedRepeat)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (initial : DerivedBalancingState path) :
    Nonempty
      (DerivedBalancingChain hg hground hinitial bound initial) := by
  let states :=
    derivedBalancingStates hg hnormal hground hinitial
      hnoRepeat hexposureBound initial
  exact ⟨
    { states := states
      steps := fun j =>
        chooseDerivedBalancingStep hg hnormal hground hinitial
          hnoRepeat hexposureBound (states j)
      starts := rfl
      advances := fun j => rfl }⟩

end TracePath

end EncodedFirstOrderGrammar

end DCFEquivalence
