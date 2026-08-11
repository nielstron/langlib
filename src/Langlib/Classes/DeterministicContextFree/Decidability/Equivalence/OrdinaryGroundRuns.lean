module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.TracePathRuns
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FinitePrefixExecution

@[expose]
public section

/-!
# Ground runs contain only ordinary grammar actions

Private variable labels are observable only at a variable root.  Reachable
ground terms always have application roots, so every finite run from a ground
term is the ordinary-label image of a word over grammar actions.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- The deterministic label selected by a trace path at one level. -/
noncomputable def TracePath.nextLabel
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (n : ℕ) :
    Label Action :=
  Classical.choose (path.step n)

public theorem TracePath.nextLabel_spec
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight) (n : ℕ) :
    path.word (n + 1) = path.word n ++ [path.nextLabel n] ∧
      g.step? (path.nextLabel n) (path.left n) =
        some (path.left (n + 1)) ∧
      g.step? (path.nextLabel n) (path.right n) =
        some (path.right (n + 1)) :=
  Classical.choose_spec (path.step n)

/-- The exact finite path segment beginning at `start`. -/
noncomputable def TracePath.segmentWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start : ℕ) : ℕ → List (Label Action)
  | 0 => []
  | length + 1 =>
      path.segmentWord start length ++
        [path.nextLabel (start + length)]

@[simp] public theorem TracePath.segmentWord_length
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start length : ℕ) :
    (path.segmentWord start length).length = length := by
  induction length with
  | zero => simp [segmentWord]
  | succ length ih => simp [segmentWord, ih]

/-- Adjacent exact path segments concatenate. -/
public theorem TracePath.segmentWord_add
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start first second : ℕ) :
    path.segmentWord start (first + second) =
      path.segmentWord start first ++
        path.segmentWord (start + first) second := by
  induction second with
  | zero => simp [segmentWord]
  | succ second ih =>
      rw [show first + (second + 1) = (first + second) + 1 by omega]
      simp only [segmentWord]
      rw [ih]
      simp [List.append_assoc, Nat.add_assoc]

/-- Taking an initial number of labels from a path segment gives the shorter
exact segment. -/
public theorem TracePath.take_segmentWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start : ℕ) {small large : ℕ}
    (hle : small ≤ large) :
    (path.segmentWord start large).take small =
      path.segmentWord start small := by
  have hsplit : small + (large - small) = large := by omega
  rw [← hsplit, path.segmentWord_add]
  rw [List.take_append_of_le_length (by
    simp [path.segmentWord_length])]
  exact (List.take_eq_self_iff
    (path.segmentWord start small)).mpr (by
      simp [path.segmentWord_length])

/-- Accumulated path words split into an old prefix and the exact intervening
segment. -/
public theorem TracePath.word_add
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start length : ℕ) :
    path.word (start + length) =
      path.word start ++ path.segmentWord start length := by
  induction length with
  | zero => simp [segmentWord]
  | succ length ih =>
      have hstep := (path.nextLabel_spec (start + length)).1
      calc
        path.word (start + (length + 1)) =
            path.word ((start + length) + 1) := by
              exact congrArg path.word (by omega)
        _ = path.word (start + length) ++
              [path.nextLabel (start + length)] := hstep
        _ = path.word start ++ path.segmentWord start (length + 1) := by
              rw [ih]
              simp [segmentWord, List.append_assoc]

/-- The left residual executes the exact selected path segment. -/
public theorem TracePath.left_segment_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start length : ℕ) :
    g.run? (path.segmentWord start length) (path.left start) =
      some (path.left (start + length)) := by
  induction length with
  | zero => simp [segmentWord]
  | succ length ih =>
      rw [segmentWord, g.run?_append, ih]
      simpa [Nat.add_assoc] using
        (path.nextLabel_spec (start + length)).2.1

/-- The right residual executes the exact selected path segment. -/
public theorem TracePath.right_segment_run
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (start length : ℕ) :
    g.run? (path.segmentWord start length) (path.right start) =
      some (path.right (start + length)) := by
  induction length with
  | zero => simp [segmentWord]
  | succ length ih =>
      rw [segmentWord, g.run?_append, ih]
      simpa [Nat.add_assoc] using
        (path.nextLabel_spec (start + length)).2.2

/-- A private variable label is disabled at every ground term. -/
public theorem stepPrivate?_eq_none_of_ground
    {g : EncodedFirstOrderGrammar Action}
    {term : RegularTerm} (hground : term.Ground g.ranks)
    (x : ℕ) :
    g.step? (.inr x) term = none := by
  obtain ⟨X, children, hroot⟩ := hground.exists_rootApplication
  have hrootNode :=
    RegularTerm.nodeAt?_root_of_rootApplication? hroot
  unfold step?
  simp [RegularTerm.rootNode?, hrootNode]

/-- Every successful finite run from a ground source contains only ordinary
grammar labels. -/
public theorem PreservesGroundSteps.exists_actions_of_ground_run
    {g : EncodedFirstOrderGrammar Action}
    (hsteps : g.PreservesGroundSteps)
    {source target : RegularTerm} {labels : List (Label Action)}
    (hsource : source.Ground g.ranks)
    (hrun : g.run? labels source = some target) :
    ∃ actions : List Action, labels = actions.map Sum.inl := by
  induction labels generalizing source with
  | nil => exact ⟨[], rfl⟩
  | cons label labels ih =>
      simp only [run?_cons] at hrun
      cases hstep : g.step? label source with
      | none => simp [hstep] at hrun
      | some next =>
          have htail : g.run? labels next = some target := by
            simpa [hstep] using hrun
          cases label with
          | inl action =>
              obtain ⟨actions, hlabels⟩ :=
                ih (hsteps hsource hstep) htail
              exact ⟨action :: actions, by simp [hlabels]⟩
          | inr x =>
              rw [stepPrivate?_eq_none_of_ground hsource x] at hstep
              contradiction

/-- Every accumulated word of a common ground trace path is ordinary. -/
public theorem TracePath.exists_actions_word
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hgroundSteps : g.PreservesGroundSteps)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (n : ℕ) :
    ∃ actions : List Action,
      path.word n = actions.map Sum.inl := by
  unfold groundPairCode at hground
  rw [Bool.and_eq_true] at hground
  exact hgroundSteps.exists_actions_of_ground_run
    ((RegularTerm.groundCode_eq_true_iff g.ranks initialLeft).mp
      hground.1)
    (path.left_run n)

/-- Every exact segment of a common ground trace path is ordinary. -/
public theorem TracePath.exists_actions_segmentWord
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hgroundSteps : g.PreservesGroundSteps)
    (hground : g.groundPairCode initialLeft initialRight = true)
    (start length : ℕ) :
    ∃ actions : List Action,
      path.segmentWord start length = actions.map Sum.inl := by
  have hpairGround :=
    path.residual_ground hgroundSteps hground start
  unfold groundPairCode at hpairGround
  rw [Bool.and_eq_true] at hpairGround
  exact hgroundSteps.exists_actions_of_ground_run
    ((RegularTerm.groundCode_eq_true_iff g.ranks (path.left start)).mp
      hpairGround.1)
    (path.left_segment_run start length)

/-- Any non-sinking left path window is a left balancing segment. -/
public def TracePath.leftBalancingSegment
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hnoEarlyRootSink : ∀ initialSegment suffix,
      path.segmentWord start bound = initialSegment ++ suffix →
      suffix ≠ [] →
      ¬g.RootSinksBy (path.left start) initialSegment) :
    BalancingSegment g bound (path.left start) (path.right start)
      (path.segmentWord start bound) :=
  { active_target := path.left (start + bound)
    word_length := path.segmentWord_length start bound
    agreement :=
      (g.traceEquivalent_iff_forall_traceApprox _ _).mp
        (path.residual_traceEquivalent hinitial start) bound
    active_run := path.left_segment_run start bound
    no_early_root_sink := hnoEarlyRootSink }

/-- Any non-sinking right path window is a right balancing segment. -/
public def TracePath.rightBalancingSegment
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    (path : TracePath g initialLeft initialRight)
    (hinitial : g.TraceEquivalent initialLeft initialRight)
    (start bound : ℕ)
    (hnoEarlyRootSink : ∀ initialSegment suffix,
      path.segmentWord start bound = initialSegment ++ suffix →
      suffix ≠ [] →
      ¬g.RootSinksBy (path.right start) initialSegment) :
    BalancingSegment g bound (path.right start) (path.left start)
      (path.segmentWord start bound) :=
  { active_target := path.right (start + bound)
    word_length := path.segmentWord_length start bound
    agreement :=
      ((g.traceEquivalent_iff_forall_traceApprox _ _).mp
        (path.residual_traceEquivalent hinitial start) bound).symm
    active_run := path.right_segment_run start bound
    no_early_root_sink := hnoEarlyRootSink }

end EncodedFirstOrderGrammar

end DCFEquivalence
