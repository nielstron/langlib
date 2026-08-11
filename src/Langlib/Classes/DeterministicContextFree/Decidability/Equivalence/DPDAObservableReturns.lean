module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.DPDANormalization

@[expose]
public section

/-!
# Effective arbitrary-input head returns

The universality development already computes the least summary relation of
the pushdown system obtained by erasing input labels.  By changing only the
rejecting-state selector, the same saturation decides whether a head
configuration `(q,[Z])` can consume some word and return with empty stack in a
specified control state.

Unlike the epsilon-only return table used during DPDA normalization, this
query retains all effective input rows.  It is the executable mask needed to
retain exactly the exposable arguments of the translated first-order grammar.
-/

open DCFEncodedDPDA

namespace DCFEquivalence

namespace DPDAObservableReturns

variable {Action : Type} [Fintype Action] [DecidableEq Action]

/-- The source transition system with `target` as its sole rejecting control.
Initial-state and start-symbol fields are irrelevant to head queries. -/
@[expose] public def targetMachine
    (machine : EncodedDPDA Action) (target : ℕ) :
    EncodedDPDA Action :=
  (machine.numStates - 1,
    machine.numStackSymbols - 1,
    0,
    0,
    (List.range machine.numStates).filter fun state =>
      decide (state ≠ target % machine.numStates),
    machine.inputRows,
    machine.epsilonRows)

omit [Fintype Action] [DecidableEq Action] in
@[simp] public theorem targetMachine_numStates
    (machine : EncodedDPDA Action) (target : ℕ) :
    (targetMachine machine target).numStates = machine.numStates := by
  unfold targetMachine EncodedDPDA.numStates
  omega

omit [Fintype Action] [DecidableEq Action] in
@[simp] public theorem targetMachine_numStackSymbols
    (machine : EncodedDPDA Action) (target : ℕ) :
    (targetMachine machine target).numStackSymbols =
      machine.numStackSymbols := by
  unfold targetMachine EncodedDPDA.numStackSymbols
  change machine.numStackSymbols - 1 + 1 = machine.numStackSymbols
  have hpositive := machine.numStackSymbols_pos
  omega

omit [Fintype Action] [DecidableEq Action] in
@[simp] public theorem targetMachine_inputRows
    (machine : EncodedDPDA Action) (target : ℕ) :
    (targetMachine machine target).inputRows = machine.inputRows := rfl

omit [Fintype Action] [DecidableEq Action] in
@[simp] public theorem targetMachine_epsilonRows
    (machine : EncodedDPDA Action) (target : ℕ) :
    (targetMachine machine target).epsilonRows =
      machine.epsilonRows := rfl

omit [Fintype Action] [DecidableEq Action] in
@[simp] public theorem targetMachine_effectiveEpsilonRows
    (machine : EncodedDPDA Action) (target : ℕ) :
    (targetMachine machine target).effectiveEpsilonRows =
      machine.effectiveEpsilonRows := by
  unfold EncodedDPDA.effectiveEpsilonRows
  simp only [targetMachine_epsilonRows]
  congr 1

omit [Fintype Action] in
@[simp] public theorem targetMachine_effectiveInputRows
    (machine : EncodedDPDA Action) (target : ℕ) :
    (targetMachine machine target).effectiveInputRows =
      machine.effectiveInputRows := by
  unfold EncodedDPDA.effectiveInputRows
  simp only [targetMachine_inputRows, targetMachine_epsilonRows]
  congr 1

omit [Fintype Action] in
public theorem targetMachine_rawErasedStep_iff
    (machine : EncodedDPDA Action) (target : ℕ)
    (x y : ℕ × List ℕ) :
    (targetMachine machine target).RawErasedStep x y ↔
      machine.RawErasedStep x y := by
  constructor <;> intro hstep
  · cases hstep with
    | @epsilon row suffix hrow =>
        have hrow' : row ∈ machine.effectiveEpsilonRows := by
          simpa using hrow
        simpa [EncodedDPDA.normalizedEpsilonSource,
          EncodedDPDA.normalizedEpsilonTop,
          EncodedDPDA.normalizedEpsilonTarget,
          EncodedDPDA.normalizedEpsilonReplacement] using
            (EncodedDPDA.RawErasedStep.epsilon
              (c := machine) (suffix := suffix) hrow')
    | @input row suffix hrow =>
        have hrow' : row ∈ machine.effectiveInputRows := by
          simpa using hrow
        simpa [EncodedDPDA.normalizedInputSource,
          EncodedDPDA.normalizedInputTop,
          EncodedDPDA.normalizedInputTarget,
          EncodedDPDA.normalizedInputReplacement] using
            (EncodedDPDA.RawErasedStep.input
              (c := machine) (suffix := suffix) hrow')
  · cases hstep with
    | @epsilon row suffix hrow =>
        have hrow' :
            row ∈ (targetMachine machine target).effectiveEpsilonRows := by
          simpa using hrow
        simpa [EncodedDPDA.normalizedEpsilonSource,
          EncodedDPDA.normalizedEpsilonTop,
          EncodedDPDA.normalizedEpsilonTarget,
          EncodedDPDA.normalizedEpsilonReplacement] using
            (EncodedDPDA.RawErasedStep.epsilon
              (c := targetMachine machine target)
              (suffix := suffix) hrow')
    | @input row suffix hrow =>
        have hrow' :
            row ∈ (targetMachine machine target).effectiveInputRows := by
          simpa using hrow
        simpa [EncodedDPDA.normalizedInputSource,
          EncodedDPDA.normalizedInputTop,
          EncodedDPDA.normalizedInputTarget,
          EncodedDPDA.normalizedInputReplacement] using
            (EncodedDPDA.RawErasedStep.input
              (c := targetMachine machine target)
              (suffix := suffix) hrow')

omit [Fintype Action] in
public theorem targetMachine_rawErasedReaches_iff
    (machine : EncodedDPDA Action) (target : ℕ)
    (x y : ℕ × List ℕ) :
    (targetMachine machine target).RawErasedReaches x y ↔
      machine.RawErasedReaches x y := by
  constructor <;> intro hreach
  · exact Relation.ReflTransGen.mono
      (fun x y hstep =>
        (targetMachine_rawErasedStep_iff machine target x y).mp hstep)
      hreach
  · exact Relation.ReflTransGen.mono
      (fun x y hstep =>
        (targetMachine_rawErasedStep_iff machine target x y).mpr hstep)
      hreach

/-- Semantic arbitrary-input return of one stack head to one control state. -/
@[expose] public def RawHeadReturns
    (machine : EncodedDPDA Action) (q Z target : ℕ) : Prop :=
  let query := targetMachine machine target
  query.RawErasedReaches
    (q % machine.numStates, [Z % machine.numStackSymbols])
    (target % machine.numStates, [])

/-- Executable arbitrary-input return test, using the existing least summary
relation. -/
@[expose] public def headReturnsCode
    (machine : EncodedDPDA Action) (q Z target : ℕ) : Bool :=
  decide ((q % machine.numStates, Z % machine.numStackSymbols,
    target % machine.numStates) ∈
      (targetMachine machine target).leastSummaryRelation)

omit [Fintype Action] in
private theorem summaryPath_from_sink
    {machine : EncodedDPDA Action}
    {R : List EncodedDPDA.SummaryTriple}
    (hR : ∀ t ∈ R,
      t.2.2 = machine.sinkIndex ∨
        (t.1 < machine.numStates ∧
          t.2.1 < machine.numStackSymbols ∧
          t.2.2 < machine.numStates ∧
          machine.RawErasedReaches (t.1, [t.2.1]) (t.2.2, [])))
    {p : ℕ} (hp : p = machine.sinkIndex)
    {gamma : List ℕ} {r : ℕ}
    (hpath : EncodedDPDA.RawSummaryPath machine R p gamma r) :
    r = machine.sinkIndex := by
  induction hpath with
  | nil => exact hp
  | @cons source middle _ Z gamma _ hedge _ ih =>
      subst source
      rcases hR _ hedge with hmiddle | hsemantic
      · have hmiddle' : middle = machine.sinkIndex := by
          simpa using hmiddle
        subst middle
        exact ih rfl
      · simp [EncodedDPDA.sinkIndex] at hsemantic

private theorem summaryPath_returns
    {machine : EncodedDPDA Action}
    {R : List EncodedDPDA.SummaryTriple}
    (hR : ∀ t ∈ R,
      t.2.2 = machine.sinkIndex ∨
        (t.1 < machine.numStates ∧
          t.2.1 < machine.numStackSymbols ∧
          t.2.2 < machine.numStates ∧
          machine.RawErasedReaches (t.1, [t.2.1]) (t.2.2, [])))
    {p r : ℕ} {gamma : List ℕ}
    (hpath : EncodedDPDA.RawSummaryPath machine R p gamma r)
    (hr : r < machine.numStates) :
    machine.RawErasedReaches
      (p, gamma.map fun Z => Z % machine.numStackSymbols) (r, []) := by
  induction hpath with
  | nil => exact Relation.ReflTransGen.refl
  | @cons p middle r Z gamma hmiddle hedge htail ih =>
      have hmiddleNotSink : middle ≠ machine.sinkIndex := by
        intro hmiddleSink
        subst middle
        have hrSink := summaryPath_from_sink hR rfl htail
        subst r
        simp [EncodedDPDA.sinkIndex] at hr
      have hmiddleState : middle < machine.numStates := by
        have hle : middle ≤ machine.numStates := by
          simpa [EncodedDPDA.pStateCount] using Nat.le_of_lt_succ hmiddle
        exact lt_of_le_of_ne hle hmiddleNotSink
      have hhead : machine.RawErasedReaches
          (p, [Z % machine.numStackSymbols]) (middle, []) := by
        rcases hR _ hedge with hSink | hsemantic
        · exact (hmiddleNotSink hSink).elim
        · simpa [Nat.mod_mod] using hsemantic.2.2.2
      have hheadSuffix :=
        DPDANormalization.Popping.rawErasedReaches_suffix hhead
          (gamma.map fun Y => Y % machine.numStackSymbols)
      exact Relation.ReflTransGen.trans
        (by simpa using hheadSuffix) (ih hr)

private theorem leastSummary_sound_return
    (machine : EncodedDPDA Action) (q Z target : ℕ)
    (hmem : (q % machine.numStates, Z % machine.numStackSymbols,
      target % machine.numStates) ∈
        (targetMachine machine target).leastSummaryRelation) :
    RawHeadReturns machine q Z target := by
  classical
  let query := targetMachine machine target
  let semantic : List EncodedDPDA.SummaryTriple :=
    query.allSummaryTriples.filter fun t => decide
      (t.2.2 = query.sinkIndex ∨
        (t.1 < query.numStates ∧
          t.2.1 < query.numStackSymbols ∧
          t.2.2 < query.numStates ∧
          query.RawErasedReaches (t.1, [t.2.1]) (t.2.2, [])))
  have hsemantic : ∀ t ∈ semantic,
      t.2.2 = query.sinkIndex ∨
        (t.1 < query.numStates ∧
          t.2.1 < query.numStackSymbols ∧
          t.2.2 < query.numStates ∧
          query.RawErasedReaches (t.1, [t.2.1]) (t.2.2, [])) := by
    intro t ht
    exact of_decide_eq_true (List.mem_filter.mp ht).2
  have hclosed : EncodedDPDA.RawSummaryClosed query semantic := by
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      apply List.mem_filter.mpr
      refine ⟨(List.mem_filter.mp ht).1, ?_⟩
      rw [decide_eq_true_eq]
      have hbase := of_decide_eq_true (List.mem_filter.mp ht).2
      rcases hbase with hsink | hreject
      · exact Or.inl hsink.2
      · exact Or.inl hreject.2
    · intro row hrow r hr hpath
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · rw [EncodedDPDA.mem_allSummaryTriples_iff]
        exact ⟨(Nat.mod_lt _ query.numStates_pos).trans
            (by simp [EncodedDPDA.pStateCount]),
          Nat.mod_lt _ query.numStackSymbols_pos, hr⟩
      · rw [decide_eq_true_eq]
        by_cases hrsink : r = query.sinkIndex
        · exact Or.inl hrsink
        · right
          have hrState : r < query.numStates := by
            have hle : r ≤ query.numStates := by
              simpa [EncodedDPDA.pStateCount] using Nat.le_of_lt_succ hr
            exact lt_of_le_of_ne hle hrsink
          have hreplacement := summaryPath_returns hsemantic hpath hrState
          refine ⟨Nat.mod_lt _ query.numStates_pos,
            Nat.mod_lt _ query.numStackSymbols_pos, hrState, ?_⟩
          have hfirst : query.RawErasedStep
              (query.normalizedEpsilonSource row,
                [query.normalizedEpsilonTop row])
              (query.normalizedEpsilonTarget row,
                query.normalizedEpsilonReplacement row) := by
            simpa using (EncodedDPDA.RawErasedStep.epsilon
              (c := query) (suffix := []) hrow)
          have hreplacement' : query.RawErasedReaches
              (query.normalizedEpsilonTarget row,
                query.normalizedEpsilonReplacement row) (r, []) := by
            simpa [EncodedDPDA.normalizedEpsilonReplacement,
              List.map_map, Function.comp_def, Nat.mod_mod]
              using hreplacement
          exact Relation.ReflTransGen.head hfirst hreplacement'
    · intro row hrow r hr hpath
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · rw [EncodedDPDA.mem_allSummaryTriples_iff]
        exact ⟨(Nat.mod_lt _ query.numStates_pos).trans
            (by simp [EncodedDPDA.pStateCount]),
          Nat.mod_lt _ query.numStackSymbols_pos, hr⟩
      · rw [decide_eq_true_eq]
        by_cases hrsink : r = query.sinkIndex
        · exact Or.inl hrsink
        · right
          have hrState : r < query.numStates := by
            have hle : r ≤ query.numStates := by
              simpa [EncodedDPDA.pStateCount] using Nat.le_of_lt_succ hr
            exact lt_of_le_of_ne hle hrsink
          have hreplacement := summaryPath_returns hsemantic hpath hrState
          refine ⟨Nat.mod_lt _ query.numStates_pos,
            Nat.mod_lt _ query.numStackSymbols_pos, hrState, ?_⟩
          have hfirst : query.RawErasedStep
              (query.normalizedInputSource row,
                [query.normalizedInputTop row])
              (query.normalizedInputTarget row,
                query.normalizedInputReplacement row) := by
            simpa using (EncodedDPDA.RawErasedStep.input
              (c := query) (suffix := []) hrow)
          have hreplacement' : query.RawErasedReaches
              (query.normalizedInputTarget row,
                query.normalizedInputReplacement row) (r, []) := by
            simpa [EncodedDPDA.normalizedInputReplacement,
              List.map_map, Function.comp_def, Nat.mod_mod]
              using hreplacement
          exact Relation.ReflTransGen.head hfirst hreplacement'
  have hin := EncodedDPDA.leastSummaryRelation_minimal query hclosed hmem
  have hmeaning := hsemantic _ hin
  rcases hmeaning with hsink | hreturn
  · have hlt := Nat.mod_lt target machine.numStates_pos
    simp [query, EncodedDPDA.sinkIndex] at hsink
    omega
  · simpa [RawHeadReturns, query] using hreturn.2.2.2

private theorem leastSummaryPath_of_rawReturn
    {machine : EncodedDPDA Action}
    {x : ℕ × List ℕ} {target : ℕ}
    (hreach : machine.RawErasedReaches x (target, [])) :
    EncodedDPDA.RawSummaryPath machine machine.leastSummaryRelation
      x.1 x.2 target := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact .nil target
  | @head x y hstep hrest ih =>
      cases hstep with
      | @epsilon row suffix hrow =>
          obtain ⟨middle, hreplacement, hsuffix⟩ :=
            EncodedDPDA.RawSummaryPath.of_append_left ih
          have hmiddle : middle < machine.pStateCount :=
            hreplacement.end_lt
              ((Nat.mod_lt _ machine.numStates_pos).trans
                (by simp [EncodedDPDA.pStateCount]))
          refine .cons hmiddle ?_ hsuffix
          simpa [EncodedDPDA.normalizedEpsilonTop, Nat.mod_mod] using
            (EncodedDPDA.leastSummaryRelation_closed machine).2.1
              row hrow middle hmiddle hreplacement
      | @input row suffix hrow =>
          obtain ⟨middle, hreplacement, hsuffix⟩ :=
            EncodedDPDA.RawSummaryPath.of_append_left ih
          have hmiddle : middle < machine.pStateCount :=
            hreplacement.end_lt
              ((Nat.mod_lt _ machine.numStates_pos).trans
                (by simp [EncodedDPDA.pStateCount]))
          refine .cons hmiddle ?_ hsuffix
          simpa [EncodedDPDA.normalizedInputTop, Nat.mod_mod] using
            (EncodedDPDA.leastSummaryRelation_closed machine).2.2
              row hrow middle hmiddle hreplacement

private theorem leastSummary_complete_return
    (machine : EncodedDPDA Action) (q Z target : ℕ)
    (hreturn : RawHeadReturns machine q Z target) :
    (q % machine.numStates, Z % machine.numStackSymbols,
      target % machine.numStates) ∈
        (targetMachine machine target).leastSummaryRelation := by
  let query := targetMachine machine target
  have hpath : EncodedDPDA.RawSummaryPath query
      query.leastSummaryRelation
      (q % machine.numStates) [Z % machine.numStackSymbols]
      (target % machine.numStates) := by
    have hreach : query.RawErasedReaches
        (q % machine.numStates, [Z % machine.numStackSymbols])
        (target % machine.numStates, []) := by
      simpa [RawHeadReturns, query] using hreturn
    exact leastSummaryPath_of_rawReturn hreach
  cases hpath with
  | @cons _ middle _ top tail _ hedge htail =>
      cases htail with
      | nil =>
          simpa [query, EncodedDPDA.normalizedEpsilonTop,
            Nat.mod_mod] using hedge

/-- Correctness of the executable arbitrary-input head-return mask. -/
public theorem headReturnsCode_eq_true_iff
    (machine : EncodedDPDA Action) (q Z target : ℕ) :
    headReturnsCode machine q Z target = true ↔
      RawHeadReturns machine q Z target := by
  rw [headReturnsCode, decide_eq_true_eq]
  exact ⟨leastSummary_sound_return machine q Z target,
    leastSummary_complete_return machine q Z target⟩

/-- Every positive return mask entry supplies an ordinary input word realizing
the corresponding decoded DPDA return. -/
public theorem exists_word_reaches_of_headReturnsCode
    (machine : EncodedDPDA Action) {q Z target : ℕ}
    (hreturn : headReturnsCode machine q Z target = true) :
    ∃ word, @PDA.Reaches _ _ _ _ _ _ machine.toDPDA.toPDA
      (machine.decodeRawConf
        (q % machine.numStates, [Z % machine.numStackSymbols]) word)
      (machine.decodeRawConf
        (target % machine.numStates, []) []) := by
  have hrawQuery :=
    (headReturnsCode_eq_true_iff machine q Z target).mp hreturn
  let query := targetMachine machine target
  have hraw :
      machine.RawErasedReaches
        (q % machine.numStates, [Z % machine.numStackSymbols])
        (target % machine.numStates, []) := by
    exact (targetMachine_rawErasedReaches_iff machine target _ _).mp
      hrawQuery
  exact machine.exists_word_reaches_of_rawErasedReaches hraw

/-- All target controls to which one stack head can return after consuming
some ordinary input word. -/
@[expose] public def returnTargets
    (machine : EncodedDPDA Action) (q Z : ℕ) : List ℕ :=
  (List.range machine.numStates).filter fun target =>
    headReturnsCode machine q Z target

public theorem mem_returnTargets_iff
    (machine : EncodedDPDA Action) (q Z target : ℕ) :
    target ∈ returnTargets machine q Z ↔
      target < machine.numStates ∧
        RawHeadReturns machine q Z target := by
  rw [returnTargets, List.mem_filter, List.mem_range]
  exact and_congr_right fun _ =>
    headReturnsCode_eq_true_iff machine q Z target

omit [Fintype Action] in
public theorem returnTargets_nodup
    (machine : EncodedDPDA Action) (q Z : ℕ) :
    (returnTargets machine q Z).Nodup := by
  exact List.Nodup.filter _ List.nodup_range

/-- Retained grammar arguments at one translated head.  Epsilon heads have no
grammar rule and therefore retain no formal argument; stable heads retain
exactly the arbitrary-input return targets. -/
@[expose] public def exposedTargets
    (machine : EncodedDPDA Action) (q Z : ℕ) : List ℕ :=
  if DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none then
    returnTargets machine q Z
  else
    []

public theorem mem_exposedTargets_iff
    (machine : EncodedDPDA Action) (q Z target : ℕ) :
    target ∈ exposedTargets machine q Z ↔
      DPDAToFirstOrder.Machine.epsilonStep? machine q Z = none ∧
        target < machine.numStates ∧
        RawHeadReturns machine q Z target := by
  unfold exposedTargets
  split <;> rename_i hstable
  · rw [mem_returnTargets_iff]
    exact ⟨fun h => ⟨hstable, h⟩, fun h => h.2⟩
  · simp [hstable]

omit [Fintype Action] in
public theorem exposedTargets_nodup
    (machine : EncodedDPDA Action) (q Z : ℕ) :
    (exposedTargets machine q Z).Nodup := by
  unfold exposedTargets
  split
  · exact returnTargets_nodup machine q Z
  · exact List.nodup_nil

end DPDAObservableReturns

end DCFEquivalence
