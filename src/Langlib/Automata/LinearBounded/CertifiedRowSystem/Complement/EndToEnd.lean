module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.ProtocolPhaseInversion
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.PathSemanticPreservation
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.PathWitnessRuns
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.CanonicalRuns
import Mathlib.Tactic

@[expose]
public section

/-!
# End-to-end correctness of certified-row complementation

This file combines the finite-graph counting semantics with the executable protocol.
The central theorem is machine independent: for every deterministic certified row
system and every nonempty encoded input, the protocol accepts exactly when the source
system has no accepting run.
-/

open Classical

namespace CertifiedRowSystem.Complement

variable {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

private theorem input_hasPhase
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) :
    HasPhase .input (input.map (inputProtocolCell D.inputCell)) := by
  intro cell hcell
  rw [List.mem_map] at hcell
  obtain ⟨symbol, _, rfl⟩ := hcell
  rfl

private theorem canonicalSelected_succ_of_mem
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    {depth innerIndex : Nat}
    (hinner : innerIndex < Fintype.card A ^ input.length)
    (hmem : (⟨innerIndex, hinner⟩ : RankVertex A input.length) ∈
      protocolReached D input depth) :
    insert ⟨innerIndex, hinner⟩
        (protocolReached D input depth ∩ rankPrefix input.length innerIndex) =
      protocolReached D input depth ∩
        rankPrefix input.length (innerIndex + 1) := by
  rw [rankPrefix_succ hinner]
  ext vertex
  by_cases hcurrent : vertex = ⟨innerIndex, hinner⟩
  · subst vertex
    simp [hmem]
  · simp [hcurrent]

private theorem canonicalSelected_succ_of_not_mem
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    {depth innerIndex : Nat}
    (hinner : innerIndex < Fintype.card A ^ input.length)
    (hmem : (⟨innerIndex, hinner⟩ : RankVertex A input.length) ∉
      protocolReached D input depth) :
    protocolReached D input depth ∩ rankPrefix input.length innerIndex =
      protocolReached D input depth ∩
        rankPrefix input.length (innerIndex + 1) := by
  rw [rankPrefix_succ hinner]
  ext vertex
  by_cases hcurrent : vertex = ⟨innerIndex, hinner⟩
  · subst vertex
    simp [hmem]
  · simp [hcurrent]

@[simp]
private theorem canonicalSelected_capacity
    (D : CertifiedRowSystem I A Unit Q F) (input : List I) (depth : Nat) :
    protocolReached D input depth ∩
        rankPrefix input.length (Fintype.card A ^ input.length) =
      protocolReached D input depth := by
  simp

private theorem not_rankFinal_of_sourceRejects_of_mem
    (D : CertifiedRowSystem I A Unit Q F) (input : List I)
    (hrejects : SourceRejects D input) {depth : Nat}
    {vertex : RankVertex A input.length}
    (hmem : vertex ∈ protocolReached D input depth) :
    ¬ rankFinal D input.length vertex := by
  intro hfinal
  apply (sourceRejects_iff_ranked D input).1 hrejects
  refine ⟨vertex, ?_, hfinal⟩
  letI : DecidableRel (rankEdge D input.length) := Classical.decRel _
  exact FiniteReachabilityCounting.reached_sound
    (rankEdge D input.length) (protocolSourceRank D input) hmem

/-! ## Soundness -/

/-- Every semantic protocol step preserves the appropriate exact counting invariant. -/
public theorem protocolInvariant_step
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    {old new : ProtocolRow A} (hinput : input ≠ [])
    (hinv : ProtocolInvariant D input old) (hstep : ProtocolStep D old new) :
    ProtocolInvariant D input new := by
  cases hinv with
  | input =>
      have hboot : IsBoot
          (input.map (inputProtocolCell D.inputCell)) new := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D (input_hasPhase D input) hstep)
      have hnew :=
        (isBoot_input_iff_eq_initialized D.inputCell hinput new).1 hboot
      subst new
      exact .roundStart (initialized_roundStartInvariant D hinput)
  | roundStart hinv =>
      have haction : BeginRoundSpec old new := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D hinv.phase hstep)
      exact .chooseInner (beginRound_preserves hinv haction)
  | chooseInner hinv =>
      have haction :
          SkipInnerSpec old new ∨ StartsPath .chooseInner .path old new := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D hinv.phase hstep)
      rcases haction with hskip | hstart
      · rcases skipInner_preserves hinv hskip with ⟨_, hchoose⟩ | ⟨_, hfinish⟩
        · exact .chooseInner hchoose
        · exact .finishOuter hfinish
      · exact .countingPath (startsPath_preserves hinv hstart)
  | countingPath hinv =>
      have haction : IsPathStep D .path old new ∨ IsFinishWitness D old new := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D hinv.phase hstep)
      rcases haction with hpath | hfinish
      · obtain ⟨_, hnext⟩ := pathStep_preserves hinv hpath
        exact .countingPath hnext
      · rcases finishWitness_preserves hinput hinv hfinish with
          ⟨_, hchoose⟩ | ⟨_, houter⟩
        · exact .chooseInner hchoose
        · exact .finishOuter houter
  | finishOuter hinv =>
      have haction : FinishOuterSpec old new := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D hinv.phase hstep)
      rcases finishOuter_preserves hinput hinv haction with
        ⟨_, hchoose⟩ | ⟨_, hfinish⟩
      · exact .chooseInner hchoose
      · exact .finishRound hfinish
  | finishRound hinv =>
      have haction : FinishRoundSpec old new := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D hinv.phase hstep)
      rcases finishRound_preserves hinput hinv haction with hfinal | hround
      · exact .finalChoose hfinal
      · exact .roundStart hround
  | finalChoose hinv =>
      have haction :
          FinalSkipSpec old new ∨ StartsPath .finalChoose .finalPath old new := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D hinv.phase hstep)
      rcases haction with hskip | hstart
      · rcases finalSkip_preserves hinv hskip with ⟨_, hchoose⟩ | ⟨_, hfinish⟩
        · exact .finalChoose hchoose
        · exact .finalFinish hfinish
      · exact .finalPath (finalStartsPath_preserves hinv hstart)
  | finalPath hinv =>
      have haction :
          IsPathStep D .finalPath old new ∨ IsFinalWitness D old new := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D hinv.phase hstep)
      rcases haction with hpath | hfinish
      · obtain ⟨_, hnext⟩ := finalPathStep_preserves hinv hpath
        exact .finalPath hnext
      · rcases finalWitness_preserves hinput hinv hfinish with
          ⟨_, hchoose⟩ | ⟨_, hfinal⟩
        · exact .finalChoose hchoose
        · exact .finalFinish hfinal
  | finalFinish hinv =>
      have haction : FinalFinishSpec old new := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D hinv.phase hstep)
      rcases finalFinish_rejects hinput hinv haction with
        ⟨hrejects, haccept, hlength⟩
      exact .accept hrejects haccept hlength
  | accept hrejects haccept hlength =>
      have hfalse : False := by
        simpa [ActionsAtPhase] using
          (protocolStep_action_of_phase D haccept hstep)
      exact hfalse.elim

/-- The semantic protocol cannot falsely accept a source input. -/
public theorem protocolAccepts_sound
    (D : CertifiedRowSystem I A Unit Q F) {input : List I} (hinput : input ≠ []) :
    ProtocolAccepts D input → SourceRejects D input := by
  rintro ⟨row, hreach, haccept⟩
  have hinvariant : ∀ {target},
      Relation.ReflTransGen (ProtocolStep D)
          (input.map (inputProtocolCell D.inputCell)) target →
        ProtocolInvariant D input target := by
    intro target htarget
    induction htarget with
    | refl => exact .input
    | tail _hreach hstep ih =>
        exact protocolInvariant_step hinput ih hstep
  have hinv : ProtocolInvariant D input row := hinvariant hreach
  have hrow : row ≠ [] := row_ne_nil_of_length_eq hinv.length_eq hinput
  exact hinv.rejects_of_accept haccept hrow

/-! ## Completeness -/

/-- Canonically scan all possible predecessor rows for one fixed outer row. -/
private theorem completeInnerScan
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    (hinput : input ≠ []) {old : ProtocolRow A}
    {depth oldCount newCount outerIndex innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinv : ChooseInnerInvariant D input old depth oldCount newCount outerIndex
      innerIndex selected)
    (hselected : selected = protocolReached D input depth ∩
      rankPrefix input.length innerIndex) :
    ∃ new, Relation.ReflTransGen (ProtocolStep D) old new ∧
      FinishOuterInvariant D input new depth oldCount newCount outerIndex
        (protocolReached D input depth) := by
  let N := Fintype.card A ^ input.length
  let reached := protocolReached D input depth
  have go : ∀ measure, ∀ {old : ProtocolRow A} {innerIndex : Nat}
      {selected : Finset (RankVertex A input.length)},
      N - innerIndex = measure →
      ChooseInnerInvariant D input old depth oldCount newCount outerIndex
        innerIndex selected →
      selected = reached ∩ rankPrefix input.length innerIndex →
      ∃ new, Relation.ReflTransGen (ProtocolStep D) old new ∧
        FinishOuterInvariant D input new depth oldCount newCount outerIndex reached := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure ih =>
      intro old innerIndex selected hmeasure hinv hselected
      let current : RankVertex A input.length := ⟨innerIndex, hinv.inner_lt⟩
      by_cases hmem : current ∈ reached
      · obtain ⟨next, hrun, hnext⟩ := reachableWitness_run hinput hinv hmem
        have hselectedNext :
            insert current selected =
              reached ∩ rankPrefix input.length (innerIndex + 1) := by
          rw [hselected]
          exact canonicalSelected_succ_of_mem D input hinv.inner_lt hmem
        rcases hnext with ⟨hlt, hchoose⟩ | ⟨heq, hfinish⟩
        · have hmeasureLt : N - (innerIndex + 1) < measure := by
            dsimp only [N] at hmeasure ⊢
            omega
          obtain ⟨endRow, hrest, hend⟩ :=
            ih (N - (innerIndex + 1)) hmeasureLt rfl hchoose hselectedNext
          exact ⟨endRow, hrun.trans hrest, hend⟩
        · have hfull : insert current selected = reached := by
            calc
              insert current selected =
                  reached ∩ rankPrefix input.length (innerIndex + 1) :=
                hselectedNext
              _ = reached := by
                rw [heq]
                exact canonicalSelected_capacity D input depth
          refine ⟨next, hrun, ?_⟩
          change FinishOuterInvariant D input next depth oldCount newCount
            outerIndex (insert current selected) at hfinish
          rw [hfull] at hfinish
          exact hfinish
      · obtain ⟨next, hstep, hnext⟩ := exists_skipInner_step hinput hinv
        have hselectedNext :
            selected = reached ∩ rankPrefix input.length (innerIndex + 1) := by
          rw [hselected]
          exact canonicalSelected_succ_of_not_mem D input hinv.inner_lt hmem
        rcases hnext with ⟨hlt, hchoose⟩ | ⟨heq, hfinish⟩
        · have hmeasureLt : N - (innerIndex + 1) < measure := by
            dsimp only [N] at hmeasure ⊢
            omega
          obtain ⟨endRow, hrest, hend⟩ :=
            ih (N - (innerIndex + 1)) hmeasureLt rfl hchoose hselectedNext
          exact ⟨endRow,
            (Relation.ReflTransGen.single hstep).trans hrest, hend⟩
        · have hfull : selected = reached := by
            calc
              selected = reached ∩
                  rankPrefix input.length (innerIndex + 1) := hselectedNext
              _ = reached := by
                rw [heq]
                exact canonicalSelected_capacity D input depth
          refine ⟨next, Relation.ReflTransGen.single hstep, ?_⟩
          simpa only [reached, hfull] using hfinish
  exact go (N - innerIndex) rfl hinv hselected

/-- Canonically classify every possible outer row in one counting round. -/
private theorem completeOuterScan
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    (hinput : input ≠ []) {old : ProtocolRow A}
    {depth oldCount newCount outerIndex : Nat}
    (hinv : ChooseInnerInvariant D input old depth oldCount newCount outerIndex
      0 ∅) :
    ∃ new, Relation.ReflTransGen (ProtocolStep D) old new ∧
      FinishRoundInvariant D input new depth oldCount
        (protocolReached D input (depth + 1)).card := by
  let N := Fintype.card A ^ input.length
  have go : ∀ measure, ∀ {old : ProtocolRow A} {newCount outerIndex : Nat},
      N - outerIndex = measure →
      ChooseInnerInvariant D input old depth oldCount newCount outerIndex 0 ∅ →
      ∃ new, Relation.ReflTransGen (ProtocolStep D) old new ∧
        FinishRoundInvariant D input new depth oldCount
          (protocolReached D input (depth + 1)).card := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure ih =>
      intro old newCount outerIndex hmeasure hinv
      obtain ⟨afterInner, hinnerRun, hfinishOuter⟩ :=
        completeInnerScan hinput hinv (by simp)
      obtain ⟨afterOuter, houterStep, hnext⟩ :=
        exists_finishOuter_step hinput hfinishOuter rfl
      have hprefixRun : Relation.ReflTransGen (ProtocolStep D) old afterOuter :=
        hinnerRun.trans (Relation.ReflTransGen.single houterStep)
      rcases hnext with ⟨hlt, hchoose⟩ | ⟨heq, hfinish⟩
      · have hmeasureLt : N - (outerIndex + 1) < measure := by
          dsimp only [N] at hmeasure ⊢
          omega
        obtain ⟨endRow, hrest, hend⟩ :=
          ih (N - (outerIndex + 1)) hmeasureLt rfl hchoose
        exact ⟨endRow, hprefixRun.trans hrest, hend⟩
      · have hcount :
            (classifiedPrefix D input depth (outerIndex + 1)).card =
              (protocolReached D input (depth + 1)).card := by
          rw [heq, classifiedPrefix, rankPrefix_capacity, Finset.inter_univ]
        refine ⟨afterOuter, hprefixRun, ?_⟩
        simpa only [hcount] using hfinish
  exact go (N - outerIndex) rfl hinv

/-- Execute one complete canonical inductive-counting round. -/
private theorem completeCountingRound
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    (hinput : input ≠ []) {old : ProtocolRow A} {depth count : Nat}
    (hinv : RoundStartInvariant D input old depth count) :
    ∃ new, Relation.ReflTransGen (ProtocolStep D) old new ∧
      FinishRoundInvariant D input new depth count
        (protocolReached D input (depth + 1)).card := by
  obtain ⟨choose, hbegin, hchoose⟩ := exists_beginRound_step hinput hinv
  obtain ⟨finish, hrest, hfinish⟩ := completeOuterScan hinput hchoose
  exact ⟨finish, (Relation.ReflTransGen.single hbegin).trans hrest, hfinish⟩

/-- Repeated exact rounds necessarily reach a genuine count plateau. -/
private theorem reachFinalChoose
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    (hinput : input ≠ []) {old : ProtocolRow A} {depth count : Nat}
    (hinv : RoundStartInvariant D input old depth count) :
    ∃ new depth' count',
      Relation.ReflTransGen (ProtocolStep D) old new ∧
        FinalChooseInvariant D input new depth' count' 0 ∅ := by
  let N := Fintype.card A ^ input.length
  have go : ∀ measure, ∀ {old : ProtocolRow A} {depth count : Nat},
      N - depth = measure →
      RoundStartInvariant D input old depth count →
      ∃ new depth' count',
        Relation.ReflTransGen (ProtocolStep D) old new ∧
          FinalChooseInvariant D input new depth' count' 0 ∅ := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure ih =>
      intro old depth count hmeasure hinv
      obtain ⟨finish, hroundRun, hfinish⟩ :=
        completeCountingRound hinput hinv
      obtain ⟨next, hfinishStep, hnext⟩ :=
        exists_finishRound_step hinput hfinish
      have hprefixRun : Relation.ReflTransGen (ProtocolStep D) old next :=
        hroundRun.trans (Relation.ReflTransGen.single hfinishStep)
      rcases hnext with hfinal | hround
      · exact ⟨next, depth, count, hprefixRun, hfinal⟩
      · have hmeasureLt : N - (depth + 1) < measure := by
          have hdepthLt := hinv.depth_lt
          dsimp only [N] at hmeasure ⊢
          omega
        obtain ⟨endRow, endDepth, endCount, hrest, hend⟩ :=
          ih (N - (depth + 1)) hmeasureLt rfl hround
        exact ⟨endRow, endDepth, endCount, hprefixRun.trans hrest, hend⟩
  exact go (N - depth) rfl hinv

/-- Exhaustively enumerate the plateau layer and certify that each reachable row is
nonfinal. -/
private theorem completeFinalScan
    {D : CertifiedRowSystem I A Unit Q F} {input : List I}
    (hinput : input ≠ []) (hrejects : SourceRejects D input)
    {old : ProtocolRow A} {depth count innerIndex : Nat}
    {selected : Finset (RankVertex A input.length)}
    (hinv : FinalChooseInvariant D input old depth count innerIndex selected)
    (hselected : selected = protocolReached D input depth ∩
      rankPrefix input.length innerIndex) :
    ∃ new, Relation.ReflTransGen (ProtocolStep D) old new ∧
      HasPhase .accept new := by
  let N := Fintype.card A ^ input.length
  let reached := protocolReached D input depth
  have go : ∀ measure, ∀ {old : ProtocolRow A} {innerIndex : Nat}
      {selected : Finset (RankVertex A input.length)},
      N - innerIndex = measure →
      FinalChooseInvariant D input old depth count innerIndex selected →
      selected = reached ∩ rankPrefix input.length innerIndex →
      ∃ new, Relation.ReflTransGen (ProtocolStep D) old new ∧
        HasPhase .accept new := by
    intro measure
    induction measure using Nat.strong_induction_on with
    | h measure ih =>
      intro old innerIndex selected hmeasure hinv hselected
      let current : RankVertex A input.length := ⟨innerIndex, hinv.inner_lt⟩
      by_cases hmem : current ∈ reached
      · have hnonfinal : ¬ rankFinal D input.length current :=
          not_rankFinal_of_sourceRejects_of_mem D input hrejects hmem
        obtain ⟨next, hrun, hnext⟩ :=
          finalReachableWitness_run hinput hinv hmem hnonfinal
        have hselectedNext :
            insert current selected =
              reached ∩ rankPrefix input.length (innerIndex + 1) := by
          rw [hselected]
          exact canonicalSelected_succ_of_mem D input hinv.inner_lt hmem
        rcases hnext with ⟨hlt, hchoose⟩ | ⟨heq, hfinish⟩
        · have hmeasureLt : N - (innerIndex + 1) < measure := by
            dsimp only [N] at hmeasure ⊢
            omega
          obtain ⟨endRow, hrest, hend⟩ :=
            ih (N - (innerIndex + 1)) hmeasureLt rfl hchoose hselectedNext
          exact ⟨endRow, hrun.trans hrest, hend⟩
        · have hfull : insert current selected = reached := by
            calc
              insert current selected =
                  reached ∩ rankPrefix input.length (innerIndex + 1) :=
                hselectedNext
              _ = reached := by
                rw [heq]
                exact canonicalSelected_capacity D input depth
          obtain ⟨accept, hacceptStep, haccept⟩ :=
            exists_finalFinish_step hinput hfinish hfull
          exact ⟨accept, hrun.trans (Relation.ReflTransGen.single hacceptStep),
            haccept⟩
      · obtain ⟨next, hstep, _hfound, hnext⟩ :=
          exists_finalSkip_step hinput hinv
        have hselectedNext :
            selected = reached ∩ rankPrefix input.length (innerIndex + 1) := by
          rw [hselected]
          exact canonicalSelected_succ_of_not_mem D input hinv.inner_lt hmem
        rcases hnext with ⟨hlt, hchoose⟩ | ⟨heq, hfinish⟩
        · have hmeasureLt : N - (innerIndex + 1) < measure := by
            dsimp only [N] at hmeasure ⊢
            omega
          obtain ⟨endRow, hrest, hend⟩ :=
            ih (N - (innerIndex + 1)) hmeasureLt rfl hchoose hselectedNext
          exact ⟨endRow,
            (Relation.ReflTransGen.single hstep).trans hrest, hend⟩
        · have hfull : selected = reached := by
            calc
              selected = reached ∩
                  rankPrefix input.length (innerIndex + 1) := hselectedNext
              _ = reached := by
                rw [heq]
                exact canonicalSelected_capacity D input depth
          obtain ⟨accept, hacceptStep, haccept⟩ :=
            exists_finalFinish_step hinput hfinish hfull
          exact ⟨accept,
            (Relation.ReflTransGen.single hstep).trans
              (Relation.ReflTransGen.single hacceptStep), haccept⟩
  exact go (N - innerIndex) rfl hinv hselected

/-- If the source rejects, the canonical inductive-counting choices form an accepting
protocol run. -/
public theorem protocolAccepts_complete
    (D : CertifiedRowSystem I A Unit Q F) {input : List I} (hinput : input ≠ []) :
    SourceRejects D input → ProtocolAccepts D input := by
  intro hrejects
  let initial := input.map (inputProtocolCell D.inputCell)
  let initialized := initializedProtocolRow (input.map D.inputCell)
  have hboot : IsBoot initial initialized := by
    simpa only [initial, initialized] using
      (isBoot_input_initialized D.inputCell hinput)
  have hinitial : initial ≠ [] := by
    intro hnil
    apply hinput
    have hlength := congrArg List.length hnil
    simpa only [initial, List.length_map, List.length_nil,
      List.length_eq_zero_iff] using hlength
  have hbootStep : ProtocolStep D initial initialized :=
    ⟨hinitial, Or.inl hboot⟩
  have hinitialized : RoundStartInvariant D input initialized 0 1 := by
    simpa only [initialized] using initialized_roundStartInvariant D hinput
  obtain ⟨finalChoose, depth, count, hcounting, hfinalChoose⟩ :=
    reachFinalChoose hinput hinitialized
  obtain ⟨accept, hfinalScan, haccept⟩ :=
    completeFinalScan hinput hrejects hfinalChoose (by simp)
  refine ⟨accept, ?_, haccept⟩
  simpa only [initial] using
    (Relation.ReflTransGen.single hbootStep).trans (hcounting.trans hfinalScan)

/-- The machine-independent certified-row complement protocol accepts exactly the
inputs rejected by its deterministic source system. -/
public theorem protocolAccepts_iff_sourceRejects
    (D : CertifiedRowSystem I A Unit Q F) {input : List I} (hinput : input ≠ []) :
    ProtocolAccepts D input ↔ SourceRejects D input :=
  ⟨protocolAccepts_sound D hinput, protocolAccepts_complete D hinput⟩

/-! ## Language correctness -/

/-- The compiled deterministic-source system recognizes the complement of the source
row language, relative to nonempty inputs. -/
public theorem rowReachLanguage_deterministicComplementSystem
    [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) :
    (deterministicComplementSystem D).rowReachLanguage =
      D.rowReachLanguageᶜ \ ({[]} : Set (List I)) := by
  ext input
  change input ∈ (deterministicComplementSystem D).rowReachLanguage ↔
    input ∈ D.rowReachLanguageᶜ \ ({[]} : Set (List I))
  rw [mem_deterministicComplementSystem_iff_protocolAccepts]
  change (input ≠ [] ∧ ProtocolAccepts D input) ↔
    input ∉ D.rowReachLanguage ∧ input ≠ []
  constructor
  · rintro ⟨hinput, haccepts⟩
    have hrejects := (protocolAccepts_iff_sourceRejects D hinput).1 haccepts
    exact ⟨(sourceRejects_iff_not_mem D hinput).1 hrejects, hinput⟩
  · rintro ⟨hnotMem, hinput⟩
    have hrejects := (sourceRejects_iff_not_mem D hinput).2 hnotMem
    exact ⟨hinput, (protocolAccepts_iff_sourceRejects D hinput).2 hrejects⟩

end CertifiedRowSystem.Complement

namespace CertifiedRowSystem

/-- Machine-independent complementation for an arbitrary finite certified row system.
The certificate alphabet is determinized before the counting protocol is installed. -/
public theorem rowReachLanguage_complementSystem
    {I A C Q F : Type*}
    [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype C] [Fintype Q] [DecidableEq Q] [Fintype F]
    (S : CertifiedRowSystem I A C Q F) :
    (Complement.complementSystem S).rowReachLanguage =
      S.rowReachLanguageᶜ \ ({[]} : Set (List I)) := by
  change (Complement.deterministicComplementSystem S.determinize).rowReachLanguage = _
  rw [Complement.rowReachLanguage_deterministicComplementSystem,
    S.rowReachLanguage_determinize]

end CertifiedRowSystem
