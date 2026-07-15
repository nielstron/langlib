module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CountedSpine
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CrossInputDeterminism
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulDeterminism

/-!
# Prefix uniqueness of productive single completions

Two retained returns from the same globally reached stack cut cannot complete
the same characteristic `single` on strictly prefix-related words.  Lifting
the shorter return under the unmatched suffix puts both runs at one common
source.  At the shorter endpoint the retained frame is already exposed, so
the longer retained run has no legal step left.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Productive retained returns from one globally reached cut have
prefix-incomparable consumed words.  The stated prefix is therefore equal. -/
public theorem productiveRetainedReturn_prefix_eq
    (M : DPDA Q T S)
    {beforeWord word extra tail : List T}
    {prefixSteps shortSteps longSteps : ℕ}
    {source returnState shortFinal longFinal : EState M}
    {top : EStack M} {frame : List (EStack M)}
    (global : (emptyStackPDA M).ReachesIn prefixSteps
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (word ++ (extra ++ tail)),
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, word ++ (extra ++ tail), top :: frame⟩)
    (short : PDA.RetainedFrameRun (emptyStackPDA M) frame shortSteps
      ⟨source, word, top :: frame⟩
      ⟨returnState, [], frame⟩)
    (long : PDA.RetainedFrameRun (emptyStackPDA M) frame longSteps
      ⟨source, word ++ extra, top :: frame⟩
      ⟨returnState, [], frame⟩)
    (shortUseful : (emptyStackPDA M).Reaches
      ⟨returnState, extra ++ tail, frame⟩
      ⟨shortFinal, [], []⟩)
    (longUseful : (emptyStackPDA M).Reaches
      ⟨returnState, tail, frame⟩
      ⟨longFinal, [], []⟩) :
    extra = [] := by
  have shortLift := short.appendInput (extra ++ tail)
  have longLift := long.appendInput tail
  simp only [PDA.conf.appendInput, List.nil_append,
    List.append_assoc] at shortLift longLift
  have shortGlobal : (emptyStackPDA M).ReachesIn
      (prefixSteps + shortSteps)
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (word ++ (extra ++ tail)),
        [(emptyStackPDA M).start_symbol]⟩
      ⟨returnState, extra ++ tail, frame⟩ := by
    simpa [PDA.conf.appendInput, List.append_assoc] using
      prefixRunIn_trans_retainedFrameRun global shortLift
  have longGlobal : (emptyStackPDA M).ReachesIn
      (prefixSteps + longSteps)
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (word ++ (extra ++ tail)),
        [(emptyStackPDA M).start_symbol]⟩
      ⟨returnState, tail, frame⟩ := by
    simpa [PDA.conf.appendInput, List.append_assoc] using
      prefixRunIn_trans_retainedFrameRun global longLift
  rcases Nat.le_total shortSteps longSteps with hle | hle
  · obtain ⟨remainingSteps, hsteps⟩ := Nat.exists_eq_add_of_le hle
    subst longSteps
    obtain ⟨middleState, middleInput, upper,
        before, after⟩ := longLift.split_add
    have middleGlobal : (emptyStackPDA M).ReachesIn
        (prefixSteps + shortSteps)
        ⟨(emptyStackPDA M).initial_state,
          beforeWord ++ (word ++ (extra ++ tail)),
          [(emptyStackPDA M).start_symbol]⟩
        ⟨middleState, middleInput, upper ++ frame⟩ := by
      exact prefixRunIn_trans_retainedFrameRun global before
    have middleUseful : (emptyStackPDA M).Reaches
        ⟨middleState, middleInput, upper ++ frame⟩
        ⟨longFinal, [], []⟩ :=
      (PDA.reaches_of_reachesIn after.toReachesIn).trans longUseful
    have hmiddle :
        (⟨returnState, extra ++ tail, frame⟩ :
          PDA.conf (emptyStackPDA M)) =
        ⟨middleState, middleInput, upper ++ frame⟩ :=
      emptyStack_globally_useful_reachesIn_deterministic M
        shortGlobal middleGlobal shortUseful middleUseful
    rw [← hmiddle] at after
    have hremaining : remainingSteps = 0 :=
      after.eq_zero_of_start_at_frame
    subst remainingSteps
    have hend := PDA.reachesIn_zero after.toReachesIn
    have hinput := congrArg PDA.conf.input hend
    have hlength := congrArg List.length hinput
    simp only [List.length_append] at hlength
    exact List.length_eq_zero_iff.mp (by omega)
  · obtain ⟨remainingSteps, hsteps⟩ := Nat.exists_eq_add_of_le hle
    subst shortSteps
    obtain ⟨middleState, middleInput, upper,
        before, after⟩ := shortLift.split_add
    have middleGlobal : (emptyStackPDA M).ReachesIn
        (prefixSteps + longSteps)
        ⟨(emptyStackPDA M).initial_state,
          beforeWord ++ (word ++ (extra ++ tail)),
          [(emptyStackPDA M).start_symbol]⟩
        ⟨middleState, middleInput, upper ++ frame⟩ := by
      exact prefixRunIn_trans_retainedFrameRun global before
    have middleUseful : (emptyStackPDA M).Reaches
        ⟨middleState, middleInput, upper ++ frame⟩
        ⟨shortFinal, [], []⟩ :=
      (PDA.reaches_of_reachesIn after.toReachesIn).trans shortUseful
    have hmiddle :
        (⟨returnState, tail, frame⟩ :
          PDA.conf (emptyStackPDA M)) =
        ⟨middleState, middleInput, upper ++ frame⟩ :=
      emptyStack_globally_useful_reachesIn_deterministic M
        longGlobal middleGlobal longUseful middleUseful
    rw [← hmiddle] at after
    have hremaining : remainingSteps = 0 :=
      after.eq_zero_of_start_at_frame
    subst remainingSteps
    have hend := PDA.reachesIn_zero after.toReachesIn
    have hinput := congrArg PDA.conf.input hend
    have hlength := congrArg List.length hinput
    simp only [List.length_append] at hlength
    exact List.length_eq_zero_iff.mp (by omega)

/-- Cross-input form of `productiveRetainedReturn_prefix_eq`.  The two
productive continuations may have different tails, provided that their next
visible input symbols agree. -/
public theorem productiveRetainedReturn_prefix_eq_cross_input
    (M : DPDA Q T S)
    {beforeWord word extra tail₁ tail₂ : List T}
    {prefixSteps shortSteps longSteps : ℕ}
    {source returnState shortFinal longFinal : EState M}
    {top : EStack M} {frame : List (EStack M)}
    (global : (emptyStackPDA M).ReachesIn prefixSteps
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (word ++ extra),
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, word ++ extra, top :: frame⟩)
    (short : PDA.RetainedFrameRun (emptyStackPDA M) frame shortSteps
      ⟨source, word, top :: frame⟩
      ⟨returnState, [], frame⟩)
    (long : PDA.RetainedFrameRun (emptyStackPDA M) frame longSteps
      ⟨source, word ++ extra, top :: frame⟩
      ⟨returnState, [], frame⟩)
    (shortUseful : (emptyStackPDA M).Reaches
      ⟨returnState, extra ++ tail₁, frame⟩
      ⟨shortFinal, [], []⟩)
    (longUseful : (emptyStackPDA M).Reaches
      ⟨returnState, tail₂, frame⟩
      ⟨longFinal, [], []⟩)
    (hlook : tail₁.take 1 = tail₂.take 1) :
    extra = [] := by
  by_cases hextra : extra = []
  · exact hextra
  have hlookExtra :
      (extra ++ tail₁).take 1 = (extra ++ tail₂).take 1 := by
    cases extra with
    | nil => exact (hextra rfl).elim
    | cons a rest => simp
  have global₁ := (PDA.unconsumed_input_N
    (pda := emptyStackPDA M) tail₁).mp global
  have global₂ := (PDA.unconsumed_input_N
    (pda := emptyStackPDA M) tail₂).mp global
  have shortLift := short.appendInput (extra ++ tail₁)
  have longLift := long.appendInput tail₂
  simp only [PDA.conf.appendInput, List.nil_append,
    List.append_assoc] at global₁ global₂ shortLift longLift
  have shortGlobal : (emptyStackPDA M).ReachesIn
      (prefixSteps + shortSteps)
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (word ++ (extra ++ tail₁)),
        [(emptyStackPDA M).start_symbol]⟩
      ⟨returnState, extra ++ tail₁, frame⟩ := by
    exact prefixRunIn_trans_retainedFrameRun global₁ shortLift
  have longGlobal : (emptyStackPDA M).ReachesIn
      (prefixSteps + longSteps)
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (word ++ (extra ++ tail₂)),
        [(emptyStackPDA M).start_symbol]⟩
      ⟨returnState, tail₂, frame⟩ := by
    exact prefixRunIn_trans_retainedFrameRun global₂ longLift
  rcases Nat.le_total shortSteps longSteps with hle | hle
  · obtain ⟨remainingSteps, hsteps⟩ := Nat.exists_eq_add_of_le hle
    subst longSteps
    obtain ⟨middleState, middleInput, upper,
        before, after⟩ := longLift.split_add
    have middleGlobal : (emptyStackPDA M).ReachesIn
        (prefixSteps + shortSteps)
        ⟨(emptyStackPDA M).initial_state,
          beforeWord ++ (word ++ (extra ++ tail₂)),
          [(emptyStackPDA M).start_symbol]⟩
        ⟨middleState, middleInput, upper ++ frame⟩ := by
      exact prefixRunIn_trans_retainedFrameRun global₂ before
    have middleUseful : (emptyStackPDA M).Reaches
        ⟨middleState, middleInput, upper ++ frame⟩
        ⟨longFinal, [], []⟩ :=
      (PDA.reaches_of_reachesIn after.toReachesIn).trans longUseful
    have shortGlobal' : (emptyStackPDA M).ReachesIn
        (prefixSteps + shortSteps)
        ⟨(emptyStackPDA M).initial_state,
          (beforeWord ++ word) ++ (extra ++ tail₁),
          [(emptyStackPDA M).start_symbol]⟩
        ⟨returnState, extra ++ tail₁, frame⟩ := by
      simpa only [List.append_assoc] using shortGlobal
    have middleGlobal' : (emptyStackPDA M).ReachesIn
        (prefixSteps + shortSteps)
        ⟨(emptyStackPDA M).initial_state,
          (beforeWord ++ word) ++ (extra ++ tail₂),
          [(emptyStackPDA M).start_symbol]⟩
        ⟨middleState, middleInput, upper ++ frame⟩ := by
      simpa only [List.append_assoc] using middleGlobal
    have hmiddle :
        (⟨returnState, extra ++ tail₂, frame⟩ :
          PDA.conf (emptyStackPDA M)) =
        ⟨middleState, middleInput, upper ++ frame⟩ := by
      exact (emptyStack_globally_useful_reachesIn_cross_input M
        (pre := beforeWord ++ word)
        (tail₁ := extra ++ tail₁) (tail₂ := extra ++ tail₂)
        shortGlobal' middleGlobal' shortUseful middleUseful hlookExtra).symm
    rw [← hmiddle] at after
    have hremaining : remainingSteps = 0 :=
      after.eq_zero_of_start_at_frame
    subst remainingSteps
    have hend := PDA.reachesIn_zero after.toReachesIn
    have hinput := congrArg PDA.conf.input hend
    have hlength := congrArg List.length hinput
    simp only [List.length_append] at hlength
    exact List.length_eq_zero_iff.mp (by omega)
  · obtain ⟨remainingSteps, hsteps⟩ := Nat.exists_eq_add_of_le hle
    subst shortSteps
    obtain ⟨middleState, middleInput, upper,
        before, after⟩ := shortLift.split_add
    have middleGlobal : (emptyStackPDA M).ReachesIn
        (prefixSteps + longSteps)
        ⟨(emptyStackPDA M).initial_state,
          beforeWord ++ (word ++ (extra ++ tail₁)),
          [(emptyStackPDA M).start_symbol]⟩
        ⟨middleState, middleInput, upper ++ frame⟩ := by
      exact prefixRunIn_trans_retainedFrameRun global₁ before
    have middleUseful : (emptyStackPDA M).Reaches
        ⟨middleState, middleInput, upper ++ frame⟩
        ⟨shortFinal, [], []⟩ :=
      (PDA.reaches_of_reachesIn after.toReachesIn).trans shortUseful
    have longGlobal' : (emptyStackPDA M).ReachesIn
        (prefixSteps + longSteps)
        ⟨(emptyStackPDA M).initial_state,
          ((beforeWord ++ word) ++ extra) ++ tail₂,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨returnState, tail₂, frame⟩ := by
      simpa only [List.append_assoc] using longGlobal
    have middleGlobal' : (emptyStackPDA M).ReachesIn
        (prefixSteps + longSteps)
        ⟨(emptyStackPDA M).initial_state,
          ((beforeWord ++ word) ++ extra) ++ tail₁,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨middleState, middleInput, upper ++ frame⟩ := by
      simpa only [List.append_assoc] using middleGlobal
    have hmiddle :
        (⟨returnState, tail₁, frame⟩ :
          PDA.conf (emptyStackPDA M)) =
        ⟨middleState, middleInput, upper ++ frame⟩ := by
      exact (emptyStack_globally_useful_reachesIn_cross_input M
        (pre := beforeWord ++ word ++ extra)
        (tail₁ := tail₂) (tail₂ := tail₁)
        longGlobal' middleGlobal' longUseful middleUseful hlook.symm).symm
    rw [← hmiddle] at after
    have hremaining : remainingSteps = 0 :=
      after.eq_zero_of_start_at_frame
    subst remainingSteps
    have hend := PDA.reachesIn_zero after.toReachesIn
    have hinput := congrArg PDA.conf.input hend
    have hlength := congrArg List.length hinput
    simp only [List.length_append] at hlength
    exact List.length_eq_zero_iff.mp (by omega)
end

end DPDA_to_LR
