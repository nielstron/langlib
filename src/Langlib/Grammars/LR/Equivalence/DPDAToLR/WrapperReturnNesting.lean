module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ReturnIntervalNesting
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulDeterminism

/-!
# Nesting of useful return intervals in the empty-stack wrapper

Useful paths of the normalized final-state-to-empty-stack wrapper are
deterministic even though the raw wrapper has an extra drain edge.  Combining
that useful-path determinism with retained stack frames gives the return
interval nesting theorem needed by the characteristic-grammar spine proof.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem reachesIn_trans_exact
    {P : PDA Q T S} {n m : ℕ} {a b c : PDA.conf P}
    (hab : P.ReachesIn n a b) (hbc : P.ReachesIn m b c) :
    P.ReachesIn (n + m) a c := by
  induction hbc with
  | refl => simpa using hab
  | @step m b middle c hprefix hlast ih =>
      simpa [Nat.add_assoc] using PDA.ReachesIn.step (ih hab) hlast

private theorem transGen_of_reachesIn_pos
    {P : PDA Q T S} {n : ℕ} {a b : PDA.conf P}
    (hn : 0 < n) (h : P.ReachesIn n a b) :
    Relation.TransGen (@PDA.Reaches₁ Q T S _ _ _ P) a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨middle, hfirst, hrest⟩ :=
    PDA.reachesIn_iff_split_first.mpr (by simpa [Nat.add_comm] using h)
  exact Relation.TransGen.head'
    (PDA.reaches₁_iff_reachesIn_one.mpr hfirst)
    (PDA.reaches_of_reachesIn hrest)

private theorem retainedFrameRun_start_shape
    {P : PDA Q T S} {frame : List S} {n : ℕ}
    {c d : PDA.conf P}
    (h : PDA.RetainedFrameRun P frame n c d) :
    ∃ (q : Q) (input : List T) (upper : List S),
      c = ⟨q, input, upper ++ frame⟩ := by
  induction h with
  | refl q input upper => exact ⟨q, input, upper, rfl⟩
  | step run last ih => exact ih

/-- Segment form of the proper-nesting obstruction for the normalized
empty-stack wrapper. -/
public theorem emptyStack_no_properly_nested_productive_retained_returns_of_segments
    (M : DPDA Q T S)
    {a b c : ℕ} {source returnState final : EState M}
    {sourceInput returnInput : List T} {Z : EStack M}
    {outerFrame innerFrame : List (EStack M)}
    (before : PDA.RetainedFrameRun (emptyStackPDA M) outerFrame a
      ⟨source, sourceInput, Z :: outerFrame⟩
      ⟨source, sourceInput, Z :: innerFrame⟩)
    (inner : PDA.RetainedFrameRun (emptyStackPDA M) innerFrame b
      ⟨source, sourceInput, Z :: innerFrame⟩
      ⟨returnState, returnInput, innerFrame⟩)
    (after : PDA.RetainedFrameRun (emptyStackPDA M) outerFrame c
      ⟨returnState, returnInput, innerFrame⟩
      ⟨returnState, returnInput, outerFrame⟩)
    (hproper : 0 < a ∧ 0 < c)
    (huseful : (emptyStackPDA M).Reaches
      ⟨returnState, returnInput, outerFrame⟩ ⟨final, [], []⟩) :
    False := by
  obtain ⟨startState, startInput, added, hstart⟩ :=
    retainedFrameRun_start_shape after
  have hframe := congrArg PDA.conf.stack hstart
  change innerFrame = added ++ outerFrame at hframe
  by_cases hadded : added = []
  · subst added
    have hinnerFrame : innerFrame = outerFrame := by simpa using hframe
    subst innerFrame
    have hcycle := transGen_of_reachesIn_pos hproper.2 after.toReachesIn
    exact emptyStack_no_useful_cycle M hcycle huseful
  · have beforeFramed : PDA.RetainedFrameRun (emptyStackPDA M) outerFrame a
        ⟨source, sourceInput, [Z] ++ outerFrame⟩
        ⟨source, sourceInput, (Z :: added) ++ outerFrame⟩ := by
      simpa [hframe, List.append_assoc] using before
    have beforeStripped := beforeFramed.changeFrame ([] : List (EStack M))
    have hgrowthWithInput : (emptyStackPDA M).ReachesIn a
        ⟨source, sourceInput, [Z]⟩
        ⟨source, sourceInput, [Z] ++ added⟩ := by
      simpa using beforeStripped.toReachesIn
    have hgrowthWithoutInput : (emptyStackPDA M).ReachesIn a
        ⟨source, [], [Z]⟩
        ⟨source, [], [Z] ++ added⟩ := by
      apply (PDA.unconsumed_input_N
        (pda := emptyStackPDA M) sourceInput).mpr
      simpa [PDA.conf.appendInput] using hgrowthWithInput
    have hinnerUseful : (emptyStackPDA M).Reaches
        ⟨source, sourceInput, Z :: innerFrame⟩
        ⟨final, [], []⟩ :=
      (PDA.reaches_of_reachesIn inner.toReachesIn).trans
        ((PDA.reaches_of_reachesIn after.toReachesIn).trans huseful)
    apply emptyStack_no_useful_stack_growth M
      (q := source) (base := [Z]) (extra := added)
      (context := outerFrame) (input := sourceInput) (final := final)
    · exact PDA.reaches_of_reachesIn hgrowthWithoutInput
    · exact hadded
    · simpa [hframe, List.append_assoc] using hinnerUseful

/-- Rooted/count-indexed proper-nesting obstruction for `emptyStackPDA`.
Both return endpoints are assumed useful so that useful-path determinism can
identify the two boundaries of the nested interval inside the outer one. -/
public theorem emptyStack_no_properly_nested_productive_retained_returns
    (M : DPDA Q T S)
    {w : List T} {n a b c : ℕ}
    {source returnState outerFinal innerFinal : EState M}
    {sourceInput returnInput : List T} {Z : EStack M}
    {outerFrame innerFrame : List (EStack M)}
    (houterPrefix : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, sourceInput, Z :: outerFrame⟩)
    (houter : PDA.RetainedFrameRun (emptyStackPDA M) outerFrame (a + b + c)
      ⟨source, sourceInput, Z :: outerFrame⟩
      ⟨returnState, returnInput, outerFrame⟩)
    (hinnerPrefix : (emptyStackPDA M).ReachesIn (n + a)
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, sourceInput, Z :: innerFrame⟩)
    (hinner : PDA.RetainedFrameRun (emptyStackPDA M) innerFrame b
      ⟨source, sourceInput, Z :: innerFrame⟩
      ⟨returnState, returnInput, innerFrame⟩)
    (ha : 0 < a) (hc : 0 < c)
    (houterUseful : (emptyStackPDA M).Reaches
      ⟨returnState, returnInput, outerFrame⟩ ⟨outerFinal, [], []⟩)
    (hinnerUseful : (emptyStackPDA M).Reaches
      ⟨returnState, returnInput, innerFrame⟩ ⟨innerFinal, [], []⟩) :
    False := by
  have houter' : PDA.RetainedFrameRun (emptyStackPDA M) outerFrame
      (a + (b + c))
      ⟨source, sourceInput, Z :: outerFrame⟩
      ⟨returnState, returnInput, outerFrame⟩ := by
    simpa [Nat.add_assoc] using houter
  obtain ⟨stateA, inputA, upperA, before, rest⟩ := houter'.split_add
  obtain ⟨stateB, inputB, upperB, middle, after⟩ := rest.split_add
  have hglobalA : (emptyStackPDA M).ReachesIn (n + a)
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨stateA, inputA, upperA ++ outerFrame⟩ :=
    reachesIn_trans_exact houterPrefix before.toReachesIn
  have houterAtAUseful : (emptyStackPDA M).Reaches
      ⟨stateA, inputA, upperA ++ outerFrame⟩ ⟨outerFinal, [], []⟩ :=
    (PDA.reaches_of_reachesIn rest.toReachesIn).trans houterUseful
  have hinnerStartUseful : (emptyStackPDA M).Reaches
      ⟨source, sourceInput, Z :: innerFrame⟩ ⟨innerFinal, [], []⟩ :=
    (PDA.reaches_of_reachesIn hinner.toReachesIn).trans hinnerUseful
  have hatInnerStart :
      (⟨stateA, inputA, upperA ++ outerFrame⟩ :
          PDA.conf (emptyStackPDA M)) =
        ⟨source, sourceInput, Z :: innerFrame⟩ :=
    emptyStack_globally_useful_reachesIn_deterministic M
      hglobalA hinnerPrefix houterAtAUseful hinnerStartUseful
  have hglobalB : (emptyStackPDA M).ReachesIn (n + a + b)
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨stateB, inputB, upperB ++ outerFrame⟩ :=
    reachesIn_trans_exact hglobalA middle.toReachesIn
  have hinnerGlobal : (emptyStackPDA M).ReachesIn (n + a + b)
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨returnState, returnInput, innerFrame⟩ :=
    reachesIn_trans_exact hinnerPrefix hinner.toReachesIn
  have houterAtBUseful : (emptyStackPDA M).Reaches
      ⟨stateB, inputB, upperB ++ outerFrame⟩ ⟨outerFinal, [], []⟩ :=
    (PDA.reaches_of_reachesIn after.toReachesIn).trans houterUseful
  have hatInnerReturn :
      (⟨stateB, inputB, upperB ++ outerFrame⟩ :
          PDA.conf (emptyStackPDA M)) =
        ⟨returnState, returnInput, innerFrame⟩ :=
    emptyStack_globally_useful_reachesIn_deterministic M
      hglobalB hinnerGlobal houterAtBUseful hinnerUseful
  rw [hatInnerStart] at before
  rw [hatInnerReturn] at after
  exact emptyStack_no_properly_nested_productive_retained_returns_of_segments
    M before hinner after ⟨ha, hc⟩ houterUseful

/-- Two useful one-symbol return intervals on a globally rooted computation
of `emptyStackPDA` cannot strictly cross.

The first interval occupies `[n, n + a + b]`; the second occupies
`[n + a, n + a + b + c]`.  Positive `b` and `c` express a strict overlap and
a strict overhang. -/
public theorem emptyStack_no_strictly_crossing_retained_returns
    (M : DPDA Q T S)
    {w : List T} {n a b c : ℕ}
    {q₁ q₂ returnState final₁ final₂ : EState M}
    {input₁ input₂ returnInput : List T}
    {Z₁ Z₂ : EStack M} {frame₁ frame₂ : List (EStack M)}
    (hprefix₁ : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, input₁, Z₁ :: frame₁⟩)
    (hreturn₁ : PDA.RetainedFrameRun (emptyStackPDA M) frame₁ (a + b)
      ⟨q₁, input₁, Z₁ :: frame₁⟩
      ⟨returnState, returnInput, frame₁⟩)
    (hprefix₂ : (emptyStackPDA M).ReachesIn (n + a)
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, input₂, Z₂ :: frame₂⟩)
    (hreturn₂ : PDA.RetainedFrameRun (emptyStackPDA M) frame₂ (b + c)
      ⟨q₂, input₂, Z₂ :: frame₂⟩
      ⟨returnState, returnInput, frame₂⟩)
    (hb : 0 < b) (hc : 0 < c)
    (huseful₁ : (emptyStackPDA M).Reaches
      ⟨returnState, returnInput, frame₁⟩ ⟨final₁, [], []⟩)
    (huseful₂ : (emptyStackPDA M).Reaches
      ⟨returnState, returnInput, frame₂⟩ ⟨final₂, [], []⟩) :
    False := by
  obtain ⟨insideState₁, insideInput₁, upper₁,
      hbefore₁, hafter₁⟩ := hreturn₁.split_add
  have hatSecondStart :
      (⟨insideState₁, insideInput₁, upper₁ ++ frame₁⟩ :
          PDA.conf (emptyStackPDA M)) =
        ⟨q₂, input₂, Z₂ :: frame₂⟩ := by
    have hleft := reachesIn_trans_exact hprefix₁ hbefore₁.toReachesIn
    have hleftUseful : (emptyStackPDA M).Reaches
        ⟨insideState₁, insideInput₁, upper₁ ++ frame₁⟩
        ⟨final₁, [], []⟩ :=
      (PDA.reaches_of_reachesIn hafter₁.toReachesIn).trans huseful₁
    have hrightUseful : (emptyStackPDA M).Reaches
        ⟨q₂, input₂, Z₂ :: frame₂⟩ ⟨final₂, [], []⟩ :=
      (PDA.reaches_of_reachesIn hreturn₂.toReachesIn).trans huseful₂
    exact emptyStack_globally_useful_reachesIn_deterministic M
      hleft hprefix₂ hleftUseful hrightUseful
  have hupper₁ : upper₁ ≠ [] := by
    intro hempty
    subst upper₁
    have hzero := DPDA.retainedFrameRun_eq_zero_of_start_at_frame hafter₁
    omega
  obtain ⟨insideState₂, insideInput₂, upper₂,
      hbefore₂, hafter₂⟩ := hreturn₂.split_add
  have hatFirstReturn :
      (⟨insideState₂, insideInput₂, upper₂ ++ frame₂⟩ :
          PDA.conf (emptyStackPDA M)) =
        ⟨returnState, returnInput, frame₁⟩ := by
    have hleft : (emptyStackPDA M).ReachesIn (n + a + b)
        ⟨(emptyStackPDA M).initial_state, w,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨insideState₂, insideInput₂, upper₂ ++ frame₂⟩ :=
      reachesIn_trans_exact hprefix₂ hbefore₂.toReachesIn
    have hright : (emptyStackPDA M).ReachesIn (n + (a + b))
        ⟨(emptyStackPDA M).initial_state, w,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨returnState, returnInput, frame₁⟩ :=
      reachesIn_trans_exact hprefix₁ hreturn₁.toReachesIn
    have hleftUseful : (emptyStackPDA M).Reaches
        ⟨insideState₂, insideInput₂, upper₂ ++ frame₂⟩
        ⟨final₂, [], []⟩ :=
      (PDA.reaches_of_reachesIn hafter₂.toReachesIn).trans huseful₂
    exact emptyStack_globally_useful_reachesIn_deterministic M
      (by simpa [Nat.add_assoc] using hleft) hright
      hleftUseful huseful₁
  have hstackStart := congrArg PDA.conf.stack hatSecondStart
  have hstackReturn := congrArg PDA.conf.stack hatFirstReturn
  change upper₁ ++ frame₁ = Z₂ :: frame₂ at hstackStart
  change upper₂ ++ frame₂ = frame₁ at hstackReturn
  have hlengthStart := congrArg List.length hstackStart
  have hlengthReturn := congrArg List.length hstackReturn
  simp only [List.length_append, List.length_cons] at hlengthStart hlengthReturn
  have hupper₁Length : upper₁.length = 1 := by
    have hpositive : 0 < upper₁.length :=
      List.length_pos_of_ne_nil hupper₁
    omega
  have hupper₂Length : upper₂.length = 0 := by omega
  have hupper₂ : upper₂ = [] := List.length_eq_zero_iff.mp hupper₂Length
  subst upper₂
  have hframe : frame₂ = frame₁ := by simpa using hstackReturn
  subst frame₂
  have hcycleIn : (emptyStackPDA M).ReachesIn c
      ⟨returnState, returnInput, frame₁⟩
      ⟨returnState, returnInput, frame₁⟩ := by
    have hcycleIn' := hafter₂.toReachesIn
    rw [hatFirstReturn] at hcycleIn'
    exact hcycleIn'
  have hcycle := transGen_of_reachesIn_pos hc hcycleIn
  exact emptyStack_no_useful_cycle M hcycle huseful₂

end

end DPDA_to_LR
