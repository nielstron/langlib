module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CrossInputOrder
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CountedSpine
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.LeftmostEpsilonTrace
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SpineSynchronization

/-!
# Synchronizing two epsilon introductions

Two epsilon rules which introduce the same characteristic list child have
the same productive future.  This file isolates the counted synchronization
argument from the remaining structural ancestry argument: equal global
positions force the two source heads to be literally equal, even though the
terminal suffixes following the child may differ.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem take_one_append_eq
    {common left right : List T}
    (h : left.take 1 = right.take 1) :
    (common ++ left).take 1 = (common ++ right).take 1 := by
  cases common with
  | nil => simpa using h
  | cons a rest => simp

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

private theorem transGen_append_input
    {P : PDA Q T S} {c d : PDA.conf P}
    (h : Relation.TransGen (@PDA.Reaches₁ Q T S _ _ _ P) c d)
    (inputSuffix : List T) :
    Relation.TransGen (@PDA.Reaches₁ Q T S _ _ _ P)
      (c.appendInput inputSuffix) (d.appendInput inputSuffix) := by
  obtain ⟨next, hfirst, hrest⟩ := Relation.TransGen.head'_iff.mp h
  have hfirstInput : P.Reaches₁
      (c.appendInput inputSuffix) (next.appendInput inputSuffix) := by
    apply PDA.reaches₁_iff_reachesIn_one.mpr
    exact (PDA.unconsumed_input_N (pda := P) inputSuffix).mp
      (PDA.reaches₁_iff_reachesIn_one.mp hfirst)
  have hrestInput := (PDA.unconsumed_input inputSuffix).mp hrest
  exact Relation.TransGen.head' hfirstInput hrestInput

/-- A leftmost structural trace from a list position to a single position
may move the entire hidden context into the displayed list at its source.
The trace cannot be reflexive, and its first event is necessarily `split`;
after that event both source decompositions reach the identical single
position. -/
public theorem LeftmostEpsilonTrace.expandListContext_toSingle
    (M : DPDA Q T S)
    {q source : State M} {Z : StackSymbol M}
    {displayed context finalContext : List (StackSymbol M)}
    (trace : LeftmostEpsilonTrace M (.list q displayed context)
      (.single source Z finalContext)) :
    LeftmostEpsilonTrace M (.list q (displayed ++ context) [])
      (.single source Z finalContext) := by
  cases trace with
  | @head _ middle _ first rest =>
      cases first with
      | @split q' Z' gamma' context' =>
          have expandedFirst : LeftmostEpsilonStep M
              (.list q (Z' :: (gamma' ++ context)) [])
              (.single q Z' ((gamma' ++ context) ++ [])) :=
            LeftmostEpsilonStep.split
          have rest' : LeftmostEpsilonTrace M
              (.single q Z' ((gamma' ++ context) ++ []))
              (.single source Z finalContext) := by
            simpa using rest
          simpa [List.append_assoc] using
            (LeftmostEpsilonTrace.head expandedFirst rest')

/-- Converging epsilon exits also synchronize when their two structural
traces start from different displayed/hidden decompositions of the same
physical list cut.  Expanding both source contexts into their displayed
lists gives a literal common `LeftmostEpsilonPosition`, after which the
general converging-trace theorem applies. -/
public theorem leftmostEpsilonTrace_converging_heads_eq_of_list_cut_eq
    (M : DPDA Q T S)
    {anchorState₁ anchorState₂ q₁ q₂ next final₁ final₂ : State M}
    {Z₁ Z₂ : StackSymbol M}
    {displayed₁ displayed₂ anchorContext₁ anchorContext₂
      gamma context₁ context₂ : List (StackSymbol M)}
    {suffix₁ suffix₂ whole₁ whole₂ : List T}
    (trace₁ : LeftmostEpsilonTrace M
      (.list anchorState₁ displayed₁ anchorContext₁)
      (.single q₁ Z₁ context₁))
    (trace₂ : LeftmostEpsilonTrace M
      (.list anchorState₂ displayed₂ anchorContext₂)
      (.single q₂ Z₂ context₂))
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (hstate : anchorState₁ = anchorState₂)
    (hstack : displayed₁ ++ anchorContext₁ =
      displayed₂ ++ anchorContext₂)
    (global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₁,
        [(emptyStackPDA M).start_symbol]⟩
      ((.list anchorState₁ displayed₁ anchorContext₁ :
        LeftmostEpsilonPosition M).conf M suffix₁))
    (global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₂,
        [(emptyStackPDA M).start_symbol]⟩
      ((.list anchorState₂ displayed₂ anchorContext₂ :
        LeftmostEpsilonPosition M).conf M suffix₂))
    (useful₁ : (emptyStackPDA M).Reaches
      ((.list next gamma context₁ : LeftmostEpsilonPosition M).conf M
        suffix₁) ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ((.list next gamma context₂ : LeftmostEpsilonPosition M).conf M
        suffix₂) ⟨final₂, [], []⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  let start : LeftmostEpsilonPosition M :=
    .list anchorState₁ (displayed₁ ++ anchorContext₁) []
  have expanded₁ : LeftmostEpsilonTrace M start
      (.single q₁ Z₁ context₁) := by
    simpa [start] using trace₁.expandListContext_toSingle M
  have expanded₂ : LeftmostEpsilonTrace M start
      (.single q₂ Z₂ context₂) := by
    simpa [start, hstate, hstack] using
      trace₂.expandListContext_toSingle M
  have global₁' : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₁,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₁) := by
    simpa [start, LeftmostEpsilonPosition.conf] using global₁
  have global₂' : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₂,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₂) := by
    simpa [start, LeftmostEpsilonPosition.conf, hstate, hstack] using global₂
  exact leftmostEpsilonTrace_converging_epsilon_heads_eq M
    expanded₁ expanded₂ transition₁ transition₂
    global₁' global₂' useful₁ useful₂ hlook

/-- A zero-visible tail starting at a `single` node retains the complete
hidden context of that node.  This is the non-anchor variant needed when one
epsilon parent is assumed to be a structural descendant of the other. -/
public theorem ZeroVisibleTail.fromSingle_exists_retainedFrameRun
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {q target : State M} {Z : StackSymbol M}
    {anchorSuffix : List T}
    {anchorContext : List (StackSymbol M)}
    {current : Nonterminal M} {currentSuffix : List T}
    {currentContext : List (StackSymbol M)}
    (h : ZeroVisibleTail M p preWord
      (PDA_to_CFG.N.single q Z target) anchorSuffix anchorContext
      current currentSuffix currentContext) :
    ∃ n : ℕ,
      PDA.RetainedFrameRun (emptyStackPDA M) anchorContext n
        ⟨q, [], Z :: anchorContext⟩
        ⟨spineCutState M current, [],
          spineCutStack M current currentContext⟩ := by
  induction h with
  | refl =>
      exact ⟨0, by
        simpa [spineCutState, spineCutStack] using
          (PDA.RetainedFrameRun.refl
            (P := emptyStackPDA M) (frame := anchorContext)
            q [] [Z])⟩
  | start previous hrule => cases previous
  | @epsilon suffix context source returnState next top replacement
      previous htransition hrule ih =>
      obtain ⟨n, hrun⟩ := ih
      obtain ⟨added, hcontext⟩ := previous.context_eq_append M
      have hrunAligned :
          PDA.RetainedFrameRun (emptyStackPDA M) anchorContext n
            ⟨q, [], Z :: anchorContext⟩
            ⟨source, [], (top :: added) ++ anchorContext⟩ := by
        simpa [spineCutState, spineCutStack, hcontext,
          List.append_assoc] using hrun
      have hstep : (emptyStackPDA M).Reaches₁
          ⟨source, [], top :: added⟩
          ⟨next, [], replacement ++ added⟩ :=
        ⟨next, replacement, htransition, by simp⟩
      have hrun' := PDA.RetainedFrameRun.step
        (P := emptyStackPDA M) hrunAligned hstep
      exact ⟨n + 1, by
        simpa [spineCutState, spineCutStack, hcontext,
          List.append_assoc] using hrun'⟩
  | @splitLeft suffix z context source middle returnState top saved
      previous hlength hrule hright ih =>
      obtain ⟨n, hrun⟩ := ih
      exact ⟨n, by
        simpa [spineCutState, spineCutStack,
          List.append_assoc] using hrun⟩

/-- Equal-length globally rooted realizations of two concrete epsilon
introductions of the same list child have the same source state and exposed
stack symbol.

The common completion of the child supplies usefulness on both sides.  The
one-symbol hypothesis is needed only when that completion is empty. -/
public theorem concreteEpsilonEpsilon_heads_eq_of_equal_steps
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {preWord suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {q₁ q₂ next target : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    {steps : ℕ}
    (parent₁ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ preWord context₁)
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (rule₁ : (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (parent₂ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ preWord context₂)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (rule₂ : (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (run₁ : (emptyStackPDA M).ReachesIn steps
      ⟨(emptyStackPDA M).initial_state, preWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, [], Z₁ :: context₁⟩)
    (run₂ : (emptyStackPDA M).ReachesIn steps
      ⟨(emptyStackPDA M).initial_state, preWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, [], Z₂ :: context₂⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  let introduction₁ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₁ preWord context₁
      (PDA_to_CFG.N.single q₁ Z₁ target)
      (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon parent₁ transition₁ rule₁
  let introduction₂ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₂ preWord context₂
      (PDA_to_CFG.N.single q₂ Z₂ target)
      (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon parent₂ transition₂ rule₂
  obtain ⟨childWord, childCompletion⟩ := introduction₁.childCompletion M
  obtain ⟨final₁, continuation₁⟩ := introduction₁.childContinuation M
  obtain ⟨final₂, continuation₂⟩ := introduction₂.childContinuation M
  have childUseful₁ : (emptyStackPDA M).Reaches
      ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩
      ⟨final₁, [], []⟩ :=
    completedList_useful_with_context M
      (introduction₁.gammaLength M) childCompletion continuation₁
  have childUseful₂ : (emptyStackPDA M).Reaches
      ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩
      ⟨final₂, [], []⟩ :=
    completedList_useful_with_context M
      (introduction₂.gammaLength M) childCompletion continuation₂
  have parentStep₁ : (emptyStackPDA M).Reaches₁
      ⟨q₁, childWord ++ suffix₁, Z₁ :: context₁⟩
      ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩ := by
    have hcore : (emptyStackPDA M).Reaches₁
        ⟨q₁, [], Z₁ :: context₁⟩
        ⟨next, [], gamma ++ context₁⟩ :=
      ⟨next, gamma, transition₁, by simp⟩
    apply PDA.reaches₁_iff_reachesIn_one.mpr
    have hlift := (PDA.unconsumed_input_N
      (pda := emptyStackPDA M) (childWord ++ suffix₁)).mp
      (PDA.reaches₁_iff_reachesIn_one.mp hcore)
    simpa [PDA.conf.appendInput] using hlift
  have parentStep₂ : (emptyStackPDA M).Reaches₁
      ⟨q₂, childWord ++ suffix₂, Z₂ :: context₂⟩
      ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩ := by
    have hcore : (emptyStackPDA M).Reaches₁
        ⟨q₂, [], Z₂ :: context₂⟩
        ⟨next, [], gamma ++ context₂⟩ :=
      ⟨next, gamma, transition₂, by simp⟩
    apply PDA.reaches₁_iff_reachesIn_one.mpr
    have hlift := (PDA.unconsumed_input_N
      (pda := emptyStackPDA M) (childWord ++ suffix₂)).mp
      (PDA.reaches₁_iff_reachesIn_one.mp hcore)
    simpa [PDA.conf.appendInput] using hlift
  have parentUseful₁ : (emptyStackPDA M).Reaches
      ⟨q₁, childWord ++ suffix₁, Z₁ :: context₁⟩
      ⟨final₁, [], []⟩ :=
    (Relation.ReflTransGen.single parentStep₁).trans childUseful₁
  have parentUseful₂ : (emptyStackPDA M).Reaches
      ⟨q₂, childWord ++ suffix₂, Z₂ :: context₂⟩
      ⟨final₂, [], []⟩ :=
    (Relation.ReflTransGen.single parentStep₂).trans childUseful₂
  have liftedRun₁ :=
    (PDA.unconsumed_input_N (pda := emptyStackPDA M)
      (childWord ++ suffix₁)).mp run₁
  have liftedRun₂ :=
    (PDA.unconsumed_input_N (pda := emptyStackPDA M)
      (childWord ++ suffix₂)).mp run₂
  have synchronized := emptyStack_globally_useful_reachesIn_cross_input M
    (by simpa [PDA.conf.appendInput] using liftedRun₁)
    (by simpa [PDA.conf.appendInput] using liftedRun₂)
    parentUseful₁ parentUseful₂ (take_one_append_eq hlook)
  have hstate : q₂ = q₁ := congrArg PDA.conf.state synchronized
  have hstack : Z₂ :: context₂ = Z₁ :: context₁ :=
    congrArg PDA.conf.stack synchronized
  exact ⟨hstate.symm, (List.cons.inj hstack).1.symm⟩

/-- If the second epsilon parent is a zero-visible structural descendant of
the first, the two exposed heads are equal.  A genuinely nonempty descendant
tail retains the first hidden context.  Its first PDA step synchronizes with
the direct epsilon edge to the common child; the remaining retained segment
therefore repeats that child cut, either exactly or with a nonempty inserted
stack block.  Both alternatives contradict usefulness. -/
public theorem concreteEpsilonEpsilon_heads_eq_of_zeroVisibleTail
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {preWord suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {q₁ q₂ next target : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ preWord context₁)
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (rule₁ : (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (parent₂ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ preWord context₂)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (rule₂ : (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (tail : ZeroVisibleTail M childPrefix preWord
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ context₁
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ context₂)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  rcases tail.epsilonFree_or_epsilonBearing M with hfree | hbearing
  · have hcut := hfree.cut_eq M
    have hstate : q₁ = q₂ := congrArg PDA.conf.state hcut
    have hstack : Z₁ :: context₁ = Z₂ :: context₂ :=
      congrArg PDA.conf.stack hcut
    exact ⟨hstate, (List.cons.inj hstack).1⟩
  · let introduction₁ : ConcreteListIntroduction M childPrefix next gamma
        target suffix₁ preWord context₁
        (PDA_to_CFG.N.single q₁ Z₁ target)
        (PDA_to_CFG.N.single q₁ Z₁ target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
      ConcreteListIntroduction.epsilon parent₁ transition₁ rule₁
    let introduction₂ : ConcreteListIntroduction M childPrefix next gamma
        target suffix₂ preWord context₂
        (PDA_to_CFG.N.single q₂ Z₂ target)
        (PDA_to_CFG.N.single q₂ Z₂ target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
      ConcreteListIntroduction.epsilon parent₂ transition₂ rule₂
    obtain ⟨childWord, childCompletion⟩ := introduction₁.childCompletion M
    obtain ⟨final₁, continuation₁⟩ := introduction₁.childContinuation M
    obtain ⟨final₂, continuation₂⟩ := introduction₂.childContinuation M
    have childUseful₁ : (emptyStackPDA M).Reaches
        ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩
        ⟨final₁, [], []⟩ :=
      completedList_useful_with_context M
        (introduction₁.gammaLength M) childCompletion continuation₁
    have childUseful₂ : (emptyStackPDA M).Reaches
        ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩
        ⟨final₂, [], []⟩ :=
      completedList_useful_with_context M
        (introduction₂.gammaLength M) childCompletion continuation₂
    have parentStep₁ : (emptyStackPDA M).Reaches₁
        ⟨q₁, childWord ++ suffix₁, Z₁ :: context₁⟩
        ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩ := by
      have hcore : (emptyStackPDA M).Reaches₁
          ⟨q₁, [], Z₁ :: context₁⟩
          ⟨next, [], gamma ++ context₁⟩ :=
        ⟨next, gamma, transition₁, by simp⟩
      apply PDA.reaches₁_iff_reachesIn_one.mpr
      have hlift := (PDA.unconsumed_input_N
        (pda := emptyStackPDA M) (childWord ++ suffix₁)).mp
        (PDA.reaches₁_iff_reachesIn_one.mp hcore)
      simpa [PDA.conf.appendInput] using hlift
    have parentStep₂ : (emptyStackPDA M).Reaches₁
        ⟨q₂, childWord ++ suffix₂, Z₂ :: context₂⟩
        ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩ := by
      have hcore : (emptyStackPDA M).Reaches₁
          ⟨q₂, [], Z₂ :: context₂⟩
          ⟨next, [], gamma ++ context₂⟩ :=
        ⟨next, gamma, transition₂, by simp⟩
      apply PDA.reaches₁_iff_reachesIn_one.mpr
      have hlift := (PDA.unconsumed_input_N
        (pda := emptyStackPDA M) (childWord ++ suffix₂)).mp
        (PDA.reaches₁_iff_reachesIn_one.mp hcore)
      simpa [PDA.conf.appendInput] using hlift
    obtain ⟨tailSteps, retainedTail⟩ :=
      tail.fromSingle_exists_retainedFrameRun M
    by_cases hzero : tailSteps = 0
    · subst tailSteps
      have hcuts := PDA.reachesIn_zero retainedTail.toReachesIn
      have hcycle₀ : Relation.TransGen
          (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
          ⟨q₁, [], Z₁ :: context₁⟩
          ⟨q₂, [], Z₂ :: context₂⟩ := by
        simpa [spineCutState, spineCutStack] using hbearing.transGen_cut M
      rw [hcuts] at hcycle₀
      have hcycle := transGen_append_input hcycle₀
        (childWord ++ suffix₂)
      have parentUseful₂ : (emptyStackPDA M).Reaches
          ⟨q₂, childWord ++ suffix₂, Z₂ :: context₂⟩
          ⟨final₂, [], []⟩ :=
        (Relation.ReflTransGen.single parentStep₂).trans childUseful₂
      exact False.elim <| emptyStack_no_useful_cycle M
        (by simpa [PDA.conf.appendInput] using hcycle) parentUseful₂
    · obtain ⟨restSteps, htailSteps⟩ :=
        Nat.exists_eq_succ_of_ne_zero hzero
      subst tailSteps
      have retainedTail' : PDA.RetainedFrameRun (emptyStackPDA M) context₁
          (1 + restSteps)
          ⟨q₁, [], Z₁ :: context₁⟩
          ⟨q₂, [], Z₂ :: context₂⟩ := by
        simpa [Nat.add_comm] using retainedTail
      obtain ⟨firstState, firstInput, firstUpper, first, rest⟩ :=
        retainedTail'.split_add
      have hfirstInput : firstInput = [] := by
        obtain ⟨consumed, hinput⟩ :=
          PDA.decreasing_input (PDA.reaches_of_reachesIn first.toReachesIn)
        simp at hinput
        exact hinput.2
      subst firstInput
      obtain ⟨prefixSteps, parentRun⟩ := parent₁.exists_prefixRunIn M
      have global₁ : (emptyStackPDA M).Reaches
          ⟨(emptyStackPDA M).initial_state,
            preWord ++ (childWord ++ suffix₁),
            [(emptyStackPDA M).start_symbol]⟩
          ⟨q₁, childWord ++ suffix₁, Z₁ :: context₁⟩ := by
        have hlift := (PDA.unconsumed_input
          (pda := emptyStackPDA M) (childWord ++ suffix₁)).mp
          (PDA.reaches_of_reachesIn parentRun)
        simpa [PDA.conf.appendInput] using hlift
      have global₂ : (emptyStackPDA M).Reaches
          ⟨(emptyStackPDA M).initial_state,
            preWord ++ (childWord ++ suffix₂),
            [(emptyStackPDA M).start_symbol]⟩
          ⟨q₁, childWord ++ suffix₂, Z₁ :: context₁⟩ := by
        have hlift := (PDA.unconsumed_input
          (pda := emptyStackPDA M) (childWord ++ suffix₂)).mp
          (PDA.reaches_of_reachesIn parentRun)
        simpa [PDA.conf.appendInput] using hlift
      have firstStep₀ : (emptyStackPDA M).Reaches₁
          ⟨q₁, [], Z₁ :: context₁⟩
          ⟨firstState, [], firstUpper ++ context₁⟩ :=
        PDA.reaches₁_iff_reachesIn_one.mpr first.toReachesIn
      have firstStep : (emptyStackPDA M).Reaches₁
          ⟨q₁, childWord ++ suffix₂, Z₁ :: context₁⟩
          ⟨firstState, childWord ++ suffix₂,
            firstUpper ++ context₁⟩ := by
        apply PDA.reaches₁_iff_reachesIn_one.mpr
        have hlift := (PDA.unconsumed_input_N
          (pda := emptyStackPDA M) (childWord ++ suffix₂)).mp
          (PDA.reaches₁_iff_reachesIn_one.mp firstStep₀)
        simpa [PDA.conf.appendInput] using hlift
      have restUseful₂ : (emptyStackPDA M).Reaches
          ⟨firstState, childWord ++ suffix₂,
            firstUpper ++ context₁⟩
          ⟨final₂, [], []⟩ := by
        have restLifted := (PDA.unconsumed_input
          (pda := emptyStackPDA M) (childWord ++ suffix₂)).mp
          (PDA.reaches_of_reachesIn rest.toReachesIn)
        have toParent : (emptyStackPDA M).Reaches
            ⟨firstState, childWord ++ suffix₂,
              firstUpper ++ context₁⟩
            ⟨q₂, childWord ++ suffix₂, Z₂ :: context₂⟩ := by
          simpa [PDA.conf.appendInput] using restLifted
        exact toParent.trans
          ((Relation.ReflTransGen.single parentStep₂).trans childUseful₂)
      obtain ⟨hfirstState, hfirstStack, hinputs⟩ :=
        emptyStack_globally_useful_step_cross_input M
          (take_one_append_eq hlook) global₁ global₂
          parentStep₁ firstStep childUseful₁ restUseful₂
      have hstate : firstState = next := hfirstState.symm
      have hupper : firstUpper = gamma := by
        exact (List.append_cancel_right hfirstStack).symm
      subst firstState
      subst firstUpper
      obtain ⟨added, hcontext⟩ := tail.context_eq_append M
      have restAligned : PDA.RetainedFrameRun (emptyStackPDA M) context₁
          restSteps
          ⟨next, [], gamma ++ context₁⟩
          ⟨q₂, [], (Z₂ :: added) ++ context₁⟩ := by
        simpa [hcontext, List.append_assoc] using rest
      have finalStep₀ : (emptyStackPDA M).Reaches₁
          ⟨q₂, [], Z₂ :: added⟩
          ⟨next, [], gamma ++ added⟩ :=
        ⟨next, gamma, transition₂, by simp⟩
      have repeated := PDA.RetainedFrameRun.step
        (P := emptyStackPDA M) restAligned finalStep₀
      have repeated' : PDA.RetainedFrameRun (emptyStackPDA M) context₁
          (restSteps + 1)
          ⟨next, [], gamma ++ context₁⟩
          ⟨next, [], (gamma ++ added) ++ context₁⟩ := by
        simpa [List.append_assoc] using repeated
      by_cases hadded : added = []
      · subst added
        have hcycle₀ := transGen_of_reachesIn_pos (by omega)
          repeated'.toReachesIn
        have hcycle := transGen_append_input hcycle₀
          (childWord ++ suffix₂)
        exact False.elim <| emptyStack_no_useful_cycle M
          (by simpa [PDA.conf.appendInput] using hcycle)
          (by simpa [hcontext] using childUseful₂)
      · have stripped := repeated'.changeFrame ([] : List (StackSymbol M))
        exfalso
        apply emptyStack_no_useful_stack_growth M
          (q := next) (base := gamma) (extra := added)
          (context := context₁) (input := childWord ++ suffix₂)
          (final := final₂)
        · exact PDA.reaches_of_reachesIn (by
            simpa using stripped.toReachesIn)
        · exact hadded
        · simpa [hcontext, List.append_assoc] using childUseful₂

/-- Symmetric interface: structural zero-visible comparability of the two
parent occurrences is sufficient for epsilon/epsilon head uniqueness. -/
public theorem concreteEpsilonEpsilon_heads_eq_of_zeroVisibleComparable
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {preWord suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {q₁ q₂ next target : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ preWord context₁)
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (rule₁ : (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (parent₂ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ preWord context₂)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (rule₂ : (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (comparable :
      ZeroVisibleTail M childPrefix preWord
          (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ context₁
          (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ context₂ ∨
        ZeroVisibleTail M childPrefix preWord
          (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ context₂
          (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ context₁)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  rcases comparable with tail | tail
  · exact concreteEpsilonEpsilon_heads_eq_of_zeroVisibleTail M
      parent₁ transition₁ rule₁ parent₂ transition₂ rule₂
      tail hlook
  · obtain ⟨hq, hZ⟩ :=
      concreteEpsilonEpsilon_heads_eq_of_zeroVisibleTail M
        parent₂ transition₂ rule₂ parent₁ transition₁ rule₁
        tail hlook.symm
    exact ⟨hq.symm, hZ.symm⟩

/-- Two concrete epsilon introductions whose last-visible anchors denote the
same physical position have equal source heads.  The anchors may retain
different grammar target indices: `LeftmostEpsilonPosition` deliberately
forgets those indices and synchronizes the productive zero-visible traces
at the operational cut. -/
public theorem concreteEpsilonEpsilon_heads_eq_of_anchor_position_eq
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {preWord suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {q₁ q₂ next target : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ preWord context₁)
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (rule₁ : (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (parent₂ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ preWord context₂)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (rule₂ : (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    {anchor₁ anchor₂ : Nonterminal M}
    {anchorSuffix₁ anchorSuffix₂ : List T}
    {anchorContext₁ anchorContext₂ : List (StackSymbol M)}
    (leftAnchor : VisibleSpineAnchor M childPrefix anchor₁
      anchorSuffix₁ preWord anchorContext₁)
    (rightAnchor : VisibleSpineAnchor M childPrefix anchor₂
      anchorSuffix₂ preWord anchorContext₂)
    (leftTail : ZeroVisibleTail M childPrefix preWord
      anchor₁ anchorSuffix₁ anchorContext₁
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ context₁)
    (rightTail : ZeroVisibleTail M childPrefix preWord
      anchor₂ anchorSuffix₂ anchorContext₂
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ context₂)
    (hposition : leftmostEpsilonPositionOf M anchor₁ anchorContext₁ =
      leftmostEpsilonPositionOf M anchor₂ anchorContext₂)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  let introduction₁ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₁ preWord context₁
      (PDA_to_CFG.N.single q₁ Z₁ target)
      (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon parent₁ transition₁ rule₁
  let introduction₂ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₂ preWord context₂
      (PDA_to_CFG.N.single q₂ Z₂ target)
      (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon parent₂ transition₂ rule₂
  obtain ⟨childWord, childCompletion⟩ := introduction₁.childCompletion M
  obtain ⟨final₁, continuation₁⟩ := introduction₁.childContinuation M
  obtain ⟨final₂, continuation₂⟩ := introduction₂.childContinuation M
  have childUseful₁ : (emptyStackPDA M).Reaches
      ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩
      ⟨final₁, [], []⟩ :=
    completedList_useful_with_context M
      (introduction₁.gammaLength M) childCompletion continuation₁
  have childUseful₂ : (emptyStackPDA M).Reaches
      ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩
      ⟨final₂, [], []⟩ :=
    completedList_useful_with_context M
      (introduction₂.gammaLength M) childCompletion continuation₂
  let start := leftmostEpsilonPositionOf M anchor₁ anchorContext₁
  have trace₁ : LeftmostEpsilonTrace M start
      (.single q₁ Z₁ context₁) := by
    simpa [start, leftmostEpsilonPositionOf] using
      leftTail.leftmostEpsilonTrace M
  have trace₂ : LeftmostEpsilonTrace M start
      (.single q₂ Z₂ context₂) := by
    simpa [start, hposition, leftmostEpsilonPositionOf] using
      rightTail.leftmostEpsilonTrace M
  have anchorRun₁ := (PDA.unconsumed_input (childWord ++ suffix₁)).mp
    (leftAnchor.prefixPath M)
  have anchorRun₂ := (PDA.unconsumed_input (childWord ++ suffix₂)).mp
    (rightAnchor.prefixPath M)
  have global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        preWord ++ (childWord ++ suffix₁),
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M (childWord ++ suffix₁)) := by
    change (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        preWord ++ (childWord ++ suffix₁),
        [(emptyStackPDA M).start_symbol]⟩
      ((leftmostEpsilonPositionOf M anchor₁ anchorContext₁).conf M
        (childWord ++ suffix₁))
    rw [leftmostEpsilonPositionOf_conf]
    simpa [PDA.conf.appendInput] using anchorRun₁
  have global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        preWord ++ (childWord ++ suffix₂),
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M (childWord ++ suffix₂)) := by
    change (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        preWord ++ (childWord ++ suffix₂),
        [(emptyStackPDA M).start_symbol]⟩
      ((leftmostEpsilonPositionOf M anchor₁ anchorContext₁).conf M
        (childWord ++ suffix₂))
    rw [hposition, leftmostEpsilonPositionOf_conf]
    simpa [PDA.conf.appendInput] using anchorRun₂
  exact leftmostEpsilonTrace_converging_epsilon_heads_eq M
    trace₁ trace₂ transition₁ transition₂ global₁ global₂
    (by simpa [LeftmostEpsilonPosition.conf] using childUseful₁)
    (by simpa [LeftmostEpsilonPosition.conf] using childUseful₂)
    (take_one_append_eq hlook)

/-- Two concrete epsilon introductions also synchronize when their selected
last-visible anchors are list nodes with the same physical PDA cut.  The
displayed lists and hidden contexts need not agree separately: equality of
their concatenations is exactly the information supplied by equality of two
split-return endpoint configurations. -/
public theorem concreteEpsilonEpsilon_heads_eq_of_list_anchor_cut_eq
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {preWord suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {q₁ q₂ next target : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ preWord context₁)
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (rule₁ : (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (parent₂ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ preWord context₂)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (rule₂ : (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    {anchorState₁ anchorState₂ anchorTarget₁ anchorTarget₂ : State M}
    {displayed₁ displayed₂ : List (StackSymbol M)}
    {anchorSuffix₁ anchorSuffix₂ : List T}
    {anchorContext₁ anchorContext₂ : List (StackSymbol M)}
    (leftAnchor : VisibleSpineAnchor M childPrefix
      (PDA_to_CFG.N.list anchorState₁ displayed₁ anchorTarget₁)
      anchorSuffix₁ preWord anchorContext₁)
    (rightAnchor : VisibleSpineAnchor M childPrefix
      (PDA_to_CFG.N.list anchorState₂ displayed₂ anchorTarget₂)
      anchorSuffix₂ preWord anchorContext₂)
    (leftTail : ZeroVisibleTail M childPrefix preWord
      (PDA_to_CFG.N.list anchorState₁ displayed₁ anchorTarget₁)
      anchorSuffix₁ anchorContext₁
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ context₁)
    (rightTail : ZeroVisibleTail M childPrefix preWord
      (PDA_to_CFG.N.list anchorState₂ displayed₂ anchorTarget₂)
      anchorSuffix₂ anchorContext₂
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ context₂)
    (hstate : anchorState₁ = anchorState₂)
    (hstack : displayed₁ ++ anchorContext₁ =
      displayed₂ ++ anchorContext₂)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ ∧ Z₁ = Z₂ := by
  let introduction₁ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₁ preWord context₁
      (PDA_to_CFG.N.single q₁ Z₁ target)
      (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon parent₁ transition₁ rule₁
  let introduction₂ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₂ preWord context₂
      (PDA_to_CFG.N.single q₂ Z₂ target)
      (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon parent₂ transition₂ rule₂
  obtain ⟨childWord, childCompletion⟩ := introduction₁.childCompletion M
  obtain ⟨final₁, continuation₁⟩ := introduction₁.childContinuation M
  obtain ⟨final₂, continuation₂⟩ := introduction₂.childContinuation M
  have childUseful₁ : (emptyStackPDA M).Reaches
      ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩
      ⟨final₁, [], []⟩ :=
    completedList_useful_with_context M
      (introduction₁.gammaLength M) childCompletion continuation₁
  have childUseful₂ : (emptyStackPDA M).Reaches
      ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩
      ⟨final₂, [], []⟩ :=
    completedList_useful_with_context M
      (introduction₂.gammaLength M) childCompletion continuation₂
  have trace₁ : LeftmostEpsilonTrace M
      (.list anchorState₁ displayed₁ anchorContext₁)
      (.single q₁ Z₁ context₁) := by
    simpa [leftmostEpsilonPositionOf] using
      leftTail.leftmostEpsilonTrace M
  have trace₂ : LeftmostEpsilonTrace M
      (.list anchorState₂ displayed₂ anchorContext₂)
      (.single q₂ Z₂ context₂) := by
    simpa [leftmostEpsilonPositionOf] using
      rightTail.leftmostEpsilonTrace M
  have anchorRun₁ := (PDA.unconsumed_input (childWord ++ suffix₁)).mp
    (leftAnchor.prefixPath M)
  have anchorRun₂ := (PDA.unconsumed_input (childWord ++ suffix₂)).mp
    (rightAnchor.prefixPath M)
  have global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        preWord ++ (childWord ++ suffix₁),
        [(emptyStackPDA M).start_symbol]⟩
      ((.list anchorState₁ displayed₁ anchorContext₁ :
        LeftmostEpsilonPosition M).conf M (childWord ++ suffix₁)) := by
    simpa [LeftmostEpsilonPosition.conf, spineCutState, spineCutStack,
      PDA.conf.appendInput] using anchorRun₁
  have global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        preWord ++ (childWord ++ suffix₂),
        [(emptyStackPDA M).start_symbol]⟩
      ((.list anchorState₂ displayed₂ anchorContext₂ :
        LeftmostEpsilonPosition M).conf M (childWord ++ suffix₂)) := by
    simpa [LeftmostEpsilonPosition.conf, spineCutState, spineCutStack,
      PDA.conf.appendInput] using anchorRun₂
  exact leftmostEpsilonTrace_converging_heads_eq_of_list_cut_eq M
    trace₁ trace₂ transition₁ transition₂ hstate hstack
    global₁ global₂
    (by simpa [LeftmostEpsilonPosition.conf] using childUseful₁)
    (by simpa [LeftmostEpsilonPosition.conf] using childUseful₂)
    (take_one_append_eq hlook)

/-- The last structural residual for two epsilon introductions of one list
child.  Both concrete parents and their zero-visible ancestries are retained.
The paired anchors have unequal physical positions; paired root and read
anchors therefore cannot inhabit this datum, so its paired witness is
necessarily a `splitRight`/`splitRight` pair.

Keeping the position inequality, rather than flattening the split
constructor into a large tuple, preserves the two original structural
spines for the interval argument which consumes this residual. -/
@[expose]
public def PairedSplitEpsilonEpsilonHeadsData (M : DPDA Q T S)
    (childPrefix : List (symbol T (Nonterminal M)))
    (q₁ q₂ next target : State M) (Z₁ Z₂ : StackSymbol M)
    (gamma : List (StackSymbol M))
    (suffix₁ suffix₂ : List T) : Prop :=
  ∃ (preWord : List T)
      (context₁ context₂ : List (StackSymbol M))
      (anchor₁ anchor₂ : Nonterminal M)
      (anchorSuffix₁ anchorSuffix₂ : List T)
      (anchorContext₁ anchorContext₂ : List (StackSymbol M)),
    ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ preWord context₁ ∧
    ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ preWord context₂ ∧
    (next, gamma) ∈ (emptyStackPDA M).transition_fun' q₁ Z₁ ∧
    (next, gamma) ∈ (emptyStackPDA M).transition_fun' q₂ Z₂ ∧
    (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules ∧
    (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules ∧
    VisibleSpineAnchor M childPrefix anchor₁ anchorSuffix₁
      preWord anchorContext₁ ∧
    VisibleSpineAnchor M childPrefix anchor₂ anchorSuffix₂
      preWord anchorContext₂ ∧
    ZeroVisibleTail M childPrefix preWord
      anchor₁ anchorSuffix₁ anchorContext₁
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ context₁ ∧
    ZeroVisibleTail M childPrefix preWord
      anchor₂ anchorSuffix₂ anchorContext₂
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ context₂ ∧
    PairedVisibleAnchors M childPrefix preWord
      anchor₁ anchorSuffix₁ anchorContext₁
      anchor₂ anchorSuffix₂ anchorContext₂ ∧
    leftmostEpsilonPositionOf M anchor₁ anchorContext₁ ≠
      leftmostEpsilonPositionOf M anchor₂ anchorContext₂ ∧
    suffix₁.take 1 = suffix₂.take 1

/-- Concrete epsilon introductions either synchronize at their paired
last-visible anchor, or expose the exact unequal-position paired-split
residual.  Root and read pairs have equal physical anchor positions, so the
right disjunct can only survive the `splitRight` constructor of
`PairedVisibleAnchors`. -/
public theorem concreteEpsilonEpsilon_heads_eq_or_pairedSplit
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {preWord suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {q₁ q₂ next target : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ preWord context₁)
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (rule₁ : (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (parent₂ : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ preWord context₂)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (rule₂ : (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    (q₁ = q₂ ∧ Z₁ = Z₂) ∨
      PairedSplitEpsilonEpsilonHeadsData M childPrefix q₁ q₂ next
        target Z₁ Z₂ gamma suffix₁ suffix₂ := by
  obtain ⟨anchor₁, anchorSuffix₁, anchorContext₁,
      leftAnchor, leftTail⟩ := parent₁.zeroVisibleDecomposition M
  obtain ⟨anchor₂, anchorSuffix₂, anchorContext₂,
      rightAnchor, rightTail⟩ := parent₂.zeroVisibleDecomposition M
  let paired := pairedVisibleAnchors_of_same_prefix M
    leftAnchor rightAnchor rfl rfl
  by_cases hposition :
      leftmostEpsilonPositionOf M anchor₁ anchorContext₁ =
        leftmostEpsilonPositionOf M anchor₂ anchorContext₂
  · left
    exact concreteEpsilonEpsilon_heads_eq_of_anchor_position_eq M
      parent₁ transition₁ rule₁ parent₂ transition₂ rule₂
      leftAnchor rightAnchor leftTail rightTail hposition hlook
  · right
    exact ⟨preWord, context₁, context₂,
      anchor₁, anchor₂, anchorSuffix₁, anchorSuffix₂,
      anchorContext₁, anchorContext₂,
      parent₁, parent₂, transition₁, transition₂, rule₁, rule₂,
      leftAnchor, rightAnchor, leftTail, rightTail, paired,
      hposition, hlook⟩

/-- Active-spine interface for the same classifier.  A single completion of
the shared child prefix is chosen first, so both returned concrete parent
spines live over the same completed word. -/
public theorem activeEpsilonEpsilon_heads_eq_or_pairedSplit
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {suffix₁ suffix₂ : List T}
    {q₁ q₂ next target : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (parent₁ : ActiveSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁)
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (rule₁ : (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (parent₂ : ActiveSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (rule₂ : (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    (q₁ = q₂ ∧ Z₁ = Z₂) ∨
      PairedSplitEpsilonEpsilonHeadsData M childPrefix q₁ q₂ next
        target Z₁ Z₂ gamma suffix₁ suffix₂ := by
  obtain ⟨preWord, hp⟩ :=
    prehandle_prefix_completion M rule₁ (parent₁.derivesRightmost M)
  obtain ⟨context₁, concreteParent₁⟩ :=
    concreteOperationalSpine_of_activeSpine M parent₁ hp
  obtain ⟨context₂, concreteParent₂⟩ :=
    concreteOperationalSpine_of_activeSpine M parent₂ hp
  exact concreteEpsilonEpsilon_heads_eq_or_pairedSplit M
    concreteParent₁ transition₁ rule₁
    concreteParent₂ transition₂ rule₂ hlook

/-- The exact unequal-position residual for two epsilon introductions.  It
retains the normalized parent spines and their globally counted source cuts;
no interval or hidden context has been compressed away. -/
@[expose]
public def UnequalCountEpsilonEpsilonHeadsData (M : DPDA Q T S)
    (childPrefix : List (symbol T (Nonterminal M)))
    (q₁ q₂ next target : State M) (Z₁ Z₂ : StackSymbol M)
    (gamma : List (StackSymbol M))
    (suffix₁ suffix₂ : List T) : Prop :=
  ∃ (preWord : List T)
      (context₁ context₂ : List (StackSymbol M))
      (steps₁ steps₂ : ℕ),
    steps₁ ≠ steps₂ ∧
    ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁ preWord context₁ ∧
    ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂ preWord context₂ ∧
    (next, gamma) ∈ (emptyStackPDA M).transition_fun' q₁ Z₁ ∧
    (next, gamma) ∈ (emptyStackPDA M).transition_fun' q₂ Z₂ ∧
    (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules ∧
    (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules ∧
    (emptyStackPDA M).ReachesIn steps₁
      ⟨(emptyStackPDA M).initial_state, preWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, [], Z₁ :: context₁⟩ ∧
    (emptyStackPDA M).ReachesIn steps₂
      ⟨(emptyStackPDA M).initial_state, preWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, [], Z₂ :: context₂⟩ ∧
    suffix₁.take 1 = suffix₂.take 1

/-- Active epsilon introductions either already have equal source heads, or
expose the exact unequal-count structural datum needed by the frontier-trace
comparison argument. -/
public theorem activeEpsilonEpsilon_heads_eq_or_unequal_counts
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {suffix₁ suffix₂ : List T}
    {q₁ q₂ next target : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (parent₁ : ActiveSpine M childPrefix
      (PDA_to_CFG.N.single q₁ Z₁ target) suffix₁)
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ Z₁)
    (rule₁ : (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (parent₂ : ActiveSpine M childPrefix
      (PDA_to_CFG.N.single q₂ Z₂ target) suffix₂)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ Z₂)
    (rule₂ : (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    (q₁ = q₂ ∧ Z₁ = Z₂) ∨
      UnequalCountEpsilonEpsilonHeadsData M childPrefix q₁ q₂ next
        target Z₁ Z₂ gamma suffix₁ suffix₂ := by
  obtain ⟨preWord, hp⟩ :=
    prehandle_prefix_completion M rule₁ (parent₁.derivesRightmost M)
  obtain ⟨context₁, concreteParent₁⟩ :=
    concreteOperationalSpine_of_activeSpine M parent₁ hp
  obtain ⟨context₂, concreteParent₂⟩ :=
    concreteOperationalSpine_of_activeSpine M parent₂ hp
  obtain ⟨steps₁, run₁⟩ := concreteParent₁.exists_prefixRunIn M
  obtain ⟨steps₂, run₂⟩ := concreteParent₂.exists_prefixRunIn M
  by_cases hsteps : steps₁ = steps₂
  · left
    subst steps₂
    exact concreteEpsilonEpsilon_heads_eq_of_equal_steps M
      concreteParent₁ transition₁ rule₁
      concreteParent₂ transition₂ rule₂ run₁ run₂ hlook
  · right
    exact ⟨preWord, context₁, context₂, steps₁, steps₂,
      hsteps, concreteParent₁, concreteParent₂,
      transition₁, transition₂, rule₁, rule₂, run₁, run₂,
      hlook⟩

/-- Operational orientation of the unequal-count residual.  Besides the
positive epsilon-only segment between the two parent cuts, the conclusion
retains a common completion of the shared child and both useful child
endpoints.  These are the exact ingredients needed to rule out a purported
structural extension by the useful-cycle and stack-growth kernels. -/
public theorem UnequalCountEpsilonEpsilonHeadsData.strict_extension
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {suffix₁ suffix₂ : List T}
    {q₁ q₂ next target : State M}
    {Z₁ Z₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (data : UnequalCountEpsilonEpsilonHeadsData M childPrefix q₁ q₂
      next target Z₁ Z₂ gamma suffix₁ suffix₂) :
    ∃ (childWord : List T)
        (context₁ context₂ : List (StackSymbol M))
        (final₁ final₂ : State M),
      (emptyStackPDA M).Reaches
          ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩
          ⟨final₁, [], []⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩
          ⟨final₂, [], []⟩ ∧
      ((∃ k, 0 < k ∧
          (emptyStackPDA M).ReachesIn k
            ⟨q₁, childWord ++ suffix₁, Z₁ :: context₁⟩
            ⟨q₂, childWord ++ suffix₁, Z₂ :: context₂⟩) ∨
        (∃ k, 0 < k ∧
          (emptyStackPDA M).ReachesIn k
            ⟨q₂, childWord ++ suffix₂, Z₂ :: context₂⟩
            ⟨q₁, childWord ++ suffix₂, Z₁ :: context₁⟩)) := by
  rcases data with ⟨preWord, context₁, context₂, steps₁, steps₂,
    hsteps, parent₁, parent₂, transition₁, transition₂, rule₁,
    rule₂, run₁, run₂, hlook⟩
  let introduction₁ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₁ preWord context₁
      (PDA_to_CFG.N.single q₁ Z₁ target)
      (PDA_to_CFG.N.single q₁ Z₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon parent₁ transition₁ rule₁
  let introduction₂ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₂ preWord context₂
      (PDA_to_CFG.N.single q₂ Z₂ target)
      (PDA_to_CFG.N.single q₂ Z₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon parent₂ transition₂ rule₂
  obtain ⟨childWord, childCompletion⟩ := introduction₁.childCompletion M
  obtain ⟨final₁, continuation₁⟩ := introduction₁.childContinuation M
  obtain ⟨final₂, continuation₂⟩ := introduction₂.childContinuation M
  have childUseful₁ : (emptyStackPDA M).Reaches
      ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩
      ⟨final₁, [], []⟩ :=
    completedList_useful_with_context M
      (introduction₁.gammaLength M) childCompletion continuation₁
  have childUseful₂ : (emptyStackPDA M).Reaches
      ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩
      ⟨final₂, [], []⟩ :=
    completedList_useful_with_context M
      (introduction₂.gammaLength M) childCompletion continuation₂
  have parentStep₁ : (emptyStackPDA M).Reaches₁
      ⟨q₁, childWord ++ suffix₁, Z₁ :: context₁⟩
      ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩ := by
    have hcore : (emptyStackPDA M).Reaches₁
        ⟨q₁, [], Z₁ :: context₁⟩
        ⟨next, [], gamma ++ context₁⟩ :=
      ⟨next, gamma, transition₁, by simp⟩
    apply PDA.reaches₁_iff_reachesIn_one.mpr
    have hlift := (PDA.unconsumed_input_N
      (pda := emptyStackPDA M) (childWord ++ suffix₁)).mp
      (PDA.reaches₁_iff_reachesIn_one.mp hcore)
    simpa [PDA.conf.appendInput] using hlift
  have parentStep₂ : (emptyStackPDA M).Reaches₁
      ⟨q₂, childWord ++ suffix₂, Z₂ :: context₂⟩
      ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩ := by
    have hcore : (emptyStackPDA M).Reaches₁
        ⟨q₂, [], Z₂ :: context₂⟩
        ⟨next, [], gamma ++ context₂⟩ :=
      ⟨next, gamma, transition₂, by simp⟩
    apply PDA.reaches₁_iff_reachesIn_one.mpr
    have hlift := (PDA.unconsumed_input_N
      (pda := emptyStackPDA M) (childWord ++ suffix₂)).mp
      (PDA.reaches₁_iff_reachesIn_one.mp hcore)
    simpa [PDA.conf.appendInput] using hlift
  have parentUseful₁ : (emptyStackPDA M).Reaches
      ⟨q₁, childWord ++ suffix₁, Z₁ :: context₁⟩
      ⟨final₁, [], []⟩ :=
    (Relation.ReflTransGen.single parentStep₁).trans childUseful₁
  have parentUseful₂ : (emptyStackPDA M).Reaches
      ⟨q₂, childWord ++ suffix₂, Z₂ :: context₂⟩
      ⟨final₂, [], []⟩ :=
    (Relation.ReflTransGen.single parentStep₂).trans childUseful₂
  have liftedRun₁ :=
    (PDA.unconsumed_input_N (pda := emptyStackPDA M)
      (childWord ++ suffix₁)).mp run₁
  have liftedRun₂ :=
    (PDA.unconsumed_input_N (pda := emptyStackPDA M)
      (childWord ++ suffix₂)).mp run₂
  have fullRun₁ : (emptyStackPDA M).ReachesIn steps₁
      ⟨(emptyStackPDA M).initial_state,
        preWord ++ (childWord ++ suffix₁),
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, childWord ++ suffix₁, Z₁ :: context₁⟩ := by
    simpa [PDA.conf.appendInput] using liftedRun₁
  have fullRun₂ : (emptyStackPDA M).ReachesIn steps₂
      ⟨(emptyStackPDA M).initial_state,
        preWord ++ (childWord ++ suffix₂),
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, childWord ++ suffix₂, Z₂ :: context₂⟩ := by
    simpa [PDA.conf.appendInput] using liftedRun₂
  refine ⟨childWord, context₁, context₂, final₁, final₂,
    childUseful₁, childUseful₂, ?_⟩
  rcases Nat.lt_or_gt_of_ne hsteps with hlt | hgt
  · left
    exact emptyStack_cross_input_strict_extension M fullRun₁ fullRun₂
      parentUseful₁ parentUseful₂ (take_one_append_eq hlook) hlt
  · right
    exact emptyStack_cross_input_strict_extension M fullRun₂ fullRun₁
      parentUseful₂ parentUseful₁
      (take_one_append_eq hlook).symm hgt

end

end DPDA_to_LR
