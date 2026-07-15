module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CountedSpine
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.EmptyReturnSynchronization

/-!
# Counted retained-frame intervals for characteristic spines

This file records the exact counted intervals which are still implicit in
zero-visible spine tails and concrete empty-return edges.  In both cases the
selected run stays strictly above a named outer stack context, so that later
comparison arguments may split or reframe the interval without reconstructing
an existential reachability witness.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A zero-visible tail is a counted run which retains the complete hidden
context of its visible anchor.  Structural `start` and `splitLeft` steps cost
zero PDA steps; every `epsilon` constructor contributes exactly one step. -/
public theorem ZeroVisibleTail.exists_retainedFrameRun
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M}
    {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (hanchor : VisibleSpineAnchor M p anchor anchorSuffix
      preWord anchorContext)
    (htail : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      current currentSuffix currentContext) :
    ∃ n : ℕ,
      PDA.RetainedFrameRun (emptyStackPDA M) anchorContext n
        ⟨spineCutState M anchor, [],
          spineCutStack M anchor anchorContext⟩
        ⟨spineCutState M current, [],
          spineCutStack M current currentContext⟩ := by
  induction htail with
  | refl =>
      cases hanchor with
      | root =>
          exact ⟨0, by
            simpa [spineCutState, spineCutStack] using
              (PDA.RetainedFrameRun.refl
                (P := emptyStackPDA M)
                (frame := ([] : List (StackSymbol M)))
                (emptyStackPDA M).initial_state []
                [(emptyStackPDA M).start_symbol])⟩
      | @read p suffix preWord context q target next a Z gamma
          parent htransition hrule =>
          exact ⟨0, by
            simpa [spineCutState, spineCutStack] using
              (PDA.RetainedFrameRun.refl
                (P := emptyStackPDA M)
                next [] gamma)⟩
      | @splitRight p suffix preWord leftWord context
          q middle target Z gamma parent hlength hrule hleft =>
          exact ⟨0, by
            simpa [spineCutState, spineCutStack] using
              (PDA.RetainedFrameRun.refl
                (P := emptyStackPDA M)
                middle [] gamma)⟩
  | start previous hrule ih =>
      obtain ⟨n, hrun⟩ := ih
      exact ⟨n, by
        simpa [spineCutState, spineCutStack] using hrun⟩
  | @epsilon suffix context q target next Z gamma
      previous htransition hrule ih =>
      obtain ⟨n, hrun⟩ := ih
      obtain ⟨added, hcontext⟩ := previous.context_eq_append M
      have hrunAligned :
          PDA.RetainedFrameRun (emptyStackPDA M) anchorContext n
            ⟨spineCutState M anchor, [],
              spineCutStack M anchor anchorContext⟩
            ⟨q, [], (Z :: added) ++ anchorContext⟩ := by
        simpa [spineCutState, spineCutStack, hcontext,
          List.append_assoc] using hrun
      have hstep : (emptyStackPDA M).Reaches₁
          ⟨q, [], Z :: added⟩ ⟨next, [], gamma ++ added⟩ := by
        exact ⟨next, gamma, htransition, by simp⟩
      have hrun' := PDA.RetainedFrameRun.step
        (P := emptyStackPDA M) hrunAligned hstep
      exact ⟨n + 1, by
        simpa [spineCutState, spineCutStack, hcontext,
          List.append_assoc] using hrun'⟩
  | @splitLeft suffix z context q middle target Z gamma
      previous hlength hrule hright ih =>
      obtain ⟨n, hrun⟩ := ih
      exact ⟨n, by
        simpa [spineCutState, spineCutStack,
          List.append_assoc] using hrun⟩

/-- Counted global position of a zero-visible interval, together with its
retained-frame subrun. -/
public theorem VisibleSpineAnchor.exists_countedZeroVisibleInterval
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M}
    {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (hanchor : VisibleSpineAnchor M p anchor anchorSuffix
      preWord anchorContext)
    (htail : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      current currentSuffix currentContext) :
    ∃ prefixSteps tailSteps : ℕ,
      (emptyStackPDA M).ReachesIn prefixSteps
        ⟨(emptyStackPDA M).initial_state, preWord,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨spineCutState M anchor, [],
          spineCutStack M anchor anchorContext⟩ ∧
      PDA.RetainedFrameRun (emptyStackPDA M) anchorContext tailSteps
        ⟨spineCutState M anchor, [],
          spineCutStack M anchor anchorContext⟩
        ⟨spineCutState M current, [],
          spineCutStack M current currentContext⟩ ∧
      (emptyStackPDA M).ReachesIn (prefixSteps + tailSteps)
        ⟨(emptyStackPDA M).initial_state, preWord,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨spineCutState M current, [],
          spineCutStack M current currentContext⟩ := by
  obtain ⟨prefixSteps, hprefix⟩ :=
    (hanchor.concreteOperationalSpine M).exists_prefixRunIn M
  obtain ⟨tailSteps, htailRun⟩ :=
    htail.exists_retainedFrameRun M hanchor
  exact ⟨prefixSteps, tailSteps, hprefix, htailRun,
    prefixRunIn_trans_retainedFrameRun hprefix htailRun⟩

/-- Counted factorization of a concrete empty return.  `prefixSteps` locates
the parent cut globally, while the positive `returnSteps` interval pops the
selected top symbol without touching `context`. -/
@[expose]
public def CountedConcreteEmptyReturnInterval (M : DPDA Q T S)
    (completion suffix : List T) (q : State M) : Prop :=
  ∃ (beforeWord segmentWord : List T) (source : State M)
      (top : StackSymbol M) (context : List (StackSymbol M))
      (final : State M) (prefixSteps returnSteps : ℕ),
    completion = beforeWord ++ segmentWord ∧
    (emptyStackPDA M).ReachesIn prefixSteps
      ⟨(emptyStackPDA M).initial_state, beforeWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, [], top :: context⟩ ∧
    0 < returnSteps ∧
    PDA.RetainedFrameRun (emptyStackPDA M) context returnSteps
      ⟨source, segmentWord, top :: context⟩
      ⟨q, [], context⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨q, suffix, context⟩ ⟨final, [], []⟩

private theorem terminal_completion_singleton
    (M : DPDA Q T S) {a : T} {w : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [symbol.terminal a] (w.map symbol.terminal)) :
    w = [a] := by
  have h' : (characteristicGrammar M).DerivesRightmost
      ([a].map (symbol.terminal (N := Nonterminal M)))
      (w.map symbol.terminal) := by simpa using h
  have heq := h'.eq_of_map_terminal_source
  have hmap : w.map (symbol.terminal (N := Nonterminal M)) =
      [a].map symbol.terminal := by simpa using heq
  exact (List.map_injective_iff.mpr fun _ _ hsymbol =>
    symbol.terminal.inj hsymbol) hmap

private theorem oneStep_retainedFrameRun
    {P : PDA Q T S} {source target : Q} {input : List T}
    {top : S} {frame : List S}
    (hstep : P.Reaches₁ ⟨source, input, [top]⟩ ⟨target, [], []⟩) :
    PDA.RetainedFrameRun P frame 1
      ⟨source, input, top :: frame⟩ ⟨target, [], frame⟩ := by
  have hcounted : P.ReachesIn 1
      ⟨source, input, [top]⟩ ⟨target, [], []⟩ := by
    simpa using PDA.ReachesIn.step (PDA.ReachesIn.refl _) hstep
  simpa [PDA.conf.appendStack] using
    (PDA.RetainedFrameRun.ofReachesIn (frame := frame) hcounted)

/-- Every concrete empty edge exposes a counted positive retained-frame
return interval at any chosen completion of its visible prefix. -/
public theorem ConcreteEmptyEdge.countedReturnIntervalAtCompletion
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix completion : List T} (edge : ConcreteEmptyEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (completion.map symbol.terminal)) :
    CountedConcreteEmptyReturnInterval M completion suffix q := by
  cases edge with
  | @read base suffix oldWord oldContext source a Z q
      parent htransition hrule =>
      obtain ⟨beforeWord, segmentWord, hcompletion, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      have hsegmentWord : segmentWord = [a] :=
        terminal_completion_singleton M hsegment
      subst segmentWord
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hbase
      obtain ⟨prefixSteps, hprefix⟩ := hparent.exists_prefixRunIn M
      cases hparent.focusedExact M with
      | single _ _ _ _ _ _ final oldPrefix continuation =>
          have hcore : (emptyStackPDA M).Reaches₁
              ⟨source, [a], [Z]⟩ ⟨q, [], []⟩ := by
            exact Or.inl ⟨q, [], htransition, by simp⟩
          exact ⟨beforeWord, [a], source, Z, context, final,
            prefixSteps, 1, hcompletion, hprefix, by simp,
            oneStep_retainedFrameRun hcore, continuation⟩
  | @epsilon base suffix oldWord oldContext source Z q
      parent htransition hrule =>
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hp
      obtain ⟨prefixSteps, hprefix⟩ := hparent.exists_prefixRunIn M
      cases hparent.focusedExact M with
      | single _ _ _ _ _ _ final oldPrefix continuation =>
          have hcore : (emptyStackPDA M).Reaches₁
              ⟨source, [], [Z]⟩ ⟨q, [], []⟩ := by
            exact ⟨q, [], htransition, by simp⟩
          exact ⟨completion, [], source, Z, context, final,
            prefixSteps, 1, by simp, hprefix, by simp,
            oneStep_retainedFrameRun hcore, continuation⟩
  | @split base suffix oldWord leftWord oldContext source Z q
      parent hlength hrule hleft =>
      obtain ⟨beforeWord, segmentWord, hcompletion, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hbase
      obtain ⟨prefixSteps, hprefix⟩ := hparent.exists_prefixRunIn M
      obtain ⟨returnSteps, hpositive, hreturn⟩ :=
        completedSingle_exists_retainedFrameRun M
          (frame := context) hsegment
      cases hparent.focusedExact M with
      | list _ _ _ _ _ _ final oldPrefix continuation =>
          exact ⟨beforeWord, segmentWord, source, Z, context, final,
            prefixSteps, returnSteps, hcompletion, hprefix, hpositive,
            hreturn, continuation⟩

/-- Concatenating the counted prefix and retained return locates the empty
child cut after exactly `prefixSteps + returnSteps` PDA steps. -/
public theorem CountedConcreteEmptyReturnInterval.exists_globalRunIn
    (M : DPDA Q T S)
    {completion suffix : List T} {q : State M}
    (h : CountedConcreteEmptyReturnInterval M completion suffix q) :
    ∃ (context : List (StackSymbol M)) (final : State M)
        (prefixSteps returnSteps : ℕ),
      0 < returnSteps ∧
      (emptyStackPDA M).ReachesIn (prefixSteps + returnSteps)
        ⟨(emptyStackPDA M).initial_state, completion,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨q, [], context⟩ ∧
      (emptyStackPDA M).Reaches
        ⟨q, suffix, context⟩ ⟨final, [], []⟩ := by
  rcases h with ⟨beforeWord, segmentWord, source, top, context, final,
    prefixSteps, returnSteps, hcompletion, hprefix, hpositive,
    hreturn, hcontinuation⟩
  have hprefix' := (PDA.unconsumed_input_N segmentWord).mp hprefix
  have hglobal := prefixRunIn_trans_retainedFrameRun hprefix' hreturn
  subst completion
  exact ⟨context, final, prefixSteps, returnSteps, hpositive,
    by simpa [PDA.conf.appendInput] using hglobal, hcontinuation⟩

end

end DPDA_to_LR
