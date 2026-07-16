module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CountedSpine
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SpineSynchronization
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.WrapperReturnNesting

/-!
# Counted intervals of paired split-right anchors

A split-right visible anchor executes the completed `single` marker as a
positive one-symbol net-pop interval.  This file retains the exact interval
position, its untouched child/outer frame, and a productive future from its
return endpoint.  For a paired split anchor it also records the exhaustive
Allen-style order of the two positive intervals.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A counted, retained, productive interval represented by one split-right
anchor.  `startSteps` is measured from the wrapper's global initial
configuration on the entire completed visible-prefix word. -/
@[expose]
public def SplitRightInterval (M : DPDA Q T S)
    (completedWord _suffix : List T)
    (source : State M) (top : StackSymbol M) (returnState : State M)
    (gamma : List (StackSymbol M)) (_target : State M)
    (context : List (StackSymbol M))
    (startSteps returnSteps : ℕ) : Prop :=
  ∃ (segmentWord futureInput : List T) (final : State M),
    0 < returnSteps ∧
    (emptyStackPDA M).ReachesIn startSteps
      ⟨(emptyStackPDA M).initial_state, completedWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, segmentWord, top :: (gamma ++ context)⟩ ∧
    PDA.RetainedFrameRun (emptyStackPDA M)
      (gamma ++ context) returnSteps
      ⟨source, segmentWord, top :: (gamma ++ context)⟩
      ⟨returnState, [], gamma ++ context⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨returnState, futureInput, gamma ++ context⟩
      ⟨final, [], []⟩

/-- Construct the counted interval directly from the retained data of a
split-right visible anchor. -/
public theorem splitRightInterval_of_anchor_data (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))}
    {completedWord beforeWord leftWord suffix : List T}
    {context : List (StackSymbol M)}
    {source returnState target : State M} {top : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (parent : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.list source (top :: gamma) target)
      suffix beforeWord context)
    (hlength : (top :: gamma).length ≤
      PDA_to_CFG.max_push (emptyStackPDA M))
    (hrule : (PDA_to_CFG.N.list source (top :: gamma) target,
        [symbol.nonterminal
            (PDA_to_CFG.N.single source top returnState),
          symbol.nonterminal
            (PDA_to_CFG.N.list returnState gamma target)]) ∈
      (characteristicGrammar M).rules)
    (hleft : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal
        (PDA_to_CFG.N.single source top returnState)]
      (leftWord.map symbol.terminal))
    (hword : completedWord = beforeWord ++ leftWord) :
    ∃ startSteps returnSteps,
      SplitRightInterval M completedWord suffix source top returnState
        gamma target context startSteps returnSteps := by
  obtain ⟨startSteps, hprefix⟩ := parent.exists_prefixRunIn M
  obtain ⟨returnSteps, hreturnPositive, hreturn⟩ :=
    completedSingle_exists_retainedFrameRun M
      (frame := gamma ++ context) hleft
  let introduction : ConcreteListIntroduction M
      (base ++ [symbol.nonterminal
        (PDA_to_CFG.N.single source top returnState)])
      returnState gamma target suffix completedWord context
      (PDA_to_CFG.N.list source (top :: gamma) target)
      (PDA_to_CFG.N.list source (top :: gamma) target,
        [symbol.nonterminal
            (PDA_to_CFG.N.single source top returnState),
          symbol.nonterminal
            (PDA_to_CFG.N.list returnState gamma target)]) := by
    simpa [hword] using ConcreteListIntroduction.splitRight
      parent hlength hrule hleft
  obtain ⟨childWord, hchild⟩ := introduction.childCompletion M
  obtain ⟨final, hcontinuation⟩ := introduction.childContinuation M
  have hgamma : gamma.length ≤
      PDA_to_CFG.max_push (emptyStackPDA M) := by
    rw [List.length_cons] at hlength
    exact le_trans (WithBot.coe_le_coe.mpr (Nat.le_succ gamma.length))
      hlength
  have huseful := completedList_useful_with_context M
    (gamma := gamma) (context := context)
    (w := childWord) (suffix := suffix)
    hgamma hchild hcontinuation
  refine ⟨startSteps, returnSteps, leftWord, childWord ++ suffix, final,
    hreturnPositive, ?_, hreturn, huseful⟩
  have hprefix' := (PDA.unconsumed_input_N
    (pda := emptyStackPDA M) leftWord).mp hprefix
  subst completedWord
  simpa [PDA.conf.appendInput, List.append_assoc] using hprefix'

/-- The exhaustive relative order of two positive half-open return
intervals `[start, start + length]`.  Equal starts and equal finishes are
kept separate because they lead to different synchronization arguments. -/
@[expose]
public def ReturnIntervalOrder
    (start₁ length₁ start₂ length₂ : ℕ) : Prop :=
  (start₁ = start₂ ∧ start₁ + length₁ = start₂ + length₂) ∨
  (start₁ = start₂ ∧ start₁ + length₁ < start₂ + length₂) ∨
  (start₁ = start₂ ∧ start₂ + length₂ < start₁ + length₁) ∨
  (start₁ + length₁ < start₂) ∨
  (start₁ + length₁ = start₂) ∨
  (start₁ < start₂ ∧ start₂ < start₁ + length₁ ∧
    start₁ + length₁ < start₂ + length₂) ∨
  (start₁ < start₂ ∧
    start₁ + length₁ = start₂ + length₂) ∨
  (start₁ < start₂ ∧
    start₂ + length₂ < start₁ + length₁) ∨
  (start₂ + length₂ < start₁) ∨
  (start₂ + length₂ = start₁) ∨
  (start₂ < start₁ ∧ start₁ < start₂ + length₂ ∧
    start₂ + length₂ < start₁ + length₁) ∨
  (start₂ < start₁ ∧
    start₂ + length₂ = start₁ + length₁) ∨
  (start₂ < start₁ ∧
    start₁ + length₁ < start₂ + length₂)

/-- Every pair of positive return intervals has one of the thirteen standard
relative orders. -/
public theorem returnIntervalOrder_total
    {start₁ length₁ start₂ length₂ : ℕ}
    (hpositive₁ : 0 < length₁) (hpositive₂ : 0 < length₂) :
    ReturnIntervalOrder start₁ length₁ start₂ length₂ := by
  unfold ReturnIntervalOrder
  omega

/-- The two sides of a paired split-right anchor expose counted retained
return intervals and their exhaustive relative order. -/
public theorem pairedSplitRight_intervals (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))} {completedWord : List T}
    {beforeWord₁ leftWord₁ beforeWord₂ leftWord₂ : List T}
    {suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {source returnState target₁ target₂ : State M}
    {top : StackSymbol M}
    {gamma₁ gamma₂ : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.list source (top :: gamma₁) target₁)
      suffix₁ beforeWord₁ context₁)
    (length₁ : (top :: gamma₁).length ≤
      PDA_to_CFG.max_push (emptyStackPDA M))
    (rule₁ : (PDA_to_CFG.N.list source (top :: gamma₁) target₁,
        [symbol.nonterminal
            (PDA_to_CFG.N.single source top returnState),
          symbol.nonterminal
            (PDA_to_CFG.N.list returnState gamma₁ target₁)]) ∈
      (characteristicGrammar M).rules)
    (left₁ : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal
        (PDA_to_CFG.N.single source top returnState)]
      (leftWord₁.map symbol.terminal))
    (parent₂ : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.list source (top :: gamma₂) target₂)
      suffix₂ beforeWord₂ context₂)
    (length₂ : (top :: gamma₂).length ≤
      PDA_to_CFG.max_push (emptyStackPDA M))
    (rule₂ : (PDA_to_CFG.N.list source (top :: gamma₂) target₂,
        [symbol.nonterminal
            (PDA_to_CFG.N.single source top returnState),
          symbol.nonterminal
            (PDA_to_CFG.N.list returnState gamma₂ target₂)]) ∈
      (characteristicGrammar M).rules)
    (left₂ : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal
        (PDA_to_CFG.N.single source top returnState)]
      (leftWord₂.map symbol.terminal))
    (word₁ : completedWord = beforeWord₁ ++ leftWord₁)
    (word₂ : completedWord = beforeWord₂ ++ leftWord₂) :
    ∃ start₁ return₁ start₂ return₂,
      SplitRightInterval M completedWord suffix₁ source top returnState
          gamma₁ target₁ context₁ start₁ return₁ ∧
      SplitRightInterval M completedWord suffix₂ source top returnState
          gamma₂ target₂ context₂ start₂ return₂ ∧
      ReturnIntervalOrder start₁ return₁ start₂ return₂ := by
  obtain ⟨start₁, return₁, interval₁⟩ :=
    splitRightInterval_of_anchor_data M parent₁ length₁
      rule₁ left₁ word₁
  obtain ⟨start₂, return₂, interval₂⟩ :=
    splitRightInterval_of_anchor_data M parent₂ length₂
      rule₂ left₂ word₂
  rcases interval₁ with
    ⟨segment₁, future₁, final₁, positive₁,
      prefix₁, retained₁, useful₁⟩
  rcases interval₂ with
    ⟨segment₂, future₂, final₂, positive₂,
      prefix₂, retained₂, useful₂⟩
  exact ⟨start₁, return₁, start₂, return₂,
    ⟨segment₁, future₁, final₁, positive₁,
      prefix₁, retained₁, useful₁⟩,
    ⟨segment₂, future₂, final₂, positive₂,
      prefix₂, retained₂, useful₂⟩,
    returnIntervalOrder_total positive₁ positive₂⟩

end

end DPDA_to_LR
