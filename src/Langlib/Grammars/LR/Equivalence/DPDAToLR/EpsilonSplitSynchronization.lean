module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CountedRetainedIntervals
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.PairedSplitIntervals

/-!
# The concrete overlap behind an epsilon/split conflict

An epsilon introduction and a split-right introduction of the same list
child have the same completed visible prefix.  Decomposing the epsilon
parent at its last visible event therefore produces a paired visible anchor;
the tail on that side is genuinely epsilon-bearing, while the other anchor
is the displayed split-right child itself.  This file packages that exact
configuration together with a common completion of the list child.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- All ancestry and productivity data present in an active epsilon/split
conflict after choosing one common completion of the shared list child. -/
public inductive EpsilonSplitTailData (M : DPDA Q T S)
    (childPrefix : List (symbol T (Nonterminal M)))
    (next target : State M) (gamma : List (StackSymbol M))
    (epsilonSuffix splitSuffix : List T) : Prop
  | mk
      (preWord : List T)
      (epsilonContext splitContext : List (StackSymbol M))
      (base : List (symbol T (Nonterminal M)))
      (beforeWord leftWord : List T)
      (splitSource : State M) (splitTop : StackSymbol M)
      (splitParent : ConcreteOperationalSpine M base
        (PDA_to_CFG.N.list splitSource (splitTop :: gamma) target)
        splitSuffix beforeWord splitContext)
      (splitLength : (splitTop :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (splitRule :
        (PDA_to_CFG.N.list splitSource (splitTop :: gamma) target,
          [symbol.nonterminal
              (PDA_to_CFG.N.single splitSource splitTop next),
            symbol.nonterminal
              (PDA_to_CFG.N.list next gamma target)]) ∈
          (characteristicGrammar M).rules)
      (splitLeft : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal
          (PDA_to_CFG.N.single splitSource splitTop next)]
        (leftWord.map symbol.terminal))
      (childPrefixEq : childPrefix =
        base ++ [symbol.nonterminal
          (PDA_to_CFG.N.single splitSource splitTop next)])
      (preWordEq : preWord = beforeWord ++ leftWord)
      (anchor : Nonterminal M) (anchorSuffix : List T)
      (anchorContext : List (StackSymbol M))
      (anchorWitness : VisibleSpineAnchor M childPrefix anchor anchorSuffix
        preWord anchorContext)
      (tail : ZeroVisibleTail M childPrefix preWord anchor anchorSuffix
        anchorContext (PDA_to_CFG.N.list next gamma target)
        epsilonSuffix epsilonContext)
      (bearing : EpsilonBearingZeroVisibleTail M childPrefix preWord anchor
        anchorSuffix anchorContext (PDA_to_CFG.N.list next gamma target)
        epsilonSuffix epsilonContext)
      (splitAnchor : VisibleSpineAnchor M childPrefix
        (PDA_to_CFG.N.list next gamma target) splitSuffix preWord splitContext)
      (paired : PairedVisibleAnchors M childPrefix preWord anchor anchorSuffix
        anchorContext (PDA_to_CFG.N.list next gamma target) splitSuffix
        splitContext)
      (childWord : List T)
      (childCompletion : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]
        (childWord.map symbol.terminal))
      (epsilonFinal splitFinal : State M)
      (epsilonUseful : (emptyStackPDA M).Reaches
        ⟨next, childWord ++ epsilonSuffix, gamma ++ epsilonContext⟩
        ⟨epsilonFinal, [], []⟩)
      (splitUseful : (emptyStackPDA M).Reaches
        ⟨next, childWord ++ splitSuffix, gamma ++ splitContext⟩
        ⟨splitFinal, [], []⟩)
      (suffixLookahead :
        epsilonSuffix.take 1 = splitSuffix.take 1)
      (futureLookahead :
        (childWord ++ epsilonSuffix).take 1 =
          (childWord ++ splitSuffix).take 1) :
      EpsilonSplitTailData M childPrefix next target gamma
        epsilonSuffix splitSuffix

/-- Construct the exact paired-anchor/epsilon-tail configuration from the
two active introductions.  The theorem deliberately keeps the paired
anchor abstract; inversion of `data.paired` exposes the two split-right
return intervals and their hidden contexts without losing the tail. -/
public theorem activeEpsilonSplit_tailData (M : DPDA Q T S)
    {childPrefix base : List (symbol T (Nonterminal M))}
    {epsilonSuffix splitSuffix : List T}
    {epsilonSource next target splitSource : State M}
    {epsilonTop splitTop : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (epsilonParent : ActiveSpine M childPrefix
      (PDA_to_CFG.N.single epsilonSource epsilonTop target)
      epsilonSuffix)
    (epsilonTransition : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' epsilonSource epsilonTop)
    (epsilonRule :
      (PDA_to_CFG.N.single epsilonSource epsilonTop target,
        [symbol.nonterminal
          (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules)
    (splitParent : ActiveSpine M base
      (PDA_to_CFG.N.list splitSource (splitTop :: gamma) target)
      splitSuffix)
    (splitLength : (splitTop :: gamma).length ≤
      PDA_to_CFG.max_push (emptyStackPDA M))
    (splitRule :
      (PDA_to_CFG.N.list splitSource (splitTop :: gamma) target,
        [symbol.nonterminal
            (PDA_to_CFG.N.single splitSource splitTop next),
          symbol.nonterminal
            (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules)
    (hprefix : childPrefix =
      base ++ [symbol.nonterminal
        (PDA_to_CFG.N.single splitSource splitTop next)])
    (hlook : epsilonSuffix.take 1 = splitSuffix.take 1) :
    EpsilonSplitTailData M childPrefix next target gamma
      epsilonSuffix splitSuffix := by
  obtain ⟨preWord, hpreWord⟩ :=
    prehandle_prefix_completion M epsilonRule
      (epsilonParent.derivesRightmost M)
  obtain ⟨epsilonContext, concreteEpsilonParent⟩ :=
    concreteOperationalSpine_of_activeSpine M epsilonParent hpreWord
  obtain ⟨anchor, anchorSuffix, anchorContext,
      anchorWitness, parentTail⟩ :=
    concreteEpsilonParent.zeroVisibleDecomposition M
  let tail : ZeroVisibleTail M childPrefix preWord anchor anchorSuffix
      anchorContext (PDA_to_CFG.N.list next gamma target)
      epsilonSuffix epsilonContext :=
    ZeroVisibleTail.epsilon parentTail epsilonTransition epsilonRule
  let bearing : EpsilonBearingZeroVisibleTail M childPrefix preWord anchor
      anchorSuffix anchorContext (PDA_to_CFG.N.list next gamma target)
      epsilonSuffix epsilonContext :=
    EpsilonBearingZeroVisibleTail.epsilon parentTail
      epsilonTransition epsilonRule
  have hsplitPre := hpreWord
  rw [hprefix] at hsplitPre
  obtain ⟨beforeWord, leftWord, hword, hbase, hleft⟩ :=
    CF_grammar.DerivesRightmost.append_to_terminals_split hsplitPre
  obtain ⟨splitContext, concreteSplitParent⟩ :=
    concreteOperationalSpine_of_activeSpine M splitParent hbase
  let concreteSplit : ConcreteListIntroduction M childPrefix next gamma
      target splitSuffix preWord splitContext
      (PDA_to_CFG.N.list splitSource (splitTop :: gamma) target)
      (PDA_to_CFG.N.list splitSource (splitTop :: gamma) target,
        [symbol.nonterminal
            (PDA_to_CFG.N.single splitSource splitTop next),
          symbol.nonterminal
            (PDA_to_CFG.N.list next gamma target)]) := by
    rw [hprefix]
    simpa [hword] using ConcreteListIntroduction.splitRight
      concreteSplitParent splitLength splitRule hleft
  let splitAnchor : VisibleSpineAnchor M childPrefix
      (PDA_to_CFG.N.list next gamma target) splitSuffix preWord
      splitContext := by
    rw [hprefix]
    simpa [hword] using VisibleSpineAnchor.splitRight
      concreteSplitParent splitLength splitRule hleft
  let paired := pairedVisibleAnchors_of_same_prefix M
    anchorWitness splitAnchor rfl rfl
  let epsilonIntroduction : ConcreteListIntroduction M childPrefix
      next gamma target epsilonSuffix preWord epsilonContext
      (PDA_to_CFG.N.single epsilonSource epsilonTop target)
      (PDA_to_CFG.N.single epsilonSource epsilonTop target,
        [symbol.nonterminal
          (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon concreteEpsilonParent
      epsilonTransition epsilonRule
  obtain ⟨childWord, childCompletion⟩ :=
    epsilonIntroduction.childCompletion M
  obtain ⟨epsilonFinal, epsilonContinuation⟩ :=
    epsilonIntroduction.childContinuation M
  obtain ⟨splitFinal, splitContinuation⟩ :=
    concreteSplit.childContinuation M
  have epsilonUseful := completedList_useful_with_context M
    (epsilonIntroduction.gammaLength M) childCompletion
    epsilonContinuation
  have splitUseful := completedList_useful_with_context M
    (concreteSplit.gammaLength M) childCompletion splitContinuation
  apply EpsilonSplitTailData.mk preWord epsilonContext splitContext base
    beforeWord leftWord splitSource splitTop concreteSplitParent splitLength
    splitRule hleft hprefix hword anchor anchorSuffix anchorContext
    anchorWitness tail bearing
    splitAnchor paired childWord childCompletion epsilonFinal splitFinal
    epsilonUseful splitUseful hlook
  by_cases hchildWord : childWord = []
  · subst childWord
    simpa using hlook
  · obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hchildWord
    simp

/-- The only possible paired-anchor branch of an epsilon/split conflict is
split-right/split-right.  This proposition is the fully specialized branch,
with no dependent equalities or irrelevant read case left to invert. -/
public inductive EpsilonSplitReturnData (M : DPDA Q T S)
    (next target : State M) (gamma : List (StackSymbol M))
    (epsilonSuffix splitSuffix : List T) : Prop
  | mk
      (preWord childWord : List T)
      (epsilonContext splitContext : List (StackSymbol M))
      (base : List (symbol T (Nonterminal M)))
      (anchorSuffix : List T) (anchorContext : List (StackSymbol M))
      (beforeWord₁ leftWord₁ beforeWord₂ leftWord₂ : List T)
      (source target₁ : State M) (top : StackSymbol M)
      (gamma₁ : List (StackSymbol M))
      (parent₁ : ConcreteOperationalSpine M base
        (PDA_to_CFG.N.list source (top :: gamma₁) target₁)
        anchorSuffix beforeWord₁ anchorContext)
      (length₁ : (top :: gamma₁).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (rule₁ :
        (PDA_to_CFG.N.list source (top :: gamma₁) target₁,
          [symbol.nonterminal (PDA_to_CFG.N.single source top next),
            symbol.nonterminal
              (PDA_to_CFG.N.list next gamma₁ target₁)]) ∈
          (characteristicGrammar M).rules)
      (left₁ : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single source top next)]
        (leftWord₁.map symbol.terminal))
      (parent₂ : ConcreteOperationalSpine M base
        (PDA_to_CFG.N.list source (top :: gamma) target)
        splitSuffix beforeWord₂ splitContext)
      (length₂ : (top :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (rule₂ :
        (PDA_to_CFG.N.list source (top :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single source top next),
            symbol.nonterminal
              (PDA_to_CFG.N.list next gamma target)]) ∈
          (characteristicGrammar M).rules)
      (left₂ : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single source top next)]
        (leftWord₂.map symbol.terminal))
      (word₁ : preWord = beforeWord₁ ++ leftWord₁)
      (word₂ : preWord = beforeWord₂ ++ leftWord₂)
      (tail : ZeroVisibleTail M
        (base ++ [symbol.nonterminal
          (PDA_to_CFG.N.single source top next)]) preWord
        (PDA_to_CFG.N.list next gamma₁ target₁)
        anchorSuffix anchorContext
        (PDA_to_CFG.N.list next gamma target)
        epsilonSuffix epsilonContext)
      (bearing : EpsilonBearingZeroVisibleTail M
        (base ++ [symbol.nonterminal
          (PDA_to_CFG.N.single source top next)]) preWord
        (PDA_to_CFG.N.list next gamma₁ target₁)
        anchorSuffix anchorContext
        (PDA_to_CFG.N.list next gamma target)
        epsilonSuffix epsilonContext)
      (childCompletion : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]
        (childWord.map symbol.terminal))
      (epsilonFinal splitFinal : State M)
      (epsilonUseful : (emptyStackPDA M).Reaches
        ⟨next, childWord ++ epsilonSuffix, gamma ++ epsilonContext⟩
        ⟨epsilonFinal, [], []⟩)
      (splitUseful : (emptyStackPDA M).Reaches
        ⟨next, childWord ++ splitSuffix, gamma ++ splitContext⟩
        ⟨splitFinal, [], []⟩)
      (suffixLookahead :
        epsilonSuffix.take 1 = splitSuffix.take 1)
      (futureLookahead :
        (childWord ++ epsilonSuffix).take 1 =
          (childWord ++ splitSuffix).take 1) :
      EpsilonSplitReturnData M next target gamma
        epsilonSuffix splitSuffix

/-- Eliminate the impossible read/read paired-anchor branch and expose the
two concrete split-right return intervals. -/
public theorem EpsilonSplitTailData.returnData (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {next target : State M} {gamma : List (StackSymbol M)}
    {epsilonSuffix splitSuffix : List T}
    (h : EpsilonSplitTailData M childPrefix next target gamma
      epsilonSuffix splitSuffix) :
    EpsilonSplitReturnData M next target gamma
      epsilonSuffix splitSuffix := by
  cases h with
  | mk preWord epsilonContext splitContext storedBase storedBeforeWord
      storedLeftWord storedSource storedTop storedParent storedLength
      storedRule storedLeft childPrefixEq preWordEq anchor anchorSuffix
      anchorContext anchorWitness tail bearing splitAnchor paired childWord
      childCompletion epsilonFinal splitFinal epsilonUseful splitUseful
      suffixLookahead futureLookahead =>
    cases paired with
    | read parent₁ transition₁ rule₁ parent₂ transition₂ rule₂ =>
        obtain ⟨_, hlast⟩ := append_singleton_injective childPrefixEq
        cases hlast
    | splitRight parent₁ length₁ rule₁ left₁ parent₂ length₂ rule₂
        left₂ word₁ word₂ =>
        exact EpsilonSplitReturnData.mk
          (preWord := preWord) (childWord := childWord)
          (epsilonContext := epsilonContext) (splitContext := splitContext)
          (parent₁ := parent₁) (length₁ := length₁) (rule₁ := rule₁)
          (left₁ := left₁) (parent₂ := parent₂) (length₂ := length₂)
          (rule₂ := rule₂) (left₂ := left₂) (word₁ := word₁)
          (word₂ := word₂) (tail := tail) (bearing := bearing)
          (childCompletion := childCompletion) (epsilonFinal := epsilonFinal)
          (splitFinal := splitFinal) (epsilonUseful := epsilonUseful)
          (splitUseful := splitUseful) (suffixLookahead := suffixLookahead)
          (futureLookahead := futureLookahead)

/-- If the anchor-side right-list stack already agrees with the exact child
stack, the epsilon-bearing tail is immediately a forbidden useful return to
the same list cut.  Thus every genuine residual split branch must have
different right-list stack texts. -/
public theorem epsilonSplitTail_false_of_gamma_eq (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))} {preWord : List T}
    {next target target₁ source : State M} {top : StackSymbol M}
    {gamma gamma₁ : List (StackSymbol M)}
    {beforeWord leftWord anchorSuffix epsilonSuffix : List T}
    {anchorContext epsilonContext : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.list source (top :: gamma₁) target₁)
      anchorSuffix beforeWord anchorContext)
    (length₁ : (top :: gamma₁).length ≤
      PDA_to_CFG.max_push (emptyStackPDA M))
    (rule₁ :
      (PDA_to_CFG.N.list source (top :: gamma₁) target₁,
        [symbol.nonterminal (PDA_to_CFG.N.single source top next),
          symbol.nonterminal
            (PDA_to_CFG.N.list next gamma₁ target₁)]) ∈
        (characteristicGrammar M).rules)
    (left₁ : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (PDA_to_CFG.N.single source top next)]
      (leftWord.map symbol.terminal))
    (hword : preWord = beforeWord ++ leftWord)
    (tail : ZeroVisibleTail M
      (base ++ [symbol.nonterminal
        (PDA_to_CFG.N.single source top next)]) preWord
      (PDA_to_CFG.N.list next gamma₁ target₁)
      anchorSuffix anchorContext
      (PDA_to_CFG.N.list next gamma target)
      epsilonSuffix epsilonContext)
    (bearing : EpsilonBearingZeroVisibleTail M
      (base ++ [symbol.nonterminal
        (PDA_to_CFG.N.single source top next)]) preWord
      (PDA_to_CFG.N.list next gamma₁ target₁)
      anchorSuffix anchorContext
      (PDA_to_CFG.N.list next gamma target)
      epsilonSuffix epsilonContext)
    (hgamma : gamma₁ = gamma)
    {childWord : List T}
    (childCompletion : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]
      (childWord.map symbol.terminal)) : False := by
  subst gamma₁
  let anchor : VisibleSpineAnchor M
      (base ++ [symbol.nonterminal
        (PDA_to_CFG.N.single source top next)])
      (PDA_to_CFG.N.list next gamma target₁) anchorSuffix preWord
      anchorContext := by
    simpa [hword] using VisibleSpineAnchor.splitRight
      parent₁ length₁ rule₁ left₁
  have childSpine := tail.concreteOperationalSpine M
    (anchor.concreteOperationalSpine M)
  cases childSpine.focusedExact M with
  | list _ _ _ _ _ _ final prefixPath continuation =>
      exact epsilonBearing_sameListCutTail_false M tail bearing
        (by
          rw [List.length_cons] at length₁
          exact le_trans
            (WithBot.coe_le_coe.mpr (Nat.le_succ gamma.length)) length₁)
        childCompletion continuation

end

end DPDA_to_LR
