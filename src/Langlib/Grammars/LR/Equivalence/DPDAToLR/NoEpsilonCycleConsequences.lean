module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.HeadPairs
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SpineEdges
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulCycles
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulEpsilonCycles
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.TransitionRuns
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SpineSynchronization
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ConcreteReturnClassifier
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.EpsilonSplitResidual
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.EpsilonEpsilonHeads

/-!
# Hypothesis-driven closure of the remaining epsilon-head cases

This module keeps the three hard branches of `epsilonIntroducingHeadsUnique`
separate from `NoEpsilonCycle`.  They all follow from the same
boundary-sensitive paired-anchor synchronization hypothesis used by the
empty-return classifier.
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

/-- An epsilon-bearing tail which starts at the same boundary-sensitive
position as its displayed list endpoint is a forbidden useful return to that
list cut. -/
public theorem epsilonBearing_sameListPosition_false_of_useful
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor : Nonterminal M} {anchorSuffix suffix future : List T}
    {anchorContext comparisonContext currentContext :
      List (StackSymbol M)}
    {q target final : State M} {gamma : List (StackSymbol M)}
    (tail : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      (PDA_to_CFG.N.list q gamma target) suffix currentContext)
    (bearing : EpsilonBearingZeroVisibleTail M p preWord anchor
      anchorSuffix anchorContext
      (PDA_to_CFG.N.list q gamma target) suffix currentContext)
    (hposition : leftmostEpsilonPositionOf M anchor anchorContext =
      leftmostEpsilonPositionOf M
        (PDA_to_CFG.N.list q gamma target) comparisonContext)
    (useful : (emptyStackPDA M).Reaches
      ⟨q, future, gamma ++ currentContext⟩ ⟨final, [], []⟩) :
    False := by
  cases anchor with
  | start => cases hposition
  | single source top anchorTarget => cases hposition
  | list anchorState displayed anchorTarget =>
      simp only [leftmostEpsilonPositionOf] at hposition
      injection hposition with hstate hdisplayed hcontext
      subst anchorState
      subst displayed
      subst anchorContext
      exact epsilonBearing_sameListCutTail_false_of_useful M
        tail bearing useful

/-- The paired-anchor position theorem eliminates the epsilon/split branch
after `activeEpsilonSplit_tailData` has exposed its common child and useful
futures. -/
public theorem EpsilonSplitTailData.false_of_productivePositions
    (M : DPDA Q T S)
    (hpositions : ProductivePairedVisibleAnchorPositionsEqual M)
    {childPrefix : List (symbol T (Nonterminal M))}
    {next target : State M} {gamma : List (StackSymbol M)}
    {epsilonSuffix splitSuffix : List T}
    (data : EpsilonSplitTailData M childPrefix next target gamma
      epsilonSuffix splitSuffix) : False := by
  cases data with
  | mk preWord epsilonContext splitContext base beforeWord leftWord
      splitSource splitTop splitParent splitLength splitRule splitLeft
      childPrefixEq preWordEq anchor anchorSuffix anchorContext
      anchorWitness tail bearing splitAnchor paired childWord childCompletion
      epsilonFinal splitFinal epsilonUseful splitUseful suffixLookahead
      futureLookahead =>
      have anchorUseful : (emptyStackPDA M).Reaches
          ⟨spineCutState M anchor, childWord ++ epsilonSuffix,
            spineCutStack M anchor anchorContext⟩
          ⟨epsilonFinal, [], []⟩ := by
        have lifted :=
          (PDA.unconsumed_input (childWord ++ epsilonSuffix)).mp
            (tail.reaches_cut M)
        have lifted' : (emptyStackPDA M).Reaches
            ⟨spineCutState M anchor, childWord ++ epsilonSuffix,
              spineCutStack M anchor anchorContext⟩
            ⟨next, childWord ++ epsilonSuffix,
              gamma ++ epsilonContext⟩ := by
          simpa [PDA.conf.appendInput, spineCutState, spineCutStack]
            using lifted
        exact lifted'.trans epsilonUseful
      have hposition := hpositions childPrefix preWord anchor
        (PDA_to_CFG.N.list next gamma target)
        anchorSuffix splitSuffix anchorContext splitContext
        (childWord ++ epsilonSuffix) (childWord ++ splitSuffix)
        epsilonFinal splitFinal paired anchorUseful splitUseful
        futureLookahead
      exact epsilonBearing_sameListPosition_false_of_useful M
        tail bearing hposition epsilonUseful

/-- Active epsilon/split introductions of one list child are impossible once
productive paired anchors have equal boundary-sensitive positions. -/
public theorem activeEpsilonSplit_false_of_productivePositions
    (M : DPDA Q T S)
    (hpositions : ProductivePairedVisibleAnchorPositionsEqual M)
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
    (hlook : epsilonSuffix.take 1 = splitSuffix.take 1) : False := by
  exact (activeEpsilonSplit_tailData M epsilonParent epsilonTransition
    epsilonRule splitParent splitLength splitRule hprefix hlook).false_of_productivePositions
      M hpositions

/-- Symmetric callable form for the split/epsilon branch. -/
public theorem activeSplitEpsilon_false_of_productivePositions
    (M : DPDA Q T S)
    (hpositions : ProductivePairedVisibleAnchorPositionsEqual M)
    {childPrefix base : List (symbol T (Nonterminal M))}
    {splitSuffix epsilonSuffix : List T}
    {splitSource next target epsilonSource : State M}
    {splitTop epsilonTop : StackSymbol M}
    {gamma : List (StackSymbol M)}
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
    (hprefix :
      base ++ [symbol.nonterminal
        (PDA_to_CFG.N.single splitSource splitTop next)] = childPrefix)
    (hlook : splitSuffix.take 1 = epsilonSuffix.take 1) : False := by
  exact activeEpsilonSplit_false_of_productivePositions M hpositions
    epsilonParent epsilonTransition epsilonRule
    splitParent splitLength splitRule hprefix.symm hlook.symm

/-- Two active epsilon introductions of the same list child have equal
source state and exposed stack symbol under the paired-position hypothesis. -/
public theorem activeEpsilonEpsilon_heads_eq_of_productivePositions
    (M : DPDA Q T S)
    (hpositions : ProductivePairedVisibleAnchorPositionsEqual M)
    {childPrefix : List (symbol T (Nonterminal M))}
    {suffix₁ suffix₂ : List T}
    {q₁ q₂ next target : State M}
    {top₁ top₂ : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (parent₁ : ActiveSpine M childPrefix
      (PDA_to_CFG.N.single q₁ top₁ target) suffix₁)
    (transition₁ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₁ top₁)
    (rule₁ : (PDA_to_CFG.N.single q₁ top₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (parent₂ : ActiveSpine M childPrefix
      (PDA_to_CFG.N.single q₂ top₂ target) suffix₂)
    (transition₂ : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' q₂ top₂)
    (rule₂ : (PDA_to_CFG.N.single q₂ top₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ ∧ top₁ = top₂ := by
  obtain ⟨preWord, hp⟩ :=
    prehandle_prefix_completion M rule₁ (parent₁.derivesRightmost M)
  obtain ⟨context₁, concreteParent₁⟩ :=
    concreteOperationalSpine_of_activeSpine M parent₁ hp
  obtain ⟨context₂, concreteParent₂⟩ :=
    concreteOperationalSpine_of_activeSpine M parent₂ hp
  obtain ⟨anchor₁, anchorSuffix₁, anchorContext₁,
      leftAnchor, leftTail⟩ :=
    concreteParent₁.zeroVisibleDecomposition M
  obtain ⟨anchor₂, anchorSuffix₂, anchorContext₂,
      rightAnchor, rightTail⟩ :=
    concreteParent₂.zeroVisibleDecomposition M
  let paired := pairedVisibleAnchors_of_same_prefix M
    leftAnchor rightAnchor rfl rfl
  let introduction₁ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₁ preWord context₁
      (PDA_to_CFG.N.single q₁ top₁ target)
      (PDA_to_CFG.N.single q₁ top₁ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon concreteParent₁ transition₁ rule₁
  let introduction₂ : ConcreteListIntroduction M childPrefix next gamma
      target suffix₂ preWord context₂
      (PDA_to_CFG.N.single q₂ top₂ target)
      (PDA_to_CFG.N.single q₂ top₂ target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon concreteParent₂ transition₂ rule₂
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
      ⟨q₁, childWord ++ suffix₁, top₁ :: context₁⟩
      ⟨next, childWord ++ suffix₁, gamma ++ context₁⟩ := by
    have hcore : (emptyStackPDA M).Reaches₁
        ⟨q₁, [], top₁ :: context₁⟩
        ⟨next, [], gamma ++ context₁⟩ :=
      ⟨next, gamma, transition₁, by simp⟩
    apply PDA.reaches₁_iff_reachesIn_one.mpr
    have hlift := (PDA.unconsumed_input_N
      (pda := emptyStackPDA M) (childWord ++ suffix₁)).mp
      (PDA.reaches₁_iff_reachesIn_one.mp hcore)
    simpa [PDA.conf.appendInput] using hlift
  have parentStep₂ : (emptyStackPDA M).Reaches₁
      ⟨q₂, childWord ++ suffix₂, top₂ :: context₂⟩
      ⟨next, childWord ++ suffix₂, gamma ++ context₂⟩ := by
    have hcore : (emptyStackPDA M).Reaches₁
        ⟨q₂, [], top₂ :: context₂⟩
        ⟨next, [], gamma ++ context₂⟩ :=
      ⟨next, gamma, transition₂, by simp⟩
    apply PDA.reaches₁_iff_reachesIn_one.mpr
    have hlift := (PDA.unconsumed_input_N
      (pda := emptyStackPDA M) (childWord ++ suffix₂)).mp
      (PDA.reaches₁_iff_reachesIn_one.mp hcore)
    simpa [PDA.conf.appendInput] using hlift
  have parentUseful₁ :=
    (Relation.ReflTransGen.single parentStep₁).trans childUseful₁
  have parentUseful₂ :=
    (Relation.ReflTransGen.single parentStep₂).trans childUseful₂
  have anchorUseful₁ : (emptyStackPDA M).Reaches
      ⟨spineCutState M anchor₁, childWord ++ suffix₁,
        spineCutStack M anchor₁ anchorContext₁⟩
      ⟨final₁, [], []⟩ := by
    have lifted := (PDA.unconsumed_input (childWord ++ suffix₁)).mp
      (leftTail.reaches_cut M)
    have lifted' : (emptyStackPDA M).Reaches
        ⟨spineCutState M anchor₁, childWord ++ suffix₁,
          spineCutStack M anchor₁ anchorContext₁⟩
        ⟨q₁, childWord ++ suffix₁, top₁ :: context₁⟩ := by
      simpa [PDA.conf.appendInput, spineCutState, spineCutStack]
        using lifted
    exact lifted'.trans parentUseful₁
  have anchorUseful₂ : (emptyStackPDA M).Reaches
      ⟨spineCutState M anchor₂, childWord ++ suffix₂,
        spineCutStack M anchor₂ anchorContext₂⟩
      ⟨final₂, [], []⟩ := by
    have lifted := (PDA.unconsumed_input (childWord ++ suffix₂)).mp
      (rightTail.reaches_cut M)
    have lifted' : (emptyStackPDA M).Reaches
        ⟨spineCutState M anchor₂, childWord ++ suffix₂,
          spineCutStack M anchor₂ anchorContext₂⟩
        ⟨q₂, childWord ++ suffix₂, top₂ :: context₂⟩ := by
      simpa [PDA.conf.appendInput, spineCutState, spineCutStack]
        using lifted
    exact lifted'.trans parentUseful₂
  have futureLook := take_one_append_eq (common := childWord) hlook
  have hposition := hpositions childPrefix preWord anchor₁ anchor₂
    anchorSuffix₁ anchorSuffix₂ anchorContext₁ anchorContext₂
    (childWord ++ suffix₁) (childWord ++ suffix₂)
    final₁ final₂ paired anchorUseful₁ anchorUseful₂ futureLook
  exact concreteEpsilonEpsilon_heads_eq_of_anchor_position_eq M
    concreteParent₁ transition₁ rule₁
    concreteParent₂ transition₂ rule₂
    leftAnchor rightAnchor leftTail rightTail hposition hlook

@[simp]
private theorem not_isEpsilonRule_read_for_positions (M : DPDA Q T S)
    {q target next : State M} {a : T} {Z : StackSymbol M}
    {gamma : List (StackSymbol M)} :
    ¬ IsEpsilonRule M
      (PDA_to_CFG.N.single q Z target,
        [symbol.terminal a,
          symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) := by
  rintro ⟨q', target', next', Z', gamma', _, heq⟩
  have hrhs := congrArg Prod.snd heq
  simp at hrhs

@[simp]
private theorem not_isEpsilonRule_split_for_positions (M : DPDA Q T S)
    {q middle target : State M} {Z : StackSymbol M}
    {gamma : List (StackSymbol M)} :
    ¬ IsEpsilonRule M
      (PDA_to_CFG.N.list q (Z :: gamma) target,
        [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
          symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) := by
  rintro ⟨q', target', next', Z', gamma', _, heq⟩
  have hlhs := congrArg Prod.fst heq
  cases hlhs

@[simp]
private theorem not_isEpsilonRule_start_for_positions (M : DPDA Q T S)
    {target : State M} :
    ¬ IsEpsilonRule M
      (PDA_to_CFG.N.start,
        [symbol.nonterminal (PDA_to_CFG.N.list
          (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target)]) := by
  rintro ⟨q, target', next, Z, gamma, _, heq⟩
  have hlhs := congrArg Prod.fst heq
  cases hlhs

private theorem emptyStack_epsilon_view_for_positions (M : DPDA Q T S)
    {q next : State M} {Z : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (h : (next, gamma) ∈ (emptyStackPDA M).transition_fun' q Z) :
    (q = Sum.inr 0 ∧ Z = none ∧
      next = Sum.inl M.firstFinal.initial_state ∧
      gamma = [some M.firstFinal.start_symbol, none]) ∨
    (∃ (source target : Q × Bool) (top : S) (replacement : List S),
      q = Sum.inl source ∧ Z = some top ∧ next = Sum.inl target ∧
      gamma = replacement.map some ∧
      (target, replacement) ∈
        M.firstFinal.toPDA.transition_fun' source top) ∨
    (next = Sum.inr 1 ∧ gamma = []) := by
  classical
  cases q with
  | inr i =>
      rcases i with ⟨i, hi⟩
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · cases Z with
        | none =>
            left
            simpa [emptyStackPDA, PDA_FS_to_ES_pda,
              PDA_FS_to_ES_eps] using h
        | some Z =>
            simp [emptyStackPDA, PDA_FS_to_ES_pda,
              PDA_FS_to_ES_eps] at h
      · right
        right
        simpa [emptyStackPDA, PDA_FS_to_ES_pda,
          PDA_FS_to_ES_eps] using h
  | inl source =>
      cases Z with
      | none =>
          right
          right
          change (next, gamma) ∈
            (if source ∈ M.firstFinal.toPDA.final_states then
              {(Sum.inr 1, [])} else ∅) at h
          split_ifs at h with hfinal
          · simpa using h
          · simp at h
      | some top =>
          change (next, gamma) ∈
            ((fun out : (Q × Bool) × List S =>
              (Sum.inl out.1, out.2.map some)) ''
                M.firstFinal.toPDA.transition_fun' source top ∪
              if source ∈ M.firstFinal.toPDA.final_states then
                {(Sum.inr 1, [])} else ∅) at h
          rcases h with hsimulation | hdrain
          · rcases hsimulation with
              ⟨⟨target, replacement⟩, htransition, heq⟩
            right
            left
            rcases heq with ⟨rfl, rfl⟩
            exact ⟨source, target, top, replacement,
              rfl, rfl, rfl, rfl, htransition⟩
          · right
            right
            split_ifs at hdrain with hfinal
            · simpa using hdrain
            · simp at hdrain

/-- Productive paired-anchor position synchronization discharges every
epsilon-bearing case of active introducing-head uniqueness. -/
public theorem epsilonIntroducingHeadsUnique_of_productivePositions
    (M : DPDA Q T S)
    (hpositions : ProductivePairedVisibleAnchorPositionsEqual M) :
    EpsilonIntroducingHeadsUnique M := by
  intro childPrefix child suffix₁ suffix₂
    parentPrefix₁ parentPrefix₂ parent₁ parent₂ rule₁ rule₂
    hlist h₁ h₂ hlook hepsilon
  have hv₁ := listIntroduction_of_introduces M hlist h₁
  have hv₂ := listIntroduction_of_introduces M hlist h₂
  generalize hprefix : childPrefix = childPrefix₂ at hv₂
  generalize hchild : child = child₂ at hv₂
  cases hv₁ <;> cases hv₂ <;>
    (try simp only [not_isEpsilonRule_read_for_positions,
      not_isEpsilonRule_split_for_positions,
      not_isEpsilonRule_start_for_positions,
      false_or, or_false] at hepsilon) <;>
    simp only [activeDescriptor]
  case read.epsilon =>
    rename_i qRead targetRead nextRead a ZRead gammaRead
      readTransition readRule readParent
      qEpsilon targetEpsilon nextEpsilon ZEpsilon gammaEpsilon
      epsilonTransition epsilonRule epsilonParent
    injection hchild with hnext hgamma htarget
    subst nextEpsilon
    subst gammaEpsilon
    subst targetEpsilon
    exact False.elim (activeRead_epsilon_false M
      readParent readTransition readRule epsilonParent
      epsilonTransition epsilonRule hprefix)
  case epsilon.read =>
    rename_i qEpsilon targetEpsilon nextEpsilon ZEpsilon gammaEpsilon
      epsilonTransition epsilonRule epsilonParent
      qRead targetRead nextRead a ZRead gammaRead
      readTransition readRule readParent
    injection hchild with hnext hgamma htarget
    subst nextRead
    subst gammaRead
    subst targetRead
    exact False.elim (activeRead_epsilon_false M
      readParent readTransition readRule epsilonParent
      epsilonTransition epsilonRule hprefix.symm)
  case epsilon.epsilon =>
    rename_i q₁ target₁ next₁ top₁ gamma₁
      transition₁ epsilonRule₁ epsilonParent₁
      q₂ target₂ next₂ top₂ gamma₂
      transition₂ epsilonRule₂ epsilonParent₂
    injection hchild with hnext hgamma htarget
    subst next₂
    subst gamma₂
    subst target₂
    rw [← hprefix] at epsilonParent₂
    obtain ⟨hq, htop⟩ :=
      activeEpsilonEpsilon_heads_eq_of_productivePositions M hpositions
        epsilonParent₁ transition₁ epsilonRule₁
        epsilonParent₂ transition₂ epsilonRule₂ hlook
    simp [hq, htop]
  case epsilon.split =>
    rename_i epsilonSource target₁ next₁ epsilonTop gamma₁
      epsilonTransition epsilonRule epsilonParent
      splitSource middle₂ target₂ splitTop gamma₂
      splitLength splitRule splitParent
    injection hchild with hnext hgamma htarget
    subst middle₂
    subst gamma₂
    subst target₂
    exact False.elim
      (activeEpsilonSplit_false_of_productivePositions M hpositions
        epsilonParent epsilonTransition epsilonRule
        splitParent splitLength splitRule hprefix hlook)
  case epsilon.start htransition₁ hrule₁ hparent₁
      target₂ hparent₂ hrule₂ =>
    injection hchild with hnext hgamma htarget
    change _ = Sum.inr 0 at hnext
    obtain hboot | hsimulation | hdrain :=
      emptyStack_epsilon_view_for_positions M htransition₁
    · have hbad : (Sum.inl M.firstFinal.initial_state : State M) =
          Sum.inr 0 := hboot.2.2.1.symm.trans hnext
      cases hbad
    · rcases hsimulation with
        ⟨source, target, top, replacement, _, _, hnext', _, _⟩
      have hbad : (Sum.inl target : State M) = Sum.inr 0 :=
        hnext'.symm.trans hnext
      cases hbad
    · have hbad : (1 : Fin 2) = 0 :=
        Sum.inr.inj (hdrain.1.symm.trans hnext)
      omega
  case split.epsilon =>
    rename_i splitSource middle₁ target₁ splitTop gamma₁
      splitLength splitRule splitParent
      epsilonSource target₂ next₂ epsilonTop gamma₂
      epsilonTransition epsilonRule epsilonParent
    injection hchild with hnext hgamma htarget
    subst next₂
    subst gamma₂
    subst target₂
    exact False.elim
      (activeSplitEpsilon_false_of_productivePositions M hpositions
        splitParent splitLength splitRule
        epsilonParent epsilonTransition epsilonRule hprefix hlook)
  case start.epsilon q₂ target₂ next₂ Z₂ gamma₂
      htransition₂ hrule₂ hparent₂ =>
    injection hchild with hnext hgamma htarget
    change (Sum.inr 0 : State M) = next₂ at hnext
    obtain hboot | hsimulation | hdrain :=
      emptyStack_epsilon_view_for_positions M htransition₂
    · have hbad : (Sum.inr 0 : State M) =
          Sum.inl M.firstFinal.initial_state :=
        hnext.trans hboot.2.2.1
      cases hbad
    · rcases hsimulation with
        ⟨source, target, top, replacement, _, _, hnext', _, _⟩
      have hbad : (Sum.inr 0 : State M) = Sum.inl target :=
        hnext.trans hnext'
      cases hbad
    · have hbad : (0 : Fin 2) = 1 :=
        Sum.inr.inj (hnext.trans hdrain.1)
      omega

end

end DPDA_to_LR
