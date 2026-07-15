module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.EpsilonSplitSynchronization

/-!
# The residual case of epsilon/split synchronization

This file separates the easy paired-read contradiction from the genuinely
interval-sensitive paired-split case.  In particular, the useful endpoint
form below avoids rebuilding a list completion merely to exclude a
nonempty zero-visible return to the same physical list cut.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem transGen_append_input_exact_residual
    {Q₀ T₀ S₀ : Type} [Fintype Q₀] [Fintype T₀] [Fintype S₀]
    {P : PDA Q₀ T₀ S₀} {c d : PDA.conf P}
    (h : Relation.TransGen (@PDA.Reaches₁ _ _ _ _ _ _ P) c d)
    (inputSuffix : List T₀) :
    Relation.TransGen (@PDA.Reaches₁ _ _ _ _ _ _ P)
      (c.appendInput inputSuffix) (d.appendInput inputSuffix) := by
  obtain ⟨next, hfirst, hrest⟩ := Relation.TransGen.head'_iff.mp h
  have hfirstInput : P.Reaches₁
      (c.appendInput inputSuffix) (next.appendInput inputSuffix) := by
    apply PDA.reaches₁_iff_reachesIn_one.mpr
    exact (PDA.unconsumed_input_N (pda := P) inputSuffix).mp
      (PDA.reaches₁_iff_reachesIn_one.mp hfirst)
  have hrestInput := (PDA.unconsumed_input inputSuffix).mp hrest
  exact Relation.TransGen.head' hfirstInput hrestInput

/-- A useful epsilon-bearing tail cannot return to the same physical list
head.  This is the direct-usefulness variant of
`epsilonBearing_sameListCutTail_false`: the caller may already have the
combined child-completion/continuation path. -/
public theorem epsilonBearing_sameListCutTail_false_of_useful
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {q anchorTarget currentTarget final : State M}
    {gamma : List (StackSymbol M)}
    {anchorSuffix currentSuffix future : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (htail : ZeroVisibleTail M p preWord
      (PDA_to_CFG.N.list q gamma anchorTarget) anchorSuffix anchorContext
      (PDA_to_CFG.N.list q gamma currentTarget) currentSuffix currentContext)
    (hbearing : EpsilonBearingZeroVisibleTail M p preWord
      (PDA_to_CFG.N.list q gamma anchorTarget) anchorSuffix anchorContext
      (PDA_to_CFG.N.list q gamma currentTarget) currentSuffix currentContext)
    (huseful : (emptyStackPDA M).Reaches
      ⟨q, future, gamma ++ currentContext⟩ ⟨final, [], []⟩) :
    False := by
  obtain ⟨added, hcontext, hstripped⟩ :=
    htail.reachesCutWithoutAnchorContext M
  by_cases hadded : added = []
  · subst added
    have hcycle₀ := hbearing.transGen_cut M
    have hcycle := transGen_append_input_exact_residual hcycle₀ future
    have hcycle' : Relation.TransGen
        (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
        ⟨q, future, gamma ++ anchorContext⟩
        ⟨q, future, gamma ++ anchorContext⟩ := by
      simpa [spineCutState, spineCutStack, hcontext,
        PDA.conf.appendInput] using hcycle
    exact emptyStack_no_useful_cycle M hcycle'
      (by simpa [hcontext] using huseful)
  · apply emptyStack_no_useful_stack_growth M
      (q := q) (base := gamma) (extra := added)
      (context := anchorContext) (input := future) (final := final)
    · simpa [spineCutState, spineCutStack] using hstripped
    · exact hadded
    · simpa [hcontext, List.append_assoc] using huseful

/-- The paired-read constructor of an epsilon/split tail is impossible.
Both read anchors have the same deterministic output cut, so the bearing
tail is a nonempty useful return to that same physical list head. -/
public theorem epsilonBearing_pairedRead_false (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))}
    {beforeWord suffix₁ suffix₂ currentSuffix future : List T}
    {context₁ context₂ currentContext : List (StackSymbol M)}
    {q₁ target₁ next₁ q₂ target₂ next₂ final : State M}
    {a : T} {Z₁ Z₂ : StackSymbol M}
    {gamma₁ gamma₂ : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.single q₁ Z₁ target₁)
      suffix₁ beforeWord context₁)
    (transition₁ : (next₁, gamma₁) ∈
      (emptyStackPDA M).transition_fun q₁ a Z₁)
    (parent₂ : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.single q₂ Z₂ target₂)
      suffix₂ beforeWord context₂)
    (transition₂ : (next₂, gamma₂) ∈
      (emptyStackPDA M).transition_fun q₂ a Z₂)
    (tail : ZeroVisibleTail M (base ++ [symbol.terminal a])
      (beforeWord ++ [a])
      (PDA_to_CFG.N.list next₁ gamma₁ target₁) suffix₁ context₁
      (PDA_to_CFG.N.list next₂ gamma₂ target₂) currentSuffix
      currentContext)
    (bearing : EpsilonBearingZeroVisibleTail M
      (base ++ [symbol.terminal a]) (beforeWord ++ [a])
      (PDA_to_CFG.N.list next₁ gamma₁ target₁) suffix₁ context₁
      (PDA_to_CFG.N.list next₂ gamma₂ target₂) currentSuffix
      currentContext)
    (useful : (emptyStackPDA M).Reaches
      ⟨next₂, future, gamma₂ ++ currentContext⟩ ⟨final, [], []⟩) :
    False := by
  obtain ⟨hnext, hgamma, hcontext⟩ :=
    concreteRead_anchor_data_eq M parent₁ parent₂
      transition₁ transition₂
  subst next₂
  subst gamma₂
  subst context₂
  exact epsilonBearing_sameListCutTail_false_of_useful M
    tail bearing useful

/-- The counted operational content left by the paired-split constructor.
The first two intervals are the two completed `single source top next`
returns.  The last retained run is the genuinely nonempty epsilon-bearing
tail from the first return endpoint to the epsilon child cut. -/
@[expose]
public def SplitRightEpsilonIntervalResidual (M : DPDA Q T S)
    (completedWord : List T) (next target : State M)
    (gamma : List (StackSymbol M))
    (childWord epsilonSuffix splitSuffix : List T) : Prop :=
  ∃ (source : State M) (top : StackSymbol M)
      (gamma₁ context₁ splitContext epsilonContext :
        List (StackSymbol M))
      (finalEpsilon finalSplit : State M)
      (start₁ return₁ start₂ return₂ tailSteps : ℕ)
      (segment₁ segment₂ : List T),
    0 < return₁ ∧ 0 < return₂ ∧ 0 < tailSteps ∧
    (emptyStackPDA M).ReachesIn start₁
      ⟨(emptyStackPDA M).initial_state, completedWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, segment₁, top :: (gamma₁ ++ context₁)⟩ ∧
    PDA.RetainedFrameRun (emptyStackPDA M)
      (gamma₁ ++ context₁) return₁
      ⟨source, segment₁, top :: (gamma₁ ++ context₁)⟩
      ⟨next, [], gamma₁ ++ context₁⟩ ∧
    (emptyStackPDA M).ReachesIn start₂
      ⟨(emptyStackPDA M).initial_state, completedWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, segment₂, top :: (gamma ++ splitContext)⟩ ∧
    PDA.RetainedFrameRun (emptyStackPDA M)
      (gamma ++ splitContext) return₂
      ⟨source, segment₂, top :: (gamma ++ splitContext)⟩
      ⟨next, [], gamma ++ splitContext⟩ ∧
    PDA.RetainedFrameRun (emptyStackPDA M) context₁ tailSteps
      ⟨next, [], gamma₁ ++ context₁⟩
      ⟨next, [], gamma ++ epsilonContext⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨next, childWord, gamma ++ epsilonContext⟩
      ⟨target, [], epsilonContext⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨next, childWord, gamma ++ splitContext⟩
      ⟨target, [], splitContext⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨next, childWord ++ epsilonSuffix, gamma ++ epsilonContext⟩
      ⟨finalEpsilon, [], []⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨next, childWord ++ splitSuffix, gamma ++ splitContext⟩
      ⟨finalSplit, [], []⟩ ∧
    (childWord ++ epsilonSuffix).take 1 =
      (childWord ++ splitSuffix).take 1

/-- Every epsilon/split tail reduces to the counted paired-split residual.
The root constructor is excluded by the right list index, while the read
constructor is discharged by `epsilonBearing_pairedRead_false`. -/
public theorem EpsilonSplitTailData.splitRightIntervalResidual
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {next target : State M} {gamma : List (StackSymbol M)}
    {epsilonSuffix splitSuffix : List T}
    (data : EpsilonSplitTailData M childPrefix next target gamma
      epsilonSuffix splitSuffix) :
    ∃ (completedWord childWord : List T),
      SplitRightEpsilonIntervalResidual M completedWord next target gamma childWord
        epsilonSuffix splitSuffix := by
  cases data with
  | mk preWord epsilonContext splitContext base beforeWord leftWord
      splitSource splitTop splitParent splitLength splitRule splitLeft
      childPrefixEq preWordEq anchor anchorSuffix anchorContext
      anchorWitness tail bearing splitAnchor paired childWord childCompletion
      epsilonFinal splitFinal epsilonUseful splitUseful suffixLookahead
      futureLookahead =>
      cases paired with
      | read parent₁ transition₁ rule₁ parent₂ transition₂ rule₂ =>
          exact False.elim <| epsilonBearing_pairedRead_false M
            parent₁ transition₁ parent₂ transition₂
            tail bearing epsilonUseful
      | @splitRight pairedBase completedWord beforeWord₁ leftWord₁
          beforeWord₂ leftWord₂ suffix₁ suffix₂ context₁ context₂
          source returnState target₁ target₂ top gamma₁ gamma₂
          parent₁ length₁ rule₁ left₁ parent₂ length₂ rule₂ left₂
          word₁ word₂ =>
          obtain ⟨start₁, return₁, start₂, return₂,
              interval₁, interval₂, intervalOrder⟩ :=
            pairedSplitRight_intervals M parent₁ length₁ rule₁ left₁
              parent₂ length₂ rule₂ left₂ word₁ word₂
          rcases interval₁ with
            ⟨segment₁, future₁, intervalFinal₁, positive₁,
              prefix₁, retained₁, intervalUseful₁⟩
          rcases interval₂ with
            ⟨segment₂, future₂, intervalFinal₂, positive₂,
              prefix₂, retained₂, intervalUseful₂⟩
          obtain ⟨tailSteps, tailRun⟩ :=
            tail.exists_retainedFrameRun M anchorWitness
          have tailPositive : 0 < tailSteps := by
            by_contra hpositive
            have hzero : tailSteps = 0 := Nat.eq_zero_of_not_pos hpositive
            subst tailSteps
            have heq := PDA.reachesIn_zero tailRun.toReachesIn
            have hcycle₀ := bearing.transGen_cut M
            rw [heq] at hcycle₀
            have hcycle := transGen_append_input_exact_residual hcycle₀
              (childWord ++ epsilonSuffix)
            exact emptyStack_no_useful_cycle M
              (by simpa [PDA.conf.appendInput] using hcycle)
              epsilonUseful
          have gammaLength : gamma.length ≤
              PDA_to_CFG.max_push (emptyStackPDA M) := by
            rw [List.length_cons] at length₂
            exact le_trans
              (WithBot.coe_le_coe.mpr (Nat.le_succ gamma.length)) length₂
          have childRunEpsilon := completedList_reaches_with_context M
            gammaLength childCompletion (context := epsilonContext)
          have childRunSplit := completedList_reaches_with_context M
            gammaLength childCompletion (context := splitContext)
          exact ⟨preWord, childWord, source, top, gamma₁, anchorContext,
            splitContext, epsilonContext, epsilonFinal, splitFinal,
            start₁, return₁, start₂, return₂, tailSteps,
            segment₁, segment₂, positive₁, positive₂,
            tailPositive, prefix₁, retained₁, prefix₂, retained₂,
            tailRun, childRunEpsilon, childRunSplit,
            epsilonUseful, splitUseful, futureLookahead⟩

end

end DPDA_to_LR
