module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SamePrefixTransitionReturns
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CrossInputDeterminism
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.LeftmostEpsilonTrace

/-!
# Structural residual for same-prefix epsilon returns

The read-generated part of same-prefix empty-return synchronization is already
settled by `concreteReadEmptyReturn_samePrefix_state_eq`.  This file records
all of the ancestry which remains when the transition-generated edge is an
epsilon edge.  In particular, it does not identify the two empty-list
children: their return states are deliberately kept distinct.

The resulting proposition is the narrow structural theorem still needed by
the concrete empty-return classifier.  It retains a common terminal
completion, the paired last-visible anchors, both zero-visible tails, the
genuinely epsilon-bearing left tail, and both useful continuations.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Complete ancestry and productivity data for an epsilon-generated empty
return compared with an arbitrary empty return at the same visible prefix.

The two child indices remain `list q₁ [] q₁` and `list q₂ [] q₂`;
assuming them equal here would be circular. -/
@[expose]
public def SamePrefixEpsilonReturnData (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) (q₁ q₂ : State M)
    (suffix₁ suffix₂ : List T) : Prop :=
  ∃ (completion : List T)
      (context₁ context₂ : List (StackSymbol M))
      (anchor₁ anchor₂ : Nonterminal M)
      (anchorSuffix₁ anchorSuffix₂ : List T)
      (anchorContext₁ anchorContext₂ : List (StackSymbol M)),
    VisibleSpineAnchor M p anchor₁ anchorSuffix₁ completion anchorContext₁ ∧
    VisibleSpineAnchor M p anchor₂ anchorSuffix₂ completion anchorContext₂ ∧
    ZeroVisibleTail M p completion anchor₁ anchorSuffix₁ anchorContext₁
      (PDA_to_CFG.N.list q₁ [] q₁) suffix₁ context₁ ∧
    ZeroVisibleTail M p completion anchor₂ anchorSuffix₂ anchorContext₂
      (PDA_to_CFG.N.list q₂ [] q₂) suffix₂ context₂ ∧
    EpsilonBearingZeroVisibleTail M p completion anchor₁ anchorSuffix₁
      anchorContext₁ (PDA_to_CFG.N.list q₁ [] q₁) suffix₁ context₁ ∧
    PairedVisibleAnchors M p completion
      anchor₁ anchorSuffix₁ anchorContext₁
      anchor₂ anchorSuffix₂ anchorContext₂ ∧
    ∃ (final₁ final₂ : State M),
      (emptyStackPDA M).Reaches
          ⟨q₁, suffix₁, context₁⟩ ⟨final₁, [], []⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨q₂, suffix₂, context₂⟩ ⟨final₂, [], []⟩ ∧
      suffix₁.take 1 = suffix₂.take 1

/-- The exact remaining semantic statement.  Unlike the earlier
`SamePrefixEpsilonReturnResidual`, this property exposes the paired structural
history required by an interval/ancestry proof. -/
@[expose]
public def SamePrefixEpsilonReturnsStateUnique (M : DPDA Q T S) : Prop :=
  ∀ (p : List (symbol T (Nonterminal M))) (q₁ q₂ : State M)
      (suffix₁ suffix₂ : List T),
    SamePrefixEpsilonReturnData M p q₁ q₂ suffix₁ suffix₂ →
      q₁ = q₂

/-- Two productive zero-visible tails whose anchors denote the same physical
displayed-stack position have the same empty-list return state.  This is the
forward synchronization principle used for root/root and read/read paired
anchors; it does not assume equal operational step counts. -/
public theorem zeroVisibleEmptyList_state_eq_of_anchor_position_eq
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {completion : List T}
    {anchor₁ anchor₂ : Nonterminal M}
    {anchorSuffix₁ anchorSuffix₂ suffix₁ suffix₂ : List T}
    {anchorContext₁ anchorContext₂ context₁ context₂ :
      List (StackSymbol M)}
    {q₁ q₂ final₁ final₂ : State M}
    (leftAnchor : VisibleSpineAnchor M p anchor₁ anchorSuffix₁
      completion anchorContext₁)
    (rightAnchor : VisibleSpineAnchor M p anchor₂ anchorSuffix₂
      completion anchorContext₂)
    (leftTail : ZeroVisibleTail M p completion anchor₁ anchorSuffix₁
      anchorContext₁ (PDA_to_CFG.N.list q₁ [] q₁) suffix₁ context₁)
    (rightTail : ZeroVisibleTail M p completion anchor₂ anchorSuffix₂
      anchorContext₂ (PDA_to_CFG.N.list q₂ [] q₂) suffix₂ context₂)
    (hposition : leftmostEpsilonPositionOf M anchor₁ anchorContext₁ =
      leftmostEpsilonPositionOf M anchor₂ anchorContext₂)
    (useful₁ : (emptyStackPDA M).Reaches
      ⟨q₁, suffix₁, context₁⟩ ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ⟨q₂, suffix₂, context₂⟩ ⟨final₂, [], []⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ := by
  let start := leftmostEpsilonPositionOf M anchor₁ anchorContext₁
  have trace₁ : LeftmostEpsilonTrace M start (.list q₁ [] context₁) := by
    simpa [start, leftmostEpsilonPositionOf] using
      leftTail.leftmostEpsilonTrace M
  have trace₂ : LeftmostEpsilonTrace M start (.list q₂ [] context₂) := by
    simpa [start, hposition, leftmostEpsilonPositionOf] using
      rightTail.leftmostEpsilonTrace M
  have anchorRun₁ := (PDA.unconsumed_input suffix₁).mp
    (leftAnchor.prefixPath M)
  have anchorRun₂ := (PDA.unconsumed_input suffix₂).mp
    (rightAnchor.prefixPath M)
  have global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, completion ++ suffix₁,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₁) := by
    change (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, completion ++ suffix₁,
        [(emptyStackPDA M).start_symbol]⟩
      ((leftmostEpsilonPositionOf M anchor₁ anchorContext₁).conf M suffix₁)
    rw [leftmostEpsilonPositionOf_conf]
    simpa [PDA.conf.appendInput] using anchorRun₁
  have global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, completion ++ suffix₂,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₂) := by
    change (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, completion ++ suffix₂,
        [(emptyStackPDA M).start_symbol]⟩
      ((leftmostEpsilonPositionOf M anchor₁ anchorContext₁).conf M suffix₂)
    rw [hposition, leftmostEpsilonPositionOf_conf]
    simpa [PDA.conf.appendInput] using anchorRun₂
  exact leftmostEpsilonTrace_empty_state_unique M trace₁ trace₂
    global₁ global₂
    (by simpa [LeftmostEpsilonPosition.conf] using useful₁)
    (by simpa [LeftmostEpsilonPosition.conf] using useful₂) hlook

/-- The exact counted residual after useful cross-input determinism has
disposed of equal-length computations.  Keeping the structural datum in the
proposition prevents the unequal-count branch from discarding its grammar
ancestry. -/
@[expose]
public def UnequalCountSamePrefixEpsilonReturnData (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) (q₁ q₂ : State M)
    (suffix₁ suffix₂ : List T) : Prop :=
  SamePrefixEpsilonReturnData M p q₁ q₂ suffix₁ suffix₂ ∧
  ∃ (completion : List T)
      (context₁ context₂ : List (StackSymbol M))
      (final₁ final₂ : State M) (steps₁ steps₂ : ℕ),
    steps₁ ≠ steps₂ ∧
    (emptyStackPDA M).ReachesIn steps₁
      ⟨(emptyStackPDA M).initial_state, completion,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, [], context₁⟩ ∧
    (emptyStackPDA M).ReachesIn steps₂
      ⟨(emptyStackPDA M).initial_state, completion,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, [], context₂⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨q₁, suffix₁, context₁⟩ ⟨final₁, [], []⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨q₂, suffix₂, context₂⟩ ⟨final₂, [], []⟩ ∧
    suffix₁.take 1 = suffix₂.take 1

/-- Equal-length globally useful cuts at a common completed prefix have the
same state even when their untouched suffixes differ. -/
public theorem samePrefixEmptyListCuts_state_eq_of_equal_steps
    (M : DPDA Q T S)
    {completion suffix₁ suffix₂ : List T} {steps : ℕ}
    {q₁ q₂ final₁ final₂ : State M}
    {context₁ context₂ : List (StackSymbol M)}
    (run₁ : (emptyStackPDA M).ReachesIn steps
      ⟨(emptyStackPDA M).initial_state, completion,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, [], context₁⟩)
    (run₂ : (emptyStackPDA M).ReachesIn steps
      ⟨(emptyStackPDA M).initial_state, completion,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, [], context₂⟩)
    (useful₁ : (emptyStackPDA M).Reaches
      ⟨q₁, suffix₁, context₁⟩ ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ⟨q₂, suffix₂, context₂⟩ ⟨final₂, [], []⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ := by
  have lifted₁ :=
    (PDA.unconsumed_input_N (pda := emptyStackPDA M) suffix₁).mp run₁
  have lifted₂ :=
    (PDA.unconsumed_input_N (pda := emptyStackPDA M) suffix₂).mp run₂
  have synchronized := emptyStack_globally_useful_reachesIn_cross_input M
    (by simpa [PDA.conf.appendInput] using lifted₁)
    (by simpa [PDA.conf.appendInput] using lifted₂)
    useful₁ useful₂ hlook
  exact (congrArg PDA.conf.state synchronized).symm

/-- Cross-input determinism closes the equal-count branch of the structural
residual.  Hence a genuinely distinct return pair has unequal global step
counts; all of its paired-anchor ancestry is retained for the subsequent
interval-order argument. -/
public theorem SamePrefixEpsilonReturnData.state_eq_or_unequal_counts
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q₁ q₂ : State M}
    {suffix₁ suffix₂ : List T}
    (data : SamePrefixEpsilonReturnData M p q₁ q₂ suffix₁ suffix₂) :
    q₁ = q₂ ∨
      UnequalCountSamePrefixEpsilonReturnData M p q₁ q₂ suffix₁ suffix₂ := by
  have retainedData := data
  rcases data with ⟨completion, context₁, context₂,
    anchor₁, anchor₂, anchorSuffix₁, anchorSuffix₂,
    anchorContext₁, anchorContext₂,
    leftAnchor, rightAnchor, leftTail, rightTail, leftBearing, paired,
    final₁, final₂, useful₁, useful₂, hlook⟩
  obtain ⟨prefixSteps₁, tailSteps₁, prefixRun₁, tailRun₁,
      globalRun₁⟩ :=
    leftAnchor.exists_countedZeroVisibleInterval M leftTail
  obtain ⟨prefixSteps₂, tailSteps₂, prefixRun₂, tailRun₂,
      globalRun₂⟩ :=
    rightAnchor.exists_countedZeroVisibleInterval M rightTail
  let steps₁ := prefixSteps₁ + tailSteps₁
  let steps₂ := prefixSteps₂ + tailSteps₂
  by_cases hsteps : steps₁ = steps₂
  · left
    have run₁ : (emptyStackPDA M).ReachesIn steps₁
        ⟨(emptyStackPDA M).initial_state, completion,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨q₁, [], context₁⟩ := by
      simpa [steps₁, spineCutState, spineCutStack] using globalRun₁
    have run₂ : (emptyStackPDA M).ReachesIn steps₂
        ⟨(emptyStackPDA M).initial_state, completion,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨q₂, [], context₂⟩ := by
      simpa [steps₂, spineCutState, spineCutStack] using globalRun₂
    have run₂' : (emptyStackPDA M).ReachesIn steps₁
        ⟨(emptyStackPDA M).initial_state, completion,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨q₂, [], context₂⟩ := by
      rw [hsteps]
      exact run₂
    exact samePrefixEmptyListCuts_state_eq_of_equal_steps M
      run₁ run₂' useful₁ useful₂ hlook
  · right
    refine ⟨retainedData, completion, context₁, context₂,
      final₁, final₂, steps₁, steps₂, hsteps, ?_, ?_,
      useful₁, useful₂, hlook⟩
    · simpa [steps₁, spineCutState, spineCutStack] using globalRun₁
    · simpa [steps₂, spineCutState, spineCutStack] using globalRun₂

/-- Build the full paired-anchor/two-tail residual directly from the
constructor-exact epsilon edge and the other concrete empty edge. -/
public theorem samePrefixEpsilonReturnData (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q₁ q₂ : State M}
    {suffix₁ suffix₂ : List T}
    (edge₁ : ConcreteEpsilonEmptyEdge M p q₁ suffix₁)
    (edge₂ : ConcreteEmptyEdge M p q₂ suffix₂)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    SamePrefixEpsilonReturnData M p q₁ q₂ suffix₁ suffix₂ := by
  rcases edge₁ with
    ⟨oldWord, oldContext, source, top, parent, transition, rule⟩
  let concreteEdge₁ : ConcreteEmptyEdge M p q₁ suffix₁ :=
    ConcreteEmptyEdge.epsilon parent transition rule
  obtain ⟨completion, hp⟩ := concreteEdge₁.exists_prefixCompletion M
  obtain ⟨parentContext, concreteParent⟩ :=
    concreteOperationalSpine_of_activeSpine M
      ((parent.operationalSpine M).activeSpine M) hp
  obtain ⟨anchor₁, anchorSuffix₁, anchorContext₁,
      leftAnchor, parentTail⟩ := concreteParent.zeroVisibleDecomposition M
  let leftTail : ZeroVisibleTail M p completion anchor₁ anchorSuffix₁
      anchorContext₁ (PDA_to_CFG.N.list q₁ [] q₁) suffix₁
      parentContext :=
    ZeroVisibleTail.epsilon parentTail transition rule
  let leftBearing : EpsilonBearingZeroVisibleTail M p completion anchor₁
      anchorSuffix₁ anchorContext₁ (PDA_to_CFG.N.list q₁ [] q₁)
      suffix₁ parentContext :=
    EpsilonBearingZeroVisibleTail.epsilon parentTail transition rule
  let child₁ : ConcreteOperationalSpine M p
      (PDA_to_CFG.N.list q₁ [] q₁) suffix₁ completion parentContext :=
    ConcreteOperationalSpine.epsilon concreteParent transition rule
  obtain ⟨context₂, child₂⟩ := edge₂.exists_childSpineAtCompletion M hp
  obtain ⟨anchor₂, anchorSuffix₂, anchorContext₂,
      rightAnchor, rightTail⟩ := child₂.zeroVisibleDecomposition M
  let paired := pairedVisibleAnchors_of_same_prefix M
    leftAnchor rightAnchor rfl rfl
  cases child₁.focusedExact M with
  | list _ _ _ _ _ _ final₁ prefix₁ useful₁ =>
      cases child₂.focusedExact M with
      | list _ _ _ _ _ _ final₂ prefix₂ useful₂ =>
          exact ⟨completion, parentContext, context₂,
            anchor₁, anchor₂, anchorSuffix₁, anchorSuffix₂,
            anchorContext₁, anchorContext₂,
            leftAnchor, rightAnchor, leftTail, rightTail, leftBearing, paired,
            final₁, final₂, useful₁, useful₂, hlook⟩

/-- Once the paired structural residual is discharged, every
transition-generated empty return is synchronized with an arbitrary empty
return at the same visible prefix. -/
public theorem concreteTransitionEmptyReturn_samePrefix_state_eq_of_structural
    (M : DPDA Q T S) (hstructural : SamePrefixEpsilonReturnsStateUnique M)
    {p : List (symbol T (Nonterminal M))} {q₁ q₂ : State M}
    {suffix₁ suffix₂ : List T}
    (edge₁ : ConcreteEmptyTransitionEdge M p q₁ suffix₁)
    (edge₂ : ConcreteEmptyEdge M p q₂ suffix₂)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    q₁ = q₂ := by
  cases edge₁ with
  | @read base suffix₁ preWord context source a top q₁
      parent transition rule =>
      exact concreteReadEmptyReturn_samePrefix_state_eq M
        parent transition rule edge₂
  | @epsilon p suffix₁ preWord context source top q₁
      parent transition rule =>
      apply hstructural p q₁ q₂ suffix₁ suffix₂
      exact samePrefixEpsilonReturnData M
        ⟨preWord, context, source, top, parent, transition, rule⟩
        edge₂ hlook

end

end DPDA_to_LR
