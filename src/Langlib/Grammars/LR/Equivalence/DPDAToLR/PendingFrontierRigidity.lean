module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.PendingFrontierTrace
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ProductiveListPositions
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SingleCompletionPrefix

/-!
# Rigidity of productive pending frontiers

A pending frontier records the visible events of a characteristic-spine
execution.  This file proves that two productive counted executions which
have reached the same pending frontier have consumed the same prefix of their
fixed input word.  The productive continuations may use different appended
input tails; equality of their first symbols is enough.

The proof factors each counted trace after its last visible event.  It then
recurses on the shorter common frontier.  Reading anchors synchronize by
determinism.  At paired split-right anchors, the recursive synchronization of
the parent positions gives one common retained frame, and prefix-freeness of
productive retained returns forces the two selected completion words to be
equal.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- The root or the child of the last visible event of a counted pending
frontier trace. -/
public inductive PendingFrontierVisibleAnchor (M : DPDA Q T S)
    (word : List T) : PendingFrontierPosition M → ℕ → Prop
  | root : PendingFrontierVisibleAnchor M word
      ⟨[], PDA_to_CFG.N.start, [], [], [], word⟩ 0
  | read
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed remaining : List T}
      {context : List (StackSymbol M)} {steps : ℕ}
      {q target next : State M} {a : T} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierTrace M word
        ⟨p, PDA_to_CFG.N.single q Z target, suffix, consumed,
          context, a :: remaining⟩ steps)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun q a Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      PendingFrontierVisibleAnchor M word
        ⟨p ++ [symbol.terminal a],
          PDA_to_CFG.N.list next gamma target, suffix,
          consumed ++ [a], context, remaining⟩ (steps + 1)
  | splitRight
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed leftWord remaining : List T}
      {context : List (StackSymbol M)} {steps returnSteps : ℕ}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierTrace M word
        ⟨p, PDA_to_CFG.N.list q (Z :: gamma) target, suffix,
          consumed, context, leftWord ++ remaining⟩ steps)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hleft : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)]
        (leftWord.map symbol.terminal))
      (hpositive : 0 < returnSteps)
      (hreturn : PDA.RetainedFrameRun (emptyStackPDA M)
        (gamma ++ context) returnSteps
        ⟨q, leftWord, Z :: (gamma ++ context)⟩
        ⟨middle, [], gamma ++ context⟩) :
      PendingFrontierVisibleAnchor M word
        ⟨p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)],
          PDA_to_CFG.N.list middle gamma target, suffix,
          consumed ++ leftWord, context, remaining⟩
        (steps + returnSteps)

/-- A counted visible anchor is itself a complete counted pending-frontier
trace. -/
public theorem PendingFrontierVisibleAnchor.trace
    (M : DPDA Q T S) {word : List T}
    {position : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierVisibleAnchor M word position steps) :
    PendingFrontierTrace M word position steps := by
  cases h with
  | root => exact PendingFrontierTrace.root
  | read previous htransition hrule =>
      exact PendingFrontierTrace.read previous htransition hrule
  | splitRight previous hlength hrule hleft hpositive hreturn =>
      exact PendingFrontierTrace.splitRight previous hlength hrule hleft
        hpositive hreturn

/-- Forgetting the count and remaining input gives the corresponding
ordinary last-visible spine anchor. -/
public theorem PendingFrontierVisibleAnchor.visibleSpineAnchor
    (M : DPDA Q T S) {word : List T}
    {position : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierVisibleAnchor M word position steps) :
    VisibleSpineAnchor M position.frontier position.node position.suffix
      position.consumed position.context := by
  cases h with
  | root => exact VisibleSpineAnchor.root
  | read previous htransition hrule =>
      exact VisibleSpineAnchor.read
        (previous.concreteOperationalSpine M) htransition hrule
  | splitRight previous hlength hrule hleft hpositive hreturn =>
      exact VisibleSpineAnchor.splitRight
        (previous.concreteOperationalSpine M) hlength hrule hleft

/-- Every counted pending-frontier trace factors as its last visible anchor
followed by a counted zero-visible suffix. -/
public theorem PendingFrontierTrace.exists_visibleAnchor_decomposition
    (M : DPDA Q T S) {word : List T}
    {position : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierTrace M word position steps) :
    ∃ (anchorPosition : PendingFrontierPosition M)
        (anchorSteps tailSteps : ℕ),
      PendingFrontierVisibleAnchor M word anchorPosition anchorSteps ∧
      ZeroVisibleFrontierExtension M anchorPosition position tailSteps := by
  induction h with
  | root =>
      exact ⟨_, 0, 0, PendingFrontierVisibleAnchor.root,
        ZeroVisibleFrontierExtension.refl⟩
  | start hrule =>
      exact ⟨_, 0, 0, PendingFrontierVisibleAnchor.root,
        ZeroVisibleFrontierExtension.start
          ZeroVisibleFrontierExtension.refl hrule⟩
  | read previous htransition hrule ih =>
      exact ⟨_, _, 0,
        PendingFrontierVisibleAnchor.read previous htransition hrule,
        ZeroVisibleFrontierExtension.refl⟩
  | epsilon previous htransition hrule ih =>
      obtain ⟨anchorPosition, anchorSteps, tailSteps, anchor, tail⟩ := ih
      exact ⟨anchorPosition, anchorSteps, tailSteps + 1, anchor,
        ZeroVisibleFrontierExtension.epsilon tail htransition hrule⟩
  | splitLeft previous hlength hrule hright ih =>
      obtain ⟨anchorPosition, anchorSteps, tailSteps, anchor, tail⟩ := ih
      exact ⟨anchorPosition, anchorSteps, tailSteps, anchor,
        ZeroVisibleFrontierExtension.splitLeft tail hlength hrule hright⟩
  | splitRight previous hlength hrule hleft hpositive hreturn ih =>
      exact ⟨_, _, 0,
        PendingFrontierVisibleAnchor.splitRight previous hlength hrule hleft
          hpositive hreturn,
        ZeroVisibleFrontierExtension.refl⟩

/-- A zero-visible counted suffix does not change the pending frontier. -/
private theorem ZeroVisibleFrontierExtension.frontier_eq
    (M : DPDA Q T S)
    {startPosition endPosition : PendingFrontierPosition M} {steps : ℕ}
    (h : ZeroVisibleFrontierExtension M startPosition endPosition steps) :
    endPosition.frontier = startPosition.frontier := by
  induction h with
  | refl => rfl
  | start previous hrule ih => exact ih
  | epsilon previous htransition hrule ih => exact ih
  | splitLeft previous hlength hrule hright ih => exact ih

/-- Pull a useful continuation back through a zero-visible counted suffix.
The appended input is untouched by every step of the suffix. -/
private theorem ZeroVisibleFrontierExtension.useful_start
    (M : DPDA Q T S)
    {startPosition endPosition : PendingFrontierPosition M} {steps : ℕ}
    {future : List T} {final : State M}
    (h : ZeroVisibleFrontierExtension M startPosition endPosition steps)
    (useful : (emptyStackPDA M).Reaches
      ((endPosition.cut M).appendInput future) ⟨final, [], []⟩) :
    (emptyStackPDA M).Reaches
      ((startPosition.cut M).appendInput future) ⟨final, [], []⟩ := by
  have lifted := (PDA.unconsumed_input_N
    (pda := emptyStackPDA M) future).mp (h.reachesIn M)
  exact (PDA.reaches_of_reachesIn lifted).trans useful

private theorem take_one_append_eq
    {common left right : List T}
    (h : left.take 1 = right.take 1) :
    (common ++ left).take 1 = (common ++ right).take 1 := by
  cases common with
  | nil => simpa using h
  | cons a rest => simp

private theorem read_source_useful
    (M : DPDA Q T S)
    {q next final : State M} {a : T} {Z : StackSymbol M}
    {gamma context : List (StackSymbol M)}
    {remaining future : List T}
    (htransition : (next, gamma) ∈
      (emptyStackPDA M).transition_fun q a Z)
    (useful : (emptyStackPDA M).Reaches
      ⟨next, remaining ++ future, gamma ++ context⟩
      ⟨final, [], []⟩) :
    (emptyStackPDA M).Reaches
      ⟨q, (a :: remaining) ++ future, Z :: context⟩
      ⟨final, [], []⟩ := by
  have step : (emptyStackPDA M).Reaches₁
      ⟨q, (a :: remaining) ++ future, Z :: context⟩
      ⟨next, remaining ++ future, gamma ++ context⟩ := by
    exact Or.inl ⟨next, gamma, htransition, by simp⟩
  exact (Relation.ReflTransGen.single step).trans useful

private theorem retained_return_source_useful
    (M : DPDA Q T S)
    {q middle final : State M} {Z : StackSymbol M}
    {frame : List (StackSymbol M)} {returnSteps : ℕ}
    {leftWord remaining future : List T}
    (hreturn : PDA.RetainedFrameRun (emptyStackPDA M) frame returnSteps
      ⟨q, leftWord, Z :: frame⟩ ⟨middle, [], frame⟩)
    (useful : (emptyStackPDA M).Reaches
      ⟨middle, remaining ++ future, frame⟩ ⟨final, [], []⟩) :
    (emptyStackPDA M).Reaches
      ⟨q, (leftWord ++ remaining) ++ future, Z :: frame⟩
      ⟨final, [], []⟩ := by
  have lifted := hreturn.appendInput (remaining ++ future)
  have hprefix : (emptyStackPDA M).Reaches
      ⟨q, (leftWord ++ remaining) ++ future, Z :: frame⟩
      ⟨middle, remaining ++ future, frame⟩ := by
    simpa [PDA.conf.appendInput, List.append_assoc] using
      PDA.reaches_of_reachesIn lifted.toReachesIn
  exact hprefix.trans useful

/-- Boundary-sensitive synchronization of two nonempty list endpoints whose
counted last-visible anchors have already been synchronized. -/
private theorem nonempty_list_positions_eq_of_counted_anchors
    (M : DPDA Q T S)
    {word : List T}
    {p : List (symbol T (Nonterminal M))}
    {anchorPosition₁ anchorPosition₂ : PendingFrontierPosition M}
    {anchorSteps₁ anchorSteps₂ tailSteps₁ tailSteps₂ : ℕ}
    {q target₁ target₂ final₁ final₂ : State M}
    {Z : StackSymbol M}
    {gamma₁ gamma₂ context₁ context₂ :
      List (StackSymbol M)}
    {suffix₁ suffix₂ consumed₁ consumed₂
      remaining₁ remaining₂ future₁ future₂ : List T}
    (anchor₁ : PendingFrontierVisibleAnchor M word
      anchorPosition₁ anchorSteps₁)
    (anchor₂ : PendingFrontierVisibleAnchor M word
      anchorPosition₂ anchorSteps₂)
    (tail₁ : ZeroVisibleFrontierExtension M anchorPosition₁
      ⟨p, PDA_to_CFG.N.list q (Z :: gamma₁) target₁, suffix₁,
        consumed₁, context₁, remaining₁⟩ tailSteps₁)
    (tail₂ : ZeroVisibleFrontierExtension M anchorPosition₂
      ⟨p, PDA_to_CFG.N.list q (Z :: gamma₂) target₂, suffix₂,
        consumed₂, context₂, remaining₂⟩ tailSteps₂)
    (anchorPositionEq :
      leftmostEpsilonPositionOf M anchorPosition₁.node
          anchorPosition₁.context =
        leftmostEpsilonPositionOf M anchorPosition₂.node
          anchorPosition₂.context)
    (useful₁ : (emptyStackPDA M).Reaches
      ((⟨p, PDA_to_CFG.N.list q (Z :: gamma₁) target₁, suffix₁,
          consumed₁, context₁, remaining₁⟩ :
        PendingFrontierPosition M).cut M |>.appendInput future₁)
      ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ((⟨p, PDA_to_CFG.N.list q (Z :: gamma₂) target₂, suffix₂,
          consumed₂, context₂, remaining₂⟩ :
        PendingFrontierPosition M).cut M |>.appendInput future₂)
      ⟨final₂, [], []⟩)
    (hlook : (remaining₁ ++ future₁).take 1 =
      (remaining₂ ++ future₂).take 1) :
    (LeftmostEpsilonPosition.list q (Z :: gamma₁) context₁ :
        LeftmostEpsilonPosition M) =
      .list q (Z :: gamma₂) context₂ := by
  let start := leftmostEpsilonPositionOf M anchorPosition₁.node
    anchorPosition₁.context
  have trace₁ : LeftmostEpsilonTrace M start
      (.list q (Z :: gamma₁) context₁) := by
    simpa [start, leftmostEpsilonPositionOf] using
      (tail₁.zeroVisibleTail M).leftmostEpsilonTrace M
  have trace₂ : LeftmostEpsilonTrace M start
      (.list q (Z :: gamma₂) context₂) := by
    simpa [start, anchorPositionEq, leftmostEpsilonPositionOf] using
      (tail₂.zeroVisibleTail M).leftmostEpsilonTrace M
  have anchorRun₁ := (PDA.unconsumed_input_N
    (pda := emptyStackPDA M) future₁).mp (anchor₁.trace M).reachesIn
  have anchorRun₂ := (PDA.unconsumed_input_N
    (pda := emptyStackPDA M) future₂).mp (anchor₂.trace M).reachesIn
  have anchorRemaining₁ : anchorPosition₁.remaining = remaining₁ :=
    (tail₁.remaining_eq M).symm
  have anchorRemaining₂ : anchorPosition₂.remaining = remaining₂ :=
    (tail₂.remaining_eq M).symm
  have global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, word ++ future₁,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M (remaining₁ ++ future₁)) := by
    apply PDA.reaches_of_reachesIn
    simpa [start, leftmostEpsilonPositionOf_conf,
      PendingFrontierPosition.cut, PDA.conf.appendInput,
      anchorRemaining₁] using anchorRun₁
  have global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, word ++ future₂,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M (remaining₂ ++ future₂)) := by
    apply PDA.reaches_of_reachesIn
    simpa [start, anchorPositionEq, leftmostEpsilonPositionOf_conf,
      PendingFrontierPosition.cut, PDA.conf.appendInput,
      anchorRemaining₂] using anchorRun₂
  apply leftmostEpsilonTrace_nonempty_list_position_unique M
    trace₁ trace₂ global₁ global₂
  · simpa [LeftmostEpsilonPosition.conf,
      PendingFrontierPosition.cut, PDA.conf.appendInput,
      List.append_assoc] using useful₁
  · simpa [LeftmostEpsilonPosition.conf,
      PendingFrontierPosition.cut, PDA.conf.appendInput,
      List.append_assoc] using useful₂
  · exact hlook

/-- Two productive counted last-visible anchors with the same pending
frontier have consumed the same prefix.  Their exact structural anchor
positions synchronize as well; the stronger second conclusion is what makes
the split-right induction boundary-sensitive. -/
private theorem productivePendingFrontierVisibleAnchor_rigid_aux
    (M : DPDA Q T S)
    {rank : ℕ} {word future₁ future₂ : List T}
    {position₁ position₂ : PendingFrontierPosition M}
    {steps₁ steps₂ : ℕ} {final₁ final₂ : State M}
    (hrank : position₁.frontier.length = rank)
    (anchor₁ : PendingFrontierVisibleAnchor M word position₁ steps₁)
    (anchor₂ : PendingFrontierVisibleAnchor M word position₂ steps₂)
    (hfrontier : position₁.frontier = position₂.frontier)
    (useful₁ : (emptyStackPDA M).Reaches
      ((position₁.cut M).appendInput future₁) ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ((position₂.cut M).appendInput future₂) ⟨final₂, [], []⟩)
    (hlook : future₁.take 1 = future₂.take 1) :
    position₁.consumed = position₂.consumed ∧
      leftmostEpsilonPositionOf M position₁.node position₁.context =
        leftmostEpsilonPositionOf M position₂.node position₂.context := by
  cases anchor₁ with
  | root =>
      cases anchor₂ with
      | root => exact ⟨rfl, rfl⟩
      | read previous htransition hrule => simp at hfrontier
      | splitRight previous hlength hrule hleft hpositive hreturn =>
          simp at hfrontier
  | @read p₁ suffix₁ consumed₁ remaining₁ context₁ previousSteps₁
      q₁ target₁ next₁ a₁ Z₁ gamma₁ previous₁ transition₁ rule₁ =>
      cases anchor₂ with
      | root => simp at hfrontier
      | @read p₂ suffix₂ consumed₂ remaining₂ context₂
          previousSteps₂ q₂ target₂ next₂ a₂ Z₂ gamma₂
          previous₂ transition₂ rule₂ =>
          have hp : p₁ = p₂ := List.append_inj_left' hfrontier rfl
          have hlast := List.append_inj_right' hfrontier rfl
          have ha : a₁ = a₂ := by simpa using hlast
          subst p₂
          subst a₂
          obtain ⟨parentPosition₁, parentAnchorSteps₁, tailSteps₁,
              parentAnchor₁, parentTail₁⟩ :=
            previous₁.exists_visibleAnchor_decomposition M
          obtain ⟨parentPosition₂, parentAnchorSteps₂, tailSteps₂,
              parentAnchor₂, parentTail₂⟩ :=
            previous₂.exists_visibleAnchor_decomposition M
          have parentFrontier :
              parentPosition₁.frontier = parentPosition₂.frontier := by
            exact (parentTail₁.frontier_eq M).symm.trans
              (parentTail₂.frontier_eq M)
          have childUseful₁ : (emptyStackPDA M).Reaches
              ⟨next₁, remaining₁ ++ future₁,
                gamma₁ ++ context₁⟩ ⟨final₁, [], []⟩ := by
            simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack] using useful₁
          have childUseful₂ : (emptyStackPDA M).Reaches
              ⟨next₂, remaining₂ ++ future₂,
                gamma₂ ++ context₂⟩ ⟨final₂, [], []⟩ := by
            simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack] using useful₂
          have previousUseful₁ : (emptyStackPDA M).Reaches
              ((⟨p₁, PDA_to_CFG.N.single q₁ Z₁ target₁,
                  suffix₁, consumed₁, context₁,
                  a₁ :: remaining₁⟩ : PendingFrontierPosition M).cut M
                |>.appendInput future₁) ⟨final₁, [], []⟩ := by
            simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack] using
              read_source_useful M transition₁ childUseful₁
          have previousUseful₂ : (emptyStackPDA M).Reaches
              ((⟨p₁, PDA_to_CFG.N.single q₂ Z₂ target₂,
                  suffix₂, consumed₂, context₂,
                  a₁ :: remaining₂⟩ : PendingFrontierPosition M).cut M
                |>.appendInput future₂) ⟨final₂, [], []⟩ := by
            simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack] using
              read_source_useful M transition₂ childUseful₂
          have parentUseful₁ :=
            parentTail₁.useful_start M previousUseful₁
          have parentUseful₂ :=
            parentTail₂.useful_start M previousUseful₂
          obtain ⟨parentConsumed, parentPositionEq⟩ :=
            productivePendingFrontierVisibleAnchor_rigid_aux M
              (rank := parentPosition₁.frontier.length) rfl
              parentAnchor₁ parentAnchor₂ parentFrontier
              parentUseful₁ parentUseful₂ hlook
          have previousConsumed : consumed₁ = consumed₂ :=
            (parentTail₁.consumed_eq M).trans
              (parentConsumed.trans (parentTail₂.consumed_eq M).symm)
          obtain ⟨hnext, hgamma, hcontext⟩ :=
            concreteRead_anchor_data_eq M
              (previous₁.concreteOperationalSpine M)
              (by simpa [previousConsumed] using
                previous₂.concreteOperationalSpine M)
              transition₁ transition₂
          subst next₂
          subst gamma₂
          subst context₂
          exact ⟨by simpa [previousConsumed], rfl⟩
      | splitRight previous hlength hrule hleft hpositive hreturn =>
          have hlast := List.append_inj_right' hfrontier rfl
          cases (List.cons.inj hlast).1
  | @splitRight p₁ suffix₁ consumed₁ leftWord₁ remaining₁
      context₁ previousSteps₁ returnSteps₁ q₁ middle₁ target₁
      Z₁ gamma₁ previous₁ length₁ rule₁ left₁ positive₁ return₁ =>
      cases anchor₂ with
      | root => simp at hfrontier
      | read previous htransition hrule =>
          have hlast := List.append_inj_right' hfrontier rfl
          cases (List.cons.inj hlast).1
      | @splitRight p₂ suffix₂ consumed₂ leftWord₂ remaining₂
          context₂ previousSteps₂ returnSteps₂ q₂ middle₂ target₂
          Z₂ gamma₂ previous₂ length₂ rule₂ left₂ positive₂ return₂ =>
          have hp : p₁ = p₂ := List.append_inj_left' hfrontier rfl
          have hlast := List.append_inj_right' hfrontier rfl
          have hmarker :
              (PDA_to_CFG.N.single q₁ Z₁ middle₁ : Nonterminal M) =
                PDA_to_CFG.N.single q₂ Z₂ middle₂ := by
            have hs :
                symbol.nonterminal (T := T)
                    (PDA_to_CFG.N.single q₁ Z₁ middle₁) =
                  symbol.nonterminal
                    (PDA_to_CFG.N.single q₂ Z₂ middle₂) :=
              (List.cons.inj hlast).1
            exact symbol.nonterminal.inj hs
          injection hmarker with hq hZ hmiddle
          subst p₂
          subst q₂
          subst Z₂
          subst middle₂
          obtain ⟨parentPosition₁, parentAnchorSteps₁, tailSteps₁,
              parentAnchor₁, parentTail₁⟩ :=
            previous₁.exists_visibleAnchor_decomposition M
          obtain ⟨parentPosition₂, parentAnchorSteps₂, tailSteps₂,
              parentAnchor₂, parentTail₂⟩ :=
            previous₂.exists_visibleAnchor_decomposition M
          have parentFrontier :
              parentPosition₁.frontier = parentPosition₂.frontier := by
            exact (parentTail₁.frontier_eq M).symm.trans
              (parentTail₂.frontier_eq M)
          have childUseful₁ : (emptyStackPDA M).Reaches
              ⟨middle₁, remaining₁ ++ future₁,
                gamma₁ ++ context₁⟩ ⟨final₁, [], []⟩ := by
            simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack] using useful₁
          have childUseful₂ : (emptyStackPDA M).Reaches
              ⟨middle₁, remaining₂ ++ future₂,
                gamma₂ ++ context₂⟩ ⟨final₂, [], []⟩ := by
            simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack] using useful₂
          have previousUseful₁ : (emptyStackPDA M).Reaches
              ((⟨p₁,
                  PDA_to_CFG.N.list q₁ (Z₁ :: gamma₁) target₁,
                  suffix₁, consumed₁, context₁,
                  leftWord₁ ++ remaining₁⟩ :
                PendingFrontierPosition M).cut M |>.appendInput future₁)
              ⟨final₁, [], []⟩ := by
            simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack, List.append_assoc] using
              retained_return_source_useful M return₁ childUseful₁
          have previousUseful₂ : (emptyStackPDA M).Reaches
              ((⟨p₁,
                  PDA_to_CFG.N.list q₁ (Z₁ :: gamma₂) target₂,
                  suffix₂, consumed₂, context₂,
                  leftWord₂ ++ remaining₂⟩ :
                PendingFrontierPosition M).cut M |>.appendInput future₂)
              ⟨final₂, [], []⟩ := by
            simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack, List.append_assoc] using
              retained_return_source_useful M return₂ childUseful₂
          have parentUseful₁ :=
            parentTail₁.useful_start M previousUseful₁
          have parentUseful₂ :=
            parentTail₂.useful_start M previousUseful₂
          obtain ⟨parentAnchorConsumed, parentAnchorPositionEq⟩ :=
            productivePendingFrontierVisibleAnchor_rigid_aux M
              (rank := parentPosition₁.frontier.length) rfl
              parentAnchor₁ parentAnchor₂ parentFrontier
              parentUseful₁ parentUseful₂ hlook
          have parentConsumed : consumed₁ = consumed₂ :=
            (parentTail₁.consumed_eq M).trans
              (parentAnchorConsumed.trans
                (parentTail₂.consumed_eq M).symm)
          have word₁ := previous₁.word_eq M
          have word₂ := previous₂.word_eq M
          change word = consumed₁ ++ (leftWord₁ ++ remaining₁) at word₁
          change word = consumed₂ ++ (leftWord₂ ++ remaining₂) at word₂
          have residualEq : leftWord₁ ++ remaining₁ =
              leftWord₂ ++ remaining₂ := by
            exact List.append_cancel_left
              (word₁.symm.trans (parentConsumed ▸ word₂))
          have parentLook :
              ((leftWord₁ ++ remaining₁) ++ future₁).take 1 =
                ((leftWord₂ ++ remaining₂) ++ future₂).take 1 := by
            rw [residualEq]
            exact take_one_append_eq hlook
          have parentEndpointPositionEq :=
            nonempty_list_positions_eq_of_counted_anchors M
              parentAnchor₁ parentAnchor₂ parentTail₁ parentTail₂
              parentAnchorPositionEq previousUseful₁ previousUseful₂
              parentLook
          injection parentEndpointPositionEq with _ hdisplayed hcontext
          have hgamma : gamma₁ = gamma₂ := (List.cons.inj hdisplayed).2
          subst gamma₂
          subst context₂
          have leftWordEq : leftWord₁ = leftWord₂ := by
            rcases List.append_eq_append_iff.mp residualEq with
                ⟨extra, hleft, hremaining⟩ |
                ⟨extra, hleft, hremaining⟩
            · have globalLong : (emptyStackPDA M).ReachesIn previousSteps₂
                  ⟨(emptyStackPDA M).initial_state,
                    consumed₁ ++ (leftWord₁ ++ extra),
                    [(emptyStackPDA M).start_symbol]⟩
                  ⟨q₁, leftWord₁ ++ extra,
                    Z₁ :: (gamma₁ ++ context₁)⟩ := by
                apply (PDA.unconsumed_input_N
                  (pda := emptyStackPDA M) remaining₂).mpr
                simpa [PendingFrontierPosition.cut, spineCutState,
                  spineCutStack, PDA.conf.appendInput, word₂,
                  parentConsumed, hleft, List.append_assoc] using
                  previous₂.reachesIn M
              have shortUseful : (emptyStackPDA M).Reaches
                  ⟨middle₁,
                    extra ++ (remaining₂ ++ future₁),
                    gamma₁ ++ context₁⟩ ⟨final₁, [], []⟩ := by
                simpa [hremaining, List.append_assoc] using childUseful₁
              have longReturn : PDA.RetainedFrameRun (emptyStackPDA M)
                  (gamma₁ ++ context₁) returnSteps₂
                  ⟨q₁, leftWord₁ ++ extra,
                    Z₁ :: (gamma₁ ++ context₁)⟩
                  ⟨middle₁, [], gamma₁ ++ context₁⟩ := by
                simpa [hleft] using return₂
              have hextra := productiveRetainedReturn_prefix_eq_cross_input M
                globalLong return₁ longReturn shortUseful childUseful₂
                (take_one_append_eq (common := remaining₂) hlook)
              subst extra
              simpa using hleft.symm
            · have globalLong : (emptyStackPDA M).ReachesIn previousSteps₁
                  ⟨(emptyStackPDA M).initial_state,
                    consumed₂ ++ (leftWord₂ ++ extra),
                    [(emptyStackPDA M).start_symbol]⟩
                  ⟨q₁, leftWord₂ ++ extra,
                    Z₁ :: (gamma₁ ++ context₁)⟩ := by
                apply (PDA.unconsumed_input_N
                  (pda := emptyStackPDA M) remaining₁).mpr
                simpa [PendingFrontierPosition.cut, spineCutState,
                  spineCutStack, PDA.conf.appendInput, word₁,
                  parentConsumed, hleft, List.append_assoc] using
                  previous₁.reachesIn M
              have shortUseful : (emptyStackPDA M).Reaches
                  ⟨middle₁,
                    extra ++ (remaining₁ ++ future₂),
                    gamma₁ ++ context₁⟩ ⟨final₂, [], []⟩ := by
                simpa [hremaining, List.append_assoc] using childUseful₂
              have longReturn : PDA.RetainedFrameRun (emptyStackPDA M)
                  (gamma₁ ++ context₁) returnSteps₁
                  ⟨q₁, leftWord₂ ++ extra,
                    Z₁ :: (gamma₁ ++ context₁)⟩
                  ⟨middle₁, [], gamma₁ ++ context₁⟩ := by
                simpa [hleft] using return₁
              have hextra := productiveRetainedReturn_prefix_eq_cross_input M
                globalLong return₂ longReturn shortUseful childUseful₁
                (take_one_append_eq (common := remaining₁) hlook.symm)
              subst extra
              simpa using hleft
          exact ⟨by simpa [parentConsumed, leftWordEq], rfl⟩
termination_by rank
decreasing_by
  all_goals
    have hparent : p₁.length = parentPosition₁.frontier.length := by
      simpa using congrArg List.length (parentTail₁.frontier_eq M)
    have hrank' : p₁.length + 1 = rank := by
      simpa only [List.length_append, List.length_singleton] using hrank
    exact calc
      parentPosition₁.frontier.length = p₁.length := hparent.symm
      _ < p₁.length + 1 := Nat.lt_succ_self _
      _ = rank := hrank'

/-- Two productive counted last-visible anchors with the same pending
frontier have consumed the same prefix and have the same exact structural
anchor position. -/
public theorem productivePendingFrontierVisibleAnchor_rigid
    (M : DPDA Q T S)
    {word future₁ future₂ : List T}
    {position₁ position₂ : PendingFrontierPosition M}
    {steps₁ steps₂ : ℕ} {final₁ final₂ : State M}
    (anchor₁ : PendingFrontierVisibleAnchor M word position₁ steps₁)
    (anchor₂ : PendingFrontierVisibleAnchor M word position₂ steps₂)
    (hfrontier : position₁.frontier = position₂.frontier)
    (useful₁ : (emptyStackPDA M).Reaches
      ((position₁.cut M).appendInput future₁) ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ((position₂.cut M).appendInput future₂) ⟨final₂, [], []⟩)
    (hlook : future₁.take 1 = future₂.take 1) :
    position₁.consumed = position₂.consumed ∧
      leftmostEpsilonPositionOf M position₁.node position₁.context =
        leftmostEpsilonPositionOf M position₂.node position₂.context := by
  exact productivePendingFrontierVisibleAnchor_rigid_aux M
    (rank := position₁.frontier.length) rfl anchor₁ anchor₂ hfrontier
    useful₁ useful₂ hlook

/-- Productive counted pending-frontier traces reaching the same visible
frontier have consumed the same prefix of their common fixed input word.
The productive continuations may append different tails, provided their
one-symbol lookahead agrees. -/
public theorem productivePendingFrontier_same_frontier_consumed_eq
    (M : DPDA Q T S)
    {word future₁ future₂ : List T}
    {position₁ position₂ : PendingFrontierPosition M}
    {steps₁ steps₂ : ℕ} {final₁ final₂ : State M}
    (trace₁ : PendingFrontierTrace M word position₁ steps₁)
    (trace₂ : PendingFrontierTrace M word position₂ steps₂)
    (hfrontier : position₁.frontier = position₂.frontier)
    (useful₁ : (emptyStackPDA M).Reaches
      ((position₁.cut M).appendInput future₁) ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ((position₂.cut M).appendInput future₂) ⟨final₂, [], []⟩)
    (hlook : future₁.take 1 = future₂.take 1) :
    position₁.consumed = position₂.consumed := by
  obtain ⟨anchorPosition₁, anchorSteps₁, tailSteps₁,
      anchor₁, tail₁⟩ := trace₁.exists_visibleAnchor_decomposition M
  obtain ⟨anchorPosition₂, anchorSteps₂, tailSteps₂,
      anchor₂, tail₂⟩ := trace₂.exists_visibleAnchor_decomposition M
  have anchorFrontier :
      anchorPosition₁.frontier = anchorPosition₂.frontier :=
    (tail₁.frontier_eq M).symm.trans
      (hfrontier.trans (tail₂.frontier_eq M))
  have anchorUseful₁ := tail₁.useful_start M useful₁
  have anchorUseful₂ := tail₂.useful_start M useful₂
  have anchorConsumed :=
    (productivePendingFrontierVisibleAnchor_rigid M anchor₁ anchor₂
      anchorFrontier anchorUseful₁ anchorUseful₂ hlook).1
  exact (tail₁.consumed_eq M).trans
    (anchorConsumed.trans (tail₂.consumed_eq M).symm)

end

end DPDA_to_LR
