module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.LeftmostEpsilonTrace
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SpineSynchronization

/-!
# Productive nonempty list positions

A leftmost zero-visible trace remembers the boundary between the stack text
displayed by a characteristic list nonterminal and its hidden zipper context.
This module records the corresponding uniqueness fact for a nonempty list
head.  It is deliberately boundary-sensitive: equality of the underlying PDA
stack would not suffice for the recursive split-right synchronization proof.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A productive leftmost trace cannot return to the same nonempty list head
with a different displayed/context boundary.

After the first structural split, the remainder retains the old list tail as
a frame.  Re-exposing the same state and top symbol therefore either repeats
the same physical cut, giving a useful epsilon cycle, or inserts a nonempty
block immediately below that top symbol, giving useful stack growth. -/
private theorem leftmostEpsilonTrace_same_nonempty_list_eq_of_trace
    (M : DPDA Q T S)
    {q final : State M} {Z : StackSymbol M}
    {gamma₁ gamma₂ context₁ context₂ : List (StackSymbol M)}
    {suffix : List T}
    (between : LeftmostEpsilonTrace M
      (.list q (Z :: gamma₁) context₁)
      (.list q (Z :: gamma₂) context₂))
    (useful : (emptyStackPDA M).Reaches
      ((.list q (Z :: gamma₂) context₂ :
        LeftmostEpsilonPosition M).conf M suffix)
      ⟨final, [], []⟩) :
    (LeftmostEpsilonPosition.list q (Z :: gamma₁) context₁ :
        LeftmostEpsilonPosition M) =
      .list q (Z :: gamma₂) context₂ := by
  cases between with
  | refl => rfl
  | @head _ middle _ first rest =>
      cases first with
      | @split _ _ _ _ =>
          obtain ⟨n, added, hcontext, retained⟩ :=
            rest.fromSingle_exists_retainedFrameRun M
          change context₂ = added ++ (gamma₁ ++ context₁) at hcontext
          rw [hcontext] at retained useful
          have retainedAligned :
              PDA.RetainedFrameRun (emptyStackPDA M)
                (gamma₁ ++ context₁) n
                ⟨q, [], [Z] ++ (gamma₁ ++ context₁)⟩
                ⟨q, [], ([Z] ++ (gamma₂ ++ added)) ++
                  (gamma₁ ++ context₁)⟩ := by
            simpa [LeftmostEpsilonPosition.conf,
              LeftmostEpsilonPosition.context', hcontext,
              List.append_assoc] using retained
          have stripped := retainedAligned.changeFrame
            ([] : List (StackSymbol M))
          by_cases hextra : gamma₂ ++ added = []
          · have hgamma₂ : gamma₂ = [] :=
              (List.append_eq_nil_iff.mp hextra).1
            have hadded : added = [] :=
              (List.append_eq_nil_iff.mp hextra).2
            subst gamma₂
            subst added
            have hcontext' : context₂ = gamma₁ ++ context₁ := by
              simpa using hcontext
            have cycle : Relation.TransGen
                (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
                ⟨q, suffix, Z :: gamma₁ ++ context₁⟩
                ⟨q, suffix, Z :: gamma₁ ++ context₁⟩ := by
              cases rest with
              | @head _ after _ firstStep remaining =>
                  cases firstStep with
                  | @epsilon _ next _ replacement _ transition =>
                      have step : (emptyStackPDA M).Reaches₁
                          ⟨q, suffix, Z :: gamma₁ ++ context₁⟩
                          ⟨next, suffix,
                            replacement ++ (gamma₁ ++ context₁)⟩ := by
                        have core : (emptyStackPDA M).Reaches₁
                            ⟨q, [], Z :: gamma₁ ++ context₁⟩
                            ⟨next, [],
                              replacement ++ (gamma₁ ++ context₁)⟩ :=
                          ⟨next, replacement, transition, by simp⟩
                        apply PDA.reaches₁_iff_reachesIn_one.mpr
                        simpa [PDA.conf.appendInput] using
                          ((PDA.unconsumed_input_N
                            (pda := emptyStackPDA M) suffix).mp
                            (PDA.reaches₁_iff_reachesIn_one.mp core))
                      have tail := remaining.reaches M suffix
                      simpa [LeftmostEpsilonPosition.conf, hcontext',
                        List.append_assoc] using
                        (Relation.TransGen.head' step tail)
            exact False.elim <| emptyStack_no_useful_cycle M cycle
              (by simpa [LeftmostEpsilonPosition.conf, hcontext',
                List.append_assoc] using useful)
          · have growth : (emptyStackPDA M).Reaches
                ⟨q, [], [Z]⟩
                ⟨q, [], [Z] ++ (gamma₂ ++ added)⟩ := by
              exact PDA.reaches_of_reachesIn (by
                simpa [List.append_assoc] using stripped.toReachesIn)
            exact False.elim <| emptyStack_no_useful_stack_growth M
              growth hextra
              (by simpa [LeftmostEpsilonPosition.conf, hcontext,
                List.append_assoc] using useful)

/-- Two productive zero-visible traces from a common structural position to
nonempty list positions with the same control state and exposed top symbol
have equal exact positions, including the displayed/context boundary. -/
public theorem leftmostEpsilonTrace_nonempty_list_position_unique
    (M : DPDA Q T S)
    {start : LeftmostEpsilonPosition M}
    {q final₁ final₂ : State M} {Z : StackSymbol M}
    {gamma₁ gamma₂ context₁ context₂ : List (StackSymbol M)}
    {suffix₁ suffix₂ whole₁ whole₂ : List T}
    (trace₁ : LeftmostEpsilonTrace M start
      (.list q (Z :: gamma₁) context₁))
    (trace₂ : LeftmostEpsilonTrace M start
      (.list q (Z :: gamma₂) context₂))
    (global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₁,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₁))
    (global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, whole₂,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M suffix₂))
    (useful₁ : (emptyStackPDA M).Reaches
      ((.list q (Z :: gamma₁) context₁ :
        LeftmostEpsilonPosition M).conf M suffix₁)
      ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ((.list q (Z :: gamma₂) context₂ :
        LeftmostEpsilonPosition M).conf M suffix₂)
      ⟨final₂, [], []⟩)
    (hlook : suffix₁.take 1 = suffix₂.take 1) :
    (LeftmostEpsilonPosition.list q (Z :: gamma₁) context₁ :
        LeftmostEpsilonPosition M) =
      .list q (Z :: gamma₂) context₂ := by
  rcases leftmostEpsilonTrace_productive_comparable M
      trace₁ trace₂ global₁ global₂ useful₁ useful₂ hlook with
    between | between
  · exact leftmostEpsilonTrace_same_nonempty_list_eq_of_trace M
      between useful₂
  · exact (leftmostEpsilonTrace_same_nonempty_list_eq_of_trace M
      between useful₁).symm

/-- Split-right children with a common selected word inherit exact-position
synchronization from the last-visible anchors of their two parent spines.

The common `single source top middle` consumes the same word on both sides.
Consequently each productive child future extends to a productive parent
future on `leftWord ++ future`.  Boundary-sensitive synchronization of the
two parent zero-visible tails then identifies both displayed parent stacks
and both hidden contexts, which immediately identifies the split-right
children. -/
public theorem splitRight_positions_eq_of_parent_anchor_position_eq
    (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))}
    {beforeWord leftWord : List T}
    {parentAnchor₁ parentAnchor₂ : Nonterminal M}
    {parentAnchorSuffix₁ parentAnchorSuffix₂ : List T}
    {parentAnchorContext₁ parentAnchorContext₂ :
      List (StackSymbol M)}
    {parentSuffix₁ parentSuffix₂ future₁ future₂ : List T}
    {parentContext₁ parentContext₂ : List (StackSymbol M)}
    {source middle target₁ target₂ final₁ final₂ : State M}
    {top : StackSymbol M}
    {gamma₁ gamma₂ : List (StackSymbol M)}
    (anchor₁ : VisibleSpineAnchor M base parentAnchor₁
      parentAnchorSuffix₁ beforeWord parentAnchorContext₁)
    (anchor₂ : VisibleSpineAnchor M base parentAnchor₂
      parentAnchorSuffix₂ beforeWord parentAnchorContext₂)
    (tail₁ : ZeroVisibleTail M base beforeWord
      parentAnchor₁ parentAnchorSuffix₁ parentAnchorContext₁
      (PDA_to_CFG.N.list source (top :: gamma₁) target₁)
      parentSuffix₁ parentContext₁)
    (tail₂ : ZeroVisibleTail M base beforeWord
      parentAnchor₂ parentAnchorSuffix₂ parentAnchorContext₂
      (PDA_to_CFG.N.list source (top :: gamma₂) target₂)
      parentSuffix₂ parentContext₂)
    (parentPosition :
      leftmostEpsilonPositionOf M parentAnchor₁ parentAnchorContext₁ =
        leftmostEpsilonPositionOf M parentAnchor₂ parentAnchorContext₂)
    (completion : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal
        (PDA_to_CFG.N.single source top middle)]
      (leftWord.map symbol.terminal))
    (useful₁ : (emptyStackPDA M).Reaches
      ⟨middle, future₁, gamma₁ ++ parentContext₁⟩
      ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ⟨middle, future₂, gamma₂ ++ parentContext₂⟩
      ⟨final₂, [], []⟩)
    (hlook : future₁.take 1 = future₂.take 1) :
    (LeftmostEpsilonPosition.list middle gamma₁ parentContext₁ :
        LeftmostEpsilonPosition M) =
      .list middle gamma₂ parentContext₂ := by
  let start :=
    leftmostEpsilonPositionOf M parentAnchor₁ parentAnchorContext₁
  have trace₁ : LeftmostEpsilonTrace M start
      (.list source (top :: gamma₁) parentContext₁) := by
    simpa [start, leftmostEpsilonPositionOf] using
      tail₁.leftmostEpsilonTrace M
  have trace₂ : LeftmostEpsilonTrace M start
      (.list source (top :: gamma₂) parentContext₂) := by
    simpa [start, parentPosition, leftmostEpsilonPositionOf] using
      tail₂.leftmostEpsilonTrace M
  have return₁ : (emptyStackPDA M).Reaches
      ⟨source, leftWord ++ future₁,
        top :: gamma₁ ++ parentContext₁⟩
      ⟨middle, future₁, gamma₁ ++ parentContext₁⟩ := by
    have core :=
      (reaches_of_characteristic_derives_single M completion).append_stack
        (gamma₁ ++ parentContext₁)
    have lifted := (PDA.unconsumed_input future₁).mp core
    simpa [PDA.conf.appendInput, PDA.conf.appendStack,
      List.append_assoc] using lifted
  have return₂ : (emptyStackPDA M).Reaches
      ⟨source, leftWord ++ future₂,
        top :: gamma₂ ++ parentContext₂⟩
      ⟨middle, future₂, gamma₂ ++ parentContext₂⟩ := by
    have core :=
      (reaches_of_characteristic_derives_single M completion).append_stack
        (gamma₂ ++ parentContext₂)
    have lifted := (PDA.unconsumed_input future₂).mp core
    simpa [PDA.conf.appendInput, PDA.conf.appendStack,
      List.append_assoc] using lifted
  have parentUseful₁ : (emptyStackPDA M).Reaches
      ((.list source (top :: gamma₁) parentContext₁ :
        LeftmostEpsilonPosition M).conf M (leftWord ++ future₁))
      ⟨final₁, [], []⟩ := by
    simpa [LeftmostEpsilonPosition.conf, List.append_assoc] using
      return₁.trans useful₁
  have parentUseful₂ : (emptyStackPDA M).Reaches
      ((.list source (top :: gamma₂) parentContext₂ :
        LeftmostEpsilonPosition M).conf M (leftWord ++ future₂))
      ⟨final₂, [], []⟩ := by
    simpa [LeftmostEpsilonPosition.conf, List.append_assoc] using
      return₂.trans useful₂
  have anchorRun₁ := (PDA.unconsumed_input (leftWord ++ future₁)).mp
    (anchor₁.prefixPath M)
  have anchorRun₂ := (PDA.unconsumed_input (leftWord ++ future₂)).mp
    (anchor₂.prefixPath M)
  have global₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (leftWord ++ future₁),
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M (leftWord ++ future₁)) := by
    change (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (leftWord ++ future₁),
        [(emptyStackPDA M).start_symbol]⟩
      ((leftmostEpsilonPositionOf M parentAnchor₁
        parentAnchorContext₁).conf M (leftWord ++ future₁))
    rw [leftmostEpsilonPositionOf_conf]
    simpa [PDA.conf.appendInput] using anchorRun₁
  have global₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (leftWord ++ future₂),
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M (leftWord ++ future₂)) := by
    change (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        beforeWord ++ (leftWord ++ future₂),
        [(emptyStackPDA M).start_symbol]⟩
      ((leftmostEpsilonPositionOf M parentAnchor₁
        parentAnchorContext₁).conf M (leftWord ++ future₂))
    rw [parentPosition, leftmostEpsilonPositionOf_conf]
    simpa [PDA.conf.appendInput] using anchorRun₂
  have parentLook : (leftWord ++ future₁).take 1 =
      (leftWord ++ future₂).take 1 := by
    cases leftWord with
    | nil => simpa using hlook
    | cons a rest => simp
  have parentEq := leftmostEpsilonTrace_nonempty_list_position_unique M
    trace₁ trace₂ global₁ global₂ parentUseful₁ parentUseful₂
      parentLook
  injection parentEq with _ hgamma hcontext
  have hgamma' : gamma₁ = gamma₂ := (List.cons.inj hgamma).2
  subst gamma₂
  subst parentContext₂
  rfl

/-- Nullable specialization of
`splitRight_positions_eq_of_parent_anchor_position_eq`. -/
public theorem nullableSplitRight_positions_eq_of_parent_anchor_position_eq
    (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))}
    {beforeWord : List T}
    {parentAnchor₁ parentAnchor₂ : Nonterminal M}
    {parentAnchorSuffix₁ parentAnchorSuffix₂ : List T}
    {parentAnchorContext₁ parentAnchorContext₂ :
      List (StackSymbol M)}
    {parentSuffix₁ parentSuffix₂ future₁ future₂ : List T}
    {parentContext₁ parentContext₂ : List (StackSymbol M)}
    {source middle target₁ target₂ final₁ final₂ : State M}
    {top : StackSymbol M}
    {gamma₁ gamma₂ : List (StackSymbol M)}
    (anchor₁ : VisibleSpineAnchor M base parentAnchor₁
      parentAnchorSuffix₁ beforeWord parentAnchorContext₁)
    (anchor₂ : VisibleSpineAnchor M base parentAnchor₂
      parentAnchorSuffix₂ beforeWord parentAnchorContext₂)
    (tail₁ : ZeroVisibleTail M base beforeWord
      parentAnchor₁ parentAnchorSuffix₁ parentAnchorContext₁
      (PDA_to_CFG.N.list source (top :: gamma₁) target₁)
      parentSuffix₁ parentContext₁)
    (tail₂ : ZeroVisibleTail M base beforeWord
      parentAnchor₂ parentAnchorSuffix₂ parentAnchorContext₂
      (PDA_to_CFG.N.list source (top :: gamma₂) target₂)
      parentSuffix₂ parentContext₂)
    (parentPosition :
      leftmostEpsilonPositionOf M parentAnchor₁ parentAnchorContext₁ =
        leftmostEpsilonPositionOf M parentAnchor₂ parentAnchorContext₂)
    (emptyCompletion : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal
        (PDA_to_CFG.N.single source top middle)]
      (([] : List T).map symbol.terminal))
    (useful₁ : (emptyStackPDA M).Reaches
      ⟨middle, future₁, gamma₁ ++ parentContext₁⟩
      ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ⟨middle, future₂, gamma₂ ++ parentContext₂⟩
      ⟨final₂, [], []⟩)
    (hlook : future₁.take 1 = future₂.take 1) :
    (LeftmostEpsilonPosition.list middle gamma₁ parentContext₁ :
        LeftmostEpsilonPosition M) =
      .list middle gamma₂ parentContext₂ := by
  exact splitRight_positions_eq_of_parent_anchor_position_eq M
    anchor₁ anchor₂ tail₁ tail₂ parentPosition emptyCompletion
    useful₁ useful₂ hlook

/-- The irreducible branch left after recursively peeling nullable paired
split-right markers.  At least one selected `single source top middle`
completion consumes a nonempty terminal word.  Both concrete parent spines,
their exact split rules, and the productive child futures are retained for
the terminal-extension argument. -/
public inductive ProductiveNonnullablePairedSplitResidual
    (M : DPDA Q T S) : Prop
  | mk
      {base : List (symbol T (Nonterminal M))} {completedWord : List T}
      {beforeWord₁ leftWord₁ beforeWord₂ leftWord₂ : List T}
      {suffix₁ suffix₂ future₁ future₂ : List T}
      {context₁ context₂ : List (StackSymbol M)}
      {source middle target₁ target₂ final₁ final₂ : State M}
      {top : StackSymbol M}
      {gamma₁ gamma₂ : List (StackSymbol M)}
      (parent₁ : ConcreteOperationalSpine M base
        (PDA_to_CFG.N.list source (top :: gamma₁) target₁)
        suffix₁ beforeWord₁ context₁)
      (length₁ : (top :: gamma₁).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (rule₁ :
        (PDA_to_CFG.N.list source (top :: gamma₁) target₁,
          [symbol.nonterminal (PDA_to_CFG.N.single source top middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle gamma₁ target₁)]) ∈
          (characteristicGrammar M).rules)
      (left₁ : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single source top middle)]
        (leftWord₁.map symbol.terminal))
      (parent₂ : ConcreteOperationalSpine M base
        (PDA_to_CFG.N.list source (top :: gamma₂) target₂)
        suffix₂ beforeWord₂ context₂)
      (length₂ : (top :: gamma₂).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (rule₂ :
        (PDA_to_CFG.N.list source (top :: gamma₂) target₂,
          [symbol.nonterminal (PDA_to_CFG.N.single source top middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle gamma₂ target₂)]) ∈
          (characteristicGrammar M).rules)
      (left₂ : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single source top middle)]
        (leftWord₂.map symbol.terminal))
      (word₁ : completedWord = beforeWord₁ ++ leftWord₁)
      (word₂ : completedWord = beforeWord₂ ++ leftWord₂)
      (nonnullable : leftWord₁ ≠ [] ∨ leftWord₂ ≠ [])
      (useful₁ : (emptyStackPDA M).Reaches
        ⟨middle, future₁, gamma₁ ++ context₁⟩
        ⟨final₁, [], []⟩)
      (useful₂ : (emptyStackPDA M).Reaches
        ⟨middle, future₂, gamma₂ ++ context₂⟩
        ⟨final₂, [], []⟩)
      (lookahead : future₁.take 1 = future₂.take 1) :
      ProductiveNonnullablePairedSplitResidual M

/-- Productive paired visible anchors synchronize exactly after recursively
peeling split-right markers whose selected `single` completes on `ε`.
The only branch not discharged by this shorter-frontier recursion is the
explicit nonnullable split residual above. -/
public theorem productivePairedVisibleAnchor_positions_eq_or_nonnullable
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {A₁ A₂ : Nonterminal M} {suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {future₁ future₂ : List T} {final₁ final₂ : State M}
    (paired : PairedVisibleAnchors M p preWord
      A₁ suffix₁ context₁ A₂ suffix₂ context₂)
    (useful₁ : (emptyStackPDA M).Reaches
      ⟨spineCutState M A₁, future₁,
        spineCutStack M A₁ context₁⟩
      ⟨final₁, [], []⟩)
    (useful₂ : (emptyStackPDA M).Reaches
      ⟨spineCutState M A₂, future₂,
        spineCutStack M A₂ context₂⟩
      ⟨final₂, [], []⟩)
    (hlook : future₁.take 1 = future₂.take 1) :
    leftmostEpsilonPositionOf M A₁ context₁ =
        leftmostEpsilonPositionOf M A₂ context₂ ∨
      ProductiveNonnullablePairedSplitResidual M := by
  cases paired with
  | root => exact Or.inl rfl
  | read parent₁ transition₁ rule₁ parent₂ transition₂ rule₂ =>
      obtain ⟨hnext, hgamma, hcontext⟩ :=
        concreteRead_anchor_data_eq M parent₁ parent₂
          transition₁ transition₂
      subst_vars
      exact Or.inl rfl
  | @splitRight base completedWord beforeWord₁ leftWord₁
      beforeWord₂ leftWord₂ suffix₁ suffix₂ context₁ context₂
      source middle target₁ target₂ top gamma₁ gamma₂
      parent₁ length₁ rule₁ left₁ parent₂ length₂ rule₂ left₂
      word₁ word₂ =>
      by_cases hleft₁ : leftWord₁ = []
      · by_cases hleft₂ : leftWord₂ = []
        · subst leftWord₁
          subst leftWord₂
          simp only [List.append_nil] at word₁ word₂
          subst beforeWord₁
          subst beforeWord₂
          obtain ⟨parentAnchor₁, parentAnchorSuffix₁,
              parentAnchorContext₁, anchor₁, tail₁⟩ :=
            parent₁.zeroVisibleDecomposition M
          obtain ⟨parentAnchor₂, parentAnchorSuffix₂,
              parentAnchorContext₂, anchor₂, tail₂⟩ :=
            parent₂.zeroVisibleDecomposition M
          let parentPaired := pairedVisibleAnchors_of_same_prefix M
            anchor₁ anchor₂ rfl rfl
          have return₁ : (emptyStackPDA M).Reaches
              ⟨source, future₁, top :: gamma₁ ++ context₁⟩
              ⟨middle, future₁, gamma₁ ++ context₁⟩ := by
            have core :=
              (reaches_of_characteristic_derives_single M left₁).append_stack
                (gamma₁ ++ context₁)
            have lifted := (PDA.unconsumed_input future₁).mp core
            simpa [PDA.conf.appendInput, PDA.conf.appendStack,
              List.append_assoc] using lifted
          have return₂ : (emptyStackPDA M).Reaches
              ⟨source, future₂, top :: gamma₂ ++ context₂⟩
              ⟨middle, future₂, gamma₂ ++ context₂⟩ := by
            have core :=
              (reaches_of_characteristic_derives_single M left₂).append_stack
                (gamma₂ ++ context₂)
            have lifted := (PDA.unconsumed_input future₂).mp core
            simpa [PDA.conf.appendInput, PDA.conf.appendStack,
              List.append_assoc] using lifted
          have parentListUseful₁ : (emptyStackPDA M).Reaches
              ⟨source, future₁, top :: gamma₁ ++ context₁⟩
              ⟨final₁, [], []⟩ := return₁.trans useful₁
          have parentListUseful₂ : (emptyStackPDA M).Reaches
              ⟨source, future₂, top :: gamma₂ ++ context₂⟩
              ⟨final₂, [], []⟩ := return₂.trans useful₂
          have parentAnchorUseful₁ : (emptyStackPDA M).Reaches
              ⟨spineCutState M parentAnchor₁, future₁,
                spineCutStack M parentAnchor₁ parentAnchorContext₁⟩
              ⟨final₁, [], []⟩ := by
            have lifted := (PDA.unconsumed_input future₁).mp
              (tail₁.reaches_cut M)
            have toParent : (emptyStackPDA M).Reaches
                ⟨spineCutState M parentAnchor₁, future₁,
                  spineCutStack M parentAnchor₁ parentAnchorContext₁⟩
                ⟨source, future₁, top :: gamma₁ ++ context₁⟩ := by
              simpa [PDA.conf.appendInput, spineCutState, spineCutStack,
                List.append_assoc] using lifted
            exact toParent.trans parentListUseful₁
          have parentAnchorUseful₂ : (emptyStackPDA M).Reaches
              ⟨spineCutState M parentAnchor₂, future₂,
                spineCutStack M parentAnchor₂ parentAnchorContext₂⟩
              ⟨final₂, [], []⟩ := by
            have lifted := (PDA.unconsumed_input future₂).mp
              (tail₂.reaches_cut M)
            have toParent : (emptyStackPDA M).Reaches
                ⟨spineCutState M parentAnchor₂, future₂,
                  spineCutStack M parentAnchor₂ parentAnchorContext₂⟩
                ⟨source, future₂, top :: gamma₂ ++ context₂⟩ := by
              simpa [PDA.conf.appendInput, spineCutState, spineCutStack,
                List.append_assoc] using lifted
            exact toParent.trans parentListUseful₂
          rcases productivePairedVisibleAnchor_positions_eq_or_nonnullable M
              parentPaired parentAnchorUseful₁ parentAnchorUseful₂ hlook with
            parentPosition | residual
          · left
            exact nullableSplitRight_positions_eq_of_parent_anchor_position_eq M
              anchor₁ anchor₂ tail₁ tail₂ parentPosition left₁
              useful₁ useful₂ hlook
          · exact Or.inr residual
        · exact Or.inr <| ProductiveNonnullablePairedSplitResidual.mk
            parent₁ length₁ rule₁ left₁
            parent₂ length₂ rule₂ left₂ word₁ word₂
            (Or.inr hleft₂) useful₁ useful₂ hlook
      · exact Or.inr <| ProductiveNonnullablePairedSplitResidual.mk
          parent₁ length₁ rule₁ left₁
          parent₂ length₂ rule₂ left₂ word₁ word₂
          (Or.inl hleft₁) useful₁ useful₂ hlook
termination_by p.length
decreasing_by
  simp_all only [List.length_append, List.length_singleton]
  omega

end

end DPDA_to_LR
