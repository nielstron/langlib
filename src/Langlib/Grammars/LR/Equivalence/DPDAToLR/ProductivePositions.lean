module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ConcreteReturnClassifier
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.PendingFrontierRigidity
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ProductiveListPositions

/-!
# Productive paired-anchor position synchronization

Counted pending-frontier rigidity identifies how much input two aligned
parent spines have consumed.  In the split-right case this identifies their
selected `single` completion words.  Recursing on the shorter parent frontier
then synchronizes the exact parent positions, after which the boundary-
sensitive split-right theorem identifies the two child positions.
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

private theorem productivePairedVisibleAnchor_positions_eq
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {A₁ A₂ : Nonterminal M}
    {suffix₁ suffix₂ : List T}
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
      leftmostEpsilonPositionOf M A₂ context₂ := by
  cases paired with
  | root => rfl
  | read parent₁ transition₁ rule₁ parent₂ transition₂ rule₂ =>
      obtain ⟨hnext, hgamma, hcontext⟩ :=
        concreteRead_anchor_data_eq M parent₁ parent₂
          transition₁ transition₂
      subst_vars
      rfl
  | @splitRight base completedWord beforeWord₁ leftWord₁
      beforeWord₂ leftWord₂ suffix₁ suffix₂ context₁ context₂
      source middle target₁ target₂ top gamma₁ gamma₂
      parent₁ length₁ rule₁ left₁ parent₂ length₂ rule₂ left₂
      word₁ word₂ =>
      obtain ⟨steps₁, parentTrace₁Raw⟩ :=
        parent₁.exists_pendingFrontierTrace M (remaining := leftWord₁)
      obtain ⟨steps₂, parentTrace₂Raw⟩ :=
        parent₂.exists_pendingFrontierTrace M (remaining := leftWord₂)
      have parentTrace₁ : PendingFrontierTrace M preWord
          ⟨base, PDA_to_CFG.N.list source (top :: gamma₁) target₁,
            suffix₁, beforeWord₁, context₁, leftWord₁⟩ steps₁ := by
        simpa only [word₁] using parentTrace₁Raw
      have parentTrace₂ : PendingFrontierTrace M preWord
          ⟨base, PDA_to_CFG.N.list source (top :: gamma₂) target₂,
            suffix₂, beforeWord₂, context₂, leftWord₂⟩ steps₂ := by
        simpa only [word₂] using parentTrace₂Raw
      have return₁ : (emptyStackPDA M).Reaches
          ⟨source, leftWord₁ ++ future₁,
            top :: gamma₁ ++ context₁⟩
          ⟨middle, future₁, gamma₁ ++ context₁⟩ := by
        have core :=
          (reaches_of_characteristic_derives_single M left₁).append_stack
            (gamma₁ ++ context₁)
        have lifted := (PDA.unconsumed_input future₁).mp core
        simpa [PDA.conf.appendInput, PDA.conf.appendStack,
          List.append_assoc] using lifted
      have return₂ : (emptyStackPDA M).Reaches
          ⟨source, leftWord₂ ++ future₂,
            top :: gamma₂ ++ context₂⟩
          ⟨middle, future₂, gamma₂ ++ context₂⟩ := by
        have core :=
          (reaches_of_characteristic_derives_single M left₂).append_stack
            (gamma₂ ++ context₂)
        have lifted := (PDA.unconsumed_input future₂).mp core
        simpa [PDA.conf.appendInput, PDA.conf.appendStack,
          List.append_assoc] using lifted
      have parentUseful₁ : (emptyStackPDA M).Reaches
          ⟨source, leftWord₁ ++ future₁,
            top :: gamma₁ ++ context₁⟩
          ⟨final₁, [], []⟩ := return₁.trans useful₁
      have parentUseful₂ : (emptyStackPDA M).Reaches
          ⟨source, leftWord₂ ++ future₂,
            top :: gamma₂ ++ context₂⟩
          ⟨final₂, [], []⟩ := return₂.trans useful₂
      have hbefore : beforeWord₁ = beforeWord₂ := by
        have consumedEq := productivePendingFrontier_same_frontier_consumed_eq
          M parentTrace₁ parentTrace₂ rfl
          (by simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack, List.append_assoc] using
            parentUseful₁)
          (by simpa [PendingFrontierPosition.cut, PDA.conf.appendInput,
              spineCutState, spineCutStack, List.append_assoc] using
            parentUseful₂)
          hlook
        exact consumedEq
      have hleft : leftWord₁ = leftWord₂ := by
        apply List.append_cancel_left
        exact word₁.symm.trans (hbefore ▸ word₂)
      subst beforeWord₂
      subst leftWord₂
      obtain ⟨parentAnchor₁, parentAnchorSuffix₁,
          parentAnchorContext₁, anchor₁, tail₁⟩ :=
        parent₁.zeroVisibleDecomposition M
      obtain ⟨parentAnchor₂, parentAnchorSuffix₂,
          parentAnchorContext₂, anchor₂, tail₂⟩ :=
        parent₂.zeroVisibleDecomposition M
      let parentPaired := pairedVisibleAnchors_of_same_prefix M
        anchor₁ anchor₂ rfl rfl
      have parentAnchorUseful₁ : (emptyStackPDA M).Reaches
          ⟨spineCutState M parentAnchor₁, leftWord₁ ++ future₁,
            spineCutStack M parentAnchor₁ parentAnchorContext₁⟩
          ⟨final₁, [], []⟩ := by
        have lifted := (PDA.unconsumed_input (leftWord₁ ++ future₁)).mp
          (tail₁.reaches_cut M)
        have toParent : (emptyStackPDA M).Reaches
            ⟨spineCutState M parentAnchor₁, leftWord₁ ++ future₁,
              spineCutStack M parentAnchor₁ parentAnchorContext₁⟩
            ⟨source, leftWord₁ ++ future₁,
              top :: gamma₁ ++ context₁⟩ := by
          simpa [PDA.conf.appendInput, spineCutState, spineCutStack,
            List.append_assoc] using lifted
        exact toParent.trans parentUseful₁
      have parentAnchorUseful₂ : (emptyStackPDA M).Reaches
          ⟨spineCutState M parentAnchor₂, leftWord₁ ++ future₂,
            spineCutStack M parentAnchor₂ parentAnchorContext₂⟩
          ⟨final₂, [], []⟩ := by
        have lifted := (PDA.unconsumed_input (leftWord₁ ++ future₂)).mp
          (tail₂.reaches_cut M)
        have toParent : (emptyStackPDA M).Reaches
            ⟨spineCutState M parentAnchor₂, leftWord₁ ++ future₂,
              spineCutStack M parentAnchor₂ parentAnchorContext₂⟩
            ⟨source, leftWord₁ ++ future₂,
              top :: gamma₂ ++ context₂⟩ := by
          simpa [PDA.conf.appendInput, spineCutState, spineCutStack,
            List.append_assoc] using lifted
        exact toParent.trans parentUseful₂
      have parentLook : (leftWord₁ ++ future₁).take 1 =
          (leftWord₁ ++ future₂).take 1 :=
        take_one_append_eq hlook
      have parentPosition := productivePairedVisibleAnchor_positions_eq M
        parentPaired parentAnchorUseful₁ parentAnchorUseful₂ parentLook
      exact splitRight_positions_eq_of_parent_anchor_position_eq M
        anchor₁ anchor₂ tail₁ tail₂ parentPosition left₁
        useful₁ useful₂ hlook
termination_by p.length
decreasing_by
  simp_all only [List.length_append, List.length_singleton]
  omega

/-- Productive paired visible anchors have the same exact structural
position, including the displayed-list/hidden-context boundary. -/
public theorem productivePairedVisibleAnchorPositionsEqual
    (M : DPDA Q T S) : ProductivePairedVisibleAnchorPositionsEqual M := by
  intro p preWord A₁ A₂ suffix₁ suffix₂ context₁ context₂
    future₁ future₂ final₁ final₂ paired useful₁ useful₂ hlook
  exact productivePairedVisibleAnchor_positions_eq M
    paired useful₁ useful₂ hlook

end

end DPDA_to_LR
