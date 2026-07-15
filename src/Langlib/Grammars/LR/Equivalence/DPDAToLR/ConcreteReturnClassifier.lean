module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SamePrefixEpsilonReturns

/-!
# Assembly of the concrete empty-return classifier

Equality of the two terminally completed sentential forms leaves only two
shapes: the visible prefixes agree, or one is a strict terminal extension of
the other.  Same-prefix transition returns are handled by the structural
epsilon-return uniqueness theorem.  This module isolates the one remaining
ancestry statement for strict terminal extensions and proves all downstream
classifier assembly from those two inputs.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Generic semantic interface expected from the paired-anchor interval
argument.  The two anchors represent the same visible frontier and completed
word.  If both physical cuts have useful futures with the same one-symbol
lookahead, their control states and complete stacks agree. -/
@[expose]
public def ProductivePairedVisibleAnchorCutsEqual
    (M : DPDA Q T S) : Prop :=
  ∀ (p : List (symbol T (Nonterminal M))) (preWord : List T)
      (A₁ A₂ : Nonterminal M)
      (anchorSuffix₁ anchorSuffix₂ : List T)
      (anchorContext₁ anchorContext₂ : List (StackSymbol M))
      (future₁ future₂ : List T) (final₁ final₂ : State M),
    PairedVisibleAnchors M p preWord
        A₁ anchorSuffix₁ anchorContext₁
        A₂ anchorSuffix₂ anchorContext₂ →
    (emptyStackPDA M).Reaches
        ⟨spineCutState M A₁, future₁,
          spineCutStack M A₁ anchorContext₁⟩
        ⟨final₁, [], []⟩ →
    (emptyStackPDA M).Reaches
        ⟨spineCutState M A₂, future₂,
          spineCutStack M A₂ anchorContext₂⟩
        ⟨final₂, [], []⟩ →
    future₁.take 1 = future₂.take 1 →
    spineCutState M A₁ = spineCutState M A₂ ∧
      spineCutStack M A₁ anchorContext₁ =
        spineCutStack M A₂ anchorContext₂

/-- Boundary-sensitive strengthening of physical cut equality.  This is the
form consumed directly by the existing leftmost-epsilon comparison API. -/
@[expose]
public def ProductivePairedVisibleAnchorPositionsEqual
    (M : DPDA Q T S) : Prop :=
  ∀ (p : List (symbol T (Nonterminal M))) (preWord : List T)
      (A₁ A₂ : Nonterminal M)
      (anchorSuffix₁ anchorSuffix₂ : List T)
      (anchorContext₁ anchorContext₂ : List (StackSymbol M))
      (future₁ future₂ : List T) (final₁ final₂ : State M),
    PairedVisibleAnchors M p preWord
        A₁ anchorSuffix₁ anchorContext₁
        A₂ anchorSuffix₂ anchorContext₂ →
    (emptyStackPDA M).Reaches
        ⟨spineCutState M A₁, future₁,
          spineCutStack M A₁ anchorContext₁⟩
        ⟨final₁, [], []⟩ →
    (emptyStackPDA M).Reaches
        ⟨spineCutState M A₂, future₂,
          spineCutStack M A₂ anchorContext₂⟩
        ⟨final₂, [], []⟩ →
    future₁.take 1 = future₂.take 1 →
    leftmostEpsilonPositionOf M A₁ anchorContext₁ =
      leftmostEpsilonPositionOf M A₂ anchorContext₂

/-- Equality of the boundary-sensitive anchor positions implies equality of
their physical cuts. -/
public theorem productivePairedVisibleAnchorCutsEqual_of_positionsEqual
    (M : DPDA Q T S)
    (h : ProductivePairedVisibleAnchorPositionsEqual M) :
    ProductivePairedVisibleAnchorCutsEqual M := by
  intro p preWord A₁ A₂ anchorSuffix₁ anchorSuffix₂
    anchorContext₁ anchorContext₂ future₁ future₂ final₁ final₂
    paired useful₁ useful₂ hlook
  have hposition := h p preWord A₁ A₂
    anchorSuffix₁ anchorSuffix₂ anchorContext₁ anchorContext₂
    future₁ future₂ final₁ final₂
    paired useful₁ useful₂ hlook
  have hconf := congrArg
    (fun position => position.conf M ([] : List T)) hposition
  change (leftmostEpsilonPositionOf M A₁ anchorContext₁).conf M [] =
    (leftmostEpsilonPositionOf M A₂ anchorContext₂).conf M [] at hconf
  rw [leftmostEpsilonPositionOf_conf,
    leftmostEpsilonPositionOf_conf] at hconf
  exact ⟨congrArg PDA.conf.state hconf, congrArg PDA.conf.stack hconf⟩

/-- The boundary-sensitive paired-anchor theorem is sufficient for the full
same-prefix epsilon-return uniqueness property. -/
public theorem samePrefixEpsilonReturnsStateUnique_of_productivePositions
    (M : DPDA Q T S)
    (h : ProductivePairedVisibleAnchorPositionsEqual M) :
    SamePrefixEpsilonReturnsStateUnique M := by
  intro p q₁ q₂ suffix₁ suffix₂ data
  rcases data with ⟨completion, context₁, context₂,
    anchor₁, anchor₂, anchorSuffix₁, anchorSuffix₂,
    anchorContext₁, anchorContext₂,
    leftAnchor, rightAnchor, leftTail, rightTail, leftBearing, paired,
    final₁, final₂, useful₁, useful₂, hlook⟩
  have anchorUseful₁ : (emptyStackPDA M).Reaches
      ⟨spineCutState M anchor₁, suffix₁,
        spineCutStack M anchor₁ anchorContext₁⟩
      ⟨final₁, [], []⟩ := by
    have lifted := (PDA.unconsumed_input suffix₁).mp
      (leftTail.reaches_cut M)
    have lifted' : (emptyStackPDA M).Reaches
        ⟨spineCutState M anchor₁, suffix₁,
          spineCutStack M anchor₁ anchorContext₁⟩
        ⟨q₁, suffix₁, context₁⟩ := by
      simpa [PDA.conf.appendInput, spineCutState, spineCutStack]
        using lifted
    exact lifted'.trans useful₁
  have anchorUseful₂ : (emptyStackPDA M).Reaches
      ⟨spineCutState M anchor₂, suffix₂,
        spineCutStack M anchor₂ anchorContext₂⟩
      ⟨final₂, [], []⟩ := by
    have lifted := (PDA.unconsumed_input suffix₂).mp
      (rightTail.reaches_cut M)
    have lifted' : (emptyStackPDA M).Reaches
        ⟨spineCutState M anchor₂, suffix₂,
          spineCutStack M anchor₂ anchorContext₂⟩
        ⟨q₂, suffix₂, context₂⟩ := by
      simpa [PDA.conf.appendInput, spineCutState, spineCutStack]
        using lifted
    exact lifted'.trans useful₂
  have hposition := h p completion anchor₁ anchor₂
    anchorSuffix₁ anchorSuffix₂ anchorContext₁ anchorContext₂
    suffix₁ suffix₂ final₁ final₂
    paired anchorUseful₁ anchorUseful₂ hlook
  exact zeroVisibleEmptyList_state_eq_of_anchor_position_eq M
    leftAnchor rightAnchor leftTail rightTail hposition
    useful₁ useful₂ hlook

/-- From one physical zero-visible anchor, an empty-list endpoint cannot
coexist productively with a `single` endpoint that has a useful read on the
same lookahead. -/
public theorem zeroVisibleEmptyList_read_false_of_anchor_position_eq
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {completion : List T}
    {emptyAnchor readAnchor : Nonterminal M}
    {emptyAnchorSuffix readAnchorSuffix emptySuffix readNodeSuffix
      readFutureSuffix : List T}
    {emptyAnchorContext readAnchorContext emptyContext readContext :
      List (StackSymbol M)}
    {emptyState source target next emptyFinal readFinal : State M}
    {a : T} {top : StackSymbol M}
    {replacement : List (StackSymbol M)}
    (emptyAnchorWitness : VisibleSpineAnchor M p emptyAnchor
      emptyAnchorSuffix completion emptyAnchorContext)
    (readAnchorWitness : VisibleSpineAnchor M p readAnchor
      readAnchorSuffix completion readAnchorContext)
    (emptyTail : ZeroVisibleTail M p completion
      emptyAnchor emptyAnchorSuffix emptyAnchorContext
      (PDA_to_CFG.N.list emptyState [] emptyState)
      emptySuffix emptyContext)
    (readTail : ZeroVisibleTail M p completion
      readAnchor readAnchorSuffix readAnchorContext
      (PDA_to_CFG.N.single source top target) readNodeSuffix
      readContext)
    (hposition : leftmostEpsilonPositionOf M emptyAnchor
        emptyAnchorContext =
      leftmostEpsilonPositionOf M readAnchor readAnchorContext)
    (readTransition : (next, replacement) ∈
      (emptyStackPDA M).transition_fun source a top)
    (emptyUseful : (emptyStackPDA M).Reaches
      ⟨emptyState, emptySuffix, emptyContext⟩
      ⟨emptyFinal, [], []⟩)
    (readUseful : (emptyStackPDA M).Reaches
      ⟨source, a :: readFutureSuffix, top :: readContext⟩
      ⟨readFinal, [], []⟩)
    (hlook : emptySuffix.take 1 =
      (a :: readFutureSuffix).take 1) : False := by
  let start := leftmostEpsilonPositionOf M emptyAnchor emptyAnchorContext
  have emptyTrace : LeftmostEpsilonTrace M start
      (.list emptyState [] emptyContext) := by
    simpa [start, leftmostEpsilonPositionOf] using
      emptyTail.leftmostEpsilonTrace M
  have readTrace : LeftmostEpsilonTrace M start
      (.single source top readContext) := by
    simpa [start, hposition, leftmostEpsilonPositionOf] using
      readTail.leftmostEpsilonTrace M
  have emptyAnchorRun := (PDA.unconsumed_input emptySuffix).mp
    (emptyAnchorWitness.prefixPath M)
  have readAnchorRun :=
    (PDA.unconsumed_input (a :: readFutureSuffix)).mp
    (readAnchorWitness.prefixPath M)
  have emptyGlobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, completion ++ emptySuffix,
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M emptySuffix) := by
    change (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, completion ++ emptySuffix,
        [(emptyStackPDA M).start_symbol]⟩
      ((leftmostEpsilonPositionOf M emptyAnchor
        emptyAnchorContext).conf M emptySuffix)
    rw [leftmostEpsilonPositionOf_conf]
    simpa [PDA.conf.appendInput] using emptyAnchorRun
  have readGlobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        completion ++ (a :: readFutureSuffix),
        [(emptyStackPDA M).start_symbol]⟩
      (start.conf M (a :: readFutureSuffix)) := by
    change (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state,
        completion ++ (a :: readFutureSuffix),
        [(emptyStackPDA M).start_symbol]⟩
      ((leftmostEpsilonPositionOf M emptyAnchor
        emptyAnchorContext).conf M (a :: readFutureSuffix))
    rw [hposition, leftmostEpsilonPositionOf_conf]
    simpa [PDA.conf.appendInput] using readAnchorRun
  rcases leftmostEpsilonTrace_productive_comparable M
      emptyTrace readTrace emptyGlobal readGlobal
      (by simpa [LeftmostEpsilonPosition.conf] using emptyUseful)
      (by simpa [LeftmostEpsilonPosition.conf] using readUseful)
      hlook with between | between
  · cases between with
    | head first rest => cases first
  · cases between with
    | head first rest =>
        cases first with
        | epsilon epsilonTransition =>
            have hempty : ∃ tail, emptySuffix = a :: tail := by
              cases emptySuffix with
              | nil => simp at hlook
              | cons b tail =>
                  have hab : b = a := by simpa using hlook
                  subst b
                  exact ⟨tail, rfl⟩
            obtain ⟨emptyRest, rfl⟩ := hempty
            apply read_epsilon_not_both_useful M
              readTransition epsilonTransition
            simpa [LeftmostEpsilonPosition.conf] using
              (rest.reaches M (a :: emptyRest)).trans emptyUseful

/-- The exact strict-prefix ancestry obligation left by the concrete
empty-return classifier.  The later visible prefix differs only by a
nonempty terminal block.  Such a pair must expose one of the useful
cycle/growth obstructions.

The statement deliberately does not ask which edge is transition-generated:
`ConcreteEmptyEdge.transitionEdge_of_strictTerminalExtension` already shows
that the later edge is transition-generated. -/
@[expose]
public def StrictTerminalEmptyReturnPairsClassified
    (M : DPDA Q T S) : Prop :=
  ∀ (earlyPrefix latePrefix : List (symbol T (Nonterminal M)))
      (earlyState lateState : State M)
      (earlySuffix lateSuffix displacement : List T),
    ∀ (earlyEdge : ConcreteEmptyEdge M earlyPrefix earlyState earlySuffix)
      (lateEdge : ConcreteEmptyEdge M latePrefix lateState lateSuffix),
    latePrefix = earlyPrefix ++ displacement.map symbol.terminal →
    displacement ≠ [] →
    earlySuffix.take 1 = (displacement ++ lateSuffix).take 1 →
    UsefulReturnObstruction M

/-- The non-read fragment of a concrete empty edge.  A read-generated early
edge is already incompatible with every strict terminal extension, so only
epsilon and structural split-right introductions survive in the strict
classifier. -/
public inductive ConcreteNonreadEmptyEdge (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → State M → List T → Prop
  | epsilon
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord : List T} {context : List (StackSymbol M)}
      {source : State M} {Z : StackSymbol M} {q : State M}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single source Z q) suffix preWord context)
      (transition : (q, []) ∈
        (emptyStackPDA M).transition_fun' source Z)
      (rule : (PDA_to_CFG.N.single source Z q,
          [symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteNonreadEmptyEdge M p q suffix
  | split
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord leftWord : List T}
      {context : List (StackSymbol M)}
      {source : State M} {Z : StackSymbol M} {q : State M}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.list source [Z] q) suffix preWord context)
      (length : [Z].length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (rule : (PDA_to_CFG.N.list source [Z] q,
          [symbol.nonterminal (PDA_to_CFG.N.single source Z q),
            symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules)
      (left : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single source Z q)]
        (leftWord.map symbol.terminal)) :
      ConcreteNonreadEmptyEdge M
        (p ++ [symbol.nonterminal (PDA_to_CFG.N.single source Z q)])
        q suffix

/-- Forget the non-read tag. -/
public theorem ConcreteNonreadEmptyEdge.edge (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix : List T} (edge : ConcreteNonreadEmptyEdge M p q suffix) :
    ConcreteEmptyEdge M p q suffix := by
  cases edge with
  | epsilon parent transition rule =>
      exact ConcreteEmptyEdge.epsilon parent transition rule
  | split parent length rule left =>
      exact ConcreteEmptyEdge.split parent length rule left

/-- The actual strict-prefix residual after disposing of read-generated
early edges. -/
@[expose]
public def StrictTerminalNonreadEmptyReturnPairsClassified
    (M : DPDA Q T S) : Prop :=
  ∀ (earlyPrefix latePrefix : List (symbol T (Nonterminal M)))
      (earlyState lateState : State M)
      (earlySuffix lateSuffix displacement : List T),
    ConcreteNonreadEmptyEdge M earlyPrefix earlyState earlySuffix →
    ConcreteEmptyTransitionEdge M latePrefix lateState lateSuffix →
    latePrefix = earlyPrefix ++ displacement.map symbol.terminal →
    displacement ≠ [] →
    earlySuffix.take 1 = (displacement ++ lateSuffix).take 1 →
    UsefulReturnObstruction M

/-- Boundary-sensitive paired-anchor synchronization rules out every
epsilon/split early return followed by a later transition return.  Walking
the later terminal block back to its first read produces a readable `single`
at the early frontier; the earlier empty child and that single then descend
from one structural epsilon position, contradicting useful determinism. -/
public theorem
    strictTerminalNonreadEmptyReturnPairsClassified_of_productivePositions
    (M : DPDA Q T S)
    (hpositions : ProductivePairedVisibleAnchorPositionsEqual M) :
    StrictTerminalNonreadEmptyReturnPairsClassified M := by
  intro earlyPrefix latePrefix earlyState lateState
    earlySuffix lateSuffix displacement earlyEdge lateTransition
    hprefix hdisplacement hlook
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hdisplacement
  let lateEdge := lateTransition.edge M
  obtain ⟨lateCompletion, lateContext, lateChild⟩ :=
    lateEdge.exists_childSpine M
  rw [hprefix] at lateChild
  obtain ⟨parentSuffix, beforeWord, parentContext,
      source, target, next, top, replacement,
      readParent, readTransition, readRule⟩ :=
    lateChild.firstRead_of_terminalBlock M
  have earlyPrefixCompletion : (characteristicGrammar M).DerivesRightmost
      earlyPrefix (beforeWord.map symbol.terminal) :=
    (readParent.operationalSpine M).prefixDerives M
  obtain ⟨earlyContext, earlyChild⟩ :=
    (earlyEdge.edge M).exists_childSpineAtCompletion M
      earlyPrefixCompletion
  obtain ⟨earlyAnchor, earlyAnchorSuffix, earlyAnchorContext,
      earlyAnchorWitness, earlyTail⟩ :=
    earlyChild.zeroVisibleDecomposition M
  obtain ⟨readAnchor, readAnchorSuffix, readAnchorContext,
      readAnchorWitness, readTail⟩ :=
    readParent.zeroVisibleDecomposition M
  let paired := pairedVisibleAnchors_of_same_prefix M
    earlyAnchorWitness readAnchorWitness rfl rfl
  let readIntroduction : ConcreteListIntroduction M
      (earlyPrefix ++ [symbol.terminal a]) next replacement target
      parentSuffix (beforeWord ++ [a]) parentContext
      (PDA_to_CFG.N.single source top target)
      (PDA_to_CFG.N.single source top target,
        [symbol.terminal a,
          symbol.nonterminal
            (PDA_to_CFG.N.list next replacement target)]) :=
    ConcreteListIntroduction.read readParent readTransition readRule
  obtain ⟨childWord, childCompletion⟩ :=
    readIntroduction.childCompletion M
  obtain ⟨readFinal, childContinuation⟩ :=
    readIntroduction.childContinuation M
  have childUseful : (emptyStackPDA M).Reaches
      ⟨next, childWord ++ parentSuffix,
        replacement ++ parentContext⟩
      ⟨readFinal, [], []⟩ :=
    completedList_useful_with_context M
      (readIntroduction.gammaLength M) childCompletion childContinuation
  have readStep : (emptyStackPDA M).Reaches₁
      ⟨source, a :: (childWord ++ parentSuffix), top :: parentContext⟩
      ⟨next, childWord ++ parentSuffix,
        replacement ++ parentContext⟩ := by
    exact Or.inl ⟨next, replacement, readTransition, by simp⟩
  have readUseful : (emptyStackPDA M).Reaches
      ⟨source, a :: (childWord ++ parentSuffix), top :: parentContext⟩
      ⟨readFinal, [], []⟩ :=
    (Relation.ReflTransGen.single readStep).trans childUseful
  cases earlyChild.focusedExact M with
  | list _ _ _ _ _ _ earlyFinal earlyPrefixRun earlyUseful =>
      have earlyAnchorUseful : (emptyStackPDA M).Reaches
          ⟨spineCutState M earlyAnchor, earlySuffix,
            spineCutStack M earlyAnchor earlyAnchorContext⟩
          ⟨earlyFinal, [], []⟩ := by
        have lifted := (PDA.unconsumed_input earlySuffix).mp
          (earlyTail.reaches_cut M)
        have lifted' : (emptyStackPDA M).Reaches
            ⟨spineCutState M earlyAnchor, earlySuffix,
              spineCutStack M earlyAnchor earlyAnchorContext⟩
            ⟨earlyState, earlySuffix, earlyContext⟩ := by
          simpa [PDA.conf.appendInput, spineCutState, spineCutStack]
            using lifted
        exact lifted'.trans earlyUseful
      have readAnchorUseful : (emptyStackPDA M).Reaches
          ⟨spineCutState M readAnchor,
            a :: (childWord ++ parentSuffix),
            spineCutStack M readAnchor readAnchorContext⟩
          ⟨readFinal, [], []⟩ := by
        have lifted :=
          (PDA.unconsumed_input (a :: (childWord ++ parentSuffix))).mp
            (readTail.reaches_cut M)
        have lifted' : (emptyStackPDA M).Reaches
            ⟨spineCutState M readAnchor,
              a :: (childWord ++ parentSuffix),
              spineCutStack M readAnchor readAnchorContext⟩
            ⟨source, a :: (childWord ++ parentSuffix),
              top :: parentContext⟩ := by
          simpa [PDA.conf.appendInput, spineCutState, spineCutStack]
            using lifted
        exact lifted'.trans readUseful
      have firstLook : earlySuffix.take 1 = [a] := by
        simpa using hlook
      have anchorLook : earlySuffix.take 1 =
          (a :: (childWord ++ parentSuffix)).take 1 := by
        simpa using firstLook
      have hposition := hpositions earlyPrefix beforeWord
        earlyAnchor readAnchor earlyAnchorSuffix readAnchorSuffix
        earlyAnchorContext readAnchorContext
        earlySuffix (a :: (childWord ++ parentSuffix))
        earlyFinal readFinal paired earlyAnchorUseful readAnchorUseful
        anchorLook
      exact False.elim <|
        zeroVisibleEmptyList_read_false_of_anchor_position_eq M
          earlyAnchorWitness readAnchorWitness earlyTail readTail
          hposition readTransition earlyUseful readUseful anchorLook

/-- Read-generated early returns admit no strict terminal extension at all;
hence the full strict classifier reduces to its epsilon/split fragment. -/
public theorem strictTerminalEmptyReturnPairsClassified_of_nonread
    (M : DPDA Q T S)
    (hnonread : StrictTerminalNonreadEmptyReturnPairsClassified M) :
    StrictTerminalEmptyReturnPairsClassified M := by
  intro earlyPrefix latePrefix earlyState lateState
    earlySuffix lateSuffix displacement earlyEdge lateEdge
    hprefix hdisplacement hlook
  have lateTransition :=
    lateEdge.transitionEdge_of_strictTerminalExtension M
      hprefix hdisplacement
  cases earlyEdge with
  | @read base suffix preWord context source a Z q
      parent transition rule =>
      obtain ⟨b, rest, rfl⟩ :=
        List.exists_cons_of_ne_nil hdisplacement
      obtain ⟨completion, lateContext, lateSpine⟩ :=
        lateEdge.exists_childSpine M
      apply False.elim
      apply concreteReadEmptyReturn_no_strictTerminalExtension M
        parent transition
      simpa [hprefix, List.map_cons, List.append_assoc] using lateSpine
  | epsilon parent transition rule =>
      exact hnonread _ _ _ _ _ _ _
        (.epsilon parent transition rule) lateTransition
        hprefix hdisplacement hlook
  | split parent length rule left =>
      exact hnonread _ _ _ _ _ _ _
        (.split parent length rule left) lateTransition
        hprefix hdisplacement hlook

private theorem take_one_nonempty_append_right
    {z left right : List T} (hz : z ≠ []) :
    (z ++ left).take 1 = (z ++ right).take 1 := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hz
  simp

/-- The left-transition directional classifier follows from same-prefix
epsilon-return uniqueness and the single strict-terminal ancestry property. -/
public theorem concreteLeftTransitionReturnPairsClassified_of_structural
    (M : DPDA Q T S)
    (hsame : SamePrefixEpsilonReturnsStateUnique M)
    (hstrict : StrictTerminalEmptyReturnPairsClassified M) :
    ConcreteLeftTransitionReturnPairsClassified M := by
  intro p₁ p₂ q₁ q₂ s₁ s₂ y transition₁ edge₂ hform hlook
  let edge₁ := transition₁.edge M
  rcases concreteEmptyReturn_append_terminals_eq_cases hform with
      ⟨z, hp₁, hs₂⟩ | ⟨z, hp₂, hy⟩
  · by_cases hz : z = []
    · subst z
      simp only [List.map_nil, List.append_nil] at hp₁ hs₂
      subst p₁
      subst s₂
      left
      refine ⟨rfl, ?_⟩
      exact concreteTransitionEmptyReturn_samePrefix_state_eq_of_structural
        M hsame transition₁ edge₂ hlook
    · right
      apply hstrict p₂ p₁ q₂ q₁ s₂ s₁ z edge₂ edge₁ hp₁ hz
      rw [hs₂]
      exact take_one_nonempty_append_right hz
  · by_cases hz : z = []
    · subst z
      simp only [List.map_nil, List.append_nil] at hp₂ hy
      subst p₂
      subst y
      left
      exact ⟨rfl,
        concreteTransitionEmptyReturn_samePrefix_state_eq_of_structural
          M hsame transition₁ edge₂ hlook⟩
    · right
      apply hstrict p₁ p₂ q₁ q₂ s₁ s₂ z edge₁ edge₂ hp₂ hz
      simpa [hy] using hlook

/-- The right-transition directional classifier has the same strict branch;
only the same-prefix lookahead must be reversed before applying the structural
transition-vs-return theorem. -/
public theorem concreteRightTransitionReturnPairsClassified_of_structural
    (M : DPDA Q T S)
    (hsame : SamePrefixEpsilonReturnsStateUnique M)
    (hstrict : StrictTerminalEmptyReturnPairsClassified M) :
    ConcreteRightTransitionReturnPairsClassified M := by
  intro p₁ p₂ q₁ q₂ s₁ s₂ y edge₁ transition₂ hform hlook
  let edge₂ := transition₂.edge M
  rcases concreteEmptyReturn_append_terminals_eq_cases hform with
      ⟨z, hp₁, hs₂⟩ | ⟨z, hp₂, hy⟩
  · by_cases hz : z = []
    · subst z
      simp only [List.map_nil, List.append_nil] at hp₁ hs₂
      subst p₁
      subst s₂
      left
      refine ⟨rfl, ?_⟩
      exact (concreteTransitionEmptyReturn_samePrefix_state_eq_of_structural
        M hsame transition₂ edge₁ hlook.symm).symm
    · right
      apply hstrict p₂ p₁ q₂ q₁ s₂ s₁ z edge₂ edge₁ hp₁ hz
      rw [hs₂]
      exact take_one_nonempty_append_right hz
  · by_cases hz : z = []
    · subst z
      simp only [List.map_nil, List.append_nil] at hp₂ hy
      subst p₂
      subst y
      left
      refine ⟨rfl, ?_⟩
      exact (concreteTransitionEmptyReturn_samePrefix_state_eq_of_structural
        M hsame transition₂ edge₁ hlook.symm).symm
    · right
      apply hstrict p₁ p₂ q₁ q₂ s₁ s₂ z edge₁ edge₂ hp₂ hz
      simpa [hy] using hlook

/-- Complete concrete pair classification once the same-prefix and strict
terminal ancestry statements have been supplied. -/
public theorem concreteEmptyReturnPairsClassified_of_structural
    (M : DPDA Q T S)
    (hsame : SamePrefixEpsilonReturnsStateUnique M)
    (hstrict : StrictTerminalEmptyReturnPairsClassified M) :
    ConcreteEmptyReturnPairsClassified M :=
  concreteEmptyReturnPairsClassified_of_transitionSides M
    (concreteLeftTransitionReturnPairsClassified_of_structural
      M hsame hstrict)
    (concreteRightTransitionReturnPairsClassified_of_structural
      M hsame hstrict)

/-- One boundary-sensitive paired-anchor synchronization theorem discharges
both the same-prefix epsilon branch and every strict terminal displacement,
and therefore supplies the complete concrete empty-return classifier. -/
public theorem concreteEmptyReturnPairsClassified_of_productivePositions
    (M : DPDA Q T S)
    (hpositions : ProductivePairedVisibleAnchorPositionsEqual M) :
    ConcreteEmptyReturnPairsClassified M := by
  apply concreteEmptyReturnPairsClassified_of_structural M
    (samePrefixEpsilonReturnsStateUnique_of_productivePositions
      M hpositions)
  apply strictTerminalEmptyReturnPairsClassified_of_nonread M
  exact
    strictTerminalNonreadEmptyReturnPairsClassified_of_productivePositions
      M hpositions

end

end DPDA_to_LR
