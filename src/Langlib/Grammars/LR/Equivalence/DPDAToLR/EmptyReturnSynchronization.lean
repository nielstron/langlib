module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulEpsilonCycles
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ZeroVisibleSpine
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SpineSynchronization
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.InputDisplacement

/-!
# Synchronizing concrete empty returns

Empty-list occurrences forget the stack symbol removed by their introducing
edge.  The concrete edge types below retain that edge together with the exact
outer stack context supplied by `ConcreteOperationalSpine`.  They are kept
independent of `EmptyReturns` so that the latter can adapt its syntax-facing
edge types without creating an import cycle.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- The two impossible operational outcomes of a genuinely distinct pair of
useful empty returns.  This definition is syntax-independent and can be
shared by both the concrete synchronization proof and its grammar adapter. -/
@[expose]
public def UsefulReturnObstruction (M : DPDA Q T S) : Prop :=
  (∃ (c : PDA.conf (emptyStackPDA M)) (final : State M),
      Relation.TransGen
        (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M)) c c ∧
      (emptyStackPDA M).Reaches c ⟨final, [], []⟩) ∨
  ∃ (q final : State M) (base extra context : List (StackSymbol M))
      (input : List T),
    (emptyStackPDA M).Reaches
      ⟨q, [], base⟩ ⟨q, [], base ++ extra⟩ ∧
    extra ≠ [] ∧
    (emptyStackPDA M).Reaches
      ⟨q, input, base ++ extra ++ context⟩ ⟨final, [], []⟩

/-- Useful cycles and nonempty stack self-embeddings are excluded by the
normalized FS→ES kernels. -/
public theorem noUsefulReturnObstruction (M : DPDA Q T S) :
    ¬ UsefulReturnObstruction M := by
  rintro (⟨c, final, hcycle, huseful⟩ |
    ⟨q, final, base, extra, context, input,
      hgrowth, hextra, huseful⟩)
  · exact emptyStack_no_useful_cycle M hcycle huseful
  · exact emptyStack_no_useful_stack_growth M
      hgrowth hextra huseful

/-- A concrete normalized edge introducing an active `list q [] q` node.
The chosen terminal completion and exact physical context are existential in
the constructors and therefore do not burden the syntax-facing indices. -/
public inductive ConcreteEmptyEdge (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → State M → List T → Prop
  | read
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord : List T} {context : List (StackSymbol M)}
      {source : State M} {a : T} {Z : StackSymbol M} {q : State M}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single source Z q) suffix preWord context)
      (htransition : (q, []) ∈
        (emptyStackPDA M).transition_fun source a Z)
      (hrule : (PDA_to_CFG.N.single source Z q,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteEmptyEdge M (p ++ [symbol.terminal a]) q suffix
  | epsilon
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord : List T} {context : List (StackSymbol M)}
      {source : State M} {Z : StackSymbol M} {q : State M}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single source Z q) suffix preWord context)
      (htransition : (q, []) ∈
        (emptyStackPDA M).transition_fun' source Z)
      (hrule : (PDA_to_CFG.N.single source Z q,
          [symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteEmptyEdge M p q suffix
  | split
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord leftWord : List T}
      {context : List (StackSymbol M)}
      {source : State M} {Z : StackSymbol M} {q : State M}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.list source [Z] q) suffix preWord context)
      (hlength : [Z].length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list source [Z] q,
          [symbol.nonterminal (PDA_to_CFG.N.single source Z q),
            symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules)
      (hleft : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single source Z q)]
        (leftWord.map symbol.terminal)) :
      ConcreteEmptyEdge M
        (p ++ [symbol.nonterminal (PDA_to_CFG.N.single source Z q)])
        q suffix

/-- The transition-generated concrete empty edges, excluding structural
split-right introductions. -/
public inductive ConcreteEmptyTransitionEdge (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → State M → List T → Prop
  | read
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord : List T} {context : List (StackSymbol M)}
      {source : State M} {a : T} {Z : StackSymbol M} {q : State M}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single source Z q) suffix preWord context)
      (htransition : (q, []) ∈
        (emptyStackPDA M).transition_fun source a Z)
      (hrule : (PDA_to_CFG.N.single source Z q,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteEmptyTransitionEdge M (p ++ [symbol.terminal a]) q suffix
  | epsilon
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord : List T} {context : List (StackSymbol M)}
      {source : State M} {Z : StackSymbol M} {q : State M}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single source Z q) suffix preWord context)
      (htransition : (q, []) ∈
        (emptyStackPDA M).transition_fun' source Z)
      (hrule : (PDA_to_CFG.N.single source Z q,
          [symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteEmptyTransitionEdge M p q suffix

/-- Forgetting the transition-only tag gives the corresponding concrete
empty edge. -/
public theorem ConcreteEmptyTransitionEdge.edge (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix : List T}
    (h : ConcreteEmptyTransitionEdge M p q suffix) :
    ConcreteEmptyEdge M p q suffix := by
  cases h with
  | read parent htransition hrule =>
      exact ConcreteEmptyEdge.read parent htransition hrule
  | epsilon parent htransition hrule =>
      exact ConcreteEmptyEdge.epsilon parent htransition hrule

/-- An empty edge at a prefix which strictly extends another prefix by
terminals cannot be a structural split-right edge: such an edge ends in a
nonterminal marker.  It is therefore transition-generated. -/
public theorem ConcreteEmptyEdge.transitionEdge_of_strictTerminalExtension
    (M : DPDA Q T S)
    {p base : List (symbol T (Nonterminal M))}
    {q : State M} {suffix z : List T}
    (edge : ConcreteEmptyEdge M p q suffix)
    (hp : p = base ++ z.map symbol.terminal)
    (hz : z ≠ []) :
    ConcreteEmptyTransitionEdge M p q suffix := by
  cases edge with
  | read parent htransition hrule =>
      exact ConcreteEmptyTransitionEdge.read parent htransition hrule
  | epsilon parent htransition hrule =>
      exact ConcreteEmptyTransitionEdge.epsilon parent htransition hrule
  | @split edgeBase suffix preWord leftWord context source Z q
      parent hlength hrule hleft =>
      let a := z.getLast hz
      have hzform : z.dropLast ++ [a] = z :=
        List.dropLast_append_getLast hz
      have hp' : edgeBase ++
            [symbol.nonterminal (PDA_to_CFG.N.single source Z q)] =
          (base ++ z.dropLast.map symbol.terminal) ++
            [symbol.terminal a] := by
        rw [← hzform] at hp
        simpa [List.map_append, List.append_assoc] using hp
      have hlast := List.append_inj_right' hp' (by simp)
      cases (List.cons.inj hlast).1

/-- The child of a concrete empty edge is itself a concrete normalized spine,
with the same exact outer context carried by the introducing parent. -/
public theorem ConcreteEmptyEdge.exists_childSpine (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix : List T} (h : ConcreteEmptyEdge M p q suffix) :
    ∃ (preWord : List T) (context : List (StackSymbol M)),
      ConcreteOperationalSpine M p (PDA_to_CFG.N.list q [] q)
        suffix preWord context := by
  cases h with
  | read parent htransition hrule =>
      exact ⟨_, _, ConcreteOperationalSpine.read
        parent htransition hrule⟩
  | epsilon parent htransition hrule =>
      exact ⟨_, _, ConcreteOperationalSpine.epsilon
        parent htransition hrule⟩
  | split parent hlength hrule hleft =>
      exact ⟨_, _, ConcreteOperationalSpine.splitRight
        parent hlength hrule hleft⟩

/-- Exact accepting cut carried by a concrete empty edge. -/
public theorem ConcreteEmptyEdge.exists_cut (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix : List T} (h : ConcreteEmptyEdge M p q suffix) :
    ∃ (preWord : List T) (context : List (StackSymbol M))
        (final : State M),
      (emptyStackPDA M).Reaches
          ⟨(emptyStackPDA M).initial_state, preWord,
            [(emptyStackPDA M).start_symbol]⟩
          ⟨q, [], context⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨q, suffix, context⟩ ⟨final, [], []⟩ := by
  obtain ⟨preWord, context, hspine⟩ := h.exists_childSpine M
  have hfocused := hspine.focusedExact M
  cases hfocused with
  | list _ _ _ _ _ _ final prefixPath continuation =>
      exact ⟨preWord, context, final, by simpa using prefixPath,
        continuation⟩

/-- Every concrete empty edge inherits the last-visible-event decomposition
of its exact child spine. -/
public theorem ConcreteEmptyEdge.exists_zeroVisibleDecomposition
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix : List T} (h : ConcreteEmptyEdge M p q suffix) :
    ∃ (preWord : List T) (context : List (StackSymbol M))
        (anchor : Nonterminal M) (anchorSuffix : List T)
        (anchorContext : List (StackSymbol M)),
      VisibleSpineAnchor M p anchor anchorSuffix preWord anchorContext ∧
      ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.list q [] q) suffix context := by
  obtain ⟨preWord, context, hspine⟩ := h.exists_childSpine M
  obtain ⟨anchor, anchorSuffix, anchorContext, hanchor, htail⟩ :=
    hspine.zeroVisibleDecomposition M
  exact ⟨preWord, context, anchor, anchorSuffix, anchorContext,
    hanchor, htail⟩

/-- Re-complete the visible prefix of a concrete empty edge by an arbitrary
terminal word.  The ancestry retained by the edge is independent of the
particular productive completion originally used to make it concrete. -/
public theorem ConcreteEmptyEdge.exists_childSpineAtCompletion
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix completion : List T} (h : ConcreteEmptyEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (completion.map symbol.terminal)) :
    ∃ context : List (StackSymbol M),
      ConcreteOperationalSpine M p (PDA_to_CFG.N.list q [] q)
        suffix completion context := by
  obtain ⟨oldCompletion, oldContext, hchild⟩ := h.exists_childSpine M
  have hactive := (hchild.operationalSpine M).activeSpine M
  exact concreteOperationalSpine_of_activeSpine M hactive hp

/-- Re-completing a transition-tagged edge is just the corresponding
operation on its underlying concrete empty edge. -/
public theorem ConcreteEmptyTransitionEdge.exists_childSpineAtCompletion
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix completion : List T}
    (h : ConcreteEmptyTransitionEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (completion.map symbol.terminal)) :
    ∃ context : List (StackSymbol M),
      ConcreteOperationalSpine M p (PDA_to_CFG.N.list q [] q)
        suffix completion context :=
  (h.edge M).exists_childSpineAtCompletion M hp

/-- Last-visible-event decomposition after a deliberately chosen completion
of the shared visible prefix.  This is the form needed to compare two empty
returns whose original concrete witnesses used unrelated completions. -/
public theorem ConcreteEmptyEdge.exists_zeroVisibleDecompositionAtCompletion
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix completion : List T} (h : ConcreteEmptyEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (completion.map symbol.terminal)) :
    ∃ (context : List (StackSymbol M)) (anchor : Nonterminal M)
        (anchorSuffix : List T)
        (anchorContext : List (StackSymbol M)),
      VisibleSpineAnchor M p anchor anchorSuffix completion anchorContext ∧
      ZeroVisibleTail M p completion anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.list q [] q) suffix context := by
  obtain ⟨context, hchild⟩ := h.exists_childSpineAtCompletion M hp
  obtain ⟨anchor, anchorSuffix, anchorContext, hanchor, htail⟩ :=
    hchild.zeroVisibleDecomposition M
  exact ⟨context, anchor, anchorSuffix, anchorContext, hanchor, htail⟩

/-- An empty-stack list nonterminal has no zero-visible child.  Every
zero-visible constructor expects either a `single`, a nonempty list stack,
or the start marker, so a tail beginning at `list q [] target` is literal
reflexivity. -/
public theorem ZeroVisibleTail.fromEmptyList_eq (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {q target : State M} {anchorSuffix : List T}
    {anchorContext : List (StackSymbol M)}
    {current : Nonterminal M} {currentSuffix : List T}
    {currentContext : List (StackSymbol M)}
    (h : ZeroVisibleTail M p preWord
      (PDA_to_CFG.N.list q [] target) anchorSuffix anchorContext
      current currentSuffix currentContext) :
    current = PDA_to_CFG.N.list q [] target ∧
      currentSuffix = anchorSuffix ∧ currentContext = anchorContext := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | start previous hrule ih => cases ih.1
  | epsilon previous htransition hrule ih => cases ih.1
  | @splitLeft suffix z context source middle outerTarget Z gamma
      previous hlength hrule hright ih =>
      have hstack : Z :: gamma = [] := by
        injection ih.1 with _ hstack _
      simp at hstack

/-- Every concrete empty edge has at least one productive completion of its
visible prefix. -/
public theorem ConcreteEmptyEdge.exists_prefixCompletion
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix : List T} (h : ConcreteEmptyEdge M p q suffix) :
    ∃ completion : List T,
      (characteristicGrammar M).DerivesRightmost p
        (completion.map symbol.terminal) := by
  obtain ⟨completion, context, hchild⟩ := h.exists_childSpine M
  exact ⟨completion, (hchild.operationalSpine M).prefixDerives M⟩

/-! ## Terminal displacement of two empty-return prefixes -/

/-- Equality after appending terminal suffixes exposes the precise terminal
displacement between the two visible prefixes.  Keeping this lemma in the
concrete synchronization layer lets the hard semantic proof choose aligned
terminal completions before returning to the syntax-facing adapter. -/
public theorem concreteEmptyReturn_append_terminals_eq_cases
    {N : Type} {p₁ p₂ : List (symbol T N)} {s₂ y : List T}
    (h : p₂ ++ s₂.map symbol.terminal =
      p₁ ++ y.map symbol.terminal) :
    (∃ z : List T,
      p₁ = p₂ ++ z.map symbol.terminal ∧ s₂ = z ++ y) ∨
    ∃ z : List T,
      p₂ = p₁ ++ z.map symbol.terminal ∧ y = z ++ s₂ := by
  rw [List.append_eq_append_iff] at h
  rcases h with ⟨as, hp, hs⟩ | ⟨bs, hp, hs⟩
  · have hs' : s₂.map (symbol.terminal (N := N)) =
        as ++ y.map symbol.terminal := hs
    rw [List.map_eq_append_iff] at hs'
    obtain ⟨z, y', hs₂, has, hy'⟩ := hs'
    have hy : y' = y :=
      (List.map_injective_iff.mpr fun _ _ heq =>
        symbol.terminal.inj heq) hy'
    subst y'
    exact Or.inl ⟨z, by simpa [has] using hp, hs₂⟩
  · have hs' : y.map (symbol.terminal (N := N)) =
        bs ++ s₂.map symbol.terminal := hs
    rw [List.map_eq_append_iff] at hs'
    obtain ⟨z, s₂', hy, hbs, hs₂'⟩ := hs'
    have hs₂eq : s₂' = s₂ :=
      (List.map_injective_iff.mpr fun _ _ heq =>
        symbol.terminal.inj heq) hs₂'
    subst s₂'
    exact Or.inr ⟨z, by simpa [hbs] using hp, hy⟩

/-! ## Net-pop runs at a chosen completion -/

/-- Operational factorization of a concrete empty return after deliberately
choosing a terminal completion of its visible prefix. -/
@[expose]
public def ConcreteEmptyReturnRun (M : DPDA Q T S)
    (completion suffix : List T) (q : State M) : Prop :=
  ∃ (beforeWord segmentWord : List T) (source : State M)
      (top : StackSymbol M) (context : List (StackSymbol M))
      (final : State M),
    completion = beforeWord ++ segmentWord ∧
    (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, beforeWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, [], top :: context⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨source, segmentWord, top :: context⟩
      ⟨q, [], context⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨q, suffix, context⟩ ⟨final, [], []⟩

/-- One-step specialization for a transition-generated concrete empty
return. -/
@[expose]
public def ConcreteEmptyTransitionRun (M : DPDA Q T S)
    (completion suffix : List T) (q : State M) : Prop :=
  ∃ (beforeWord segmentWord : List T) (source : State M)
      (top : StackSymbol M) (context : List (StackSymbol M))
      (final : State M),
    completion = beforeWord ++ segmentWord ∧
    (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, beforeWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, [], top :: context⟩ ∧
    (emptyStackPDA M).Reaches₁
      ⟨source, segmentWord, top :: context⟩
      ⟨q, [], context⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨q, suffix, context⟩ ⟨final, [], []⟩

/-- Forgetting the one-step tag gives the ordinary concrete return run. -/
public theorem ConcreteEmptyTransitionRun.returnRun (M : DPDA Q T S)
    {completion suffix : List T} {q : State M}
    (h : ConcreteEmptyTransitionRun M completion suffix q) :
    ConcreteEmptyReturnRun M completion suffix q := by
  rcases h with ⟨beforeWord, segmentWord, source, top, context, final,
    hcompletion, hprefix, hstep, hcontinuation⟩
  exact ⟨beforeWord, segmentWord, source, top, context, final,
    hcompletion, hprefix, Relation.ReflTransGen.single hstep, hcontinuation⟩

private theorem concrete_terminal_completion_singleton (M : DPDA Q T S)
    {a : T} {w : List T}
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

/-- At any chosen completion an empty edge is either itself the last visible
anchor (read or split-right), or its child is reached through a genuinely
epsilon-bearing zero-visible tail. -/
public theorem ConcreteEmptyEdge.directAnchor_or_epsilonBearingAtCompletion
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix completion : List T} (edge : ConcreteEmptyEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (completion.map symbol.terminal)) :
    (∃ context : List (StackSymbol M),
      VisibleSpineAnchor M p (PDA_to_CFG.N.list q [] q)
        suffix completion context) ∨
    ∃ (context : List (StackSymbol M)) (anchor : Nonterminal M)
        (anchorSuffix : List T)
        (anchorContext : List (StackSymbol M)),
      VisibleSpineAnchor M p anchor anchorSuffix completion anchorContext ∧
      ZeroVisibleTail M p completion anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.list q [] q) suffix context ∧
      EpsilonBearingZeroVisibleTail M p completion anchor anchorSuffix
        anchorContext (PDA_to_CFG.N.list q [] q) suffix context := by
  cases edge with
  | @read base suffix oldWord oldContext source a Z q
      parent htransition hrule =>
      obtain ⟨beforeWord, segmentWord, hcompletion, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      have hsegmentWord : segmentWord = [a] :=
        concrete_terminal_completion_singleton M hsegment
      subst segmentWord
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hbase
      left
      refine ⟨context, ?_⟩
      simpa [hcompletion] using
        VisibleSpineAnchor.read hparent htransition hrule
  | @epsilon base suffix oldWord oldContext source Z q
      parent htransition hrule =>
      obtain ⟨parentContext, hparent⟩ :=
        concreteOperationalSpine_of_activeSpine M
          ((parent.operationalSpine M).activeSpine M) hp
      obtain ⟨anchor, anchorSuffix, anchorContext, hanchor, hparentTail⟩ :=
        hparent.zeroVisibleDecomposition M
      right
      exact ⟨parentContext, anchor, anchorSuffix, anchorContext, hanchor,
        ZeroVisibleTail.epsilon hparentTail htransition hrule,
        EpsilonBearingZeroVisibleTail.epsilon
          hparentTail htransition hrule⟩
  | @split base suffix oldWord leftWord oldContext source Z q
      parent hlength hrule hleft =>
      obtain ⟨beforeWord, segmentWord, hcompletion, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hbase
      left
      refine ⟨context, ?_⟩
      simpa [hcompletion] using
        VisibleSpineAnchor.splitRight hparent hlength hrule hsegment

/-- Two empty returns which are both their own last visible anchors have the
same return state.  Read anchors use deterministic output synchronization;
split-right anchors already share their displayed middle state. -/
public theorem directEmptyReturnAnchors_state_eq (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {completion : List T}
    {q₁ q₂ : State M} {s₁ s₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    (h₁ : VisibleSpineAnchor M p (PDA_to_CFG.N.list q₁ [] q₁)
      s₁ completion context₁)
    (h₂ : VisibleSpineAnchor M p (PDA_to_CFG.N.list q₂ [] q₂)
      s₂ completion context₂) :
    q₁ = q₂ := by
  have hpaired := pairedVisibleAnchors_of_same_prefix M h₁ h₂ rfl rfl
  cases hpaired with
  | @read base before suffix₁ suffix₂ context₁ context₂
      source₁ target₁ next₁ source₂ target₂ next₂ a Z₁ Z₂
      gamma₁ gamma₂ parent₁ transition₁ rule₁ parent₂ transition₂ rule₂ =>
      exact (concreteRead_anchor_data_eq M parent₁ parent₂
        transition₁ transition₂).1
  | splitRight => rfl

/-- Any concrete spine aligned with a read/pop empty return is itself an
empty-stack list cut in the same state.  Deterministic read output fixes the
aligned visible anchor, and an empty-list anchor has no proper zero-visible
descendant. -/
public theorem concreteReadEmptyReturn_alignedSpine_shape
    (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))}
    {suffixRead suffixOther beforeWord : List T}
    {readContext otherContext : List (StackSymbol M)}
    {source q : State M} {a : T} {Z : StackSymbol M}
    {A : Nonterminal M}
    (parent : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.single source Z q) suffixRead beforeWord readContext)
    (htransition : (q, []) ∈
      (emptyStackPDA M).transition_fun source a Z)
    (other : ConcreteOperationalSpine M
      (base ++ [symbol.terminal a]) A suffixOther
      (beforeWord ++ [a]) otherContext) :
    ∃ target : State M, A = PDA_to_CFG.N.list q [] target := by
  obtain ⟨anchor, anchorSuffix, anchorContext, hanchor, htail⟩ :=
    other.zeroVisibleDecomposition M
  obtain ⟨target, hanchorShape, hanchorContext⟩ :=
    visibleReadAnchor_aligned_data_eq M parent htransition
      hanchor rfl rfl
  subst anchor
  exact ⟨target, (htail.fromEmptyList_eq M).1⟩

/-- A read/pop empty return is synchronized with every other empty return at
the same retained prefix.  Aligning the other edge at the read completion
either gives another direct empty-list anchor, or makes its last visible
anchor a read with the same deterministic output.  In the latter case that
anchor already has empty stack text, so its zero-visible tail is reflexive. -/
public theorem concreteReadEmptyReturn_samePrefix_state_eq
    (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))}
    {suffix₁ suffix₂ beforeWord : List T}
    {context : List (StackSymbol M)}
    {source q₁ q₂ : State M} {a : T} {Z : StackSymbol M}
    (parent : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.single source Z q₁) suffix₁ beforeWord context)
    (htransition : (q₁, []) ∈
      (emptyStackPDA M).transition_fun source a Z)
    (hrule : (PDA_to_CFG.N.single source Z q₁,
        [symbol.terminal a,
          symbol.nonterminal (PDA_to_CFG.N.list q₁ [] q₁)]) ∈
      (characteristicGrammar M).rules)
    (edge₂ : ConcreteEmptyEdge M
      (base ++ [symbol.terminal a]) q₂ suffix₂) :
    q₁ = q₂ := by
  have hpBase := (parent.operationalSpine M).prefixDerives M
  have hp : (characteristicGrammar M).DerivesRightmost
      (base ++ [symbol.terminal a])
      ((beforeWord ++ [a]).map symbol.terminal) := by
    have ha : (characteristicGrammar M).DerivesRightmost
        [symbol.terminal a]
        ([a].map symbol.terminal) := Relation.ReflTransGen.refl
    simpa [List.map_append] using hpBase.append_to_terminals ha
  let anchor₁ : VisibleSpineAnchor M
      (base ++ [symbol.terminal a])
      (PDA_to_CFG.N.list q₁ [] q₁) suffix₁
      (beforeWord ++ [a]) context :=
    VisibleSpineAnchor.read parent htransition hrule
  rcases edge₂.directAnchor_or_epsilonBearingAtCompletion M hp with
      ⟨context₂, anchor₂⟩ |
      ⟨context₂, anchor, anchorSuffix, anchorContext,
        anchor₂, tail₂, bearing₂⟩
  · exact directEmptyReturnAnchors_state_eq M anchor₁ anchor₂
  · obtain ⟨target₂, hanchor, hcontext⟩ :=
      visibleReadAnchor_aligned_data_eq M parent htransition
        anchor₂ rfl rfl
    subst anchor
    have endpoint := tail₂.fromEmptyList_eq M
    exact (PDA_to_CFG.N.list.inj endpoint.1).1.symm

/-- Symmetric orientation of `concreteReadEmptyReturn_samePrefix_state_eq`,
for a read/pop return displayed on the right. -/
public theorem concreteEmptyReturn_read_samePrefix_state_eq
    (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))}
    {suffix₁ suffix₂ beforeWord : List T}
    {context : List (StackSymbol M)}
    {source q₁ q₂ : State M} {a : T} {Z : StackSymbol M}
    (edge₁ : ConcreteEmptyEdge M
      (base ++ [symbol.terminal a]) q₁ suffix₁)
    (parent : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.single source Z q₂) suffix₂ beforeWord context)
    (htransition : (q₂, []) ∈
      (emptyStackPDA M).transition_fun source a Z)
    (hrule : (PDA_to_CFG.N.single source Z q₂,
        [symbol.terminal a,
          symbol.nonterminal (PDA_to_CFG.N.list q₂ [] q₂)]) ∈
      (characteristicGrammar M).rules) :
    q₁ = q₂ :=
  (concreteReadEmptyReturn_samePrefix_state_eq M
    parent htransition hrule edge₁).symm

/-- A concrete spine whose visible prefix ends in a terminal has a retained
last read edge.  The theorem exposes that edge together with the entire
zero-visible tail from its list child to the original endpoint; this is the
ancestry-preserving form needed by displaced empty-return comparisons. -/
public theorem ConcreteOperationalSpine.lastRead_of_terminalSuffix
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {z : List T} {a : T}
    {A : Nonterminal M} {suffix completion : List T}
    {context : List (StackSymbol M)}
    (h : ConcreteOperationalSpine M
      ((p ++ z.map symbol.terminal) ++ [symbol.terminal a])
      A suffix completion context) :
    ∃ (parentSuffix beforeWord : List T)
        (parentContext : List (StackSymbol M))
        (source target next : State M) (Z : StackSymbol M)
        (gamma : List (StackSymbol M)),
      ConcreteOperationalSpine M (p ++ z.map symbol.terminal)
        (PDA_to_CFG.N.single source Z target)
        parentSuffix beforeWord parentContext ∧
      (next, gamma) ∈ (emptyStackPDA M).transition_fun source a Z ∧
      (PDA_to_CFG.N.single source Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules ∧
      completion = beforeWord ++ [a] ∧
      ZeroVisibleTail M
        ((p ++ z.map symbol.terminal) ++ [symbol.terminal a]) completion
        (PDA_to_CFG.N.list next gamma target) parentSuffix parentContext
        A suffix context := by
  obtain ⟨anchor, anchorSuffix, anchorContext, hanchor, htail⟩ :=
    h.zeroVisibleDecomposition M
  generalize hpref :
    ((p ++ z.map symbol.terminal) ++ [symbol.terminal a]) = anchorPrefix
      at hanchor htail
  generalize hword : completion = anchorWord at hanchor htail
  cases hanchor with
  | root => simp at hpref
  | @read base readSuffix readWord readContext source target next b Z gamma
      parent transition rule =>
      have hbase : base = p ++ z.map symbol.terminal :=
        (List.append_inj_left' hpref (by simp)).symm
      have hb : b = a := by
        have hlast := List.append_inj_right' hpref (by simp)
        exact (symbol.terminal.inj (List.cons.inj hlast).1).symm
      subst base
      subst b
      subst completion
      exact ⟨anchorSuffix, readWord, anchorContext, source, target, next, Z,
        gamma, parent, transition, rule, rfl, htail⟩
  | @splitRight base readSuffix beforeWord leftWord readContext source middle
      target Z gamma parent length rule left =>
      have hlast := List.append_inj_right' hpref (by simp)
      have hbad : symbol.nonterminal (T := T)
          (PDA_to_CFG.N.single source Z middle : Nonterminal M) =
          symbol.terminal (N := Nonterminal M) a :=
        (List.cons.inj hlast).1.symm
      cases hbad

/-- Walking backward through a nonempty terminal extension exposes the read
parent of its first terminal.  The proof peels last-read anchors from the
right, preserving the concrete retained ancestry at every step. -/
public theorem ConcreteOperationalSpine.firstRead_of_terminalBlock
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {a : T} {z : List T}
    {A : Nonterminal M} {suffix completion : List T}
    {context : List (StackSymbol M)}
    (h : ConcreteOperationalSpine M
      (p ++ (a :: z).map symbol.terminal)
      A suffix completion context) :
    ∃ (parentSuffix beforeWord : List T)
        (parentContext : List (StackSymbol M))
        (source target next : State M) (Z : StackSymbol M)
        (gamma : List (StackSymbol M)),
      ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single source Z target)
        parentSuffix beforeWord parentContext ∧
      (next, gamma) ∈ (emptyStackPDA M).transition_fun source a Z ∧
      (PDA_to_CFG.N.single source Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules := by
  induction z using List.reverseRecOn generalizing A suffix completion context with
  | nil =>
      have h' : ConcreteOperationalSpine M
          ((p ++ [].map symbol.terminal) ++ [symbol.terminal a])
          A suffix completion context := by simpa using h
      obtain ⟨parentSuffix, beforeWord, parentContext,
        source, target, next, Z, gamma, parent, transition, rule,
        hcompletion, tail⟩ := h'.lastRead_of_terminalSuffix M
      exact ⟨parentSuffix, beforeWord, parentContext,
        source, target, next, Z, gamma, by simpa using parent,
        transition, rule⟩
  | append_singleton z b ih =>
      have h' : ConcreteOperationalSpine M
          ((p ++ (a :: z).map symbol.terminal) ++ [symbol.terminal b])
          A suffix completion context := by
        simpa [List.map_append, List.append_assoc] using h
      obtain ⟨parentSuffix, beforeWord, parentContext,
        source, target, next, Z, gamma, parent, transition, rule,
        hcompletion, tail⟩ := h'.lastRead_of_terminalSuffix M
      exact ih parent

/-- Once a read transition has popped its displayed symbol, no active
concrete spine can occur at a strict terminal extension of that empty-return
prefix.  Walking the extension back to its first read produces a `single`
node at the old prefix, while deterministic alignment with the pop says that
every node there is an empty-list cut. -/
public theorem concreteReadEmptyReturn_no_strictTerminalExtension
    (M : DPDA Q T S)
    {base : List (symbol T (Nonterminal M))}
    {suffixRead beforeWord : List T}
    {readContext : List (StackSymbol M)}
    {source q : State M} {a b : T} {Z : StackSymbol M}
    {z : List T} {A : Nonterminal M}
    {suffixOther completionOther : List T}
    {otherContext : List (StackSymbol M)}
    (parent : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.single source Z q) suffixRead beforeWord readContext)
    (htransition : (q, []) ∈
      (emptyStackPDA M).transition_fun source a Z)
    (other : ConcreteOperationalSpine M
      ((base ++ [symbol.terminal a]) ++
        (b :: z).map symbol.terminal)
      A suffixOther completionOther otherContext) : False := by
  obtain ⟨parentSuffix, otherBeforeWord, otherParentContext,
      otherSource, otherTarget, otherNext, otherZ, otherGamma,
      otherParent, otherTransition, otherRule⟩ :=
    other.firstRead_of_terminalBlock M
  have hpBase := (parent.operationalSpine M).prefixDerives M
  have hp : (characteristicGrammar M).DerivesRightmost
      (base ++ [symbol.terminal a])
      ((beforeWord ++ [a]).map symbol.terminal) := by
    have ha : (characteristicGrammar M).DerivesRightmost
        [symbol.terminal a]
        ([a].map symbol.terminal) := Relation.ReflTransGen.refl
    simpa [List.map_append] using hpBase.append_to_terminals ha
  obtain ⟨alignedContext, alignedParent⟩ :=
    concreteOperationalSpine_of_activeSpine M
      ((otherParent.operationalSpine M).activeSpine M) hp
  obtain ⟨target, hshape⟩ :=
    concreteReadEmptyReturn_alignedSpine_shape M
      parent htransition alignedParent
  cases hshape

/-- Every concrete empty edge has a net-pop run at every chosen terminal
completion of its visible prefix. -/
public theorem ConcreteEmptyEdge.returnRunAtCompletion
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix completion : List T} (edge : ConcreteEmptyEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (completion.map symbol.terminal)) :
    ConcreteEmptyReturnRun M completion suffix q := by
  cases edge with
  | @read base suffix oldWord oldContext source a Z q
      parent htransition hrule =>
      obtain ⟨beforeWord, segmentWord, hcompletion, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      have hsegmentWord : segmentWord = [a] :=
        concrete_terminal_completion_singleton M hsegment
      subst segmentWord
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hbase
      cases hparent.focusedExact M with
      | single _ _ _ _ _ _ final prefixPath continuation =>
          refine ⟨beforeWord, [a], source, Z, context, final,
            hcompletion, prefixPath, ?_, continuation⟩
          apply Relation.ReflTransGen.single
          exact Or.inl ⟨q, [], htransition, by simp⟩
  | @epsilon base suffix oldWord oldContext source Z q
      parent htransition hrule =>
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hp
      cases hparent.focusedExact M with
      | single _ _ _ _ _ _ final prefixPath continuation =>
          refine ⟨completion, [], source, Z, context, final, by simp,
            prefixPath, ?_, continuation⟩
          apply Relation.ReflTransGen.single
          exact ⟨q, [], htransition, by simp⟩
  | @split base suffix oldWord leftWord oldContext source Z q
      parent hlength hrule hleft =>
      obtain ⟨beforeWord, segmentWord, hcompletion, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hbase
      cases hparent.focusedExact M with
      | list _ _ _ _ _ _ final prefixPath continuation =>
          have hreturn :=
            (reaches_of_characteristic_derives_single M hsegment).append_stack
              context
          refine ⟨beforeWord, segmentWord, source, Z, context, final,
            hcompletion, ?_, ?_, continuation⟩
          · simpa using prefixPath
          · simpa using hreturn

/-- A transition-tagged concrete edge has a one-step net-pop run at every
chosen terminal completion. -/
public theorem ConcreteEmptyTransitionEdge.transitionRunAtCompletion
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix completion : List T}
    (edge : ConcreteEmptyTransitionEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (completion.map symbol.terminal)) :
    ConcreteEmptyTransitionRun M completion suffix q := by
  cases edge with
  | @read base suffix oldWord oldContext source a Z q
      parent htransition hrule =>
      obtain ⟨beforeWord, segmentWord, hcompletion, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      have hsegmentWord : segmentWord = [a] :=
        concrete_terminal_completion_singleton M hsegment
      subst segmentWord
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hbase
      cases hparent.focusedExact M with
      | single _ _ _ _ _ _ final prefixPath continuation =>
          exact ⟨beforeWord, [a], source, Z, context, final,
            hcompletion, prefixPath,
            Or.inl ⟨q, [], htransition, by simp⟩, continuation⟩
  | @epsilon base suffix oldWord oldContext source Z q
      parent htransition hrule =>
      obtain ⟨context, hparent⟩ := concreteOperationalSpine_of_activeSpine M
        ((parent.operationalSpine M).activeSpine M) hp
      cases hparent.focusedExact M with
      | single _ _ _ _ _ _ final prefixPath continuation =>
          exact ⟨completion, [], source, Z, context, final, by simp,
            prefixPath, ⟨q, [], htransition, by simp⟩, continuation⟩

/-! ## Oriented cuts for a nonempty terminal displacement -/

/-- If the second visible prefix extends the first by a nonempty terminal
block, the first empty-return cut processes exactly that block to the second
cut.  The witnesses retain both useful continuations for the subsequent
net-pop crossing argument. -/
public theorem concreteEmptyReturn_forward_displacement
    (M : DPDA Q T S)
    {p₁ p₂ : List (symbol T (Nonterminal M))}
    {q₁ q₂ : State M} {s₁ s₂ z : List T}
    (edge₁ : ConcreteEmptyEdge M p₁ q₁ s₁)
    (edge₂ : ConcreteEmptyEdge M p₂ q₂ s₂)
    (hp₂ : p₂ = p₁ ++ z.map symbol.terminal)
    (hz : z ≠ [])
    (hlook : s₁.take 1 = (z ++ s₂).take 1) :
    ∃ (completion : List T)
        (context₁ context₂ : List (StackSymbol M))
        (final₁ final₂ : State M),
      (emptyStackPDA M).Reaches
          ⟨(emptyStackPDA M).initial_state, completion,
            [(emptyStackPDA M).start_symbol]⟩
          ⟨q₁, [], context₁⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨(emptyStackPDA M).initial_state, completion ++ z,
            [(emptyStackPDA M).start_symbol]⟩
          ⟨q₂, [], context₂⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨q₁, s₁, context₁⟩ ⟨final₁, [], []⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨q₂, s₂, context₂⟩ ⟨final₂, [], []⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨q₁, z, context₁⟩ ⟨q₂, [], context₂⟩ := by
  obtain ⟨completion, hp₁⟩ := edge₁.exists_prefixCompletion M
  have hzDerives : (characteristicGrammar M).DerivesRightmost
      (z.map (symbol.terminal (N := Nonterminal M)))
      (z.map symbol.terminal) := Relation.ReflTransGen.refl
  have hp₂' : (characteristicGrammar M).DerivesRightmost p₂
      ((completion ++ z).map symbol.terminal) := by
    rw [hp₂]
    simpa [List.map_append] using hp₁.append_to_terminals hzDerives
  obtain ⟨context₁, child₁⟩ :=
    edge₁.exists_childSpineAtCompletion M hp₁
  obtain ⟨context₂, child₂⟩ :=
    edge₂.exists_childSpineAtCompletion M hp₂'
  cases child₁.focusedExact M with
  | list _ _ _ _ _ _ final₁ prefix₁ continuation₁ =>
      cases child₂.focusedExact M with
      | list _ _ _ _ _ _ final₂ prefix₂ continuation₂ =>
          have hbetween := emptyStack_global_productive_extension M hz
            (by simpa using prefix₁) (by simpa using prefix₂)
            continuation₁ continuation₂ hlook
          exact ⟨completion, context₁, context₂, final₁, final₂,
            by simpa using prefix₁, by simpa using prefix₂,
            continuation₁, continuation₂, by simpa using hbetween⟩

/-- If the first visible prefix extends the second by a nonempty terminal
block, the same comparison is oriented from the second return cut to the
first.  Here the transferred suffix equation itself supplies the common
first symbol because the displacement is nonempty. -/
public theorem concreteEmptyReturn_backward_displacement
    (M : DPDA Q T S)
    {p₁ p₂ : List (symbol T (Nonterminal M))}
    {q₁ q₂ : State M} {s₁ s₂ y z : List T}
    (edge₁ : ConcreteEmptyEdge M p₁ q₁ s₁)
    (edge₂ : ConcreteEmptyEdge M p₂ q₂ s₂)
    (hp₁ : p₁ = p₂ ++ z.map symbol.terminal)
    (hs₂ : s₂ = z ++ y)
    (hz : z ≠ []) :
    ∃ (completion : List T)
        (context₁ context₂ : List (StackSymbol M))
        (final₁ final₂ : State M),
      (emptyStackPDA M).Reaches
          ⟨(emptyStackPDA M).initial_state, completion ++ z,
            [(emptyStackPDA M).start_symbol]⟩
          ⟨q₁, [], context₁⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨(emptyStackPDA M).initial_state, completion,
            [(emptyStackPDA M).start_symbol]⟩
          ⟨q₂, [], context₂⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨q₁, s₁, context₁⟩ ⟨final₁, [], []⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨q₂, s₂, context₂⟩ ⟨final₂, [], []⟩ ∧
      (emptyStackPDA M).Reaches
          ⟨q₂, z, context₂⟩ ⟨q₁, [], context₁⟩ := by
  obtain ⟨completion, hp₂⟩ := edge₂.exists_prefixCompletion M
  have hzDerives : (characteristicGrammar M).DerivesRightmost
      (z.map (symbol.terminal (N := Nonterminal M)))
      (z.map symbol.terminal) := Relation.ReflTransGen.refl
  have hp₁' : (characteristicGrammar M).DerivesRightmost p₁
      ((completion ++ z).map symbol.terminal) := by
    rw [hp₁]
    simpa [List.map_append] using hp₂.append_to_terminals hzDerives
  obtain ⟨context₁, child₁⟩ :=
    edge₁.exists_childSpineAtCompletion M hp₁'
  obtain ⟨context₂, child₂⟩ :=
    edge₂.exists_childSpineAtCompletion M hp₂
  cases child₁.focusedExact M with
  | list _ _ _ _ _ _ final₁ prefix₁ continuation₁ =>
      cases child₂.focusedExact M with
      | list _ _ _ _ _ _ final₂ prefix₂ continuation₂ =>
          have hlook : s₂.take 1 = (z ++ s₁).take 1 := by
            obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hz
            simp [hs₂]
          have hbetween := emptyStack_global_productive_extension M hz
            (by simpa using prefix₂) (by simpa using prefix₁)
            continuation₂ continuation₁ hlook
          exact ⟨completion, context₁, context₂, final₁, final₂,
            by simpa using prefix₁, by simpa using prefix₂,
            continuation₁, continuation₂, by simpa using hbetween⟩

/-- Concrete version of the syntax-facing paired empty-return classifier.
The proof below will turn every genuinely distinct pair into one of the two
public operational obstructions. -/
@[expose]
public def ConcreteEmptyReturnPairsClassified (M : DPDA Q T S) : Prop :=
  ∀ (p₁ p₂ : List (symbol T (Nonterminal M)))
      (q₁ q₂ : State M) (s₁ s₂ y : List T),
    ∀ (edge₁ : ConcreteEmptyEdge M p₁ q₁ s₁)
      (edge₂ : ConcreteEmptyEdge M p₂ q₂ s₂),
    (ConcreteEmptyTransitionEdge M p₁ q₁ s₁ ∨
      ConcreteEmptyTransitionEdge M p₂ q₂ s₂) →
    p₂ ++ s₂.map symbol.terminal =
      p₁ ++ y.map symbol.terminal →
    s₁.take 1 = y.take 1 →
    (p₁ = p₂ ∧ q₁ = q₂) ∨ UsefulReturnObstruction M

/-- The genuinely semantic residual, with the transition witness used as
the left edge rather than carried redundantly beside another proof with the
same indices. -/
@[expose]
public def ConcreteLeftTransitionReturnPairsClassified
    (M : DPDA Q T S) : Prop :=
  ∀ (p₁ p₂ : List (symbol T (Nonterminal M)))
      (q₁ q₂ : State M) (s₁ s₂ y : List T),
    ConcreteEmptyTransitionEdge M p₁ q₁ s₁ →
    ConcreteEmptyEdge M p₂ q₂ s₂ →
    p₂ ++ s₂.map symbol.terminal =
      p₁ ++ y.map symbol.terminal →
    s₁.take 1 = y.take 1 →
    (p₁ = p₂ ∧ q₁ = q₂) ∨ UsefulReturnObstruction M

/-- Symmetric semantic residual in which the transition witness is the
right edge.  The LR lookahead equation is directional, so this is not merely
the preceding proposition with its arguments swapped. -/
@[expose]
public def ConcreteRightTransitionReturnPairsClassified
    (M : DPDA Q T S) : Prop :=
  ∀ (p₁ p₂ : List (symbol T (Nonterminal M)))
      (q₁ q₂ : State M) (s₁ s₂ y : List T),
    ConcreteEmptyEdge M p₁ q₁ s₁ →
    ConcreteEmptyTransitionEdge M p₂ q₂ s₂ →
    p₂ ++ s₂.map symbol.terminal =
      p₁ ++ y.map symbol.terminal →
    s₁.take 1 = y.take 1 →
    (p₁ = p₂ ∧ q₁ = q₂) ∨ UsefulReturnObstruction M

/-- The two directional transition-vs-return lemmas are exactly sufficient
for the concrete paired classifier; the redundant concrete edge on the
transition-tagged side is intentionally discarded. -/
public theorem concreteEmptyReturnPairsClassified_of_transitionSides
    (M : DPDA Q T S)
    (hleft : ConcreteLeftTransitionReturnPairsClassified M)
    (hright : ConcreteRightTransitionReturnPairsClassified M) :
    ConcreteEmptyReturnPairsClassified M := by
  intro p₁ p₂ q₁ q₂ s₁ s₂ y edge₁ edge₂ htransition hform hlook
  rcases htransition with htransition₁ | htransition₂
  · exact hleft p₁ p₂ q₁ q₂ s₁ s₂ y
      htransition₁ edge₂ hform hlook
  · exact hright p₁ p₂ q₁ q₂ s₁ s₂ y
      edge₁ htransition₂ hform hlook

end

end DPDA_to_LR
