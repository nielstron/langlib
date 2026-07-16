module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Spine

/-!
# Zero-visible tails of operational characteristic spines

An `OperationalSpine` deliberately retains a grammar rule in its generic
`descend` constructor.  This file normalizes that rule to one of the five
nonbase characteristic-rule shapes and, at the same time, records the hidden
outer stack context of the active occurrence.

The normalized trace makes the important dichotomy syntactic.  A read or a
split-right descent appends one visible symbol to the prehandle.  Start,
epsilon, and split-left descents leave the prehandle unchanged.  The latter
three constructors form `ZeroVisibleTail`.  Along such a tail, split-left is
the only constructor that changes the hidden context, and it does so by
prepending the saved replacement tail.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A normalized operational spine carrying the outer stack context of its
active occurrence.  At `start` the context index is a harmless `[]`
convention; every other constructor has its literal zipper meaning. -/
public inductive ConcreteOperationalSpine (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → Nonterminal M →
      List T → List T → List (StackSymbol M) → Prop
  | root : ConcreteOperationalSpine M [] PDA_to_CFG.N.start [] [] []
  | read
      {p : List (symbol T (Nonterminal M))} {suffix preWord : List T}
      {context : List (StackSymbol M)}
      {q target next : State M} {a : T} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single q Z target) suffix preWord context)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun q a Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteOperationalSpine M (p ++ [symbol.terminal a])
        (PDA_to_CFG.N.list next gamma target) suffix
        (preWord ++ [a]) context
  | epsilon
      {p : List (symbol T (Nonterminal M))} {suffix preWord : List T}
      {context : List (StackSymbol M)}
      {q target next : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single q Z target) suffix preWord context)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun' q Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteOperationalSpine M p
        (PDA_to_CFG.N.list next gamma target) suffix preWord context
  | splitLeft
      {p : List (symbol T (Nonterminal M))} {suffix preWord z : List T}
      {context : List (StackSymbol M)}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.list q (Z :: gamma) target)
        suffix preWord context)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hright : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal)) :
      ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single q Z middle) (z ++ suffix) preWord
        (gamma ++ context)
  | splitRight
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord leftWord : List T}
      {context : List (StackSymbol M)}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.list q (Z :: gamma) target)
        suffix preWord context)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hleft : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)]
        (leftWord.map symbol.terminal)) :
      ConcreteOperationalSpine M
        (p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)])
        (PDA_to_CFG.N.list middle gamma target) suffix
        (preWord ++ leftWord) context
  | start
      {target : State M}
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteOperationalSpine M []
        (PDA_to_CFG.N.list (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target) [] [] []

/-- Exact-context version of `Focused`.  Unlike `Focused`, the outer context
is an index, so consumers can relate it to the context carried by a concrete
spine without recovering an unrelated existential witness. -/
public inductive FocusedExact (M : DPDA Q T S) :
    Nonterminal M → List T → List T →
      List (StackSymbol M) → Prop
  | start : FocusedExact M PDA_to_CFG.N.start [] [] []
  | single (q target : State M) (Z : StackSymbol M)
      (preWord postWord : List T) (context : List (StackSymbol M))
      (final : State M)
      (prefixPath : (emptyStackPDA M).Reaches
        ⟨(emptyStackPDA M).initial_state, preWord,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨q, [], Z :: context⟩)
      (continuation : (emptyStackPDA M).Reaches
        ⟨target, postWord, context⟩ ⟨final, [], []⟩) :
      FocusedExact M (PDA_to_CFG.N.single q Z target)
        preWord postWord context
  | list (q target : State M) (gamma : List (StackSymbol M))
      (preWord postWord : List T) (context : List (StackSymbol M))
      (final : State M)
      (prefixPath : (emptyStackPDA M).Reaches
        ⟨(emptyStackPDA M).initial_state, preWord,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨q, [], gamma ++ context⟩)
      (continuation : (emptyStackPDA M).Reaches
        ⟨target, postWord, context⟩ ⟨final, [], []⟩) :
      FocusedExact M (PDA_to_CFG.N.list q gamma target)
        preWord postWord context

/-- Forgetting the exact context index gives the ordinary zipper invariant. -/
public theorem FocusedExact.focused (M : DPDA Q T S)
    {A : Nonterminal M} {preWord postWord : List T}
    {context : List (StackSymbol M)}
    (h : FocusedExact M A preWord postWord context) :
    Focused M A preWord postWord := by
  cases h with
  | start => exact Focused.start
  | single q target Z preWord postWord context final
      prefixPath continuation =>
      exact Focused.single q target Z preWord postWord context final
        prefixPath continuation
  | list q target gamma preWord postWord context final
      prefixPath continuation =>
      exact Focused.list q target gamma preWord postWord context final
        prefixPath continuation

/-- The context index of a normalized concrete spine has its exact
operational zipper meaning. -/
public theorem ConcreteOperationalSpine.focusedExact (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    (h : ConcreteOperationalSpine M p A suffix preWord context) :
    FocusedExact M A preWord suffix context := by
  induction h with
  | root => exact FocusedExact.start
  | @read p suffix preWord context q target next a Z gamma
      parent htransition hrule ih =>
      cases ih with
      | single _ _ _ _ _ _ final prefixPath continuation =>
          have prefixPath' := (PDA.unconsumed_input [a]).mp prefixPath
          have firstStep : (emptyStackPDA M).Reaches
              ⟨q, [a], Z :: context⟩
              ⟨next, [], gamma ++ context⟩ := by
            apply Relation.ReflTransGen.single
            exact Or.inl ⟨next, gamma, htransition, by simp⟩
          apply FocusedExact.list next target gamma
            (preWord ++ [a]) suffix context final
          · simpa [PDA.conf.appendInput] using prefixPath'.trans firstStep
          · exact continuation
  | @epsilon p suffix preWord context q target next Z gamma
      parent htransition hrule ih =>
      cases ih with
      | single _ _ _ _ _ _ final prefixPath continuation =>
          have firstStep : (emptyStackPDA M).Reaches
              ⟨q, [], Z :: context⟩
              ⟨next, [], gamma ++ context⟩ := by
            apply Relation.ReflTransGen.single
            exact ⟨next, gamma, htransition, by simp⟩
          exact FocusedExact.list next target gamma preWord suffix context final
            (prefixPath.trans firstStep) continuation
  | @splitLeft p suffix preWord z context q middle target Z gamma
      parent hlength hrule hright ih =>
      cases ih with
      | list _ _ _ _ _ _ final prefixPath continuation =>
          have hgammaLength : gamma.length ≤
              PDA_to_CFG.max_push (emptyStackPDA M) := by
            rw [List.length_cons] at hlength
            apply le_trans
            · exact WithBot.coe_le_coe.mpr (Nat.le_succ gamma.length)
            · exact hlength
          have hrightPath :=
            reaches_of_characteristic_derives_list M hgammaLength hright
          have hrightContext := hrightPath.append_stack context
          have hrightInput := (PDA.unconsumed_input suffix).mp hrightContext
          apply FocusedExact.single q middle Z preWord
            (z ++ suffix) (gamma ++ context) final
          · simpa [List.append_assoc] using prefixPath
          · exact hrightInput.trans continuation
  | @splitRight p suffix preWord leftWord context q middle target Z gamma
      parent hlength hrule hleft ih =>
      cases ih with
      | list _ _ _ _ _ _ final prefixPath continuation =>
          have hleftPath :=
            reaches_of_characteristic_derives_single M hleft
          have prefixPath' := (PDA.unconsumed_input leftWord).mp prefixPath
          have hleftContext := hleftPath.append_stack (gamma ++ context)
          apply FocusedExact.list middle target gamma
            (preWord ++ leftWord) suffix context final
          · simpa [List.append_assoc, PDA.conf.appendInput] using
              prefixPath'.trans hleftContext
          · exact continuation
  | @start target hrule =>
      apply FocusedExact.list (emptyStackPDA M).initial_state target
        [(emptyStackPDA M).start_symbol] [] [] [] target
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl

/-- Forgetting normalization and the hidden-context index recovers the
original operational spine. -/
public theorem ConcreteOperationalSpine.operationalSpine (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    (h : ConcreteOperationalSpine M p A suffix preWord context) :
    OperationalSpine M p A suffix preWord := by
  induction h with
  | root => exact OperationalSpine.root
  | read parent htransition hrule ih =>
      simpa using OperationalSpine.descend
        (alpha := [symbol.terminal _]) (beta := [])
        (z := []) (leftWord := [_]) ih hrule rfl rfl
        (Relation.ReflTransGen.refl)
        (Relation.ReflTransGen.refl)
  | epsilon parent htransition hrule ih =>
      simpa using OperationalSpine.descend
        (alpha := []) (beta := []) (z := []) (leftWord := [])
        ih hrule rfl rfl
        (Relation.ReflTransGen.refl)
        (Relation.ReflTransGen.refl)
  | splitLeft parent hlength hrule hright ih =>
      simpa using OperationalSpine.descend
        (alpha := [])
        (beta := [symbol.nonterminal _]) (leftWord := [])
        ih hrule rfl rfl
        (Relation.ReflTransGen.refl) hright
  | splitRight parent hlength hrule hleft ih =>
      simpa using OperationalSpine.descend
        (alpha := [symbol.nonterminal _]) (beta := []) (z := [])
        ih hrule rfl rfl hleft
        (Relation.ReflTransGen.refl)
  | start hrule =>
      simpa using OperationalSpine.descend
        (M := M) (alpha := []) (beta := []) (z := [])
        (leftWord := []) OperationalSpine.root hrule rfl rfl
        (Relation.ReflTransGen.refl)
        (Relation.ReflTransGen.refl)

private theorem terminal_words_eq_of_derives (G : CF_grammar T)
    {u v : List T}
    (h : G.DerivesRightmost (u.map symbol.terminal)
      (v.map symbol.terminal)) :
    u = v := by
  have heq := h.eq_of_map_terminal_source
  exact (List.map_injective_iff.mpr fun _ _ hsymbol =>
    symbol.terminal.inj hsymbol) heq.symm

private theorem decompose_one_nonterminal
    {N : Type} {A B : N}
    {left right : List (symbol T N)}
    (h : [symbol.nonterminal B] =
      left ++ [symbol.nonterminal A] ++ right) :
    left = [] ∧ A = B ∧ right = [] := by
  cases left with
  | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact ⟨rfl, (symbol.nonterminal.inj h.1).symm, h.2.symm⟩
  | cons X left =>
      simp only [List.cons_append, List.cons.injEq] at h
      have hbad : left ++ symbol.nonterminal A :: right = [] := by
        simpa using h.2.symm
      simp at hbad

private theorem decompose_terminal_nonterminal
    {N : Type} {a : T} {A B : N}
    {left right : List (symbol T N)}
    (h : [symbol.terminal a, symbol.nonterminal B] =
      left ++ [symbol.nonterminal A] ++ right) :
    left = [symbol.terminal a] ∧ A = B ∧ right = [] := by
  cases left with
  | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      cases h.1
  | cons X left =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      obtain ⟨hleft, hA, hright⟩ := decompose_one_nonterminal htail
      subst left
      exact ⟨rfl, hA, hright⟩

private theorem decompose_two_nonterminals
    {N : Type} {A B C : N}
    {left right : List (symbol T N)}
    (h : [symbol.nonterminal B, symbol.nonterminal C] =
      left ++ [symbol.nonterminal A] ++ right) :
    (left = [] ∧ A = B ∧ right = [symbol.nonterminal C]) ∨
    (left = [symbol.nonterminal B] ∧ A = C ∧ right = []) := by
  cases left with
  | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      left
      exact ⟨rfl, (symbol.nonterminal.inj h.1).symm, h.2.symm⟩
  | cons X left =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      obtain ⟨hleft, hA, hright⟩ := decompose_one_nonterminal htail
      subst left
      right
      exact ⟨rfl, hA, hright⟩

/-- Normalize every generic operational spine and recover its literal hidden
outer context. -/
public theorem concreteOperationalSpine_of_operationalSpine
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T}
    (h : OperationalSpine M p A suffix preWord) :
    ∃ context : List (StackSymbol M),
      ConcreteOperationalSpine M p A suffix preWord context := by
  induction h with
  | root => exact ⟨[], ConcreteOperationalSpine.root⟩
  | @descend p₀ alpha beta parent child t z preWord leftWord r
      parentSpine hr hlhs hrhs halpha hbeta ih =>
      obtain ⟨context, hparent⟩ := ih
      rcases characteristicGrammar_rule_shape M hr with
          hbase | hread | hepsilon | hsplit | hstart
      · rcases hbase with ⟨q, hrule⟩
        rw [hrule] at hrhs
        simp at hrhs
      · rcases hread with
          ⟨q, target, next, a, Z, gamma, htransition, hrule⟩
        rw [hrule] at hlhs hrhs
        obtain ⟨halphaShape, hchild, hbetaShape⟩ :=
          decompose_terminal_nonterminal hrhs
        subst alpha
        subst child
        subst beta
        subst parent
        have hleftWord : leftWord = [a] := by
          have hwords : [a] = leftWord :=
            terminal_words_eq_of_derives (characteristicGrammar M) (by
              simpa using halpha)
          exact hwords.symm
        have hz : z = [] := by
          have hwords : ([] : List T) = z :=
            terminal_words_eq_of_derives (characteristicGrammar M) (by
              simpa using hbeta)
          exact hwords.symm
        subst leftWord
        subst z
        exact ⟨context, by
          simpa using ConcreteOperationalSpine.read hparent htransition
            (hrule ▸ hr)⟩
      · rcases hepsilon with
          ⟨q, target, next, Z, gamma, htransition, hrule⟩
        rw [hrule] at hlhs hrhs
        obtain ⟨halphaShape, hchild, hbetaShape⟩ :=
          decompose_one_nonterminal hrhs
        subst alpha
        subst child
        subst beta
        subst parent
        have hleftWord : leftWord = [] := by
          have hwords : ([] : List T) = leftWord :=
            terminal_words_eq_of_derives (characteristicGrammar M) (by
              simpa using halpha)
          exact hwords.symm
        have hz : z = [] := by
          have hwords : ([] : List T) = z :=
            terminal_words_eq_of_derives (characteristicGrammar M) (by
              simpa using hbeta)
          exact hwords.symm
        subst leftWord
        subst z
        exact ⟨context, by
          simpa using ConcreteOperationalSpine.epsilon hparent htransition
            (hrule ▸ hr)⟩
      · rcases hsplit with
          ⟨q, middle, target, Z, gamma, hlength, hrule⟩
        rw [hrule] at hlhs hrhs
        rcases decompose_two_nonterminals hrhs with hleft | hright
        · rcases hleft with ⟨halphaShape, hchild, hbetaShape⟩
          subst alpha
          subst child
          subst beta
          subst parent
          have hleftWord : leftWord = [] := by
            have hwords : ([] : List T) = leftWord :=
              terminal_words_eq_of_derives (characteristicGrammar M) (by
                simpa using halpha)
            exact hwords.symm
          subst leftWord
          exact ⟨gamma ++ context, by
            simpa using ConcreteOperationalSpine.splitLeft hparent hlength
              (hrule ▸ hr) hbeta⟩
        · rcases hright with ⟨halphaShape, hchild, hbetaShape⟩
          subst alpha
          subst child
          subst beta
          subst parent
          have hz : z = [] := by
            have hwords : ([] : List T) = z :=
              terminal_words_eq_of_derives (characteristicGrammar M) (by
                simpa using hbeta)
            exact hwords.symm
          subst z
          exact ⟨context, by
            simpa using ConcreteOperationalSpine.splitRight hparent hlength
              (hrule ▸ hr) halpha⟩
      · rcases hstart with ⟨target, hrule⟩
        rw [hrule] at hlhs hrhs
        obtain ⟨halphaShape, hchild, hbetaShape⟩ :=
          decompose_one_nonterminal hrhs
        subst alpha
        subst child
        subst beta
        subst parent
        have hleftWord : leftWord = [] := by
          have hwords : ([] : List T) = leftWord :=
            terminal_words_eq_of_derives (characteristicGrammar M) (by
              simpa using halpha)
          exact hwords.symm
        have hz : z = [] := by
          have hwords : ([] : List T) = z :=
            terminal_words_eq_of_derives (characteristicGrammar M) (by
              simpa using hbeta)
          exact hwords.symm
        subst leftWord
        subst z
        cases hparent
        exact ⟨[], ConcreteOperationalSpine.start (hrule ▸ hr)⟩

/-- Direct normalization interface for an active spine and a chosen terminal
completion of its visible prefix. -/
public theorem concreteOperationalSpine_of_activeSpine
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T}
    (hspine : ActiveSpine M p A suffix)
    (hp : (characteristicGrammar M).DerivesRightmost p
      (preWord.map symbol.terminal)) :
    ∃ context : List (StackSymbol M),
      ConcreteOperationalSpine M p A suffix preWord context :=
  concreteOperationalSpine_of_operationalSpine M
    (operationalSpine_of_activeSpine M hspine hp)

/-- Reachability-specialized normalization interface. -/
public theorem concreteOperationalSpine_of_prehandle
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal A] ++ suffix.map symbol.terminal))
    (hp : (characteristicGrammar M).DerivesRightmost p
      (preWord.map symbol.terminal)) :
    ∃ context : List (StackSymbol M),
      ConcreteOperationalSpine M p A suffix preWord context :=
  concreteOperationalSpine_of_operationalSpine M
    (operationalSpine_of_prehandle M h hp)

/-- State component of the operational cut represented by an active
characteristic nonterminal. -/
public def spineCutState (M : DPDA Q T S) : Nonterminal M → State M
  | PDA_to_CFG.N.start => (emptyStackPDA M).initial_state
  | PDA_to_CFG.N.single q _ _ => q
  | PDA_to_CFG.N.list q _ _ => q

/-- Stack component of the operational cut.  The root convention agrees with
the initial configuration of `emptyStackPDA`. -/
public def spineCutStack (M : DPDA Q T S) :
    Nonterminal M → List (StackSymbol M) → List (StackSymbol M)
  | PDA_to_CFG.N.start, _ => [(emptyStackPDA M).start_symbol]
  | PDA_to_CFG.N.single _ Z _, context => Z :: context
  | PDA_to_CFG.N.list _ gamma _, context => gamma ++ context

/-- A suffix of a normalized spine containing no visible descent.  Its only
proper constructors are exactly start, epsilon, and split-left.  The complete
syntactic witnesses are retained, so downstream arguments can distinguish a
literal epsilon transition from a context-only split. -/
public inductive ZeroVisibleTail (M : DPDA Q T S)
    (p : List (symbol T (Nonterminal M))) (preWord : List T)
    (anchor : Nonterminal M) (anchorSuffix : List T)
    (anchorContext : List (StackSymbol M)) :
    Nonterminal M → List T → List (StackSymbol M) → Prop
  | refl : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      anchor anchorSuffix anchorContext
  | start
      {target : State M}
      (previous : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        PDA_to_CFG.N.start [] [])
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.list (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target) [] []
  | epsilon
      {suffix : List T} {context : List (StackSymbol M)}
      {q target next : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.single q Z target) suffix context)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun' q Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.list next gamma target) suffix context
  | splitLeft
      {suffix z : List T} {context : List (StackSymbol M)}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.list q (Z :: gamma) target) suffix context)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hright : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal)) :
      ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        (PDA_to_CFG.N.single q Z middle) (z ++ suffix) (gamma ++ context)

/-- Hidden contexts along a zero-visible tail are obtained only by prepending
blocks to the anchor context. -/
public theorem ZeroVisibleTail.context_eq_append (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M} {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (h : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      current currentSuffix currentContext) :
    ∃ added : List (StackSymbol M),
      currentContext = added ++ anchorContext := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | start previous hrule ih => exact ih
  | epsilon previous htransition hrule ih => exact ih
  | @splitLeft suffix z context q middle target Z gamma previous
      hlength hrule hright ih =>
      obtain ⟨added, hcontext⟩ := ih
      refine ⟨gamma ++ added, ?_⟩
      simp only [List.append_assoc, hcontext]

/-- The zero-visible tail is also a literal same-input PDA computation
between its endpoint cuts.  Start and split-left merely change the grammar
view of the same physical configuration; epsilon contributes its one
transition step. -/
public theorem ZeroVisibleTail.reaches_cut (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M} {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (h : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      current currentSuffix currentContext) :
    (emptyStackPDA M).Reaches
      ⟨spineCutState M anchor, [], spineCutStack M anchor anchorContext⟩
      ⟨spineCutState M current, [], spineCutStack M current currentContext⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | start previous hrule ih =>
      simpa [spineCutState, spineCutStack] using ih
  | @epsilon suffix context q target next Z gamma previous
      htransition hrule ih =>
      apply ih.tail
      exact ⟨next, gamma, htransition, by simp [spineCutState, spineCutStack]⟩
  | @splitLeft suffix z context q middle target Z gamma previous
      hlength hrule hright ih =>
      simpa [spineCutState, spineCutStack, List.append_assoc] using ih

/-- The node immediately before a maximal zero-visible tail.  It is either
the root or the child of the last visible event (read or split-right). -/
public inductive VisibleSpineAnchor (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → Nonterminal M →
      List T → List T → List (StackSymbol M) → Prop
  | root : VisibleSpineAnchor M [] PDA_to_CFG.N.start [] [] []
  | read
      {p : List (symbol T (Nonterminal M))} {suffix preWord : List T}
      {context : List (StackSymbol M)}
      {q target next : State M} {a : T} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single q Z target) suffix preWord context)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun q a Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      VisibleSpineAnchor M (p ++ [symbol.terminal a])
        (PDA_to_CFG.N.list next gamma target) suffix
        (preWord ++ [a]) context
  | splitRight
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord leftWord : List T}
      {context : List (StackSymbol M)}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.list q (Z :: gamma) target)
        suffix preWord context)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hleft : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)]
        (leftWord.map symbol.terminal)) :
      VisibleSpineAnchor M
        (p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)])
        (PDA_to_CFG.N.list middle gamma target) suffix
        (preWord ++ leftWord) context

/-- A visible anchor is itself a concrete normalized spine. -/
public theorem VisibleSpineAnchor.concreteOperationalSpine
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    (h : VisibleSpineAnchor M p A suffix preWord context) :
    ConcreteOperationalSpine M p A suffix preWord context := by
  cases h with
  | root => exact ConcreteOperationalSpine.root
  | read parent htransition hrule =>
      exact ConcreteOperationalSpine.read parent htransition hrule
  | splitRight parent hlength hrule hleft =>
      exact ConcreteOperationalSpine.splitRight parent hlength hrule hleft

/-- Extending a concrete anchor by a zero-visible tail reconstructs a
concrete spine at the endpoint. -/
public theorem ZeroVisibleTail.concreteOperationalSpine (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M} {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (h : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      current currentSuffix currentContext)
    (hanchor : ConcreteOperationalSpine M p anchor anchorSuffix
      preWord anchorContext) :
    ConcreteOperationalSpine M p current currentSuffix
      preWord currentContext := by
  induction h with
  | refl => exact hanchor
  | start previous hrule ih =>
      cases ih
      exact ConcreteOperationalSpine.start hrule
  | epsilon previous htransition hrule ih =>
      exact ConcreteOperationalSpine.epsilon ih htransition hrule
  | splitLeft previous hlength hrule hright ih =>
      exact ConcreteOperationalSpine.splitLeft ih hlength hrule hright

/-- Every concrete spine factors at the last visible event into a visible
anchor followed by a maximal tail of start/epsilon/split-left descents. -/
public theorem ConcreteOperationalSpine.zeroVisibleDecomposition
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    (h : ConcreteOperationalSpine M p A suffix preWord context) :
    ∃ (anchor : Nonterminal M) (anchorSuffix : List T)
        (anchorContext : List (StackSymbol M)),
      VisibleSpineAnchor M p anchor anchorSuffix preWord anchorContext ∧
      ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
        A suffix context := by
  induction h with
  | root =>
      exact ⟨PDA_to_CFG.N.start, [], [], VisibleSpineAnchor.root,
        ZeroVisibleTail.refl⟩
  | read parent htransition hrule ih =>
      exact ⟨_, _, _, VisibleSpineAnchor.read parent htransition hrule,
        ZeroVisibleTail.refl⟩
  | epsilon parent htransition hrule ih =>
      obtain ⟨anchor, anchorSuffix, anchorContext, hanchor, htail⟩ := ih
      exact ⟨anchor, anchorSuffix, anchorContext, hanchor,
        ZeroVisibleTail.epsilon htail htransition hrule⟩
  | splitLeft parent hlength hrule hright ih =>
      obtain ⟨anchor, anchorSuffix, anchorContext, hanchor, htail⟩ := ih
      exact ⟨anchor, anchorSuffix, anchorContext, hanchor,
        ZeroVisibleTail.splitLeft htail hlength hrule hright⟩
  | splitRight parent hlength hrule hleft ih =>
      exact ⟨_, _, _,
        VisibleSpineAnchor.splitRight parent hlength hrule hleft,
        ZeroVisibleTail.refl⟩
  | start hrule =>
      exact ⟨PDA_to_CFG.N.start, [], [], VisibleSpineAnchor.root,
        ZeroVisibleTail.start ZeroVisibleTail.refl hrule⟩

end

end DPDA_to_LR
