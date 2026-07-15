module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.TransitionRuns
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.UsefulEpsilonCycles
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ZeroVisibleSpine
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.SpineEdges
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.VisibleAnchorSemantics
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.InputDisplacement

/-!
# Synchronizing characteristic spines

Two independent operational run summaries do not determine an active
characteristic spine: in particular, successive drain pops can have the same
visible cut and the same transition output.  The synchronization theorem must
therefore retain the syntactic spine ancestry.  This file first records the
common-child completion facts used by that ancestry-sensitive argument.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A list-introducing edge together with its normalized concrete ancestry and
the chosen terminal completion of the child's visible prefix.  Unlike
`ListTransitionRun`, this relation retains the actual final grammar edge, so
successive drain pops cannot be confused with one another. -/
public inductive ConcreteListIntroduction (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → State M →
      List (StackSymbol M) → State M → List T → List T →
      List (StackSymbol M) → Nonterminal M →
      (Nonterminal M × List (symbol T (Nonterminal M))) → Prop
  | read
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord : List T} {context : List (StackSymbol M)}
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
      ConcreteListIntroduction M (p ++ [symbol.terminal a])
        next gamma target suffix (preWord ++ [a]) context
        (PDA_to_CFG.N.single q Z target)
        (PDA_to_CFG.N.single q Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)])
  | epsilon
      {p : List (symbol T (Nonterminal M))}
      {suffix preWord : List T} {context : List (StackSymbol M)}
      {q target next : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (parent : ConcreteOperationalSpine M p
        (PDA_to_CFG.N.single q Z target) suffix preWord context)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun' q Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteListIntroduction M p next gamma target suffix preWord context
        (PDA_to_CFG.N.single q Z target)
        (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)])
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
      ConcreteListIntroduction M
        (p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)])
        middle gamma target suffix (preWord ++ leftWord) context
        (PDA_to_CFG.N.list q (Z :: gamma) target)
        (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)])
  | start
      {target : State M}
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      ConcreteListIntroduction M [] (emptyStackPDA M).initial_state
        [(emptyStackPDA M).start_symbol] target [] [] []
        PDA_to_CFG.N.start
        (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)])

/-- The concrete introduction contains the normalized concrete spine of its
child. -/
public theorem ConcreteListIntroduction.childSpine (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {next target : State M} {gamma : List (StackSymbol M)}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (h : ConcreteListIntroduction M p next gamma target suffix preWord
      context parent rule) :
    ConcreteOperationalSpine M p (PDA_to_CFG.N.list next gamma target)
      suffix preWord context := by
  cases h with
  | read parent htransition hrule =>
      exact ConcreteOperationalSpine.read parent htransition hrule
  | epsilon parent htransition hrule =>
      exact ConcreteOperationalSpine.epsilon parent htransition hrule
  | splitRight parent hlength hrule hleft =>
      exact ConcreteOperationalSpine.splitRight parent hlength hrule hleft
  | start hrule => exact ConcreteOperationalSpine.start hrule

/-- Every replacement stack carried by a concrete list introduction satisfies
the characteristic grammar's uniform push bound. -/
public theorem ConcreteListIntroduction.gammaLength (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {next target : State M} {gamma : List (StackSymbol M)}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (h : ConcreteListIntroduction M p next gamma target suffix preWord
      context parent rule) :
    gamma.length ≤ PDA_to_CFG.max_push (emptyStackPDA M) := by
  cases h with
  | @read p suffix preWord context q target next a Z gamma
      parent htransition hrule =>
      apply PDA_to_CFG.push_le_max_push gamma q Z a
      exact ⟨(next, gamma), htransition, rfl⟩
  | @epsilon p suffix preWord context q target next Z gamma
      parent htransition hrule =>
      apply PDA_to_CFG.push_le_max_push' gamma q Z
      exact ⟨(next, gamma), htransition, rfl⟩
  | @splitRight p suffix preWord leftWord context q middle target Z gamma
      parent hlength hrule hleft =>
      rw [List.length_cons] at hlength
      exact le_trans (WithBot.coe_le_coe.mpr (Nat.le_succ gamma.length))
        hlength
  | start hrule =>
      simp [PDA_to_CFG.max_push]

private theorem terminal_completion_singleton (M : DPDA Q T S)
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

private theorem terminal_completion_nil (M : DPDA Q T S)
    {w : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [] (w.map symbol.terminal)) : w = [] := by
  have h' : (characteristicGrammar M).DerivesRightmost
      (([] : List T).map (symbol.terminal (N := Nonterminal M)))
      (w.map symbol.terminal) := by simpa using h
  have heq := h'.eq_of_map_terminal_source
  have hmap : w.map (symbol.terminal (N := Nonterminal M)) = [] := by
    simpa using heq
  exact List.map_eq_nil_iff.mp hmap

/-- Every visible prefix of a list-introducing edge has a terminal
completion.  For a split edge, productivity of the exposed left `single`
supplies the additional completed segment. -/
public theorem ListIntroduction.prefixCompletion (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {child : Nonterminal M} {childSuffix : List T}
    {parentPrefix : List (symbol T (Nonterminal M))}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (h : ListIntroduction M childPrefix child childSuffix
      parentPrefix parent rule) :
    ∃ preWord : List T,
      (characteristicGrammar M).DerivesRightmost childPrefix
        (preWord.map symbol.terminal) := by
  cases h with
  | @read p suffix q target next a Z gamma hparent htransition hrule =>
      obtain ⟨beforeWord, hbefore⟩ :=
        prehandle_prefix_completion M hrule (hparent.derivesRightmost M)
      refine ⟨beforeWord ++ [a], ?_⟩
      have ha : (characteristicGrammar M).DerivesRightmost
          [symbol.terminal a] ([a].map symbol.terminal) :=
        Relation.ReflTransGen.refl
      simpa [List.map_append] using hbefore.append_to_terminals ha
  | @epsilon p suffix q target next Z gamma hparent htransition hrule =>
      exact prehandle_prefix_completion M hrule
        (hparent.derivesRightmost M)
  | @split p suffix q middle target Z gamma hparent hlength hrule =>
      obtain ⟨beforeWord, hbefore⟩ :=
        prehandle_prefix_completion M hrule (hparent.derivesRightmost M)
      have hproductive : productive (characteristicGrammar M)
          (PDA_to_CFG.N.single q Z middle) :=
        characteristic_rule_rhs_productive_reduced M hrule (by simp)
      obtain ⟨leftWord, hleft⟩ := hproductive
      have hleft' := CF_grammar.derivesRightmost_of_derives hleft
      refine ⟨beforeWord ++ leftWord, ?_⟩
      simpa [List.map_append] using
        hbefore.append_to_terminals hleft'
  | start hparent hrule =>
      have hnil := (hparent.start_eq_nil M).1
      subst childPrefix
      exact ⟨[], Relation.ReflTransGen.refl⟩

/-- Normalize a list-introducing active edge after choosing a terminal
completion of its child prefix.  The returned witness retains both the exact
last edge and the concrete ancestry leading to its parent. -/
public theorem concreteListIntroduction_of_listIntroduction
    (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {child : Nonterminal M} {childSuffix : List T}
    {parentPrefix : List (symbol T (Nonterminal M))}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    {preWord : List T}
    (h : ListIntroduction M childPrefix child childSuffix
      parentPrefix parent rule)
    (hp : (characteristicGrammar M).DerivesRightmost childPrefix
      (preWord.map symbol.terminal)) :
    ∃ (next target : State M) (gamma context : List (StackSymbol M)),
      child = PDA_to_CFG.N.list next gamma target ∧
      ConcreteListIntroduction M childPrefix next gamma target childSuffix
        preWord context parent rule := by
  cases h with
  | @read p suffix q target next a Z gamma hparent htransition hrule =>
      obtain ⟨parentWord, leftWord, hpre, hpParent, hpLeft⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      have hleftWord : leftWord = [a] :=
        terminal_completion_singleton M hpLeft
      subst leftWord
      obtain ⟨context, hconcrete⟩ :=
        concreteOperationalSpine_of_activeSpine M hparent hpParent
      refine ⟨next, target, gamma, context, rfl, ?_⟩
      simpa [hpre] using
        ConcreteListIntroduction.read hconcrete htransition hrule
  | @epsilon p suffix q target next Z gamma hparent htransition hrule =>
      obtain ⟨context, hconcrete⟩ :=
        concreteOperationalSpine_of_activeSpine M hparent hp
      exact ⟨next, target, gamma, context, rfl,
        ConcreteListIntroduction.epsilon hconcrete htransition hrule⟩
  | @split p suffix q middle target Z gamma hparent hlength hrule =>
      obtain ⟨parentWord, leftWord, hpre, hpParent, hpLeft⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      obtain ⟨context, hconcrete⟩ :=
        concreteOperationalSpine_of_activeSpine M hparent hpParent
      refine ⟨middle, target, gamma, context, rfl, ?_⟩
      simpa [hpre] using ConcreteListIntroduction.splitRight
        hconcrete hlength hrule hpLeft
  | start hparent hrule =>
      have hchildPrefix : childPrefix = [] := (hparent.start_eq_nil M).1
      have hchildSuffix : childSuffix = [] := (hparent.start_eq_nil M).2
      subst childPrefix
      subst childSuffix
      have hpreWord : preWord = [] := terminal_completion_nil M hp
      subst preWord
      exact ⟨(emptyStackPDA M).initial_state, _,
        [(emptyStackPDA M).start_symbol], [], rfl,
        ConcreteListIntroduction.start hrule⟩

/-- A nonterminal occurring in a retained characteristic rule has a terminal
rightmost completion. -/
public theorem retainedChild_completion (M : DPDA Q T S)
    {r : Nonterminal M × List (symbol T (Nonterminal M))}
    {A : Nonterminal M}
    (hr : r ∈ (characteristicGrammar M).rules)
    (hA : symbol.nonterminal A ∈ r.2) :
    ∃ w : List T,
      (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal A] (w.map symbol.terminal) := by
  apply derivesRightmost_terminal_of_all_productive
  intro B hB
  have hBA : B = A := by simpa using hB
  subst B
  exact characteristic_rule_rhs_productive_reduced M hr hA

/-- The list child selected by a concrete introduction has a terminal
completion, independently of the surrounding active suffix. -/
public theorem ConcreteListIntroduction.childCompletion (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {next target : State M} {gamma : List (StackSymbol M)}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (h : ConcreteListIntroduction M p next gamma target suffix preWord
      context parent rule) :
    ∃ w : List T,
      (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]
        (w.map symbol.terminal) := by
  cases h with
  | read parent htransition hrule =>
      exact retainedChild_completion M hrule (by simp)
  | epsilon parent htransition hrule =>
      exact retainedChild_completion M hrule (by simp)
  | splitRight parent hlength hrule hleft =>
      exact retainedChild_completion M hrule (by simp)
  | start hrule =>
      exact retainedChild_completion M hrule (by simp)

/-- The focused continuation of a concrete introduction starts at its list
target with exactly the saved suffix and outer context. -/
public theorem ConcreteListIntroduction.childContinuation
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {next target : State M} {gamma : List (StackSymbol M)}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (h : ConcreteListIntroduction M p next gamma target suffix preWord
      context parent rule) :
    ∃ final : State M,
      (emptyStackPDA M).Reaches
        ⟨target, suffix, context⟩ ⟨final, [], []⟩ := by
  have hfocused := (h.childSpine M).focusedExact M
  cases hfocused with
  | list q target gamma preWord suffix context final
      prefixPath continuation =>
      exact ⟨final, continuation⟩

/-- A terminal completion of a characteristic list child realizes its encoded
net-pop computation under every saved outer stack context. -/
public theorem completedList_reaches_with_context (M : DPDA Q T S)
    {q target : State M} {gamma context : List (StackSymbol M)}
    {w : List T}
    (hgamma : gamma.length ≤ PDA_to_CFG.max_push (emptyStackPDA M))
    (hcomplete : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (PDA_to_CFG.N.list q gamma target)]
      (w.map symbol.terminal)) :
    (emptyStackPDA M).Reaches
      ⟨q, w, gamma ++ context⟩ ⟨target, [], context⟩ := by
  simpa [PDA.conf.appendStack, List.append_assoc] using
    (reaches_of_characteristic_derives_list M hgamma hcomplete).append_stack
      context

/-- Completing a list child and then following its focused continuation gives
an accepting continuation from the child's concrete stack cut. -/
public theorem completedList_useful_with_context (M : DPDA Q T S)
    {q target final : State M}
    {gamma context : List (StackSymbol M)} {w suffix : List T}
    (hgamma : gamma.length ≤ PDA_to_CFG.max_push (emptyStackPDA M))
    (hcomplete : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (PDA_to_CFG.N.list q gamma target)]
      (w.map symbol.terminal))
    (hcontinuation : (emptyStackPDA M).Reaches
      ⟨target, suffix, context⟩ ⟨final, [], []⟩) :
    (emptyStackPDA M).Reaches
      ⟨q, w ++ suffix, gamma ++ context⟩ ⟨final, [], []⟩ := by
  have hchild := completedList_reaches_with_context M
    hgamma hcomplete (context := context)
  exact ((PDA.unconsumed_input suffix).mp hchild).trans hcontinuation

/-! ## Concrete anchor comparison -/

/-- Recover the left visible anchor retained by a paired-anchor witness. -/
public theorem PairedVisibleAnchors.leftAnchor (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {A₁ A₂ : Nonterminal M} {suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    (h : PairedVisibleAnchors M p preWord A₁ suffix₁ context₁
      A₂ suffix₂ context₂) :
    VisibleSpineAnchor M p A₁ suffix₁ preWord context₁ := by
  cases h with
  | root => exact VisibleSpineAnchor.root
  | read parent₁ transition₁ rule₁ parent₂ transition₂ rule₂ =>
      exact VisibleSpineAnchor.read parent₁ transition₁ rule₁
  | splitRight parent₁ length₁ rule₁ left₁ parent₂ length₂ rule₂
      left₂ word₁ word₂ =>
      simpa only [← word₁] using
        VisibleSpineAnchor.splitRight parent₁ length₁ rule₁ left₁

/-- Recover the right visible anchor retained by a paired-anchor witness. -/
public theorem PairedVisibleAnchors.rightAnchor (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {A₁ A₂ : Nonterminal M} {suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    (h : PairedVisibleAnchors M p preWord A₁ suffix₁ context₁
      A₂ suffix₂ context₂) :
    VisibleSpineAnchor M p A₂ suffix₂ preWord context₂ := by
  cases h with
  | root => exact VisibleSpineAnchor.root
  | read parent₁ transition₁ rule₁ parent₂ transition₂ rule₂ =>
      exact VisibleSpineAnchor.read parent₂ transition₂ rule₂
  | splitRight parent₁ length₁ rule₁ left₁ parent₂ length₂ rule₂
      left₂ word₁ word₂ =>
      simpa only [← word₂] using
        VisibleSpineAnchor.splitRight parent₂ length₂ rule₂ left₂

/-- Paired visible anchors whose endpoint states both remain in the
simulation component lie on one ordered normalized computation.  This is the
comparison needed for split-right/split-right anchors; read anchors admit the
stronger literal equality proved below. -/
public theorem PairedVisibleAnchors.simulationCutsComparable
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {q₁ q₂ : Q × Bool} {target₁ target₂ : State M}
    {gamma₁ gamma₂ context₁ context₂ : List (StackSymbol M)}
    {suffix₁ suffix₂ : List T}
    (h : PairedVisibleAnchors M p preWord
      (PDA_to_CFG.N.list (Sum.inl q₁) gamma₁ target₁) suffix₁ context₁
      (PDA_to_CFG.N.list (Sum.inl q₂) gamma₂ target₂) suffix₂ context₂) :
    (emptyStackPDA M).Reaches
        ⟨Sum.inl q₁, [], gamma₁ ++ context₁⟩
        ⟨Sum.inl q₂, [], gamma₂ ++ context₂⟩ ∨
      (emptyStackPDA M).Reaches
        ⟨Sum.inl q₂, [], gamma₂ ++ context₂⟩
        ⟨Sum.inl q₁, [], gamma₁ ++ context₁⟩ := by
  have hleft := (h.leftAnchor M).prefixPath M
  have hright := (h.rightAnchor M).prefixPath M
  simpa [spineCutState, spineCutStack] using
    emptyStack_global_simulation_cuts_comparable M hleft hright

/-- Read transitions of the normalized empty-stack machine have a unique
output.  The FS→ES wrapper introduces nondeterminism only through an epsilon
edge into the drain, never between two reading edges. -/
public theorem emptyStack_read_output_unique (M : DPDA Q T S)
    {q next₁ next₂ : State M} {a : T} {Z : StackSymbol M}
    {gamma₁ gamma₂ : List (StackSymbol M)}
    (h₁ : (next₁, gamma₁) ∈
      (emptyStackPDA M).transition_fun q a Z)
    (h₂ : (next₂, gamma₂) ∈
      (emptyStackPDA M).transition_fun q a Z) :
    (next₁, gamma₁) = (next₂, gamma₂) := by
  classical
  cases q with
  | inr i =>
      simp [emptyStackPDA, PDA_FS_to_ES_pda,
        PDA_FS_to_ES_trans] at h₁
  | inl q =>
      cases Z with
      | none =>
          simp [emptyStackPDA, PDA_FS_to_ES_pda,
            PDA_FS_to_ES_trans] at h₁
      | some Z =>
          change (next₁, gamma₁) ∈
              (fun out : (Q × Bool) × List S =>
                (Sum.inl out.1, out.2.map some)) ''
                M.firstFinal.toPDA.transition_fun q a Z at h₁
          change (next₂, gamma₂) ∈
              (fun out : (Q × Bool) × List S =>
                (Sum.inl out.1, out.2.map some)) ''
                M.firstFinal.toPDA.transition_fun q a Z at h₂
          rcases h₁ with ⟨out₁, hout₁, heq₁⟩
          rcases h₂ with ⟨out₂, hout₂, heq₂⟩
          have hstep₁ : M.firstFinal.toPDA.Reaches₁
              ⟨q, [a], [Z]⟩ ⟨out₁.1, [], out₁.2⟩ :=
            Or.inl ⟨out₁.1, out₁.2, hout₁, by simp⟩
          have hstep₂ : M.firstFinal.toPDA.Reaches₁
              ⟨q, [a], [Z]⟩ ⟨out₂.1, [], out₂.2⟩ :=
            Or.inl ⟨out₂.1, out₂.2, hout₂, by simp⟩
          have hconf := M.firstFinal.toPDA_step_deterministic hstep₁ hstep₂
          have hout : out₁ = out₂ := Prod.ext
            (congrArg PDA.conf.state hconf)
            (congrArg PDA.conf.stack hconf)
          subst out₂
          exact heq₁.symm.trans heq₂

/-- Aligned concrete read anchors agree componentwise on their output cut,
including the hidden outer context. -/
public theorem concreteRead_anchor_data_eq (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {q₁ q₂ target₁ target₂ next₁ next₂ : State M}
    {a : T} {Z₁ Z₂ : StackSymbol M}
    {gamma₁ gamma₂ : List (StackSymbol M)}
    (parent₁ : ConcreteOperationalSpine M p
      (PDA_to_CFG.N.single q₁ Z₁ target₁)
      suffix₁ preWord context₁)
    (parent₂ : ConcreteOperationalSpine M p
      (PDA_to_CFG.N.single q₂ Z₂ target₂)
      suffix₂ preWord context₂)
    (read₁ : (next₁, gamma₁) ∈
      (emptyStackPDA M).transition_fun q₁ a Z₁)
    (read₂ : (next₂, gamma₂) ∈
      (emptyStackPDA M).transition_fun q₂ a Z₂) :
    next₁ = next₂ ∧ gamma₁ = gamma₂ ∧ context₁ = context₂ := by
  have hsource := concreteSingle_read_source_cuts_eq M
    parent₁ parent₂ read₁ read₂
  have hq : q₁ = q₂ := congrArg PDA.conf.state hsource
  have hstack : Z₁ :: context₁ = Z₂ :: context₂ :=
    congrArg PDA.conf.stack hsource
  have hZ : Z₁ = Z₂ := (List.cons.inj hstack).1
  have hcontext : context₁ = context₂ := (List.cons.inj hstack).2
  subst q₂
  subst Z₂
  have hout := emptyStack_read_output_unique M read₁ read₂
  exact ⟨congrArg Prod.fst hout, congrArg Prod.snd hout, hcontext⟩

/-- No transition of the FS→ES machine enters its distinguished boot state. -/
public theorem emptyStack_step_target_ne_boot (M : DPDA Q T S)
    {c d : PDA.conf (emptyStackPDA M)}
    (h : (emptyStackPDA M).Reaches₁ c d) :
    d.state ≠ Sum.inr 0 := by
  rcases c with ⟨state, input, stack⟩
  rcases d with ⟨next, nextInput, nextStack⟩
  intro hboot
  change next = Sum.inr 0 at hboot
  subst next
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h
  | cons Z rest =>
      rcases PDA.reaches₁_push h with hread | hepsilon
      · rcases hread with ⟨a, tail, p, alpha, _, heq, hmem⟩
        cases heq
        cases state <;> cases Z <;>
          simp [emptyStackPDA, PDA_FS_to_ES_pda,
            PDA_FS_to_ES_trans] at hmem
      · rcases hepsilon with ⟨p, alpha, heq, hmem⟩
        cases heq
        cases state with
        | inl q =>
            cases Z <;>
              simp [emptyStackPDA, PDA_FS_to_ES_pda,
                PDA_FS_to_ES_eps] at hmem
        | inr i =>
            rcases i with ⟨i, hi⟩
            have hi' : i = 0 ∨ i = 1 := by omega
            rcases hi' with rfl | rfl <;>
              cases Z <;>
              simp [emptyStackPDA, PDA_FS_to_ES_pda,
                PDA_FS_to_ES_eps] at hmem

/-- A globally reachable boot-state configuration is literally the initial
configuration; no nonempty computation can return to boot. -/
public theorem emptyStack_global_boot_cut_eq (M : DPDA Q T S)
    {w input : List T} {stack : List (StackSymbol M)}
    (h : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inr 0, input, stack⟩) :
    (⟨Sum.inr 0, input, stack⟩ : PDA.conf (emptyStackPDA M)) =
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩ := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with heq | hstrict
  · exact heq
  · obtain ⟨before, hprefix, hlast⟩ :=
      Relation.TransGen.tail'_iff.mp hstrict
    exact (emptyStack_step_target_ne_boot M hlast rfl).elim

/-- All paired visible-anchor cuts are comparable.  Read anchors are equal,
split anchors use the deterministic simulation or drain phase, and the boot
case reduces to the literal initial configuration. -/
public theorem PairedVisibleAnchors.cutsComparable (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {A₁ A₂ : Nonterminal M} {suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    (h : PairedVisibleAnchors M p preWord A₁ suffix₁ context₁
      A₂ suffix₂ context₂) :
    (emptyStackPDA M).Reaches
        ⟨spineCutState M A₁, [], spineCutStack M A₁ context₁⟩
        ⟨spineCutState M A₂, [], spineCutStack M A₂ context₂⟩ ∨
      (emptyStackPDA M).Reaches
        ⟨spineCutState M A₂, [], spineCutStack M A₂ context₂⟩
        ⟨spineCutState M A₁, [], spineCutStack M A₁ context₁⟩ := by
  cases h with
  | root => exact Or.inl Relation.ReflTransGen.refl
  | read parent₁ transition₁ rule₁ parent₂ transition₂ rule₂ =>
      obtain ⟨hnext, hgamma, hcontext⟩ :=
        concreteRead_anchor_data_eq M parent₁ parent₂
          transition₁ transition₂
      subst_vars
      exact Or.inl Relation.ReflTransGen.refl
  | @splitRight base completedWord beforeWord₁ leftWord₁
      beforeWord₂ leftWord₂ suffix₁ suffix₂ context₁ context₂
      q middle target₁ target₂ Z gamma₁ gamma₂
      parent₁ length₁ rule₁ left₁ parent₂ length₂ rule₂ left₂
      word₁ word₂ =>
      let anchor₁ := VisibleSpineAnchor.splitRight
        parent₁ length₁ rule₁ left₁
      let anchor₂ := VisibleSpineAnchor.splitRight
        parent₂ length₂ rule₂ left₂
      have hglobal₁ := anchor₁.prefixPath M
      have hglobal₂ := anchor₂.prefixPath M
      have hglobal₁' : (emptyStackPDA M).Reaches
          ⟨(emptyStackPDA M).initial_state, preWord,
            [(emptyStackPDA M).start_symbol]⟩
          ⟨spineCutState M (PDA_to_CFG.N.list middle gamma₁ target₁),
            [], spineCutStack M
              (PDA_to_CFG.N.list middle gamma₁ target₁) context₁⟩ := by
        simpa only [word₁] using hglobal₁
      have hglobal₂' : (emptyStackPDA M).Reaches
          ⟨(emptyStackPDA M).initial_state, preWord,
            [(emptyStackPDA M).start_symbol]⟩
          ⟨spineCutState M (PDA_to_CFG.N.list middle gamma₂ target₂),
            [], spineCutStack M
              (PDA_to_CFG.N.list middle gamma₂ target₂) context₂⟩ := by
        simpa only [word₂] using hglobal₂
      cases middle with
      | inl middle =>
          simpa [spineCutState, spineCutStack] using
            emptyStack_global_simulation_cuts_comparable M
              hglobal₁' hglobal₂'
      | inr i =>
          rcases i with ⟨i, hi⟩
          have hi' : i = 0 ∨ i = 1 := by omega
          rcases hi' with rfl | rfl
          · have heq₁ := emptyStack_global_boot_cut_eq M hglobal₁'
            have heq₂ := emptyStack_global_boot_cut_eq M hglobal₂'
            have heq := heq₁.trans heq₂.symm
            left
            simpa [spineCutState, spineCutStack] using
              (heq ▸ (Relation.ReflTransGen.refl :
                (emptyStackPDA M).Reaches
                  ⟨Sum.inr 0, [], gamma₁ ++ context₁⟩
                  ⟨Sum.inr 0, [], gamma₁ ++ context₁⟩))
          · simpa [spineCutState, spineCutStack] using
              emptyStack_global_drain_cuts_comparable M
                hglobal₁' hglobal₂'

/-! ## Removing the untouched outer context of a zero-visible tail -/

/-- A zero-visible tail has a context-free operational realization.  The
returned `added` block is exactly what the tail inserted immediately above
the anchor's untouched outer context. -/
public theorem ZeroVisibleTail.reachesCutWithoutAnchorContext
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {anchor current : Nonterminal M} {anchorSuffix currentSuffix : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (h : ZeroVisibleTail M p preWord anchor anchorSuffix anchorContext
      current currentSuffix currentContext) :
    ∃ added : List (StackSymbol M),
      currentContext = added ++ anchorContext ∧
      (emptyStackPDA M).Reaches
        ⟨spineCutState M anchor, [], spineCutStack M anchor []⟩
        ⟨spineCutState M current, [], spineCutStack M current added⟩ := by
  induction h with
  | refl =>
      exact ⟨[], by simp, Relation.ReflTransGen.refl⟩
  | start previous hrule ih =>
      obtain ⟨added, hcontext, hreach⟩ := ih
      have hadded : added = [] := (List.append_eq_nil_iff.mp hcontext.symm).1
      subst added
      exact ⟨[], hcontext, by
        simpa [spineCutState, spineCutStack] using hreach⟩
  | @epsilon suffix context q target next Z gamma previous
      htransition hrule ih =>
      obtain ⟨added, hcontext, hreach⟩ := ih
      refine ⟨added, hcontext, hreach.tail ?_⟩
      exact ⟨next, gamma, htransition, by
        simp [spineCutState, spineCutStack]⟩
  | @splitLeft suffix z context q middle target Z gamma previous
      hlength hrule hright ih =>
      obtain ⟨added, hcontext, hreach⟩ := ih
      refine ⟨gamma ++ added, ?_, ?_⟩
      · simp only [List.append_assoc, hcontext]
      · simpa [spineCutState, spineCutStack, List.append_assoc] using hreach

private theorem transGen_append_input_exact
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

/-- A zero-visible tail cannot return nontrivially to the same list
nonterminal on a productive spine.  With no inserted context it is a useful
cycle; with a nonempty inserted block it is useful stack growth. -/
public theorem epsilonBearing_sameListCutTail_false (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {preWord : List T}
    {q anchorTarget currentTarget final : State M}
    {gamma : List (StackSymbol M)}
    {anchorSuffix currentSuffix completion : List T}
    {anchorContext currentContext : List (StackSymbol M)}
    (htail : ZeroVisibleTail M p preWord
      (PDA_to_CFG.N.list q gamma anchorTarget) anchorSuffix anchorContext
      (PDA_to_CFG.N.list q gamma currentTarget) currentSuffix currentContext)
    (hbearing : EpsilonBearingZeroVisibleTail M p preWord
      (PDA_to_CFG.N.list q gamma anchorTarget) anchorSuffix anchorContext
      (PDA_to_CFG.N.list q gamma currentTarget) currentSuffix currentContext)
    (hgamma : gamma.length ≤ PDA_to_CFG.max_push (emptyStackPDA M))
    (hcomplete : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (PDA_to_CFG.N.list q gamma currentTarget)]
      (completion.map symbol.terminal))
    (hcontinuation : (emptyStackPDA M).Reaches
      ⟨currentTarget, currentSuffix, currentContext⟩
      ⟨final, [], []⟩) : False := by
  obtain ⟨added, hcontext, hstripped⟩ :=
    htail.reachesCutWithoutAnchorContext M
  have huseful := completedList_useful_with_context M
    hgamma hcomplete hcontinuation
  by_cases hadded : added = []
  · subst added
    have hcycle₀ := hbearing.transGen_cut M
    have hcycle := transGen_append_input_exact hcycle₀
      (completion ++ currentSuffix)
    have hcycle' : Relation.TransGen
        (@PDA.Reaches₁ _ _ _ _ _ _ (emptyStackPDA M))
        ⟨q, completion ++ currentSuffix, gamma ++ anchorContext⟩
        ⟨q, completion ++ currentSuffix, gamma ++ anchorContext⟩ := by
      simpa [spineCutState, spineCutStack, hcontext,
        PDA.conf.appendInput] using hcycle
    exact emptyStack_no_useful_cycle M hcycle'
      (by simpa [hcontext, List.append_assoc] using huseful)
  · apply emptyStack_no_useful_stack_growth M
      (q := q) (base := gamma) (extra := added)
      (context := anchorContext) (input := completion ++ currentSuffix)
      (final := final)
    · simpa [spineCutState, spineCutStack] using hstripped
    · exact hadded
    · simpa [hcontext, List.append_assoc] using huseful

/-! ## Paired read/epsilon synchronization -/

/-- Any visible anchor aligned with a concrete read anchor is another read
anchor with the same physical output data. -/
public theorem visibleReadAnchor_aligned_data_eq (M : DPDA Q T S)
    {base p₂ : List (symbol T (Nonterminal M))}
    {beforeWord preWord₂ : List T} {a : T}
    {suffix₁ suffix₂ : List T}
    {context₁ context₂ : List (StackSymbol M)}
    {q₁ target₁ next₁ : State M} {Z₁ : StackSymbol M}
    {gamma₁ : List (StackSymbol M)} {A₂ : Nonterminal M}
    (parent₁ : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.single q₁ Z₁ target₁)
      suffix₁ beforeWord context₁)
    (transition₁ : (next₁, gamma₁) ∈
      (emptyStackPDA M).transition_fun q₁ a Z₁)
    (h₂ : VisibleSpineAnchor M p₂ A₂ suffix₂ preWord₂ context₂)
    (hp : base ++ [symbol.terminal a] = p₂)
    (hw : beforeWord ++ [a] = preWord₂) :
    ∃ target₂ : State M,
      A₂ = PDA_to_CFG.N.list next₁ gamma₁ target₂ ∧
      context₂ = context₁ := by
  cases h₂ with
  | root => simp at hp
  | @read base₂ suffixTwo before₂ contextTwo
      q₂ target₂ next₂ a₂ Z₂ gamma₂ parent₂ transition₂ rule₂ =>
      have hbase := List.append_inj_left' hp rfl
      have hlast := List.append_inj_right' hp rfl
      have ha : a = a₂ := by simpa using hlast
      subst base₂
      subst a₂
      have hbefore := List.append_inj_left' hw rfl
      subst before₂
      obtain ⟨hnext, hgamma, hcontext⟩ :=
        concreteRead_anchor_data_eq M parent₁ parent₂
          transition₁ transition₂
      subst next₂
      subst gamma₂
      exact ⟨target₂, rfl, hcontext.symm⟩
  | splitRight parent₂ length₂ rule₂ left₂ =>
      have hlast := List.append_inj_right' hp rfl
      cases (List.cons.inj hlast).1

/-- A concrete read edge and a concrete epsilon edge cannot introduce the
same active list child.  Aligning their last visible read anchors makes the
epsilon side a productive nonempty return to the same physical list cut. -/
public theorem concreteRead_epsilon_false (M : DPDA Q T S)
    {base childPrefix : List (symbol T (Nonterminal M))}
    {beforeWord preWord : List T} {a : T}
    {suffixRead suffixEpsilon : List T}
    {readContext epsilonContext : List (StackSymbol M)}
    {qRead qEpsilon next target : State M}
    {ZRead ZEpsilon : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (readParent : ConcreteOperationalSpine M base
      (PDA_to_CFG.N.single qRead ZRead target)
      suffixRead beforeWord readContext)
    (readTransition : (next, gamma) ∈
      (emptyStackPDA M).transition_fun qRead a ZRead)
    (epsilonParent : ConcreteOperationalSpine M childPrefix
      (PDA_to_CFG.N.single qEpsilon ZEpsilon target)
      suffixEpsilon preWord epsilonContext)
    (epsilonTransition : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' qEpsilon ZEpsilon)
    (epsilonRule : (PDA_to_CFG.N.single qEpsilon ZEpsilon target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (hprefix : base ++ [symbol.terminal a] = childPrefix)
    (hword : beforeWord ++ [a] = preWord) : False := by
  subst childPrefix
  subst preWord
  obtain ⟨anchor, anchorSuffix, anchorContext, hanchor, hparentTail⟩ :=
    epsilonParent.zeroVisibleDecomposition M
  have htail : ZeroVisibleTail M
      (base ++ [symbol.terminal a]) (beforeWord ++ [a])
      anchor anchorSuffix anchorContext
      (PDA_to_CFG.N.list next gamma target) suffixEpsilon
      epsilonContext :=
    ZeroVisibleTail.epsilon hparentTail epsilonTransition epsilonRule
  have hbearing : EpsilonBearingZeroVisibleTail M
      (base ++ [symbol.terminal a]) (beforeWord ++ [a])
      anchor anchorSuffix anchorContext
      (PDA_to_CFG.N.list next gamma target) suffixEpsilon
      epsilonContext :=
    EpsilonBearingZeroVisibleTail.epsilon
      hparentTail epsilonTransition epsilonRule
  obtain ⟨anchorTarget, hanchorShape, hanchorContext⟩ :=
    visibleReadAnchor_aligned_data_eq M readParent readTransition
      hanchor rfl rfl
  subst anchor
  subst anchorContext
  let hepsilon : ConcreteListIntroduction M
      (base ++ [symbol.terminal a]) next gamma target suffixEpsilon
      (beforeWord ++ [a]) epsilonContext
      (PDA_to_CFG.N.single qEpsilon ZEpsilon target)
      (PDA_to_CFG.N.single qEpsilon ZEpsilon target,
        [symbol.nonterminal
          (PDA_to_CFG.N.list next gamma target)]) :=
    ConcreteListIntroduction.epsilon
      epsilonParent epsilonTransition epsilonRule
  obtain ⟨completion, hcomplete⟩ := hepsilon.childCompletion M
  obtain ⟨final, hcontinuation⟩ := hepsilon.childContinuation M
  exact epsilonBearing_sameListCutTail_false M htail hbearing
    (hepsilon.gammaLength M) hcomplete hcontinuation

/-- Active-spine form of `concreteRead_epsilon_false`, obtaining the common
visible-prefix completion and exact hidden contexts internally. -/
public theorem activeRead_epsilon_false (M : DPDA Q T S)
    {base childPrefix : List (symbol T (Nonterminal M))}
    {a : T} {suffixRead suffixEpsilon : List T}
    {qRead qEpsilon next target : State M}
    {ZRead ZEpsilon : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (readParent : ActiveSpine M base
      (PDA_to_CFG.N.single qRead ZRead target) suffixRead)
    (readTransition : (next, gamma) ∈
      (emptyStackPDA M).transition_fun qRead a ZRead)
    (readRule : (PDA_to_CFG.N.single qRead ZRead target,
        [symbol.terminal a,
          symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (epsilonParent : ActiveSpine M childPrefix
      (PDA_to_CFG.N.single qEpsilon ZEpsilon target) suffixEpsilon)
    (epsilonTransition : (next, gamma) ∈
      (emptyStackPDA M).transition_fun' qEpsilon ZEpsilon)
    (epsilonRule : (PDA_to_CFG.N.single qEpsilon ZEpsilon target,
        [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
      (characteristicGrammar M).rules)
    (hprefix : base ++ [symbol.terminal a] = childPrefix) : False := by
  obtain ⟨beforeWord, hbefore⟩ :=
    prehandle_prefix_completion M readRule (readParent.derivesRightmost M)
  have hterminal : (characteristicGrammar M).DerivesRightmost
      [symbol.terminal a] ([a].map symbol.terminal) :=
    Relation.ReflTransGen.refl
  have hchildCompletion : (characteristicGrammar M).DerivesRightmost
      childPrefix ((beforeWord ++ [a]).map symbol.terminal) := by
    rw [← hprefix]
    simpa [List.map_append] using hbefore.append_to_terminals hterminal
  obtain ⟨readContext, concreteReadParent⟩ :=
    concreteOperationalSpine_of_activeSpine M readParent hbefore
  obtain ⟨epsilonContext, concreteEpsilonParent⟩ :=
    concreteOperationalSpine_of_activeSpine M epsilonParent hchildCompletion
  exact concreteRead_epsilon_false M concreteReadParent readTransition
    concreteEpsilonParent epsilonTransition epsilonRule hprefix rfl

end

end DPDA_to_LR
