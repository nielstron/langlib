module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Spine
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ActiveHeads

/-!
# Normal forms and uniqueness of list-introducing spine edges

Every occurrence of a characteristic `list` nonterminal in a rule right side
is its final symbol.  Consequently an `Introduces` witness for such a child is
one of four exact forms: a reading move, an epsilon move, a stack split, or the
grammar start rule.  This file turns the history-sensitive parent-head theorem
into equality of the complete introducing edges.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Normal form of an introducing edge whose child is a characteristic
`list` nonterminal. -/
public inductive ListIntroduction (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → Nonterminal M → List T →
    List (symbol T (Nonterminal M)) → Nonterminal M →
    (Nonterminal M × List (symbol T (Nonterminal M))) → Prop
  | read
      {p : List (symbol T (Nonterminal M))} {t : List T}
      {q target next : State M} {a : T} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (hparent : ActiveSpine M p (PDA_to_CFG.N.single q Z target) t)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun q a Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ListIntroduction M (p ++ [symbol.terminal a])
        (PDA_to_CFG.N.list next gamma target) t p
        (PDA_to_CFG.N.single q Z target)
        (PDA_to_CFG.N.single q Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)])
  | epsilon
      {p : List (symbol T (Nonterminal M))} {t : List T}
      {q target next : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (hparent : ActiveSpine M p (PDA_to_CFG.N.single q Z target) t)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun' q Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ListIntroduction M p (PDA_to_CFG.N.list next gamma target) t p
        (PDA_to_CFG.N.single q Z target)
        (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)])
  | split
      {p : List (symbol T (Nonterminal M))} {t : List T}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (hparent : ActiveSpine M p
        (PDA_to_CFG.N.list q (Z :: gamma) target) t)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ListIntroduction M
        (p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)])
        (PDA_to_CFG.N.list middle gamma target) t p
        (PDA_to_CFG.N.list q (Z :: gamma) target)
        (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle gamma target)])
  | start
      {p : List (symbol T (Nonterminal M))} {t : List T}
      {target : State M}
      (hparent : ActiveSpine M p PDA_to_CFG.N.start t)
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      ListIntroduction M p
        (PDA_to_CFG.N.list (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target) t p
        PDA_to_CFG.N.start
        (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)])

private theorem terminal_word_eq_nil_of_derives_nil (M : DPDA Q T S)
    {z : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      ([] : List (symbol T (Nonterminal M)))
      (z.map symbol.terminal)) : z = [] := by
  have heq : z.map (symbol.terminal (N := Nonterminal M)) = [] :=
    CF_grammar.DerivesRightmost.eq_of_map_terminal_source
      (G := characteristicGrammar M) (w := []) h
  exact List.map_eq_nil_iff.mp heq

private theorem decompose_one_nonterminal (M : DPDA Q T S)
    {A B : Nonterminal M}
    {left right : List (symbol T (Nonterminal M))}
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

private theorem decompose_terminal_nonterminal (M : DPDA Q T S)
    {a : T} {A B : Nonterminal M}
    {left right : List (symbol T (Nonterminal M))}
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
      obtain ⟨hleft, hA, hright⟩ := decompose_one_nonterminal M htail
      subst left
      exact ⟨rfl, hA, hright⟩

private theorem decompose_two_nonterminals_list_child (M : DPDA Q T S)
    {A : Nonterminal M} {source middle q target : State M}
    {Z : StackSymbol M} {gamma : List (StackSymbol M)}
    {left right : List (symbol T (Nonterminal M))}
    (hA : IsListSymbol M (symbol.nonterminal A))
    (h : [symbol.nonterminal (PDA_to_CFG.N.single source Z middle),
        symbol.nonterminal (PDA_to_CFG.N.list q gamma target)] =
      left ++ [symbol.nonterminal A] ++ right) :
    left = [symbol.nonterminal (PDA_to_CFG.N.single source Z middle)] ∧
      A = PDA_to_CFG.N.list q gamma target ∧ right = [] := by
  cases left with
  | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have hAB : A = PDA_to_CFG.N.single source Z middle :=
        (symbol.nonterminal.inj h.1).symm
      subst A
      simp [IsListSymbol] at hA
  | cons X left =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      obtain ⟨hleft, hAeq, hright⟩ := decompose_one_nonterminal M htail
      subst left
      exact ⟨rfl, hAeq, hright⟩

/-- Classification of an arbitrary `Introduces` witness whose child is a
characteristic list nonterminal. -/
public theorem listIntroduction_of_introduces (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {child : Nonterminal M} {childSuffix : List T}
    {parentPrefix : List (symbol T (Nonterminal M))}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (hlist : IsListSymbol M (symbol.nonterminal child))
    (h : Introduces M childPrefix child childSuffix
      parentPrefix parent rule) :
    ListIntroduction M childPrefix child childSuffix
      parentPrefix parent rule := by
  rcases h with ⟨alpha, beta, t, z, hparent, hrule, hlhs, hrhs,
    hbeta, hprefix, hsuffix⟩
  rcases characteristicGrammar_rule_shape M hrule with
    hbase | hread | hepsilon | hsplit | hstart
  · rcases hbase with ⟨q, hruleEq⟩
    rw [hruleEq] at hrhs
    simp at hrhs
  · rcases hread with
      ⟨q, target, next, a, Z, gamma, htransition, hruleEq⟩
    rw [hruleEq] at hlhs hrhs
    obtain ⟨halpha, hchild, hbetaNil⟩ :=
      decompose_terminal_nonterminal M hrhs
    subst alpha
    subst child
    subst beta
    have hz : z = [] := terminal_word_eq_nil_of_derives_nil M hbeta
    subst z
    subst parent
    simpa [hprefix, hsuffix, hruleEq] using
      ListIntroduction.read hparent htransition (hruleEq ▸ hrule)
  · rcases hepsilon with
      ⟨q, target, next, Z, gamma, htransition, hruleEq⟩
    rw [hruleEq] at hlhs hrhs
    obtain ⟨halpha, hchild, hbetaNil⟩ :=
      decompose_one_nonterminal M hrhs
    subst alpha
    subst child
    subst beta
    have hz : z = [] := terminal_word_eq_nil_of_derives_nil M hbeta
    subst z
    subst parent
    simpa [hprefix, hsuffix, hruleEq] using
      ListIntroduction.epsilon hparent htransition (hruleEq ▸ hrule)
  · rcases hsplit with
      ⟨q, middle, target, Z, gamma, hlength, hruleEq⟩
    rw [hruleEq] at hlhs hrhs
    obtain ⟨halpha, hchild, hbetaNil⟩ :=
      decompose_two_nonterminals_list_child M hlist hrhs
    subst alpha
    subst child
    subst beta
    have hz : z = [] := terminal_word_eq_nil_of_derives_nil M hbeta
    subst z
    subst parent
    simpa [hprefix, hsuffix, hruleEq] using
      ListIntroduction.split hparent hlength (hruleEq ▸ hrule)
  · rcases hstart with ⟨target, hruleEq⟩
    rw [hruleEq] at hlhs hrhs
    obtain ⟨halpha, hchild, hbetaNil⟩ :=
      decompose_one_nonterminal M hrhs
    subst alpha
    subst child
    subst beta
    have hz : z = [] := terminal_word_eq_nil_of_derives_nil M hbeta
    subst z
    subst parent
    simpa [hprefix, hsuffix, hruleEq] using
      ListIntroduction.start hparent (hruleEq ▸ hrule)

/-! An equality-based view is more convenient when comparing two edges: its
indices remain explicit hypotheses instead of being consumed by dependent
pattern matching. -/

private def IsReadIntroduction (M : DPDA Q T S)
    (childPrefix : List (symbol T (Nonterminal M)))
    (child : Nonterminal M) (childSuffix : List T)
    (parentPrefix : List (symbol T (Nonterminal M)))
    (parent : Nonterminal M)
    (rule : Nonterminal M × List (symbol T (Nonterminal M))) : Prop :=
  ∃ (q target next : State M) (a : T) (Z : StackSymbol M)
      (gamma : List (StackSymbol M)),
    parent = PDA_to_CFG.N.single q Z target ∧
    child = PDA_to_CFG.N.list next gamma target ∧
    childPrefix = parentPrefix ++ [symbol.terminal a] ∧
    rule = (PDA_to_CFG.N.single q Z target,
      [symbol.terminal a,
        symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∧
    ActiveSpine M parentPrefix (PDA_to_CFG.N.single q Z target)
      childSuffix ∧
    (next, gamma) ∈ (emptyStackPDA M).transition_fun q a Z

private def IsEpsilonIntroduction (M : DPDA Q T S)
    (childPrefix : List (symbol T (Nonterminal M)))
    (child : Nonterminal M) (childSuffix : List T)
    (parentPrefix : List (symbol T (Nonterminal M)))
    (parent : Nonterminal M)
    (rule : Nonterminal M × List (symbol T (Nonterminal M))) : Prop :=
  ∃ (q target next : State M) (Z : StackSymbol M)
      (gamma : List (StackSymbol M)),
    parent = PDA_to_CFG.N.single q Z target ∧
    child = PDA_to_CFG.N.list next gamma target ∧
    childPrefix = parentPrefix ∧
    rule = (PDA_to_CFG.N.single q Z target,
      [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∧
    ActiveSpine M parentPrefix (PDA_to_CFG.N.single q Z target)
      childSuffix ∧
    (next, gamma) ∈ (emptyStackPDA M).transition_fun' q Z

private def IsSplitIntroduction (M : DPDA Q T S)
    (childPrefix : List (symbol T (Nonterminal M)))
    (child : Nonterminal M) (childSuffix : List T)
    (parentPrefix : List (symbol T (Nonterminal M)))
    (parent : Nonterminal M)
    (rule : Nonterminal M × List (symbol T (Nonterminal M))) : Prop :=
  ∃ (q middle target : State M) (Z : StackSymbol M)
      (gamma : List (StackSymbol M)),
    parent = PDA_to_CFG.N.list q (Z :: gamma) target ∧
    child = PDA_to_CFG.N.list middle gamma target ∧
    childPrefix = parentPrefix ++
      [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)] ∧
    rule = (PDA_to_CFG.N.list q (Z :: gamma) target,
      [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
        symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∧
    ActiveSpine M parentPrefix
      (PDA_to_CFG.N.list q (Z :: gamma) target) childSuffix

private def IsStartIntroduction (M : DPDA Q T S)
    (childPrefix : List (symbol T (Nonterminal M)))
    (child : Nonterminal M) (childSuffix : List T)
    (parentPrefix : List (symbol T (Nonterminal M)))
    (parent : Nonterminal M)
    (rule : Nonterminal M × List (symbol T (Nonterminal M))) : Prop :=
  ∃ target : State M,
    parent = PDA_to_CFG.N.start ∧
    child = PDA_to_CFG.N.list (emptyStackPDA M).initial_state
      [(emptyStackPDA M).start_symbol] target ∧
    childPrefix = parentPrefix ∧
    rule = (PDA_to_CFG.N.start,
      [symbol.nonterminal (PDA_to_CFG.N.list
        (emptyStackPDA M).initial_state
        [(emptyStackPDA M).start_symbol] target)]) ∧
    ActiveSpine M parentPrefix PDA_to_CFG.N.start childSuffix

private theorem listIntroduction_view_of_introduces (M : DPDA Q T S)
    {childPrefix : List (symbol T (Nonterminal M))}
    {child : Nonterminal M} {childSuffix : List T}
    {parentPrefix : List (symbol T (Nonterminal M))}
    {parent : Nonterminal M}
    {rule : Nonterminal M × List (symbol T (Nonterminal M))}
    (hlist : IsListSymbol M (symbol.nonterminal child))
    (h : Introduces M childPrefix child childSuffix
      parentPrefix parent rule) :
    IsReadIntroduction M childPrefix child childSuffix
        parentPrefix parent rule ∨
      IsEpsilonIntroduction M childPrefix child childSuffix
        parentPrefix parent rule ∨
      IsSplitIntroduction M childPrefix child childSuffix
        parentPrefix parent rule ∨
      IsStartIntroduction M childPrefix child childSuffix
        parentPrefix parent rule := by
  have hv := listIntroduction_of_introduces M hlist h
  cases hv with
  | read hparent htransition hrule =>
      left
      exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl,
        hparent, htransition⟩
  | epsilon hparent htransition hrule =>
      right
      left
      exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl,
        hparent, htransition⟩
  | split hparent hlength hrule =>
      right
      right
      left
      exact ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, hparent⟩
  | start hparent hrule =>
      right
      right
      right
      exact ⟨_, rfl, rfl, rfl, rfl, hparent⟩

/-! ## From head uniqueness to complete edge uniqueness -/

/-- A reading and an epsilon transition of the normalized empty-stack PDA
cannot have the same output.  In a simulation state this is inherited from
the underlying DPDA; the only additional epsilon move enters the drain state,
which no reading move can enter. -/
public theorem emptyStack_read_epsilon_same_output_false
    (M : DPDA Q T S) {q p : State M} {a : T} {Z : StackSymbol M}
    {gamma : List (StackSymbol M)}
    (hread : (p, gamma) ∈ (emptyStackPDA M).transition_fun q a Z)
    (hepsilon : (p, gamma) ∈
      (emptyStackPDA M).transition_fun' q Z) : False := by
  classical
  cases q with
  | inr i =>
      simp [emptyStackPDA, PDA_FS_to_ES_pda,
        PDA_FS_to_ES_trans] at hread
  | inl q =>
      cases Z with
      | none =>
          simp [emptyStackPDA, PDA_FS_to_ES_pda,
            PDA_FS_to_ES_trans] at hread
      | some Z =>
          change (p, gamma) ∈
              (fun out : (Q × Bool) × List S =>
                (Sum.inl out.1, out.2.map some)) ''
                M.firstFinal.toPDA.transition_fun q a Z at hread
          change (p, gamma) ∈
              ((fun out : (Q × Bool) × List S =>
                (Sum.inl out.1, out.2.map some)) ''
                  M.firstFinal.toPDA.transition_fun' q Z ∪
                if q ∈ M.firstFinal.toPDA.final_states then
                  {(Sum.inr 1, [])} else ∅) at hepsilon
          rcases hread with ⟨⟨pRead, gammaRead⟩, hread, houtRead⟩
          rcases hepsilon with hsimulation | hdrain
          · rcases hsimulation with
              ⟨⟨pEpsilon, gammaEpsilon⟩, hepsilon, houtEpsilon⟩
            have hsRead : M.firstFinal.toPDA.Reaches₁
                ⟨q, [a], [Z]⟩ ⟨pRead, [], gammaRead⟩ := by
              exact Or.inl ⟨pRead, gammaRead, hread, by simp⟩
            have hsEpsilon : M.firstFinal.toPDA.Reaches₁
                ⟨q, [a], [Z]⟩ ⟨pEpsilon, [a], gammaEpsilon⟩ := by
              exact Or.inr ⟨pEpsilon, gammaEpsilon, hepsilon, by simp⟩
            have heq := M.firstFinal.toPDA_step_deterministic
              hsRead hsEpsilon
            have hinput := congrArg PDA.conf.input heq
            simp at hinput
          · split_ifs at hdrain with hfinal
            · have hout :
                  ((Sum.inl pRead : State M), gammaRead.map some) =
                    ((Sum.inr (1 : Fin 2) : State M), []) := by
                simpa only [Prod.eta] using houtRead.trans hdrain
              cases congrArg Prod.fst hout
            · simp at hdrain

/-- The history-sensitive uniqueness of the parent head determines the whole
list-introducing edge. -/
public theorem introducingEdgesUnique_of_activeHeadUnique
    (M : DPDA Q T S) (hhead : ActiveHeadUnique M) :
    IntroducingEdgesUnique M := by
  intro childPrefix child suffix₁ suffix₂
    parentPrefix₁ parentPrefix₂ parent₁ parent₂ rule₁ rule₂
    hlist h₁ h₂ hlook
  have hdescriptor := hhead childPrefix child suffix₁ suffix₂
    parentPrefix₁ parentPrefix₂ parent₁ parent₂ rule₁ rule₂
    hlist h₁ h₂ hlook
  have hv₁ := listIntroduction_view_of_introduces M hlist h₁
  have hv₂ := listIntroduction_view_of_introduces M hlist h₂
  rcases hv₁ with hread₁ | hepsilon₁ | hsplit₁ | hstart₁ <;>
    rcases hv₂ with hread₂ | hepsilon₂ | hsplit₂ | hstart₂
  · rcases hread₁ with
      ⟨q₁, target₁, next₁, a₁, Z₁, gamma₁,
        hparent₁, hchild₁, hprefix₁, hrule₁, _, htransition₁⟩
    rcases hread₂ with
      ⟨q₂, target₂, next₂, a₂, Z₂, gamma₂,
        hparent₂, hchild₂, hprefix₂, hrule₂, _, htransition₂⟩
    have hchild := hchild₁.symm.trans hchild₂
    injection hchild with hnext hgamma htarget
    have hprefix := hprefix₁.symm.trans hprefix₂
    obtain ⟨hparentPrefix, haSymbol⟩ :=
      append_singleton_injective hprefix
    have ha : a₁ = a₂ := symbol.terminal.inj haSymbol
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
    obtain ⟨hq, hZ⟩ := hdescriptor
    subst q₂
    subst Z₂
    subst next₂
    subst gamma₂
    subst target₂
    subst a₂
    exact ⟨hparentPrefix, hrule₁.trans hrule₂.symm⟩
  · rcases hread₁ with
      ⟨q₁, target₁, next₁, a₁, Z₁, gamma₁,
        hparent₁, hchild₁, _, _, _, htransition₁⟩
    rcases hepsilon₂ with
      ⟨q₂, target₂, next₂, Z₂, gamma₂,
        hparent₂, hchild₂, _, _, _, htransition₂⟩
    have hchild := hchild₁.symm.trans hchild₂
    injection hchild with hnext hgamma htarget
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
    obtain ⟨hq, hZ⟩ := hdescriptor
    subst q₂
    subst Z₂
    subst next₂
    subst gamma₂
    subst target₂
    exact (emptyStack_read_epsilon_same_output_false M
      htransition₁ htransition₂).elim
  · rcases hread₁ with
      ⟨q₁, target₁, next₁, a₁, Z₁, gamma₁,
        hparent₁, hchild₁, _, _, _, htransition₁⟩
    rcases hsplit₂ with
      ⟨q₂, middle₂, target₂, Z₂, gamma₂,
        hparent₂, hchild₂, _, _, _⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hread₁ with
      ⟨q₁, target₁, next₁, a₁, Z₁, gamma₁,
        hparent₁, hchild₁, _, _, _, htransition₁⟩
    rcases hstart₂ with
      ⟨target₂, hparent₂, hchild₂, _, _, _⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hepsilon₁ with
      ⟨q₁, target₁, next₁, Z₁, gamma₁,
        hparent₁, hchild₁, _, _, _, htransition₁⟩
    rcases hread₂ with
      ⟨q₂, target₂, next₂, a₂, Z₂, gamma₂,
        hparent₂, hchild₂, _, _, _, htransition₂⟩
    have hchild := hchild₁.symm.trans hchild₂
    injection hchild with hnext hgamma htarget
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
    obtain ⟨hq, hZ⟩ := hdescriptor
    subst q₂
    subst Z₂
    subst next₂
    subst gamma₂
    subst target₂
    exact (emptyStack_read_epsilon_same_output_false M
      htransition₂ htransition₁).elim
  · rcases hepsilon₁ with
      ⟨q₁, target₁, next₁, Z₁, gamma₁,
        hparent₁, hchild₁, hprefix₁, hrule₁, _, htransition₁⟩
    rcases hepsilon₂ with
      ⟨q₂, target₂, next₂, Z₂, gamma₂,
        hparent₂, hchild₂, hprefix₂, hrule₂, _, htransition₂⟩
    have hchild := hchild₁.symm.trans hchild₂
    injection hchild with hnext hgamma htarget
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
    obtain ⟨hq, hZ⟩ := hdescriptor
    subst q₂
    subst Z₂
    subst next₂
    subst gamma₂
    subst target₂
    exact ⟨hprefix₁.symm.trans hprefix₂,
      hrule₁.trans hrule₂.symm⟩
  · rcases hepsilon₁ with
      ⟨q₁, target₁, next₁, Z₁, gamma₁,
        hparent₁, hchild₁, _, _, _, htransition₁⟩
    rcases hsplit₂ with
      ⟨q₂, middle₂, target₂, Z₂, gamma₂,
        hparent₂, hchild₂, _, _, _⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hepsilon₁ with
      ⟨q₁, target₁, next₁, Z₁, gamma₁,
        hparent₁, hchild₁, _, _, _, htransition₁⟩
    rcases hstart₂ with
      ⟨target₂, hparent₂, hchild₂, _, _, _⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hsplit₁ with
      ⟨q₁, middle₁, target₁, Z₁, gamma₁,
        hparent₁, hchild₁, _, _, _⟩
    rcases hread₂ with
      ⟨q₂, target₂, next₂, a₂, Z₂, gamma₂,
        hparent₂, hchild₂, _, _, _, htransition₂⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hsplit₁ with
      ⟨q₁, middle₁, target₁, Z₁, gamma₁,
        hparent₁, hchild₁, _, _, _⟩
    rcases hepsilon₂ with
      ⟨q₂, target₂, next₂, Z₂, gamma₂,
        hparent₂, hchild₂, _, _, _, htransition₂⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hsplit₁ with
      ⟨q₁, middle₁, target₁, Z₁, gamma₁,
        hparent₁, hchild₁, hprefix₁, hrule₁, _⟩
    rcases hsplit₂ with
      ⟨q₂, middle₂, target₂, Z₂, gamma₂,
        hparent₂, hchild₂, hprefix₂, hrule₂, _⟩
    have hchild := hchild₁.symm.trans hchild₂
    injection hchild with hmiddle hgamma htarget
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
    obtain ⟨hq, hZ⟩ := hdescriptor
    subst q₂
    subst Z₂
    subst middle₂
    subst gamma₂
    subst target₂
    have hprefix := hprefix₁.symm.trans hprefix₂
    obtain ⟨hparentPrefix, _⟩ := append_singleton_injective hprefix
    exact ⟨hparentPrefix, hrule₁.trans hrule₂.symm⟩
  · rcases hsplit₁ with
      ⟨q₁, middle₁, target₁, Z₁, gamma₁,
        hparent₁, hchild₁, _, _, _⟩
    rcases hstart₂ with
      ⟨target₂, hparent₂, hchild₂, _, _, _⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hstart₁ with
      ⟨target₁, hparent₁, hchild₁, _, _, _⟩
    rcases hread₂ with
      ⟨q₂, target₂, next₂, a₂, Z₂, gamma₂,
        hparent₂, hchild₂, _, _, _, htransition₂⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hstart₁ with
      ⟨target₁, hparent₁, hchild₁, _, _, _⟩
    rcases hepsilon₂ with
      ⟨q₂, target₂, next₂, Z₂, gamma₂,
        hparent₂, hchild₂, _, _, _, htransition₂⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hstart₁ with
      ⟨target₁, hparent₁, hchild₁, _, _, _⟩
    rcases hsplit₂ with
      ⟨q₂, middle₂, target₂, Z₂, gamma₂,
        hparent₂, hchild₂, _, _, _⟩
    rw [hparent₁, hparent₂] at hdescriptor
    simp [activeDescriptor] at hdescriptor
  · rcases hstart₁ with
      ⟨target₁, hparent₁, hchild₁, hprefix₁, hrule₁, _⟩
    rcases hstart₂ with
      ⟨target₂, hparent₂, hchild₂, hprefix₂, hrule₂, _⟩
    have hchild := hchild₁.symm.trans hchild₂
    injection hchild with htarget
    subst target₂
    exact ⟨hprefix₁.symm.trans hprefix₂,
      hrule₁.trans hrule₂.symm⟩

end

end DPDA_to_LR
