module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Core
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.EmptyReturnSynchronization
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Spine

/-!
# Empty-list returns on an active characteristic spine

An empty-list rule removes its active marker completely, so the final-list
cancellation used for nonbase productions is unavailable.  This file isolates
the corresponding return problem and records the exact terminal displacement
forced by equality of the two post-return forms.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- If two prefixes become equal after terminal suffixes are appended, one
prefix extends the other by a terminal word, and the same word is transferred
between the suffixes. -/
public theorem append_terminals_eq_cases
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
    have hy : y' = y := by
      exact (List.map_injective_iff.mpr fun _ _ h =>
        symbol.terminal.inj h) hy'
    subst y'
    left
    exact ⟨z, by simpa [has] using hp, hs₂⟩
  · have hs' : y.map (symbol.terminal (N := N)) =
        bs ++ s₂.map symbol.terminal := hs
    rw [List.map_eq_append_iff] at hs'
    obtain ⟨z, s₂', hy, hbs, hs₂'⟩ := hs'
    have hs₂eq : s₂' = s₂ := by
      exact (List.map_injective_iff.mpr fun _ _ h =>
        symbol.terminal.inj h) hs₂'
    subst s₂'
    right
    exact ⟨z, by simpa [hbs] using hp, hy⟩

/-- A displayed final nonterminal followed only by terminals is a unique
right marker, even when arbitrary nonterminals occur in its prefix. -/
public theorem cancel_final_nonterminal
    {N : Type} {p₁ p₂ : List (symbol T N)} {A₁ A₂ : N}
    {s₁ s₂ : List T}
    (h : p₂ ++ [symbol.nonterminal A₂] ++ s₂.map symbol.terminal =
      p₁ ++ [symbol.nonterminal A₁] ++ s₁.map symbol.terminal) :
    p₂ = p₁ ∧ A₂ = A₁ ∧ s₂ = s₁ := by
  have hrev := congrArg List.reverse h
  have hrev' :
      s₂.reverse.map symbol.terminal ++
          symbol.nonterminal A₂ :: p₂.reverse =
        s₁.reverse.map symbol.terminal ++
          symbol.nonterminal A₁ :: p₁.reverse := by
    simpa [List.reverse_append, List.map_reverse,
      List.append_assoc] using hrev
  let IsNT : symbol T N → Prop
    | symbol.terminal _ => False
    | symbol.nonterminal _ => True
  have hterm₁ : ∀ X ∈ s₁.reverse.map (symbol.terminal (N := N)),
      ¬ IsNT X := by
    intro X hX
    simp only [List.mem_map] at hX
    obtain ⟨a, _, rfl⟩ := hX
    simp [IsNT]
  have hterm₂ : ∀ X ∈ s₂.reverse.map (symbol.terminal (N := N)),
      ¬ IsNT X := by
    intro X hX
    simp only [List.mem_map] at hX
    obtain ⟨a, _, rfl⟩ := hX
    simp [IsNT]
  have hm₁ : IsNT (symbol.nonterminal (T := T) A₁) := by simp [IsNT]
  have hm₂ : IsNT (symbol.nonterminal (T := T) A₂) := by simp [IsNT]
  obtain ⟨hsrev, hmarker, hprev⟩ := cancel_unique_marker
    hterm₁ hterm₂ hm₁ hm₂ hrev'
  have hs : s₂ = s₁ := by
    have hmap : s₂.reverse.map (symbol.terminal (N := N)) =
        s₁.reverse.map symbol.terminal := hsrev
    have hreverse : s₂.reverse = s₁.reverse :=
      (List.map_injective_iff.mpr fun _ _ heq =>
        symbol.terminal.inj heq) hmap
    exact List.reverse_injective hreverse
  exact ⟨List.reverse_injective hprev,
    symbol.nonterminal.inj hmarker, hs⟩

/-- Spine-native form of the remaining empty-return uniqueness property. -/
@[expose]
public def EmptyListSpinesUnique (M : DPDA Q T S) : Prop :=
  ∀ (q₁ q₂ : State M),
    (PDA_to_CFG.N.list q₁ [] q₁,
        ([] : List (symbol T (Nonterminal M)))) ∈
      (characteristicGrammar M).rules →
    (PDA_to_CFG.N.list q₂ [] q₂,
        ([] : List (symbol T (Nonterminal M)))) ∈
      (characteristicGrammar M).rules →
    ∀ (p₁ p₂ : List (symbol T (Nonterminal M)))
        (s₁ s₂ y : List T),
      ActiveSpine M p₁ (PDA_to_CFG.N.list q₁ [] q₁) s₁ →
      ActiveSpine M p₂ (PDA_to_CFG.N.list q₂ [] q₂) s₂ →
      p₂ ++ s₂.map symbol.terminal =
        p₁ ++ y.map symbol.terminal →
      s₁.take 1 = y.take 1 →
      p₁ = p₂ ∧ q₁ = q₂

/-- A spine-level empty-return theorem supplies the exact semantic property
expected by the LR-core reduction. -/
public theorem emptyListHandlesUnique_of_spines (M : DPDA Q T S)
    (h : EmptyListSpinesUnique M) : EmptyListHandlesUnique M := by
  intro q₁ q₂ hr₁ hr₂ p₁ p₂ s₁ s₂ y hd₁ hd₂ hform hlook
  exact h q₁ q₂ hr₁ hr₂ p₁ p₂ s₁ s₂ y
    (activeSpine_of_derivesRightmost M hd₁)
    (activeSpine_of_derivesRightmost M hd₂) hform hlook

/-! ## The three possible incoming edges of an empty-list occurrence -/

/-- A normalized top spine edge whose child is `list q [] q`. -/
public inductive EmptyBaseEdge (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → State M → List T → Prop
  | read
      {p : List (symbol T (Nonterminal M))} {suffix : List T}
      {source : State M} {a : T} {Z : StackSymbol M} {q : State M}
      (hparent : ActiveSpine M p
        (PDA_to_CFG.N.single source Z q) suffix)
      (htransition : (q, []) ∈
        (emptyStackPDA M).transition_fun source a Z)
      (hrule : (PDA_to_CFG.N.single source Z q,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      EmptyBaseEdge M (p ++ [symbol.terminal a]) q suffix
  | epsilon
      {p : List (symbol T (Nonterminal M))} {suffix : List T}
      {source : State M} {Z : StackSymbol M} {q : State M}
      (hparent : ActiveSpine M p
        (PDA_to_CFG.N.single source Z q) suffix)
      (htransition : (q, []) ∈
        (emptyStackPDA M).transition_fun' source Z)
      (hrule : (PDA_to_CFG.N.single source Z q,
          [symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      EmptyBaseEdge M p q suffix
  | split
      {p : List (symbol T (Nonterminal M))} {suffix : List T}
      {source : State M} {Z : StackSymbol M} {q : State M}
      (hparent : ActiveSpine M p
        (PDA_to_CFG.N.list source [Z] q) suffix)
      (hlength : [Z].length ≤ PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list source [Z] q,
          [symbol.nonterminal (PDA_to_CFG.N.single source Z q),
            symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      EmptyBaseEdge M
        (p ++ [symbol.nonterminal (PDA_to_CFG.N.single source Z q)])
        q suffix

/-- An empty return generated by an actual PDA transition, rather than by
the structural empty right child of a stack split. -/
public inductive EmptyTransitionEdge (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → State M → List T → Prop
  | read
      {p : List (symbol T (Nonterminal M))} {suffix : List T}
      {source : State M} {a : T} {Z : StackSymbol M} {q : State M}
      (hparent : ActiveSpine M p
        (PDA_to_CFG.N.single source Z q) suffix)
      (htransition : (q, []) ∈
        (emptyStackPDA M).transition_fun source a Z)
      (hrule : (PDA_to_CFG.N.single source Z q,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      EmptyTransitionEdge M (p ++ [symbol.terminal a]) q suffix
  | epsilon
      {p : List (symbol T (Nonterminal M))} {suffix : List T}
      {source : State M} {Z : StackSymbol M} {q : State M}
      (hparent : ActiveSpine M p
        (PDA_to_CFG.N.single source Z q) suffix)
      (htransition : (q, []) ∈
        (emptyStackPDA M).transition_fun' source Z)
      (hrule : (PDA_to_CFG.N.single source Z q,
          [symbol.nonterminal (PDA_to_CFG.N.list q [] q)]) ∈
        (characteristicGrammar M).rules) :
      EmptyTransitionEdge M p q suffix

/-- Forgetting the transition-only tag gives the corresponding normalized
empty edge. -/
public theorem EmptyTransitionEdge.baseEdge (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix : List T} (h : EmptyTransitionEdge M p q suffix) :
    EmptyBaseEdge M p q suffix := by
  cases h with
  | read hparent htransition hrule =>
      exact EmptyBaseEdge.read hparent htransition hrule
  | epsilon hparent htransition hrule =>
      exact EmptyBaseEdge.epsilon hparent htransition hrule

/-- A normalized empty edge which is not transition-generated has the exact
visible-prefix shape of the right child of a split. -/
public theorem EmptyBaseEdge.split_shape_of_not_transition
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M} {suffix : List T}
    (h : EmptyBaseEdge M p q suffix)
    (hnot : ¬ EmptyTransitionEdge M p q suffix) :
    ∃ (base : List (symbol T (Nonterminal M)))
        (source : State M) (Z : StackSymbol M),
      p = base ++
        [symbol.nonterminal (PDA_to_CFG.N.single source Z q)] := by
  cases h with
  | read hparent htransition hrule =>
      exact False.elim (hnot (.read hparent htransition hrule))
  | epsilon hparent htransition hrule =>
      exact False.elim (hnot (.epsilon hparent htransition hrule))
  | @split base suffix source Z q hparent hlength hrule =>
      exact ⟨base, source, Z, rfl⟩

/-- The only possible incoming spine edge of a characteristic `single`
nonterminal.  Its parent is the corresponding nonempty `list` node, and the
terminal word stored in the child's suffix is exactly the completed right
sibling of that split. -/
public inductive SingleBaseEdge (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → State M → StackSymbol M →
      State M → List T → Prop
  | split
      {p : List (symbol T (Nonterminal M))} {parentSuffix z : List T}
      {source middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (hparent : ActiveSpine M p
        (PDA_to_CFG.N.list source (Z :: gamma) target) parentSuffix)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list source (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single source Z middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hright : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal)) :
      SingleBaseEdge M p source Z middle (z ++ parentSuffix)

private theorem empty_terminal_yield (M : DPDA Q T S) {z : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [] (z.map symbol.terminal)) : z = [] := by
  have h' : (characteristicGrammar M).DerivesRightmost
      (([] : List T).map symbol.terminal)
      (z.map symbol.terminal) := by simpa using h
  have heq := h'.eq_of_map_terminal_source
  have hmap : z.map (symbol.terminal (N := Nonterminal M)) = [] := by
    simpa using heq
  exact List.map_eq_nil_iff.mp hmap

private theorem one_list_occurrence (M : DPDA Q T S)
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

private theorem terminal_list_occurrence (M : DPDA Q T S)
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
      obtain ⟨hleft, hA, hright⟩ := one_list_occurrence M htail
      subst left
      exact ⟨rfl, hA, hright⟩

private theorem two_nonterminal_list_occurrence (M : DPDA Q T S)
    {A B C : Nonterminal M}
    {left right : List (symbol T (Nonterminal M))}
    (h : [symbol.nonterminal B, symbol.nonterminal C] =
      left ++ [symbol.nonterminal A] ++ right) :
    (left = [] ∧ A = B ∧ right = [symbol.nonterminal C]) ∨
    (left = [symbol.nonterminal B] ∧ A = C ∧ right = []) := by
  cases left with
  | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact Or.inl ⟨rfl, (symbol.nonterminal.inj h.1).symm, h.2.symm⟩
  | cons X left =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      obtain ⟨hleft, hA, hright⟩ := one_list_occurrence M htail
      subst left
      exact Or.inr ⟨rfl, hA, hright⟩

/-- Every reachable active `single` occurrence is the left child of one
split edge. -/
public theorem singleBaseEdge_of_activeSpine (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {source target : State M} {Z : StackSymbol M} {suffix : List T}
    (h : ActiveSpine M p (PDA_to_CFG.N.single source Z target) suffix) :
    SingleBaseEdge M p source Z target suffix := by
  cases h with
  | @descend p₀ alpha beta parent child t z r hparent hr hlhs hrhs hbeta =>
      rcases characteristicGrammar_rule_shape M hr with
          hbase | hread | hepsilon | hsplit | hstart
      · rcases hbase with ⟨state, hrule⟩
        rw [hrule] at hrhs
        simp at hrhs
      · rcases hread with
          ⟨q, returnState, next, a, top, gamma, htransition, hrule⟩
        rw [hrule] at hrhs
        obtain ⟨_, hchild, _⟩ := terminal_list_occurrence M hrhs
        cases hchild
      · rcases hepsilon with
          ⟨q, returnState, next, top, gamma, htransition, hrule⟩
        rw [hrule] at hrhs
        obtain ⟨_, hchild, _⟩ := one_list_occurrence M hrhs
        cases hchild
      · rcases hsplit with
          ⟨q, middle, returnState, top, gamma, hlength, hrule⟩
        rw [hrule] at hlhs hrhs
        rw [← hlhs] at hparent
        rcases two_nonterminal_list_occurrence M hrhs with
            hleft | hright
        · rcases hleft with ⟨halpha, hchild, hbeta⟩
          have hN : PDA_to_CFG.N.single source Z target =
              PDA_to_CFG.N.single q top middle := hchild
          injection hN with hsource hZ htarget
          subst q
          subst top
          subst middle
          subst alpha
          subst beta
          simpa using SingleBaseEdge.split hparent hlength
            (hrule ▸ hr) hbeta
        · rcases hright with ⟨_, hchild, _⟩
          cases hchild
      · rcases hstart with ⟨returnState, hrule⟩
        rw [hrule] at hrhs
        obtain ⟨_, hchild, _⟩ := one_list_occurrence M hrhs
        cases hchild

/-- Every active empty-list occurrence was introduced by exactly one of the
three normalized edge forms above. -/
public theorem emptyBaseEdge_of_activeSpine (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M} {suffix : List T}
    (h : ActiveSpine M p (PDA_to_CFG.N.list q [] q) suffix) :
    EmptyBaseEdge M p q suffix := by
  cases h with
  | @descend p₀ alpha beta parent child t z r hparent hr hlhs hrhs hbeta =>
      rcases characteristicGrammar_rule_shape M hr with
          hbase | hread | hepsilon | hsplit | hstart
      · rcases hbase with ⟨state, hrule⟩
        rw [hrule] at hrhs
        simp at hrhs
      · rcases hread with
          ⟨source, target, next, a, Z, gamma, htransition, hrule⟩
        rw [hrule] at hlhs hrhs
        rw [← hlhs] at hparent
        obtain ⟨halpha, hchild, hbetaNil⟩ :=
          terminal_list_occurrence M hrhs
        have hN : PDA_to_CFG.N.list q [] q =
            PDA_to_CFG.N.list next gamma target := hchild
        injection hN with hnext hgamma htarget
        subst next
        subst gamma
        subst target
        subst alpha
        subst beta
        have hz := empty_terminal_yield M hbeta
        subst z
        simpa using EmptyBaseEdge.read hparent htransition (hrule ▸ hr)
      · rcases hepsilon with
          ⟨source, target, next, Z, gamma, htransition, hrule⟩
        rw [hrule] at hlhs hrhs
        rw [← hlhs] at hparent
        obtain ⟨halpha, hchild, hbetaNil⟩ := one_list_occurrence M hrhs
        have hN : PDA_to_CFG.N.list q [] q =
            PDA_to_CFG.N.list next gamma target := hchild
        injection hN with hnext hgamma htarget
        subst next
        subst gamma
        subst target
        subst alpha
        subst beta
        have hz := empty_terminal_yield M hbeta
        subst z
        simpa using EmptyBaseEdge.epsilon hparent htransition (hrule ▸ hr)
      · rcases hsplit with
          ⟨source, middle, target, Z, gamma, hlength, hrule⟩
        rw [hrule] at hlhs hrhs
        rw [← hlhs] at hparent
        rcases two_nonterminal_list_occurrence M hrhs with
            hleft | hright
        · rcases hleft with ⟨_, hbad, _⟩
          cases hbad
        · rcases hright with ⟨halpha, hchild, hbetaNil⟩
          have hN : PDA_to_CFG.N.list q [] q =
              PDA_to_CFG.N.list middle gamma target := hchild
          injection hN with hmiddle hgamma htarget
          subst middle
          subst gamma
          subst target
          subst alpha
          subst beta
          have hz := empty_terminal_yield M hbeta
          subst z
          simpa using EmptyBaseEdge.split hparent hlength (hrule ▸ hr)
      · rcases hstart with ⟨target, hrule⟩
        rw [hrule] at hlhs hrhs
        obtain ⟨_, hchild, _⟩ := one_list_occurrence M hrhs
        cases hchild

/-! ## Operational factorization of an empty return -/

/-- Completing the visible prefix of an empty-list edge exposes one complete
net-pop segment.  The segment starts just before the edge's parent, removes
its displayed stack symbol, and ends at the empty-list state with the saved
stack context restored. -/
public def EmptyReturnRun (M : DPDA Q T S)
    (preWord suffix : List T) (q : State M) : Prop :=
  ∃ (beforeWord segmentWord : List T) (source : State M)
      (top : StackSymbol M) (context : List (StackSymbol M))
      (final : State M),
    preWord = beforeWord ++ segmentWord ∧
    (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, beforeWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, [], top :: context⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨source, segmentWord, top :: context⟩
      ⟨q, [], context⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨q, suffix, context⟩ ⟨final, [], []⟩

/-- Transition-generated empty returns have the stronger factorization in
which the net-pop segment consists of exactly one PDA step. -/
public def EmptyTransitionRun (M : DPDA Q T S)
    (preWord suffix : List T) (q : State M) : Prop :=
  ∃ (beforeWord segmentWord : List T) (source : State M)
      (top : StackSymbol M) (context : List (StackSymbol M))
      (final : State M),
    preWord = beforeWord ++ segmentWord ∧
    (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, beforeWord,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨source, [], top :: context⟩ ∧
    (emptyStackPDA M).Reaches₁
      ⟨source, segmentWord, top :: context⟩
      ⟨q, [], context⟩ ∧
    (emptyStackPDA M).Reaches
      ⟨q, suffix, context⟩ ⟨final, [], []⟩

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

/-- Every normalized empty edge has an exact useful net-pop run after any
chosen terminal completion of its visible prefix. -/
public theorem EmptyBaseEdge.returnRun (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M} {suffix preWord : List T}
    (edge : EmptyBaseEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost
      p (preWord.map symbol.terminal)) :
    EmptyReturnRun M preWord suffix q := by
  cases edge with
  | @read base suffix source a Z q hparent htransition hrule =>
      obtain ⟨beforeWord, segmentWord, hpre, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      have hsegmentWord : segmentWord = [a] :=
        terminal_completion_singleton M hsegment
      subst segmentWord
      have hfocused := focused_of_prehandle M
        (hparent.derivesRightmost M) hbase
      cases hfocused with
      | single _ _ _ _ _ context final prefixPath continuation =>
          refine ⟨beforeWord, [a], source, Z, context, final,
            hpre, prefixPath, ?_, continuation⟩
          apply Relation.ReflTransGen.single
          exact Or.inl ⟨q, [], htransition, by simp⟩
  | @epsilon base suffix source Z q hparent htransition hrule =>
      have hfocused := focused_of_prehandle M
        (hparent.derivesRightmost M) hp
      cases hfocused with
      | single _ _ _ _ _ context final prefixPath continuation =>
          refine ⟨preWord, [], source, Z, context, final, by simp,
            prefixPath, ?_, continuation⟩
          apply Relation.ReflTransGen.single
          exact ⟨q, [], htransition, by simp⟩
  | @split base suffix source Z q hparent hlength hrule =>
      obtain ⟨beforeWord, segmentWord, hpre, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      have hfocused := focused_of_prehandle M
        (hparent.derivesRightmost M) hbase
      cases hfocused with
      | list _ _ _ _ _ context final prefixPath continuation =>
          have hreturn :=
            (reaches_of_characteristic_derives_single M hsegment).append_stack
              context
          refine ⟨beforeWord, segmentWord, source, Z, context, final,
            hpre, ?_, ?_, continuation⟩
          · simpa using prefixPath
          · simpa using hreturn

/-- The one-step specialization of `EmptyBaseEdge.returnRun` for an actual
read or epsilon transition edge. -/
public theorem EmptyTransitionEdge.transitionRun (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M} {suffix preWord : List T}
    (edge : EmptyTransitionEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost
      p (preWord.map symbol.terminal)) :
    EmptyTransitionRun M preWord suffix q := by
  cases edge with
  | @read base suffix source a Z q hparent htransition hrule =>
      obtain ⟨beforeWord, segmentWord, hpre, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      have hsegmentWord : segmentWord = [a] :=
        terminal_completion_singleton M hsegment
      subst segmentWord
      have hfocused := focused_of_prehandle M
        (hparent.derivesRightmost M) hbase
      cases hfocused with
      | single _ _ _ _ _ context final prefixPath continuation =>
          refine ⟨beforeWord, [a], source, Z, context, final,
            hpre, prefixPath, ?_, continuation⟩
          exact Or.inl ⟨q, [], htransition, by simp⟩
  | @epsilon base suffix source Z q hparent htransition hrule =>
      have hfocused := focused_of_prehandle M
        (hparent.derivesRightmost M) hp
      cases hfocused with
      | single _ _ _ _ _ context final prefixPath continuation =>
          refine ⟨preWord, [], source, Z, context, final, by simp,
            prefixPath, ?_, continuation⟩
          exact ⟨q, [], htransition, by simp⟩

/-- Every visible prefix of an empty edge has a terminal completion.  In the
split case this explicitly completes the exposed left `single`; the retained
split rule guarantees that this nonterminal is productive. -/
public theorem EmptyBaseEdge.prefixCompletion (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M} {suffix : List T}
    (edge : EmptyBaseEdge M p q suffix) :
    ∃ preWord : List T,
      (characteristicGrammar M).DerivesRightmost
        p (preWord.map symbol.terminal) := by
  cases edge with
  | @read base suffix source a Z q hparent htransition hrule =>
      obtain ⟨beforeWord, hbefore⟩ :=
        prehandle_prefix_completion M hrule (hparent.derivesRightmost M)
      refine ⟨beforeWord ++ [a], ?_⟩
      have ha : (characteristicGrammar M).DerivesRightmost
          [symbol.terminal a]
          ([a].map symbol.terminal) := Relation.ReflTransGen.refl
      simpa [List.map_append] using hbefore.append_to_terminals ha
  | @epsilon base suffix source Z q hparent htransition hrule =>
      exact prehandle_prefix_completion M hrule
        (hparent.derivesRightmost M)
  | @split base suffix source Z q hparent hlength hrule =>
      obtain ⟨beforeWord, hbefore⟩ :=
        prehandle_prefix_completion M hrule (hparent.derivesRightmost M)
      have hproductive : productive (characteristicGrammar M)
          (PDA_to_CFG.N.single source Z q) :=
        characteristic_rule_rhs_productive_reduced M hrule (by simp)
      obtain ⟨segmentWord, hsegment⟩ := hproductive
      have hsegment' := CF_grammar.derivesRightmost_of_derives hsegment
      refine ⟨beforeWord ++ segmentWord, ?_⟩
      simpa [List.map_append] using
        hbefore.append_to_terminals hsegment'

/-- A chosen terminal completion of the visible prefix upgrades a normalized
empty edge to its exact-context concrete form. -/
public theorem EmptyBaseEdge.concrete (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix preWord : List T}
    (edge : EmptyBaseEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost
      p (preWord.map symbol.terminal)) :
    ConcreteEmptyEdge M p q suffix := by
  cases edge with
  | @read base suffix source a Z q hparent htransition hrule =>
      obtain ⟨beforeWord, segmentWord, hpre, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      obtain ⟨context, hconcrete⟩ :=
        concreteOperationalSpine_of_activeSpine M hparent hbase
      exact ConcreteEmptyEdge.read hconcrete htransition hrule
  | @epsilon base suffix source Z q hparent htransition hrule =>
      obtain ⟨context, hconcrete⟩ :=
        concreteOperationalSpine_of_activeSpine M hparent hp
      exact ConcreteEmptyEdge.epsilon hconcrete htransition hrule
  | @split base suffix source Z q hparent hlength hrule =>
      obtain ⟨beforeWord, leftWord, hpre, hbase, hleft⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      obtain ⟨context, hconcrete⟩ :=
        concreteOperationalSpine_of_activeSpine M hparent hbase
      exact ConcreteEmptyEdge.split hconcrete hlength hrule hleft

/-- A chosen completion similarly upgrades a transition-tagged empty edge. -/
public theorem EmptyTransitionEdge.concrete (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M}
    {suffix preWord : List T}
    (edge : EmptyTransitionEdge M p q suffix)
    (hp : (characteristicGrammar M).DerivesRightmost
      p (preWord.map symbol.terminal)) :
    ConcreteEmptyTransitionEdge M p q suffix := by
  cases edge with
  | @read base suffix source a Z q hparent htransition hrule =>
      obtain ⟨beforeWord, segmentWord, hpre, hbase, hsegment⟩ :=
        CF_grammar.DerivesRightmost.append_to_terminals_split hp
      obtain ⟨context, hconcrete⟩ :=
        concreteOperationalSpine_of_activeSpine M hparent hbase
      exact ConcreteEmptyTransitionEdge.read hconcrete htransition hrule
  | @epsilon base suffix source Z q hparent htransition hrule =>
      obtain ⟨context, hconcrete⟩ :=
        concreteOperationalSpine_of_activeSpine M hparent hp
      exact ConcreteEmptyTransitionEdge.epsilon hconcrete htransition hrule

/-- Every syntax-facing empty edge has a concrete exact-context witness. -/
public theorem EmptyBaseEdge.exists_concrete (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M} {suffix : List T}
    (edge : EmptyBaseEdge M p q suffix) :
    ConcreteEmptyEdge M p q suffix := by
  obtain ⟨preWord, hp⟩ := edge.prefixCompletion M
  exact edge.concrete M hp

/-- Every syntax-facing transition edge has a concrete transition witness. -/
public theorem EmptyTransitionEdge.exists_concrete (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M} {suffix : List T}
    (edge : EmptyTransitionEdge M p q suffix) :
    ConcreteEmptyTransitionEdge M p q suffix := by
  obtain ⟨preWord, hp⟩ := edge.baseEdge M |>.prefixCompletion M
  exact edge.concrete M hp

/-- An empty edge therefore always admits at least one concrete useful
net-pop factorization. -/
public theorem EmptyBaseEdge.exists_returnRun (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {q : State M} {suffix : List T}
    (edge : EmptyBaseEdge M p q suffix) :
    ∃ preWord : List T, EmptyReturnRun M preWord suffix q := by
  obtain ⟨preWord, hp⟩ := edge.prefixCompletion M
  exact ⟨preWord, edge.returnRun M hp⟩

/-! ## The exact semantic return residual -/

/-- Uniqueness of normalized empty-return edges.  All grammar syntax has
already been eliminated from this statement: its two witnesses are precisely
the three possible incoming edges of an active `list q [] q` node.

This is the empty-handle counterpart of `IntroducingEdgesUnique`.  The
remaining proof is the useful-path/no-epsilon-cycle argument for the
normalized DPDA; the adapters below contain the entire derivation-spine and
rule-shape assembly. -/
@[expose]
public def EmptyReturnEdgesUnique (M : DPDA Q T S) : Prop :=
  ∀ (p₁ p₂ : List (symbol T (Nonterminal M)))
      (q₁ q₂ : State M) (s₁ s₂ y : List T),
    ∀ (edge₁ : EmptyBaseEdge M p₁ q₁ s₁)
      (edge₂ : EmptyBaseEdge M p₂ q₂ s₂),
    (EmptyTransitionEdge M p₁ q₁ s₁ ∨
      EmptyTransitionEdge M p₂ q₂ s₂) →
    p₂ ++ s₂.map symbol.terminal =
      p₁ ++ y.map symbol.terminal →
    s₁.take 1 = y.take 1 →
    p₁ = p₂ ∧ q₁ = q₂

/-- Precise paired-spine classifier still needed before invoking the
cycle/growth kernels.  It says that a pair of normalized empty-return edges
is either literally the same return position and state, or its ordered hidden
contexts yield one of the two impossible useful self-embeddings above. -/
private def EmptyReturnPairsClassified (M : DPDA Q T S) : Prop :=
  ∀ (p₁ p₂ : List (symbol T (Nonterminal M)))
      (q₁ q₂ : State M) (s₁ s₂ y : List T),
    ∀ (edge₁ : EmptyBaseEdge M p₁ q₁ s₁)
      (edge₂ : EmptyBaseEdge M p₂ q₂ s₂),
    (EmptyTransitionEdge M p₁ q₁ s₁ ∨
      EmptyTransitionEdge M p₂ q₂ s₂) →
    p₂ ++ s₂.map symbol.terminal =
      p₁ ++ y.map symbol.terminal →
    s₁.take 1 = y.take 1 →
    (p₁ = p₂ ∧ q₁ = q₂) ∨
      UsefulReturnObstruction M

/-- The concrete classifier implies the syntax-facing classifier by choosing
terminal completions for each retained edge and upgrading transition tags in
the same way. -/
private theorem emptyReturnPairsClassified_of_concrete (M : DPDA Q T S)
    (h : ConcreteEmptyReturnPairsClassified M) :
    EmptyReturnPairsClassified M := by
  intro p₁ p₂ q₁ q₂ s₁ s₂ y edge₁ edge₂
    htransition hform hlook
  have concrete₁ : ConcreteEmptyEdge M p₁ q₁ s₁ :=
    edge₁.exists_concrete M
  have concrete₂ : ConcreteEmptyEdge M p₂ q₂ s₂ :=
    edge₂.exists_concrete M
  have concreteTransition :
      ConcreteEmptyTransitionEdge M p₁ q₁ s₁ ∨
        ConcreteEmptyTransitionEdge M p₂ q₂ s₂ := by
    rcases htransition with transition₁ | transition₂
    · exact Or.inl (transition₁.exists_concrete M)
    · exact Or.inr (transition₂.exists_concrete M)
  exact h p₁ p₂ q₁ q₂ s₁ s₂ y concrete₁ concrete₂
    concreteTransition hform hlook

/-- Once the paired operational spines have been classified by equality
versus useful cycle/growth, both strict alternatives are ruled out by the
FS→ES kernels. -/
private theorem emptyReturnEdgesUnique_of_classified (M : DPDA Q T S)
    (h : EmptyReturnPairsClassified M) : EmptyReturnEdgesUnique M := by
  intro p₁ p₂ q₁ q₂ s₁ s₂ y edge₁ edge₂
    htransition hform hlook
  rcases h p₁ p₂ q₁ q₂ s₁ s₂ y edge₁ edge₂
      htransition hform hlook with heq | hobstruction
  · exact heq
  · exact False.elim (noUsefulReturnObstruction M hobstruction)

/-- A concrete paired-return classifier supplies normalized empty-return edge
uniqueness.  The synchronization proof may be plugged in here once available. -/
public theorem emptyReturnEdgesUnique_of_concretePairsClassified
    (M : DPDA Q T S) (h : ConcreteEmptyReturnPairsClassified M) :
    EmptyReturnEdgesUnique M :=
  emptyReturnEdgesUnique_of_classified M
    (emptyReturnPairsClassified_of_concrete M h)

/-- Normalized empty-return edge uniqueness implies the spine-native
property used by the grammar proof. -/
public theorem emptyListSpinesUnique_of_returnEdges (M : DPDA Q T S)
    (h : EmptyReturnEdgesUnique M) : EmptyListSpinesUnique M := by
  intro q₁ q₂ hrule₁ hrule₂ p₁ p₂ s₁ s₂ y
    hspine₁ hspine₂ hform hlook
  let edge₁ := emptyBaseEdge_of_activeSpine M hspine₁
  let edge₂ := emptyBaseEdge_of_activeSpine M hspine₂
  by_cases htransition : EmptyTransitionEdge M p₁ q₁ s₁ ∨
      EmptyTransitionEdge M p₂ q₂ s₂
  · exact h p₁ p₂ q₁ q₂ s₁ s₂ y edge₁ edge₂
      htransition hform hlook
  · have hnot₁ : ¬ EmptyTransitionEdge M p₁ q₁ s₁ :=
      fun h₁ => htransition (Or.inl h₁)
    have hnot₂ : ¬ EmptyTransitionEdge M p₂ q₂ s₂ :=
      fun h₂ => htransition (Or.inr h₂)
    obtain ⟨base₁, source₁, Z₁, hp₁⟩ :=
      edge₁.split_shape_of_not_transition M hnot₁
    obtain ⟨base₂, source₂, Z₂, hp₂⟩ :=
      edge₂.split_shape_of_not_transition M hnot₂
    rw [hp₁, hp₂] at hform ⊢
    obtain ⟨hbase, hsingle, hsuffix⟩ :=
      cancel_final_nonterminal hform
    have hq : q₂ = q₁ := by
      injection hsingle
    constructor
    · rw [hbase, hsingle]
    · exact hq.symm

/-- Normalized empty-return edge uniqueness supplies the exact base-rule
obligation expected by the LR core. -/
public theorem emptyListHandlesUnique_of_returnEdges (M : DPDA Q T S)
    (h : EmptyReturnEdgesUnique M) : EmptyListHandlesUnique M :=
  emptyListHandlesUnique_of_spines M
    (emptyListSpinesUnique_of_returnEdges M h)

/-- The complete unaugmented LR(1) core, parameterized only by the two
normalized operational uniqueness statements. -/
public theorem characteristicGrammar_coreIsLR1_of_edgeSemantics
    (M : DPDA Q T S) (hedges : IntroducingEdgesUnique M)
    (hreturns : EmptyReturnEdgesUnique M) :
    (characteristicGrammar M).CoreIsLRk 1 :=
  characteristicGrammar_coreIsLR1_of_spine M hedges
    (emptyListHandlesUnique_of_returnEdges M hreturns)

/-- The complete augmented LR(1) result, with every grammar-syntactic case
already discharged. -/
public theorem characteristicGrammar_isLR1_of_edgeSemantics
    (M : DPDA Q T S) (hedges : IntroducingEdgesUnique M)
    (hreturns : EmptyReturnEdgesUnique M) :
    (characteristicGrammar M).IsLRk 1 :=
  characteristicGrammar_isLR1_of_spine M hedges
    (emptyListHandlesUnique_of_returnEdges M hreturns)

end

end DPDA_to_LR
