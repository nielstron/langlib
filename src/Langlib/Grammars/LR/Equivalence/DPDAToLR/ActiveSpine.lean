module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Focus

/-!
# Active derivation spines of the characteristic grammar

`Focused` records the operational meaning of an active characteristic
nonterminal, but intentionally hides the partial derivation tree which led to
that occurrence.  Handle-collision arguments need that tree path: in
particular, an empty-list occurrence has forgotten the return state of its
parent unless the introducing edge is retained.

`ActiveSpine` is the minimal such path.  Every descent remembers the parent
active occurrence, the exact retained rule, the position of the child in its
right-hand side, and the terminal completion of the part to the child's
right.  Its indices are exactly the visible prehandle prefix and terminal
suffix.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- The root-to-active-node path in a partial rightmost derivation tree. -/
public inductive ActiveSpine (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → Nonterminal M → List T → Prop
  | root : ActiveSpine M [] (characteristicGrammar M).initial []
  | descend
      {p₀ alpha beta : List (symbol T (Nonterminal M))}
      {parent child : Nonterminal M} {t z : List T}
      {r : Nonterminal M × List (symbol T (Nonterminal M))}
      (parentSpine : ActiveSpine M p₀ parent t)
      (hr : r ∈ (characteristicGrammar M).rules)
      (hlhs : r.1 = parent)
      (hrhs : r.2 = alpha ++ [symbol.nonterminal child] ++ beta)
      (hbeta : (characteristicGrammar M).DerivesRightmost
        beta (z.map symbol.terminal)) :
      ActiveSpine M (p₀ ++ alpha) child (z ++ t)

/-- A stored spine reconstructs its visible reachable prehandle. -/
public theorem ActiveSpine.derivesRightmost (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {A : Nonterminal M} {s : List T}
    (h : ActiveSpine M p A s) :
    (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal) := by
  induction h with
  | root => exact Relation.ReflTransGen.refl
  | @descend p₀ alpha beta parent child t z r hparent hr hlhs hrhs hbeta ih =>
      have hstep : (characteristicGrammar M).ProducesRightmost
          (p₀ ++ [symbol.nonterminal parent] ++ t.map symbol.terminal)
          (p₀ ++ r.2 ++ t.map symbol.terminal) := by
        refine ⟨r, hr, p₀, t, ?_, rfl⟩
        rw [hlhs]
      have hintroduced := ih.tail hstep
      let pre : List (symbol T (Nonterminal M)) :=
        p₀ ++ alpha ++ [symbol.nonterminal child]
      have hintroduced' : (characteristicGrammar M).DerivesRightmost
          [symbol.nonterminal (characteristicGrammar M).initial]
          (pre ++ (beta ++ t.map symbol.terminal)) := by
        dsimp [pre]
        simpa [hrhs, List.append_assoc] using hintroduced
      have hfinish := (hbeta.append_terminals_right t).append_left pre
      simpa [pre, List.map_append, List.append_assoc] using
        hintroduced'.trans hfinish

/-- Counted completeness of the active-spine representation. -/
public theorem activeSpine_of_derivesRightmostIn (M : DPDA Q T S)
    {n : ℕ} {p : List (symbol T (Nonterminal M))}
    {A : Nonterminal M} {s : List T}
    (h : (characteristicGrammar M).DerivesRightmostIn n
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal)) :
    ActiveSpine M p A s := by
  induction n using Nat.strong_induction_on generalizing p A s with
  | h n ih =>
      rcases CF_grammar.derivesRightmostIn_nonterminal_ancestry
          (characteristicGrammar M) h with
        hroot | ⟨m, r, hr, p₀, alpha, beta, t, z, hmn,
          hrhs, hp, hs, hparent, hbeta⟩
      · rcases hroot with ⟨rfl, rfl, rfl⟩
        exact ActiveSpine.root
      · subst p
        subst s
        exact ActiveSpine.descend (ih m hmn hparent) hr rfl hrhs hbeta

/-- Every reachable characteristic prehandle has a canonical active-node
ancestry spine (up to proof irrelevance). -/
public theorem activeSpine_of_derivesRightmost (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {A : Nonterminal M} {s : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (characteristicGrammar M).initial]
      (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal)) :
    ActiveSpine M p A s := by
  obtain ⟨n, hn⟩ :=
    CF_grammar.derivesRightmost_iff_exists_derivesRightmostIn.mp h
  exact activeSpine_of_derivesRightmostIn M hn

/-- Reachability and existence of an active derivation spine are equivalent. -/
public theorem activeSpine_iff_derivesRightmost (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))}
    {A : Nonterminal M} {s : List T} :
    ActiveSpine M p A s ↔
      (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (characteristicGrammar M).initial]
        (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal) :=
  ⟨ActiveSpine.derivesRightmost M, activeSpine_of_derivesRightmost M⟩

/-! ## Normalized final edges -/

/-- One characteristic rule edge on the active tree spine, normalized to its
semantic rule shape.  The indices record both the parent and child visible
prehandles. -/
public inductive ActiveEdge (M : DPDA Q T S) :
    List (symbol T (Nonterminal M)) → Nonterminal M → List T →
    List (symbol T (Nonterminal M)) → Nonterminal M → List T → Prop
  | read
      {p : List (symbol T (Nonterminal M))} {t : List T}
      {q target next : State M} {a : T} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun q a Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ActiveEdge M p (PDA_to_CFG.N.single q Z target) t
        (p ++ [symbol.terminal a])
        (PDA_to_CFG.N.list next gamma target) t
  | epsilon
      {p : List (symbol T (Nonterminal M))} {t : List T}
      {q target next : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun' q Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal
            (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ActiveEdge M p (PDA_to_CFG.N.single q Z target) t p
        (PDA_to_CFG.N.list next gamma target) t
  | splitLeft
      {p : List (symbol T (Nonterminal M))} {t z : List T}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hright : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal)) :
      ActiveEdge M p (PDA_to_CFG.N.list q (Z :: gamma) target) t p
        (PDA_to_CFG.N.single q Z middle) (z ++ t)
  | splitRight
      {p : List (symbol T (Nonterminal M))} {t : List T}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal
              (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ActiveEdge M p (PDA_to_CFG.N.list q (Z :: gamma) target) t
        (p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)])
        (PDA_to_CFG.N.list middle gamma target) t
  | start
      {p : List (symbol T (Nonterminal M))} {t : List T}
      {target : State M}
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      ActiveEdge M p PDA_to_CFG.N.start t p
        (PDA_to_CFG.N.list (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target) t

private theorem terminal_word_eq_nil_of_derives_nil (M : DPDA Q T S)
    {z : List T}
    (h : (characteristicGrammar M).DerivesRightmost
      (([] : List T).map symbol.terminal)
      (z.map symbol.terminal)) : z = [] := by
  have heq := h.eq_of_map_terminal_source
  have hmap : z.map (symbol.terminal (N := Nonterminal M)) = [] := by
    simpa using heq
  exact List.map_eq_nil_iff.mp hmap

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
      obtain ⟨hleft, hA, hright⟩ :=
        decompose_one_nonterminal M htail
      subst left
      exact ⟨rfl, hA, hright⟩

private theorem decompose_two_nonterminals (M : DPDA Q T S)
    {A B C : Nonterminal M}
    {left right : List (symbol T (Nonterminal M))}
    (h : [symbol.nonterminal B, symbol.nonterminal C] =
      left ++ [symbol.nonterminal A] ++ right) :
    (left = [] ∧ A = B ∧
      right = [symbol.nonterminal C]) ∨
    (left = [symbol.nonterminal B] ∧ A = C ∧ right = []) := by
  cases left with
  | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      left
      exact ⟨rfl, (symbol.nonterminal.inj h.1).symm, h.2.symm⟩
  | cons X left =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, htail⟩ := h
      obtain ⟨hleft, hA, hright⟩ :=
        decompose_one_nonterminal M htail
      subst left
      right
      exact ⟨rfl, hA, hright⟩

end

end DPDA_to_LR
