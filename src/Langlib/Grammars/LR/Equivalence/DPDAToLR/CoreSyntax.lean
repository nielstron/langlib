module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Focus

/-!
# Syntactic cancellation at characteristic handles

Every nonempty right side of the characteristic grammar ends in a `list`
nonterminal.  A rightmost-reachable prefix, on the other hand, contains only
terminals and `single` nonterminals.  Thus that final `list` is a genuine
marker: equality of two post-handle forms determines the text on both sides
of it.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A grammar symbol is one of the characteristic `list` nonterminals. -/
@[expose]
public def IsListSymbol (M : DPDA Q T S) :
    symbol T (Nonterminal M) → Prop
  | symbol.nonterminal (PDA_to_CFG.N.list _ _ _) => True
  | _ => False

/-- Cancellation around a marker which cannot occur in either surrounding
list.  This elementary list lemma is kept independent of grammar syntax. -/
public theorem cancel_unique_marker {X : Type} {P : X → Prop}
    {left₁ left₂ right₁ right₂ : List X} {marker₁ marker₂ : X}
    (hleft₁ : ∀ x ∈ left₁, ¬ P x)
    (hleft₂ : ∀ x ∈ left₂, ¬ P x)
    (hmarker₁ : P marker₁) (hmarker₂ : P marker₂)
    (heq : left₂ ++ marker₂ :: right₂ =
      left₁ ++ marker₁ :: right₁) :
    left₂ = left₁ ∧ marker₂ = marker₁ ∧ right₂ = right₁ := by
  induction left₂ generalizing left₁ with
  | nil =>
      cases left₁ with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          exact ⟨rfl, heq.1, heq.2⟩
      | cons x left₁ =>
          simp only [List.nil_append, List.cons_append,
            List.cons.injEq] at heq
          have hx : ¬ P x := hleft₁ x (by simp)
          exact (hx (heq.1 ▸ hmarker₂)).elim
  | cons x left₂ ih =>
      cases left₁ with
      | nil =>
          simp only [List.cons_append, List.nil_append,
            List.cons.injEq] at heq
          have hx : ¬ P x := hleft₂ x (by simp)
          exact (hx (heq.1.symm ▸ hmarker₁)).elim
      | cons y left₁ =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨hxy, htail⟩ := heq
          subst y
          have hleft₂' : ∀ z ∈ left₂, ¬ P z := by
            intro z hz
            exact hleft₂ z (by simp [hz])
          have hleft₁' : ∀ z ∈ left₁, ¬ P z := by
            intro z hz
            exact hleft₁ z (by simp [hz])
          obtain ⟨hleft, hmarker, hright⟩ :=
            ih hleft₁' hleft₂' htail
          exact ⟨by simp [hleft], hmarker, hright⟩

/-- A marker cannot occur in a list all of whose elements are nonmarkers. -/
public theorem no_marker_ne_append_marker {X : Type} {P : X → Prop}
    {plain left right : List X} {marker : X}
    (hplain : ∀ x ∈ plain, ¬ P x)
    (hmarker : P marker) :
    plain ≠ left ++ marker :: right := by
  intro heq
  have hm : marker ∈ plain := by
    rw [heq]
    simp
  exact hplain marker hm hmarker

/-- Equality of two lists with one final element cancels both final elements. -/
public theorem append_singleton_injective {X : Type}
    {left₁ left₂ : List X} {x₁ x₂ : X}
    (heq : left₂ ++ [x₂] = left₁ ++ [x₁]) :
    left₂ = left₁ ∧ x₂ = x₁ := by
  have hreverse := congrArg List.reverse heq
  simp only [List.reverse_append, List.reverse_singleton] at hreverse
  have hx : x₂ = x₁ := List.cons.inj hreverse |>.1
  have hleftReverse : left₂.reverse = left₁.reverse :=
    List.cons.inj hreverse |>.2
  exact ⟨List.reverse_injective hleftReverse, hx⟩

/-- Pending rightmost prefixes contain no characteristic `list` symbol. -/
public theorem PendingPrefix.noList (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} (hp : PendingPrefix M p) :
    ∀ X ∈ p, ¬ IsListSymbol M X := by
  intro X hX
  cases X with
  | terminal a => simp [IsListSymbol]
  | nonterminal A =>
      obtain ⟨q, target, Z, rfl⟩ := hp A hX
      simp [IsListSymbol]

/-- Terminal words contain no characteristic `list` symbol. -/
public theorem terminals_noList (M : DPDA Q T S) (w : List T) :
    ∀ X ∈ w.map (symbol.terminal (N := Nonterminal M)),
      ¬ IsListSymbol M X := by
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨a, _, rfl⟩ := hX
  simp [IsListSymbol]

/-- Appending a terminal preserves absence of characteristic list symbols. -/
public theorem PendingPrefix.noList_append_terminal (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} (hp : PendingPrefix M p) (a : T) :
    ∀ X ∈ p ++ [symbol.terminal a], ¬ IsListSymbol M X := by
  intro X hX
  simp only [List.mem_append, List.mem_singleton] at hX
  rcases hX with hpX | rfl
  · exact hp.noList M X hpX
  · simp [IsListSymbol]

/-- Appending a `single` preserves absence of characteristic list symbols. -/
public theorem PendingPrefix.noList_append_single (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} (hp : PendingPrefix M p)
    (q target : State M) (Z : StackSymbol M) :
    ∀ X ∈ p ++
        [symbol.nonterminal (PDA_to_CFG.N.single q Z target)],
      ¬ IsListSymbol M X := by
  intro X hX
  simp only [List.mem_append, List.mem_singleton] at hX
  rcases hX with hpX | rfl
  · exact hp.noList M X hpX
  · simp [IsListSymbol]

/-- Appending a terminal word preserves absence of list symbols. -/
public theorem PendingPrefix.noList_append_terminals (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} (hp : PendingPrefix M p)
    (w : List T) :
    ∀ X ∈ p ++ w.map symbol.terminal, ¬ IsListSymbol M X := by
  intro X hX
  simp only [List.mem_append] at hX
  rcases hX with hpX | hwX
  · exact hp.noList M X hpX
  · exact terminals_noList M w X hwX

@[simp]
public theorem isListSymbol_list (M : DPDA Q T S)
    (q target : State M) (gamma : List (StackSymbol M)) :
    IsListSymbol M
      (symbol.nonterminal (PDA_to_CFG.N.list q gamma target)) := by
  simp [IsListSymbol]

/-- Specialized cancellation for the final `list` nonterminal of two
characteristic right sides. -/
public theorem cancel_characteristic_list_marker (M : DPDA Q T S)
    {left₁ left₂ : List (symbol T (Nonterminal M))}
    {q₁ q₂ target₁ target₂ : State M}
    {gamma₁ gamma₂ : List (StackSymbol M)} {suffix₁ suffix₂ : List T}
    (hleft₁ : ∀ X ∈ left₁, ¬ IsListSymbol M X)
    (hleft₂ : ∀ X ∈ left₂, ¬ IsListSymbol M X)
    (heq : left₂ ++
        [symbol.nonterminal (PDA_to_CFG.N.list q₂ gamma₂ target₂)] ++
          suffix₂.map symbol.terminal =
      left₁ ++
        [symbol.nonterminal (PDA_to_CFG.N.list q₁ gamma₁ target₁)] ++
          suffix₁.map symbol.terminal) :
    left₂ = left₁ ∧ q₂ = q₁ ∧ gamma₂ = gamma₁ ∧
      target₂ = target₁ ∧ suffix₂ = suffix₁ := by
  have heq' : left₂ ++
        symbol.nonterminal (PDA_to_CFG.N.list q₂ gamma₂ target₂) ::
          suffix₂.map symbol.terminal =
      left₁ ++
        symbol.nonterminal (PDA_to_CFG.N.list q₁ gamma₁ target₁) ::
          suffix₁.map symbol.terminal := by
    simpa [List.append_assoc] using heq
  obtain ⟨hleft, hmarker, htail⟩ := cancel_unique_marker
    hleft₁ hleft₂
    (isListSymbol_list M q₁ target₁ gamma₁)
    (isListSymbol_list M q₂ target₂ gamma₂) heq'
  have hN : PDA_to_CFG.N.list q₂ gamma₂ target₂ =
      PDA_to_CFG.N.list q₁ gamma₁ target₁ :=
    symbol.nonterminal.inj hmarker
  injection hN with hq hgamma htarget
  have hsuffix : suffix₂ = suffix₁ := by
    exact (List.map_injective_iff.mpr fun _ _ h =>
      symbol.terminal.inj h) htail
  exact ⟨hleft, hq, hgamma, htarget, hsuffix⟩

end

end DPDA_to_LR
