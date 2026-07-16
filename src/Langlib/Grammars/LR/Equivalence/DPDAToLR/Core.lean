module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Introductions
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Augmentation

/-!
# LR core of the productive characteristic grammar

The syntactic reduction in this file leaves exactly two semantic spine
properties: uniqueness of the edge introducing a visible final `list` child,
and uniqueness of an empty-list return.  All characteristic rule-shape pairs
are discharged uniformly from those properties.
-/

@[expose]
public section

open Language

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A retained rule is either the unique empty-list shape, or its right side
has one final characteristic-list marker preceded only by non-list symbols in
the displayed pending prefix. -/
public theorem retained_rule_base_or_finalList (M : DPDA Q T S)
    {r : Nonterminal M × List (symbol T (Nonterminal M))}
    (hr : r ∈ (characteristicGrammar M).rules)
    {p : List (symbol T (Nonterminal M))} (hp : PendingPrefix M p) :
    (∃ q : State M,
      r = (PDA_to_CFG.N.list q [] q, [])) ∨
    ∃ (action : List (symbol T (Nonterminal M)))
        (q target : State M) (gamma : List (StackSymbol M)),
      r.2 = action ++
        [symbol.nonterminal (PDA_to_CFG.N.list q gamma target)] ∧
      ∀ X ∈ p ++ action, ¬ IsListSymbol M X := by
  rcases characteristicGrammar_rule_shape M hr with
      hbase | hread | hepsilon | hsplit | hstart
  · exact Or.inl hbase
  · rcases hread with ⟨q, target, next, a, Z, gamma, _, rfl⟩
    right
    refine ⟨[symbol.terminal a], next, target, gamma, by simp,
      hp.noList_append_terminal M a⟩
  · rcases hepsilon with ⟨q, target, next, Z, gamma, _, rfl⟩
    right
    refine ⟨[], next, target, gamma, by simp, ?_⟩
    simpa using hp.noList M
  · rcases hsplit with ⟨q, middle, target, Z, gamma, _, rfl⟩
    right
    refine ⟨[symbol.nonterminal (PDA_to_CFG.N.single q Z middle)],
      middle, target, gamma, by simp,
      hp.noList_append_single M q middle Z⟩
  · rcases hstart with ⟨target, rfl⟩
    right
    refine ⟨[], (emptyStackPDA M).initial_state, target,
      [(emptyStackPDA M).start_symbol], by simp, ?_⟩
    simpa using hp.noList M

/-- The remaining semantic obligation for base productions. -/
@[expose]
public def EmptyListHandlesUnique (M : DPDA Q T S) : Prop :=
  ∀ (q₁ q₂ : State M),
    (PDA_to_CFG.N.list q₁ [] q₁,
        ([] : List (symbol T (Nonterminal M)))) ∈
      (characteristicGrammar M).rules →
    (PDA_to_CFG.N.list q₂ [] q₂,
        ([] : List (symbol T (Nonterminal M)))) ∈
      (characteristicGrammar M).rules →
    ∀ (p₁ p₂ : List (symbol T (Nonterminal M)))
        (s₁ s₂ y : List T),
      (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (characteristicGrammar M).initial]
        (p₁ ++ [symbol.nonterminal (PDA_to_CFG.N.list q₁ [] q₁)] ++
          s₁.map symbol.terminal) →
      (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (characteristicGrammar M).initial]
        (p₂ ++ [symbol.nonterminal (PDA_to_CFG.N.list q₂ [] q₂)] ++
          s₂.map symbol.terminal) →
      p₂ ++ s₂.map symbol.terminal =
        p₁ ++ y.map symbol.terminal →
      s₁.take 1 = y.take 1 →
      p₁ = p₂ ∧ q₁ = q₂

/-- The complete LR(1) core follows from the two operational spine
uniqueness properties. -/
public theorem characteristicGrammar_coreIsLR1_of_spine
    (M : DPDA Q T S) (hedges : IntroducingEdgesUnique M)
    (hempty : EmptyListHandlesUnique M) :
    (characteristicGrammar M).CoreIsLRk 1 := by
  intro r₁ r₂ hr₁ hr₂ p₁ p₂ s₁ s₂ y hd₁ hd₂ hform hlook
  have hp₁ := pendingPrefix_of_characteristic_prehandle M hd₁
  have hp₂ := pendingPrefix_of_characteristic_prehandle M hd₂
  rcases retained_rule_base_or_finalList M hr₁ hp₁ with
      ⟨q₁, hrule₁⟩ |
      ⟨action₁, next₁, target₁, gamma₁, hrhs₁, hleft₁⟩ <;>
    rcases retained_rule_base_or_finalList M hr₂ hp₂ with
      ⟨q₂, hrule₂⟩ |
      ⟨action₂, next₂, target₂, gamma₂, hrhs₂, hleft₂⟩
  · subst r₁
    subst r₂
    obtain ⟨hp, hq⟩ := hempty q₁ q₂ hr₁ hr₂
      p₁ p₂ s₁ s₂ y hd₁ hd₂ (by simpa using hform)
      (by simpa [CF_grammar.lrLookahead] using hlook)
    subst p₂
    subst q₂
    exact ⟨rfl, rfl⟩
  · subst r₁
    exfalso
    apply base_nonbase_post_impossible M
      (plain := p₁)
      (pre := (show List (symbol T (Nonterminal M)) from p₂) ++ action₂)
      (suffixPlain := y) (suffixList := s₂)
      (q := next₂) (target := target₂) (gamma := gamma₂)
      (hp₁.noList M)
    rw [hrhs₂] at hform
    simpa [List.append_assoc] using hform.symm
  · subst r₂
    exfalso
    apply base_nonbase_post_impossible M
      (plain := p₂)
      (pre := (show List (symbol T (Nonterminal M)) from p₁) ++ action₁)
      (suffixPlain := s₂) (suffixList := y)
      (q := next₁) (target := target₁) (gamma := gamma₁)
      (hp₂.noList M)
    rw [hrhs₁] at hform
    simpa [List.append_assoc] using hform
  · apply nonbase_collision_of_introducingEdgesUnique M hedges
      hr₁ hr₂
      (activeSpine_of_derivesRightmost M hd₁)
      (activeSpine_of_derivesRightmost M hd₂)
      hrhs₁ hrhs₂ hleft₁ hleft₂ hform
    simpa [CF_grammar.lrLookahead] using hlook

/-- Augmented LR(1), still parameterized only by the two operational spine
uniqueness properties. -/
public theorem characteristicGrammar_isLR1_of_spine
    (M : DPDA Q T S) (hedges : IntroducingEdgesUnique M)
    (hempty : EmptyListHandlesUnique M) :
    (characteristicGrammar M).IsLRk 1 :=
  characteristic_isLR1_of_core M
    (characteristicGrammar_coreIsLR1_of_spine M hedges hempty)

end

end DPDA_to_LR
