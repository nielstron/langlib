module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Construction

/-!
# Rule shapes in the DPDA characteristic grammar

The PDA-to-CFG conversion stores its finite rule set in a `Finset`, translates
it to Langlib's list-based grammar, and then filters that list for fully
productive rules.  The lemmas here invert those representation layers and
recover the five semantic rule forms of the characteristic grammar.
-/

@[expose]
public section

open Symbol

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

public abbrev State (M : DPDA Q T S) := (Q × Bool) ⊕ Fin 2
public abbrev StackSymbol (M : DPDA Q T S) := Option S
public abbrev Nonterminal (M : DPDA Q T S) := PDA_to_CFG.N (emptyStackPDA M)

/-- The five possible rule forms before translating Mathlib symbols. -/
@[expose]
public def MathlibRuleShape (M : DPDA Q T S)
    (r : ContextFreeRule T (Nonterminal M)) : Prop :=
  (∃ q : State M,
    r = ⟨PDA_to_CFG.N.list q [] q, []⟩) ∨
  (∃ (q p q' : State M) (a : T) (Z : StackSymbol M)
      (α : List (StackSymbol M)),
    (q', α) ∈ (emptyStackPDA M).transition_fun q a Z ∧
    r = ⟨PDA_to_CFG.N.single q Z p,
      [terminal a, nonterminal (PDA_to_CFG.N.list q' α p)]⟩) ∨
  (∃ (q p q' : State M) (Z : StackSymbol M)
      (α : List (StackSymbol M)),
    (q', α) ∈ (emptyStackPDA M).transition_fun' q Z ∧
    r = ⟨PDA_to_CFG.N.single q Z p,
      [nonterminal (PDA_to_CFG.N.list q' α p)]⟩) ∨
  (∃ (q q' p : State M) (Z : StackSymbol M)
      (α : List (StackSymbol M)),
    (Z :: α).length ≤ PDA_to_CFG.max_push (emptyStackPDA M) ∧
    r = ⟨PDA_to_CFG.N.list q (Z :: α) p,
      [nonterminal (PDA_to_CFG.N.single q Z q'),
        nonterminal (PDA_to_CFG.N.list q' α p)]⟩) ∨
  (∃ p : State M,
    r = ⟨PDA_to_CFG.N.start,
      [nonterminal (PDA_to_CFG.N.list
        (emptyStackPDA M).initial_state
        [(emptyStackPDA M).start_symbol] p)]⟩)

/-- Invert membership in the finite rule set of Mathlib's characteristic
grammar. -/
public theorem mathlibCharacteristicGrammar_rule_shape (M : DPDA Q T S)
    {r : ContextFreeRule T (Nonterminal M)}
    (hr : r ∈ (mathlibCharacteristicGrammar M).rules) :
    MathlibRuleShape M r := by
  change r ∈ (PDA_to_CFG.G (emptyStackPDA M)).rules at hr
  simp only [PDA_to_CFG.G, PDA_to_CFG.rules, Set.Finite.mem_toFinset,
    PDA_to_CFG.RuleSet, Set.mem_union, or_assoc] at hr
  rcases hr with hr | hr | hr | hr | hr
  · simp only [Set.mem_iUnion] at hr
    obtain ⟨q, hr⟩ := hr
    simp only [PDA_to_CFG.epsilon_rule, Set.mem_singleton_iff] at hr
    exact Or.inl ⟨q, hr⟩
  · simp only [Set.mem_iUnion] at hr
    obtain ⟨q, p, a, Z, hr⟩ := hr
    simp only [PDA_to_CFG.compute_rule, Set.mem_image] at hr
    obtain ⟨⟨q', α⟩, htransition, hr⟩ := hr
    exact Or.inr <| Or.inl ⟨q, p, q', a, Z, α, htransition, hr.symm⟩
  · simp only [Set.mem_iUnion] at hr
    obtain ⟨q, p, Z, hr⟩ := hr
    simp only [PDA_to_CFG.compute_rule', Set.mem_image] at hr
    obtain ⟨⟨q', α⟩, htransition, hr⟩ := hr
    exact Or.inr <| Or.inr <| Or.inl
      ⟨q, p, q', Z, α, htransition, hr.symm⟩
  · simp only [Set.mem_iUnion] at hr
    obtain ⟨q', n, hn, hr⟩ := hr
    rcases n with _ | ⟨q, Z, p⟩ | ⟨q, α, p⟩
    · simp [PDA_to_CFG.split_rule] at hr
    · simp [PDA_to_CFG.split_rule] at hr
    · rcases α with _ | ⟨Z, α⟩
      · simp [PDA_to_CFG.split_rule] at hr
      · simp only [PDA_to_CFG.split_rule, Set.mem_singleton_iff] at hr
        exact Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨q, q', p, Z, α, hn, hr⟩
  · simp only [Set.mem_iUnion] at hr
    obtain ⟨p, hr⟩ := hr
    simp only [PDA_to_CFG.start_rule, Set.mem_singleton_iff] at hr
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨p, hr⟩

/-- A retained characteristic rule comes from a rule of Mathlib's
characteristic grammar. -/
public theorem mathlib_rule_of_characteristic_rule (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules) :
    ∃ R ∈ (mathlibCharacteristicGrammar M).rules,
      r = (R.input, lssymbol_of_lsSymbol R.output) := by
  simp only [characteristicGrammar, productiveGrammar, List.mem_filter,
    decide_eq_true_eq] at hr
  have hrRaw := hr.1
  simp only [rawCharacteristicGrammar, cfg_of_mathlib_cfg, List.mem_map] at hrRaw
  obtain ⟨R, hR, rfl⟩ := hrRaw
  refine ⟨R, ?_, rfl⟩
  simpa using hR

/-- Every retained rule is fully productive in the unfiltered characteristic
grammar. -/
public theorem characteristic_rule_fullyProductive (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules) :
    fullyProductiveRule (rawCharacteristicGrammar M) r := by
  simp only [characteristicGrammar, productiveGrammar, List.mem_filter,
    decide_eq_true_eq] at hr
  exact hr.2

/-- The five possible rule forms after translating to Langlib symbols. -/
@[expose]
public def RuleShape (M : DPDA Q T S)
    (r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)) : Prop :=
  (∃ q : State M,
    r = (PDA_to_CFG.N.list q [] q, [])) ∨
  (∃ (q p q' : State M) (a : T) (Z : StackSymbol M)
      (α : List (StackSymbol M)),
    (q', α) ∈ (emptyStackPDA M).transition_fun q a Z ∧
    r = (PDA_to_CFG.N.single q Z p,
      [symbol.terminal a,
        symbol.nonterminal (PDA_to_CFG.N.list q' α p)])) ∨
  (∃ (q p q' : State M) (Z : StackSymbol M)
      (α : List (StackSymbol M)),
    (q', α) ∈ (emptyStackPDA M).transition_fun' q Z ∧
    r = (PDA_to_CFG.N.single q Z p,
      [symbol.nonterminal (PDA_to_CFG.N.list q' α p)])) ∨
  (∃ (q q' p : State M) (Z : StackSymbol M)
      (α : List (StackSymbol M)),
    (Z :: α).length ≤ PDA_to_CFG.max_push (emptyStackPDA M) ∧
    r = (PDA_to_CFG.N.list q (Z :: α) p,
      [symbol.nonterminal (PDA_to_CFG.N.single q Z q'),
        symbol.nonterminal (PDA_to_CFG.N.list q' α p)])) ∨
  (∃ p : State M,
    r = (PDA_to_CFG.N.start,
      [symbol.nonterminal (PDA_to_CFG.N.list
        (emptyStackPDA M).initial_state
        [(emptyStackPDA M).start_symbol] p)]))

/-- Inverse rule-shape theorem for the reduced Langlib grammar. -/
public theorem characteristicGrammar_rule_shape (M : DPDA Q T S)
    {r : (characteristicGrammar M).nt ×
      List (symbol T (characteristicGrammar M).nt)}
    (hr : r ∈ (characteristicGrammar M).rules) :
    RuleShape M r := by
  obtain ⟨R, hR, rfl⟩ := mathlib_rule_of_characteristic_rule M hr
  rcases mathlibCharacteristicGrammar_rule_shape M hR with
    h | h | h | h | h
  · obtain ⟨q, rfl⟩ := h
    exact Or.inl ⟨q, rfl⟩
  · obtain ⟨q, p, q', a, Z, α, ht, rfl⟩ := h
    exact Or.inr <| Or.inl ⟨q, p, q', a, Z, α, ht, rfl⟩
  · obtain ⟨q, p, q', Z, α, ht, rfl⟩ := h
    exact Or.inr <| Or.inr <| Or.inl ⟨q, p, q', Z, α, ht, rfl⟩
  · obtain ⟨q, q', p, Z, α, hlen, rfl⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨q, q', p, Z, α, hlen, rfl⟩
  · obtain ⟨p, rfl⟩ := h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨p, rfl⟩

end

end DPDA_to_LR
