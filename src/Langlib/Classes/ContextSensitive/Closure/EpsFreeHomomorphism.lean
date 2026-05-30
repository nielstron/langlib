module

public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.RecursivelyEnumerable.Closure.Homomorphism
public import Langlib.Utilities.ClosurePredicates

@[expose]
public section

/-! # Context-Sensitive Closure Under ε-Free Homomorphism

This file proves that context-sensitive languages are closed under string
homomorphisms that do not erase symbols.
-/

variable {α β : Type}

private theorem homLiftRule_context_sensitive (h : α → List β) {g : grammar α}
    {r : grule α g.nt}
    (hr : initial_epsilon_rule g r ∨ grule_noncontracting r) :
    initial_epsilon_rule (hom_grammar g h) (@homLiftRule α β g.nt r) ∨
      @grule_noncontracting β (g.nt ⊕ α) (@homLiftRule α β g.nt r) := by
  rcases hr with hε | hnc
  · left
    rcases hε with ⟨hL, hN, hR, hO⟩
    simp [initial_epsilon_rule, hom_grammar, homLiftRule, homLiftStr, hL, hN, hR, hO]
  · right
    simpa [grule_noncontracting, homLiftRule, homLiftStr]
      using hnc

private theorem homExpandRule_noncontracting (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) (a : α) {N : Type} :
    grule_noncontracting (@homExpandRule α β N h a) := by
  simp [grule_noncontracting, homExpandRule]
  exact List.length_pos_iff.mpr (heps a)

private theorem hom_grammar_context_sensitive (g : grammar α) (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) (hg : grammar_context_sensitive g) :
    grammar_context_sensitive (hom_grammar g h) := by
  intro r hr
  change r ∈
    (g.rules.map (@homLiftRule α β g.nt) ++
      (all_used_terminals g).map (@homExpandRule α β g.nt h)) at hr
  simp only [List.mem_append, List.mem_map] at hr
  rcases hr with ⟨r₀, hr₀, rfl⟩ | ⟨a, _ha, rfl⟩
  · exact homLiftRule_context_sensitive h (hg r₀ hr₀)
  · exact Or.inr (homExpandRule_noncontracting h heps a)

/-- Context-sensitive languages are closed under ε-free string homomorphism. -/
public theorem CS_closedUnderEpsFreeHomomorphism :
    ClosedUnderEpsFreeHomomorphism is_CS := by
  intro α β _ _ L h heps hL
  obtain ⟨g, hcs, hgL⟩ := hL
  exact ⟨hom_grammar g h, hom_grammar_context_sensitive g h heps hcs,
    by rw [hom_grammar_language_epsfree g h heps, hgL]⟩
