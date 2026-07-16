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

/-- The concrete two-phase homomorphic-image grammar remains context-sensitive
for every epsilon-free homomorphism. -/
public theorem hom_grammar_context_sensitive (g : grammar α) (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) (hg : grammar_context_sensitive g) :
    grammar_context_sensitive (hom_grammar g h) := by
  refine ⟨fun r hr => ?_, ?_⟩
  · change r ∈
      (g.rules.map (@homLiftRule α β g.nt) ++
        (all_used_terminals g).map (@homExpandRule α β g.nt h)) at hr
    simp only [List.mem_append, List.mem_map] at hr
    rcases hr with ⟨r₀, hr₀, rfl⟩ | ⟨a, _ha, rfl⟩
    · exact homLiftRule_context_sensitive h (hg.1 r₀ hr₀)
    · exact Or.inr (homExpandRule_noncontracting h heps a)
  · -- The ε-rule on `hom_grammar` must be a lifted ε-rule of `g`.
    rintro ⟨r, hr, hε⟩
    change r ∈
      (g.rules.map (@homLiftRule α β g.nt) ++
        (all_used_terminals g).map (@homExpandRule α β g.nt h)) at hr
    simp only [List.mem_append, List.mem_map] at hr
    rcases hr with ⟨r₀, hr₀, rfl⟩ | ⟨a, _ha, rfl⟩
    · -- A lifted rule is the ε-rule iff `r₀` is the ε-rule of `g`.
      have hε₀ : initial_epsilon_rule g r₀ := by
        rcases hε with ⟨hL, hN, hR, hO⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [homLiftRule, homLiftStr] using hL
        · have : Sum.inl r₀.input_N = (Sum.inl g.initial : g.nt ⊕ α) := by
            simpa [hom_grammar, homLiftRule] using hN
          exact Sum.inl.inj this
        · simpa [homLiftRule, homLiftStr] using hR
        · simpa [homLiftRule, homLiftStr] using hO
      have hrhs := hg.2 ⟨r₀, hr₀, hε₀⟩
      -- Push `initial_not_on_rhs` forward along the lift.
      intro r' hr'
      change r' ∈
        (g.rules.map (@homLiftRule α β g.nt) ++
          (all_used_terminals g).map (@homExpandRule α β g.nt h)) at hr'
      simp only [List.mem_append, List.mem_map] at hr'
      rcases hr' with ⟨r₀', hr₀', rfl⟩ | ⟨a, _ha, rfl⟩
      · -- Lifted rule: `S = inl g.initial` in output iff `g.initial` in `r₀'`'s output.
        have := hrhs r₀' hr₀'
        simp only [hom_grammar, homLiftRule, homLiftStr]
        intro hmem
        rw [List.mem_map] at hmem
        obtain ⟨s, hs, hseq⟩ := hmem
        cases s with
        | terminal a => simp [homLiftSym] at hseq
        | nonterminal n =>
            simp only [homLiftSym, symbol.nonterminal.injEq, Sum.inl.injEq] at hseq
            exact this (hseq ▸ hs)
      · -- Expand rule: output is all terminals, no nonterminal `S`.
        simp [hom_grammar, homExpandRule]
    · -- An expand rule has `input_N = Sum.inr a ≠ Sum.inl g.initial`, never the ε-rule.
      rcases hε with ⟨_, hN, _, _⟩
      simp [hom_grammar, homExpandRule] at hN

/-- Context-sensitive languages are closed under ε-free string homomorphism, without requiring
the ambient terminal types themselves to be finite. -/
public theorem is_CS_homomorphicImage_epsfree (L : Language α) (h : α → List β)
    (heps : IsEpsFreeHomomorphism h) (hL : is_CS L) :
    is_CS (L.homomorphicImage h) := by
  obtain ⟨g, hcs, hgL⟩ := hL
  exact ⟨hom_grammar g h, hom_grammar_context_sensitive g h heps hcs,
    by rw [hom_grammar_language_epsfree g h heps, hgL]⟩

/-- Context-sensitive languages are closed under ε-free string homomorphism. -/
public theorem CS_closedUnderEpsFreeHomomorphism :
    ClosedUnderEpsFreeHomomorphism is_CS := by
  intro α β _ _ L h heps hL
  exact is_CS_homomorphicImage_epsfree L h heps hL
