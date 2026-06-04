module

public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
public import Mathlib.Algebra.Group.End

@[expose]
public section

/-! # Context-Sensitive Closure Under Terminal Bijections

This file proves that context-sensitive languages are preserved under bijective
renaming of terminals.
-/

variable {T₁ T₂ : Type}

private theorem bijection_grule_context_sensitive (π : T₁ ≃ T₂)
    {g : grammar T₁} {r : grule T₁ g.nt}
    (hr : initial_epsilon_rule g r ∨ grule_noncontracting r) :
    initial_epsilon_rule (bijection_grammar g π) (bijection_grule π r) ∨
      grule_noncontracting (bijection_grule π r) := by
  rcases hr with hε | hnc
  · left
    rcases hε with ⟨hL, hN, hR, hO⟩
    simp [initial_epsilon_rule, bijection_grammar, bijection_grule, hL, hN, hR, hO]
  · right
    simpa [grule_noncontracting, bijection_grule]
      using hnc

private theorem bijection_grammar_context_sensitive (g : grammar T₁) (π : T₁ ≃ T₂)
    (hg : grammar_context_sensitive g) :
    grammar_context_sensitive (bijection_grammar g π) := by
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    exact bijection_grule_context_sensitive π (hg.1 r₀ hr₀)
  · -- The ε-rule on the bijection image comes from an ε-rule on `g`.
    rintro ⟨r, hr, hε⟩
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    have hε₀ : initial_epsilon_rule g r₀ := by
      rcases hε with ⟨hL, hN, hR, hO⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [bijection_grule] using hL
      · simpa [bijection_grammar, bijection_grule] using hN
      · simpa [bijection_grule] using hR
      · simpa [bijection_grule] using hO
    have hrhs := hg.2 ⟨r₀, hr₀, hε₀⟩
    -- Push `initial_not_on_rhs` forward along the bijection.
    intro r' hr'
    obtain ⟨r₀', hr₀', rfl⟩ := List.mem_map.mp hr'
    have := hrhs r₀' hr₀'
    -- `S` is a nonterminal, so it lies in the mapped output iff it lies in the original.
    simp only [bijection_grammar, bijection_grule] at *
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨s, hs, hseq⟩ := hmem
    cases s with
    | terminal a => simp [map_symbol] at hseq
    | nonterminal n =>
        simp only [map_symbol, symbol.nonterminal.injEq] at hseq
        exact this (hseq ▸ hs)

/-- The class of context-sensitive languages is closed under bijection between terminal alphabets. -/
public theorem CS_of_bijemap_CS (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CS L → is_CS (Language.bijemapLang L π) := by
  rintro ⟨g, hcs, hgL⟩
  exact ⟨bijection_grammar g π, bijection_grammar_context_sensitive g π hcs,
    by rw [bijection_grammar_language, hgL]⟩

/-- The converse direction. -/
public theorem CS_of_bijemap_CS_rev (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CS (Language.bijemapLang L π) → is_CS L := by
  intro h
  simpa using CS_of_bijemap_CS π.symm (Language.bijemapLang L π) h

/-- A language is context-sensitive iff its image under a terminal bijection is. -/
@[simp] public theorem CS_bijemap_iff_CS (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CS (Language.bijemapLang L π) ↔ is_CS L := by
  constructor
  · exact CS_of_bijemap_CS_rev π L
  · exact CS_of_bijemap_CS π L
