import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Classes.ContextFree.Basics.Inclusion
import Grammars.Classes.Unrestricted.ClosureProperties.TerminalMap
import Grammars.Utilities.LanguageOperations


/-! # Context-Free Closure Under Bijections

This file proves that context-free languages are preserved under renaming
terminals along an equivalence.

## Strategy

Instead of re-proving the derivation argument from scratch, we reuse
`grammar_language_terminal_map_grammar` (the unrestricted result) together
with a commutation lemma showing that mapping a CF grammar's terminals and
then embedding it as an unrestricted grammar gives the same result as
embedding first and then applying the unrestricted terminal map.

## Main declarations

- `terminal_map_CF_grammar` — map terminals in a CF grammar
- `grammar_of_cfg_terminal_map_comm` — commutation with the CF→unrestricted embedding
- `CF_of_bijemap_CF`
- `CF_of_bijemap_CF_rev`
- `CF_bijemap_iff_CF`
-/

variable {T₁ T₂ : Type}

section terminal_map_defs

/-- Map terminals in a context-free grammar along a bijection. -/
def terminal_map_CF_grammar (π : T₁ ≃ T₂) (g : CF_grammar T₁) : CF_grammar T₂ :=
  CF_grammar.mk g.nt g.initial (List.map
    (fun r : g.nt × (List (symbol T₁ g.nt)) => (r.fst, terminal_map_symbols π r.snd))
    g.rules)

end terminal_map_defs

section commutation

/-- Mapping terminals in a CF grammar and then embedding as an unrestricted grammar
gives the same grammar as embedding first and then applying the unrestricted terminal
map. -/
theorem grammar_of_cfg_terminal_map_comm (π : T₁ ≃ T₂) (g : CF_grammar T₁) :
    grammar_of_cfg (terminal_map_CF_grammar π g) = terminal_map_grammar π (grammar_of_cfg g) := by
  cases g with
  | mk nt initial rules =>
    simp only [terminal_map_CF_grammar, grammar_of_cfg, terminal_map_grammar]
    congr 1
    rw [List.map_map, List.map_map]
    congr 1

end commutation

section closure

/-- The class of context-free languages is closed under bijection between terminal alphabets. -/
theorem CF_of_bijemap_CF (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CF L → is_CF (Language.bijemapLang L π) := by
  rintro ⟨g, hgL⟩
  refine ⟨terminal_map_CF_grammar π g, ?_⟩
  rw [CF_language_eq_grammar_language, grammar_of_cfg_terminal_map_comm,
      grammar_language_terminal_map_grammar, ← CF_language_eq_grammar_language, hgL]

/-- The converse direction of `CF_of_bijemap_CF`, obtained by applying the forward result
to the inverse bijection. -/
theorem CF_of_bijemap_CF_rev (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CF (Language.bijemapLang L π) → is_CF L := by
  intro h
  simpa using CF_of_bijemap_CF π.symm (Language.bijemapLang L π) h

/-- A language is context-free iff its image under a bijection of terminal alphabets is
context-free. -/
@[simp] theorem CF_bijemap_iff_CF (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CF (Language.bijemapLang L π) ↔ is_CF L := by
  constructor
  · exact CF_of_bijemap_CF_rev π L
  · exact CF_of_bijemap_CF π L

end closure
