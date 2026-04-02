import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Classes.ContextFree.ClosureProperties.Substitution
import Grammars.Classes.Unrestricted.ClosureProperties.Bijection
import Grammars.Utilities.LanguageOperations

/-! # Context-Free Closure Under Bijections

This file proves that context-free languages are preserved under renaming
terminals along an equivalence.

## Strategy

We reuse the unrestricted-level result `bijection_grammar_language` by showing
that the CF bijection construction commutes with the embedding into unrestricted
grammars. The derivation correspondence is proved only once at the unrestricted
level; the CF file only needs to verify structure preservation.

## Main declarations

- `CF_of_map_CF`
- `bijection_CF_grammar`
- `bijection_CF_grammar_language`
- `CF_of_bijemap_CF`
- `CF_of_bijemap_CF_rev`
- `CF_bijemap_iff_CF`
-/

variable {T₁ T₂ : Type}

/-- Context-free languages are closed under alphabet maps. -/
theorem CF_of_map_CF (f : T₁ → T₂) (L : Language T₁) :
    is_CF L → is_CF (Language.map f L) := by
  intro hL
  have hsubst : is_CF (L.subst (fun x => ({[f x]} : Language T₂))) := by
    apply CF_of_subst_CF L
    · exact hL
    · intro x
      rw [is_CF_iff_isContextFree]
      exact isContextFree_singleton [f x]
  simpa [Language.subst_singletons_eq_map] using hsubst

/-- Map a CF grammar along a terminal bijection. -/
def bijection_CF_grammar (g : CF_grammar T₁) (π : T₁ ≃ T₂) : CF_grammar T₂ :=
  CF_grammar.mk g.nt g.initial (List.map
    (fun r : g.nt × (List (symbol T₁ g.nt)) =>
      (r.fst, List.map (map_symbol π) r.snd))
    g.rules)

/-- The CF bijection commutes with the embedding into unrestricted grammars. -/
private theorem CF_grammar_to_grammar_bijection_comm (g : CF_grammar T₁) (π : T₁ ≃ T₂) :
    grammar_of_cfg (bijection_CF_grammar g π) =
    bijection_grammar (grammar_of_cfg g) π := by
  unfold bijection_grammar bijection_CF_grammar grammar_of_cfg
  aesop

/-- The bijection CF grammar generates exactly the π-image of the original language. -/
theorem bijection_CF_grammar_language (g : CF_grammar T₁) (π : T₁ ≃ T₂) :
    CF_language (bijection_CF_grammar g π) =
    Language.bijemapLang (CF_language g) π := by
  rw [CF_language_eq_grammar_language, CF_language_eq_grammar_language,
      CF_grammar_to_grammar_bijection_comm, bijection_grammar_language]

/-- The class of context-free languages is closed under bijection between terminal alphabets. -/
theorem CF_of_bijemap_CF (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CF L → is_CF (Language.bijemapLang L π) := by
  rintro ⟨g, hgL⟩
  exact ⟨bijection_CF_grammar g π, by rw [bijection_CF_grammar_language, hgL]⟩

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
