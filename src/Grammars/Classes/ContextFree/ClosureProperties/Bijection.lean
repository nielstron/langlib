import Grammars.Classes.ContextFree.Basics.Toolbox
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

- `bijection_CF_grammar`
- `bijection_CF_grammar_language`
- `CF_of_bijemap_CF`
- `CF_of_bijemap_CF_rev`
- `CF_bijemap_iff_CF`
-/

variable {T₁ T₂ : Type}

section embedding

/-- Embed a context-free grammar into an unrestricted grammar. -/
private def CF_grammar_to_grammar {T : Type} (g : CF_grammar T) : grammar T :=
  grammar.mk g.nt g.initial (List.map (fun r : g.nt × (List (symbol T g.nt)) =>
    grule.mk [] r.fst [] r.snd) g.rules)

/-- The unrestricted grammar recognises the same language as the CF grammar. -/
private lemma CF_language_eq_grammar_language {T : Type} (g : CF_grammar T) :
    CF_language g = grammar_language (CF_grammar_to_grammar g) := by
  ext w
  change CF_derives g _ _ ↔ grammar_derives _ _ _
  constructor
  · have indu : ∀ v, CF_derives g [symbol.nonterminal g.initial] v →
        grammar_derives (CF_grammar_to_grammar g)
          [symbol.nonterminal (CF_grammar_to_grammar g).initial] v := by
      intro v h
      induction h with
      | refl => exact grammar_deri_self
      | tail _ step ih =>
        apply grammar_deri_of_deri_tran ih
        rcases step with ⟨r, u, v, rin, bef, aft⟩
        refine ⟨grule.mk [] r.fst [] r.snd, ?_, u, v, ?_, ?_⟩
        · exact List.mem_map.mpr ⟨r, rin, rfl⟩
        · simpa using bef
        · simpa using aft
    exact indu _
  · have indu : ∀ v, grammar_derives (CF_grammar_to_grammar g)
        [symbol.nonterminal (CF_grammar_to_grammar g).initial] v →
        CF_derives g [symbol.nonterminal g.initial] v := by
      intro v h
      induction h with
      | refl => exact CF_deri_self
      | tail _ step ih =>
        apply CF_deri_of_deri_tran ih
        rcases step with ⟨r, rin, u, v, bef, aft⟩
        rcases List.mem_map.mp rin with ⟨r₀, r₀_in, r_eq⟩
        subst r_eq
        refine ⟨r₀, u, v, r₀_in, ?_, ?_⟩
        · simpa using bef
        · simpa using aft
    exact indu _

end embedding

/-- Map a CF grammar along a terminal bijection. -/
def bijection_CF_grammar (g : CF_grammar T₁) (π : T₁ ≃ T₂) : CF_grammar T₂ :=
  CF_grammar.mk g.nt g.initial (List.map
    (fun r : g.nt × (List (symbol T₁ g.nt)) =>
      (r.fst, List.map (map_symbol π) r.snd))
    g.rules)

/-- The CF bijection commutes with the embedding into unrestricted grammars. -/
private theorem CF_grammar_to_grammar_bijection_comm (g : CF_grammar T₁) (π : T₁ ≃ T₂) :
    CF_grammar_to_grammar (bijection_CF_grammar g π) =
    bijection_grammar (CF_grammar_to_grammar g) π := by
  unfold bijection_grammar bijection_CF_grammar CF_grammar_to_grammar; aesop;

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