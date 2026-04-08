import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Classes.ContextFree.Basics.Elementary
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
import Langlib.Utilities.LanguageOperations
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Basics.InclusionCS
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization

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
- `CF_of_map_injective_CF_rev`
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

private def decodeSingletonMap (f : T₁ → T₂) (y : T₂) : Language T₁ := by
  classical
  exact if h : ∃ x, f x = y then ({[Classical.choose h]} : Language T₁) else 0

private lemma mem_prod_decodeSingletonMap_iff {f : T₁ → T₂} (hf : Function.Injective f) :
    ∀ w : List T₁, ∀ u : List T₁,
      u ∈ (List.map (decodeSingletonMap f) (List.map f w)).prod ↔ u = w
  | [], u => by
      change u ∈ ({[]} : Language T₁) ↔ u = []
      rfl
  | x :: xs, u => by
      constructor
      · intro hu
        rw [show (List.map (decodeSingletonMap f) (List.map f (x :: xs))).prod =
            decodeSingletonMap f (f x) * (List.map (decodeSingletonMap f) (List.map f xs)).prod by rfl] at hu
        rw [Language.mul_def] at hu
        rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        have hx : ∃ z, f z = f x := ⟨x, rfl⟩
        have hchoose : Classical.choose hx = x := by
          apply hf
          simpa using Classical.choose_spec hx
        have hu₁' : u₁ = [x] := by
          simpa [decodeSingletonMap, hx, hchoose] using hu₁
        have hu₂' := (mem_prod_decodeSingletonMap_iff hf xs u₂).1 hu₂
        simp [hu₁', hu₂']
      · intro hu
        subst hu
        rw [show (List.map (decodeSingletonMap f) (List.map f (x :: xs))).prod =
            decodeSingletonMap f (f x) * (List.map (decodeSingletonMap f) (List.map f xs)).prod by rfl]
        rw [Language.mul_def]
        have hx : ∃ z, f z = f x := ⟨x, rfl⟩
        have hchoose : Classical.choose hx = x := by
          apply hf
          simpa using Classical.choose_spec hx
        refine ⟨[x], ?_, xs, ?_, rfl⟩
        · have hdecode : decodeSingletonMap f (f x) = ({[x]} : Language T₁) := by
            simp [decodeSingletonMap, hx, hchoose]
          rw [hdecode]
          exact Set.mem_singleton _
        exact (mem_prod_decodeSingletonMap_iff hf xs xs).2 rfl

/-- Injective alphabet maps reflect context-freeness. -/
theorem CF_of_map_injective_CF_rev {f : T₁ → T₂} (hf : Function.Injective f)
    (L : Language T₁) : is_CF (Language.map f L) → is_CF L := by
  classical
  intro hmap
  let g : T₂ → Language T₁ := decodeSingletonMap f
  have hgCF : ∀ y, is_CF (g y) := by
    intro y
    by_cases h : ∃ x, f x = y
    · simpa [g, decodeSingletonMap, h, is_CF_iff_isContextFree] using
        (isContextFree_singleton [Classical.choose h])
    · have hempty : is_CF (0 : Language T₁) := by
        have hempty_via : is_CF_via_cfg (0 : Language T₁) :=
          ⟨cfg_empty_lang, language_of_cfg_empty_lang⟩
        exact is_CF_via_cfg_implies_is_CF hempty_via
      simpa [g, decodeSingletonMap, h] using hempty
  have hsubst : is_CF ((Language.map f L).subst g) := by
    exact CF_of_subst_CF (Language.map f L) g hmap hgCF
  have hEq : (Language.map f L).subst g = L := by
    ext u
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩, hu⟩
      simpa [g] using (mem_prod_decodeSingletonMap_iff hf w u).1 hu ▸ hw
    · intro hu
      exact ⟨List.map f u, ⟨u, hu, rfl⟩, (mem_prod_decodeSingletonMap_iff hf u u).2 rfl⟩
  simpa [hEq] using hsubst

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
  intro h
  obtain ⟨g, hgL⟩ := is_CF_implies_is_CF_via_cfg h
  exact is_CF_via_cfg_implies_is_CF ⟨bijection_CF_grammar g π, by rw [bijection_CF_grammar_language, hgL]⟩

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
