import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Classes.ContextFree.Basics.Elementary
import Langlib.Classes.ContextFree.Definition
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
/-! # Context-Free Closure Converses Fail
This file proves that the closure properties of context-free languages under
union, concatenation, and substitution are strict implications, not biconditionals.
That is, while:
- `is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ + L₂)` (closure under union),
- `is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ * L₂)` (closure under concatenation),
- `is_CF L ∧ (∀ a, is_CF (f a)) → is_CF (L.subst f)` (closure under substitution),
the converses of all three fail.
## Proof sketch
All counterexamples derive from the existence of a non-context-free language,
which is obtained from `nnyCF_of_CF_i_CF` (non-closure under intersection):
there exist CF languages `L₁`, `L₂` whose intersection `L₁ ⊓ L₂` is not CF.
- **Union**: Take `A = L₁ ⊓ L₂` (not CF) and `B = L₁` (CF).
  Then `A + B = (L₁ ⊓ L₂) ⊔ L₁ = L₁` is CF, but `A` is not CF.
- **Concatenation**: Take `A = L₁ ⊓ L₂` (not CF) and `B = 0` (empty language, CF).
  Then `A * B = 0` is CF, but `A` is not CF.
- **Substitution**: Take `L = 0 : Language Unit` and `f () = L₁ ⊓ L₂` (not CF).
  Then `L.subst f = 0` is CF, but `f` maps to a non-CF language.
## Main declarations
- `not_iff_CF_union`
- `not_iff_CF_concat`
- `not_iff_CF_subst`
-/

/-- Helper: extract a non-CF language from the intersection non-closure result. -/
private lemma exists_nonCF_language :
    ∃ (T : Type) (L₁ L₂ : Language T), is_CF L₁ ∧ is_CF L₂ ∧ ¬ is_CF (L₁ ⊓ L₂) := by
  have h := nnyCF_of_CF_i_CF
  push_neg at h
  obtain ⟨T, L₁, L₂, ⟨hL₁, hL₂⟩, hI⟩ := h
  exact ⟨T, L₁, L₂, hL₁, hL₂, hI⟩

/-- The converse of union closure fails: there exist languages where `L₁ + L₂` is CF
    but not both `L₁` and `L₂` are CF. -/
theorem not_iff_CF_union :
    ¬ (∀ (T : Type) (L₁ L₂ : Language T), is_CF (L₁ + L₂) ↔ (is_CF L₁ ∧ is_CF L₂)) := by
  intro h
  obtain ⟨T, L₁, L₂, hL₁, _, hI⟩ := exists_nonCF_language
  -- (L₁ ⊓ L₂) + L₁ = L₁ since L₁ ⊓ L₂ ≤ L₁
  have hunion : is_CF ((L₁ ⊓ L₂) + L₁) := by
    have : (L₁ ⊓ L₂) + L₁ = L₁ := show (L₁ ⊓ L₂) ⊔ L₁ = L₁ from
      sup_eq_right.mpr inf_le_left
    rw [this]; exact hL₁
  exact hI ((h T (L₁ ⊓ L₂) L₁).mp hunion).1

/-- The converse of concatenation closure fails: there exist languages where `L₁ * L₂` is CF
    but not both `L₁` and `L₂` are CF. -/
theorem not_iff_CF_concat :
    ¬ (∀ (T : Type) (L₁ L₂ : Language T), is_CF (L₁ * L₂) ↔ (is_CF L₁ ∧ is_CF L₂)) := by
  intro h
  obtain ⟨T, L₁, L₂, _, _, hI⟩ := exists_nonCF_language
  have hempty : is_CF (0 : Language T) := by
    exact is_CF_via_cfg_implies_is_CF ⟨cfg_empty_lang, language_of_cfg_empty_lang⟩
  have hprod : is_CF ((L₁ ⊓ L₂) * (0 : Language T)) := by
    have : (L₁ ⊓ L₂) * (0 : Language T) = 0 := mul_zero (L₁ ⊓ L₂)
    rw [this]; exact hempty
  exact hI ((h T (L₁ ⊓ L₂) 0).mp hprod).1

/-- The converse of substitution closure fails: there exist a language `L` and substitution `f`
    where `L.subst f` is CF but the premises `is_CF L ∧ ∀ a, is_CF (f a)` fail. -/
theorem not_iff_CF_subst :
    ¬ (∀ (α β : Type) (L : Language α) (f : α → Language β),
      is_CF (L.subst f) ↔ (is_CF L ∧ ∀ a, is_CF (f a))) := by
  intro h
  obtain ⟨T, L₁, L₂, _, _, hI⟩ := exists_nonCF_language
  set f : Unit → Language T := fun _ => L₁ ⊓ L₂
  have hsubst_cf : is_CF ((0 : Language Unit).subst f) := by
    have : (0 : Language Unit).subst f = (0 : Language T) := by
      ext u; simp [Language.subst]; tauto
    rw [this]
    exact is_CF_via_cfg_implies_is_CF ⟨cfg_empty_lang, language_of_cfg_empty_lang⟩
  have hcf := (h Unit T 0 f).mp hsubst_cf
  exact hI (hcf.2 ())
