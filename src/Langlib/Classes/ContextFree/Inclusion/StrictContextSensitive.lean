module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.ContextFree.Inclusion.ContextSensitive
public import Langlib.Classes.ContextFree.Examples.AnBnCn
public import Langlib.Classes.ContextSensitive.Examples.AnBnCn
import Langlib.Classes.ContextFree.Closure.Bijection
import Langlib.Classes.ContextSensitive.Closure.EpsFreeHomomorphism
import Langlib.Utilities.Homomorphism
@[expose]
public section

/-! # Strict Inclusion: CF ⊊ CS

Context-free languages form a *strict* subclass of the context-sensitive languages.

Inclusion `CF ⊆ CS` is `is_CS_of_is_CF`. Strictness is witnessed by `{aⁿbⁿcⁿ}`
(`lang_eq_eq`), which is context-sensitive (`lang_eq_eq_is_CS`) but not context-free
(`notCF_lang_eq_eq`, via the context-free pumping lemma).

## Main declarations

- `CF_subclass_CS_and_exists_strict`
- `CF_strict_subclass_CS`
-/

open Language

/-- CF ⊊ CS: every context-free language is context-sensitive, and there is a
context-sensitive language (`{aⁿbⁿcⁿ}`) that is not context-free. -/
public theorem CF_subclass_CS_and_exists_strict :
    (∀ (T : Type) (L : Language T), is_CF L → is_CS L) ∧
    (∃ (T : Type) (L : Language T), is_CS L ∧ ¬ is_CF L) :=
  ⟨fun _ _ h => is_CS_of_is_CF h, ⟨Fin 3, lang_eq_eq, lang_eq_eq_is_CS, notCF_lang_eq_eq⟩⟩

/-- For any finite alphabet with at least `3` symbols, the context-free languages form a
strict subclass of the context-sensitive languages: `CF ⊂ CS`.

The witness `{aⁿbⁿcⁿ}` (`lang_eq_eq`, over `Fin 3`) is relabeled into `T` along an
embedding `e : Fin 3 ↪ T`. Relabeling along an injective map is an ε-free homomorphism,
under which `CS` is closed (`CS_closedUnderEpsFreeHomomorphism`), so the image stays
context-sensitive; were it context-free, injectivity of `e` would pull `{aⁿbⁿcⁿ}` itself
back into `CF` (`CF_of_map_injective_CF_rev`), contradicting `notCF_lang_eq_eq`. -/
public theorem CF_strict_subclass_CS {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (CF : Set (Language T)) ⊂ (CS : Set (Language T)) := by
  let π : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let e : Fin 3 ↪ T := (Fin.castLEEmb hT).trans π.symm.toEmbedding
  refine ⟨fun L hL => is_CS_of_is_CF hL, ?_⟩
  intro hCSsubCF
  -- Relabeling `{aⁿbⁿcⁿ}` along the embedding `e` keeps it context-sensitive.
  have hCS : is_CS (Language.map e lang_eq_eq) := by
    have key : is_CS (lang_eq_eq.homomorphicImage (fun a => [e a])) :=
      CS_closedUnderEpsFreeHomomorphism lang_eq_eq (fun a => [e a])
        (fun a => by simp) lang_eq_eq_is_CS
    rwa [Language.homomorphicImage, subst_singletons_eq_map] at key
  have hCF : is_CF (Language.map e lang_eq_eq) :=
    hCSsubCF (a := Language.map e lang_eq_eq) hCS
  exact notCF_lang_eq_eq (CF_of_map_injective_CF_rev e.injective lang_eq_eq hCF)

end
