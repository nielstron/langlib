module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.ContextFree.Inclusion.ContextSensitive
public import Langlib.Classes.ContextFree.Examples.AnBnCn
public import Langlib.Classes.ContextSensitive.Examples.AnBnCn
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

/-- The class of context-free languages is a strict subclass of the context-sensitive
languages: `CF ⊂ CS`, witnessed over the alphabet `Fin 3` by `{aⁿbⁿcⁿ}`. -/
public theorem CF_strict_subclass_CS :
    (CF : Set (Language (Fin 3))) ⊂ (CS : Set (Language (Fin 3))) := by
  refine ⟨fun L hL => is_CS_of_is_CF hL, ?_⟩
  intro hCSsubCF
  exact notCF_lang_eq_eq (hCSsubCF (a := lang_eq_eq) lang_eq_eq_is_CS)

end
