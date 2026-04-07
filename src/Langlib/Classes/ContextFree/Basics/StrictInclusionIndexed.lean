import Mathlib
import Langlib.Grammars.Indexed.Definition
import Langlib.Classes.Indexed.Definition
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Basics.InclusionIndexed
import Langlib.Classes.Indexed.Examples.AnBnCn

/-! # Strict Inclusion: CF ⊊ Indexed

This file proves that the class of indexed languages strictly contains the class of
context-free languages, by exhibiting a witness: the language `{aⁿbⁿcⁿ | n ∈ ℕ}`
is indexed but not context-free.

The indexed grammar uses a stack-bottom marker to ensure that each nonterminal
consumes exactly as many flags as were pushed.

## Main declarations

- `CF_strict_subclass_Indexed` — CF ⊊ Indexed
-/


/-- CF ⊊ Indexed: context-free languages form a strict subclass of indexed languages. -/
theorem CF_strict_subclass_Indexed :
    (∀ (T : Type) (L : Language T), is_CF L → is_Indexed L) ∧
    (∃ (T : Type) (L : Language T), is_Indexed L ∧ ¬ is_CF L) :=
  ⟨fun _ _ => CF_subclass_Indexed, ⟨Fin 3, lang_eq_eq, is_Indexed_lang_eq_eq, notCF_lang_eq_eq⟩⟩
