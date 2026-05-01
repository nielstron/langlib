import Mathlib
import Langlib.Grammars.Indexed.Definition
import Langlib.Classes.Indexed.Definition
import Langlib.Classes.Indexed.Closure.Injection
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Closure.Bijection
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Inclusion.Indexed
import Langlib.Classes.Indexed.Examples.AnBnCn

/-! # Strict Inclusion: CF ⊊ Indexed

This file proves that the class of indexed languages strictly contains the class of
context-free languages, by exhibiting a witness: the language `{aⁿbⁿcⁿ | n ∈ ℕ}`
is indexed but not context-free.

The indexed grammar uses a stack-bottom marker to ensure that each nonterminal
consumes exactly as many flags as were pushed.

## Main declarations

- `CF_strict_subclass_Indexed` — `CF ⊂ Indexed`
-/


/-- For any finite alphabet with at least `3` symbols, context-free languages form a strict
subclass of indexed languages. -/
theorem CF_strict_subclass_Indexed {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (CF : Set (Language T)) ⊂ (Indexed : Set (Language T)) := by
  let π : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let e : Fin 3 ↪ T := (Fin.castLEEmb hT).trans π.symm.toEmbedding
  refine ⟨CF_subclass_Indexed, ?_⟩
  intro hIndexedSubsetCF
  have hIndexed : is_Indexed (Language.map e lang_eq_eq) :=
    Indexed_of_map_injective_Indexed e.injective lang_eq_eq is_Indexed_lang_eq_eq
  have hCF : is_CF (Language.map e lang_eq_eq) :=
    hIndexedSubsetCF (a := Language.map e lang_eq_eq) hIndexed
  exact notCF_lang_eq_eq (CF_of_map_injective_CF_rev e.injective lang_eq_eq hCF)
