import Mathlib
import Langlib.Classes.ContextFree.Inclusion.ContextSensitive
import Langlib.Classes.ContextFree.Closure.Bijection
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
import Langlib.Classes.RecursivelyEnumerable.Examples.AnBnCn
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.ContextFree.Definition

/-! # Strict Inclusions in the Chomsky Hierarchy

This file proves strict subset relationships between the language classes
in the Chomsky hierarchy, using results already established elsewhere in
the project.

## Main results

- `CF_strict_subclass_RE` — The class CF is a strict subclass of RE.
- `CF_strictSubclass_RE` — Compatibility theorem phrased as inclusion plus witness.
-/

open Language List

-- ============================================================================
-- Section 3: Strict inclusion CF ⊊ RE
-- ============================================================================

/-- The class of context-free languages is a strict subclass of the class
    of recursively enumerable languages: every CF language is RE,
    but there exists an RE language that is not CF. -/
theorem is_RE_of_is_CF_strict :
    (∀ (T : Type) (L : Language T), is_CF L → is_RE L) ∧
    (∃ (T : Type) (L : Language T), is_RE L ∧ ¬ is_CF L) :=
  ⟨fun _ _ => CF_subclass_RE, ⟨Fin 3, lang_eq_eq, lang_eq_eq_is_RE, notCF_lang_eq_eq⟩⟩

/-- A class-level formulation of `CF_strictSubclass_RE`:
    for every alphabet, `CF ⊆ RE`, and for some alphabet the inclusion is strict. -/
theorem CF_subclass_RE_and_exists_strict :
    (∀ T : Type, (CF : Set (Language T)) ⊆ (RE : Set (Language T))) ∧
    (∃ T : Type, (CF : Set (Language T)) ⊂ (RE : Set (Language T))) := by
  rcases is_RE_of_is_CF_strict with ⟨hsub, ⟨T, L, hRE, hnotCF⟩⟩
  refine ⟨?_, ⟨T, ?_⟩⟩
  · intro T L hL
    exact hsub T L hL
  · refine ⟨?_, ?_⟩
    · intro K hK
      exact hsub T K hK
    · intro hREsubsetCF
      exact hnotCF (hREsubsetCF (a := L) hRE)

/-- For any alphabet with at least `3` symbols, context-free languages form a strict subclass
    of recursively enumerable languages. -/
theorem CF_strict_subclass_RE {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (CF : Set (Language T)) ⊂ (RE : Set (Language T)) := by
  let π : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let e : Fin 3 ↪ T := (Fin.castLEEmb hT).trans π.symm.toEmbedding
  refine ⟨?_, ?_⟩
  · intro L hL
    exact CF_subclass_RE hL
  · intro hREsubsetCF
    have hRE : is_RE (Language.map e lang_eq_eq) :=
      RE_of_map_injective_RE e.injective lang_eq_eq lang_eq_eq_is_RE
    have hCF : is_CF (Language.map e lang_eq_eq) :=
      hREsubsetCF (a := Language.map e lang_eq_eq) hRE
    exact notCF_lang_eq_eq (CF_of_map_injective_CF_rev e.injective lang_eq_eq hCF)
