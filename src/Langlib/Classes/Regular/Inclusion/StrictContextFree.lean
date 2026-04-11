import Mathlib
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Classes.ContextFree.Examples.AnBn
import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
import Langlib.Classes.Regular.Inclusion.ContextFree
import Langlib.Classes.Regular.Closure.Bijection
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree

/-! # RG ⊊ CF

This file uses the example language `{aⁿbⁿ}` to show that regular languages
form a strict subclass of context-free languages.

## Main results

- `exists_CF_not_regular` — There exists a CF language that is not regular.
- `RG_strict_subclass_CF` — Right-regular languages form a strict subclass of CF languages.
-/

open Language List

/-- There exists a context-free language that is not regular. -/
theorem exists_CF_not_regular : ∃ L : Language Bool, is_CF L ∧ ¬ L.IsRegular :=
  ⟨anbn, anbn_is_CF, anbn_not_isRegular⟩

private theorem map_anbn_is_CF (f : Bool → T) : is_CF (Language.map f anbn) := by
  have hsubst : is_CF (anbn.subst (fun x => ({[f x]} : Language T))) := by
    apply CF_of_subst_CF anbn
    · exact anbn_is_CF
    · intro x
      rw [is_CF_iff_isContextFree]
      exact isContextFree_singleton [f x]
  simpa [Language.subst_singletons_eq_map] using hsubst

/-- Right-regular languages form a strict subclass of context-free languages over any nontrivial alphabet. -/
theorem RG_strict_subclass_CF [Nontrivial T] :
  (RG : Set (Language T)) ⊂ (CF : Set (Language T)) := by
  refine ⟨RG_subclass_CF, ?_⟩
  · intro hCFsubsetRG
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    let f : Bool → T := fun x => if x then b else a
    have hf : Function.Injective f := by
      intro x y hxy
      cases x <;> cases y <;> try rfl
      · simp [f] at hxy
        exact False.elim (hab hxy)
      · simp [f] at hxy
        exact False.elim (hab hxy.symm)
    have hRG : Language.map f anbn ∈ (RG : Set (Language T)) :=
      hCFsubsetRG (a := Language.map f anbn) (map_anbn_is_CF f)
    have hreg : (Language.map f anbn).IsRegular := isRegular_of_is_RG hRG
    exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf hreg)
