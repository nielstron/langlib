import Mathlib
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Classes.ContextFree.Examples.AnBn
import Langlib.Classes.ContextSensitive.Basics.Inclusion
import Langlib.Classes.Regular.Basics.Inclusion
import Langlib.Classes.Regular.Closure.Bijection
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.DeterministicContextFree.Basics.Inclusion

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

private lemma mem_prod_singletons_iff {α β : Type} (f : α → β) :
    ∀ w : List α, ∀ u : List β,
      u ∈ (w.map fun x => ({[f x]} : Language β)).prod ↔ u = List.map f w
  | [], u => by
      change u ∈ ({[]} : Language β) ↔ u = []
      rfl
  | x :: xs, u => by
      constructor
      · intro hu
        rw [show (List.map (fun x => ({[f x]} : Language β)) (x :: xs)).prod =
            ({[f x]} : Language β) * (List.map (fun x => ({[f x]} : Language β)) xs).prod by rfl] at hu
        rw [Language.mul_def] at hu
        rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        have hu₂' := (mem_prod_singletons_iff f xs u₂).1 hu₂
        have hu₁' : u₁ = [f x] := by simpa using hu₁
        simp [hu₁', hu₂']
      · intro hu
        subst hu
        rw [show (List.map (fun x => ({[f x]} : Language β)) (x :: xs)).prod =
            ({[f x]} : Language β) * (List.map (fun x => ({[f x]} : Language β)) xs).prod by rfl]
        rw [Language.mul_def]
        refine ⟨[f x], Set.mem_singleton _, List.map f xs, ?_, rfl⟩
        exact (mem_prod_singletons_iff f xs (List.map f xs)).2 rfl

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
