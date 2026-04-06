/- 
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.DeterministicContextFree.Definition
import Langlib.Classes.DeterministicContextFree.Closure.Bijection
import Langlib.Classes.DeterministicContextFree.Examples.AnBn
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Basics.Inclusion
import Langlib.Classes.Regular.Closure.Bijection

/-! # RG ⊊ DCFL

This file uses the example language `{aⁿbⁿ}` to show that regular languages
form a strict subclass of deterministic context-free languages.

## Main results

- `RG_strict_subclass_DCFL` — Regular languages are a strict subclass of DCFLs.
-/

/-- Regular languages are a strict subclass of deterministic context-free languages over any
nontrivial alphabet. -/
theorem RG_strict_subclass_DCFL {T : Type} [Fintype T] [Nontrivial T] :
    (RG : Set (Language T)) ⊂ (DCFL : Set (Language T)) := by
  refine ⟨RG_subclass_DCFL, ?_⟩
  intro hDCFLsubsetRG
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
    hDCFLsubsetRG (a := Language.map f anbn)
      (DCFL_of_map_injective_DCFL hf anbn anbn_is_DCFL)
  have hreg : (Language.map f anbn).IsRegular := isRegular_of_is_RG hRG
  exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf hreg)
