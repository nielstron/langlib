module

/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Regular.Definition
public import Langlib.Classes.LR.Examples.AnBn
import Langlib.Classes.LR.Closure.Bijection
import Langlib.Classes.Regular.Examples.AnBn
import Langlib.Classes.Regular.Inclusion.LR
import Langlib.Classes.Regular.Closure.Bijection
import Langlib.Automata.FiniteState.Equivalence.Regular
import Mathlib

@[expose]
public section

/-! # RG ⊊ LR

This file proves that regular languages form a strict subclass of LR languages.

The witness is the language `{aⁿbⁿ}`, which is LR(1) (via `cfg_anbn`) but not
regular (by the pumping lemma). Combined with the already-established inclusion
`RG ⊆ LR`, this gives strict containment.

## Main results

- `RG_strict_subclass_LR` — `RG ⊊ LR` over any nontrivial finite alphabet.
-/

/-- `Language.map f anbn` is LR for injective `f : Bool → T`. -/
private theorem map_anbn_is_LR {T : Type} {f : Bool → T} (hf : Function.Injective f) :
    is_LR (Language.map f anbn) :=
  is_LR_map_injective hf anbn_is_LR

/-- Regular languages are a strict subclass of LR languages
over any nontrivial finite alphabet. -/
public theorem RG_strict_subclass_LR {T : Type} [Fintype T] [Nontrivial T] :
    (RG : Set (Language T)) ⊂ (LR : Set (Language T)) := by
  refine ⟨RG_subclass_LR, ?_⟩
  intro hLRsubsetRG
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  let f : Bool → T := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  have hLR : Language.map f anbn ∈ (LR : Set (Language T)) := map_anbn_is_LR hf
  have hRG : Language.map f anbn ∈ (RG : Set (Language T)) := hLRsubsetRG hLR
  have hreg : (Language.map f anbn).IsRegular := isRegular_of_is_RG hRG
  exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf hreg)
