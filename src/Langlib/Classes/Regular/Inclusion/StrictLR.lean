module

/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Regular.Definition
public import Langlib.Classes.LR.Examples.AnBn
import Langlib.Classes.Regular.Inclusion.StrictDeterministicContextFree
import Langlib.Classes.LR.Closure.Bijection
import Langlib.Classes.Regular.Examples.AnBn
import Langlib.Classes.Regular.Inclusion.LR
import Langlib.Classes.Regular.Closure.Bijection
import Langlib.Automata.FiniteState.Equivalence.Regular
import Langlib.Grammars.LR.Equivalence
import Mathlib

@[expose]
public section

/-! # RG ⊊ LR

This file proves that regular languages form a strict subclass of LR languages.

The witness is the language `{aⁿbⁿ}`, which is LR(1) (via `cfg_anbn`) but not
regular (by the pumping lemma). Combined with the already-established inclusion
`RG ⊆ LR`, this gives strict containment.

## Main results

- `RG_strict_subclass_LRk` — `RG ⊊ LR(k)` for every fixed `k > 0`.
- `RG_strict_subclass_LR` — `RG ⊊ LR` over any nontrivial finite alphabet.
-/

/-- For every fixed positive `k`, regular languages are a strict subclass of
LR(k) languages over every nontrivial finite alphabet. -/
public theorem RG_strict_subclass_LRk {T : Type} [Fintype T] [Nontrivial T]
    (k : ℕ) (hk : 0 < k) :
    (RG : Set (Language T)) ⊂ (LRk (T := T) k : Set (Language T)) := by
  rw [LRk_eq_DCF k hk]
  exact RG_strict_subclass_DCF

/-- For every fixed positive `k`, regular languages are a strict subclass of
LR(k) languages over every finite alphabet with at least two symbols. -/
public theorem RG_strict_subclass_LRk_of_card {T : Type} [Fintype T]
    (k : ℕ) (hk : 0 < k) (hT : 2 ≤ Fintype.card T) :
    (RG : Set (Language T)) ⊂ (LRk (T := T) k : Set (Language T)) := by
  letI : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact RG_strict_subclass_LRk k hk

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

/-- Regular languages are a strict subclass of existential finite-lookahead
LR languages over every finite alphabet with at least two symbols. -/
public theorem RG_strict_subclass_LR_of_card {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (RG : Set (Language T)) ⊂ (LR : Set (Language T)) := by
  letI : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact RG_strict_subclass_LR
