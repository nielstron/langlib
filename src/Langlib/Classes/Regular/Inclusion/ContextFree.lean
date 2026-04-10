/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.Regular.Definition
import Langlib.Classes.ContextFree.Definition
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Grammars.RightRegular.UnrestrictedCharacterization
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization

/-! # Regular Languages Included in Context-Free Languages

This file proves that every right-regular language is context-free.

## Main results

- `is_CF_of_is_RG` — every regular language is context-free
- `RG_subclass_CF` — `RG ⊆ CF`
-/

open Relation Classical

noncomputable section

variable {T : Type}

/-- Convert a right-regular grammar to a context-free grammar. -/
def CF_grammar_of_RG (g : RG_grammar T) : CF_grammar T where
  nt := g.nt
  initial := g.initial
  rules := g.rules.map fun r => (r.lhs, r.output)

lemma CF_transforms_of_RG_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : RG_transforms g w₁ w₂) :
    CF_transforms (CF_grammar_of_RG g) w₁ w₂ := by
  obtain ⟨r, hr, u, v, hw1, hw2⟩ := h
  exact ⟨(r.lhs, r.output), u, v, List.mem_map.mpr ⟨r, hr, rfl⟩, hw1, hw2⟩

lemma RG_transforms_of_CF_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_transforms (CF_grammar_of_RG g) w₁ w₂) :
    RG_transforms g w₁ w₂ := by
  obtain ⟨r, u, v, hr, hw1, hw2⟩ := h
  simp only [CF_grammar_of_RG, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨r', hr', u, v, hw1, hw2⟩

lemma RG_derives_iff_CF_derives (g : RG_grammar T)
    (w₁ w₂ : List (symbol T g.nt)) :
    RG_derives g w₁ w₂ ↔ CF_derives (CF_grammar_of_RG g) w₁ w₂ := by
  constructor
  · intro h
    induction h with
    | refl => exact CF_deri_self
    | tail _ hs ih =>
      exact CF_deri_of_deri_tran ih (CF_transforms_of_RG_transforms hs)
  · intro h
    induction h with
    | refl => exact RG_deri_self _
    | tail _ hs ih =>
      exact RG_deri_of_deri_tran ih (RG_transforms_of_CF_transforms hs)

/-- Every right-regular language is context-free. -/
theorem is_CF_of_is_RG {L : Language T} (h : is_RG L) : is_CF L := by
  obtain ⟨g, rfl⟩ := is_RG_implies_is_RG_via_rg h
  apply is_CF_via_cfg_implies_is_CF
  refine ⟨CF_grammar_of_RG g, ?_⟩
  ext w
  simp only [CF_language, RG_language]
  exact (RG_derives_iff_CF_derives g _ _).symm

theorem RG_subclass_CF :
  (RG : Set (Language T)) ⊆ (CF : Set (Language T)) := by
  intro L hL
  exact is_CF_of_is_RG hL

end
