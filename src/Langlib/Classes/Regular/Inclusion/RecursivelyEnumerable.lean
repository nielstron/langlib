/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.Regular.Definition
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Grammars.RightRegular.UnrestrictedCharacterization

/-! # Regular Languages Included in Recursively Enumerable Languages

This file proves that every right-regular language is recursively enumerable.

## Main results

- `RG_subclass_RE` — every regular language is recursively enumerable
-/

open Relation Classical

noncomputable section

variable {T : Type}

/-- An RG transformation step corresponds to a grammar transformation step. -/
lemma grammar_transforms_of_RG_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : RG_transforms g w₁ w₂) :
    grammar_transforms (grammar_of_RG g) w₁ w₂ := by
  obtain ⟨r, hr, u, v, hw1, hw2⟩ := h
  exact ⟨⟨[], r.lhs, [], r.output⟩,
    ⟨List.mem_map.mpr ⟨r, hr, rfl⟩, u, v, by simpa using hw1, by simpa using hw2⟩⟩

/-- A grammar transformation step from a converted RG corresponds to an RG step. -/
lemma RG_transforms_of_grammar_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : grammar_transforms (grammar_of_RG g) w₁ w₂) :
    RG_transforms g w₁ w₂ := by
  obtain ⟨r, hr, u, v, hw1, hw2⟩ := h
  simp only [grammar_of_RG, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨r', hr', u, v, by simpa using hw1, by simpa using hw2⟩

/-- RG derives iff grammar derives (for the converted grammar). -/
lemma RG_derives_iff_grammar_derives (g : RG_grammar T)
    (w₁ w₂ : List (symbol T g.nt)) :
    RG_derives g w₁ w₂ ↔ grammar_derives (grammar_of_RG g) w₁ w₂ := by
  constructor
  · intro h
    induction h with
    | refl => exact grammar_deri_self
    | tail _ hs ih =>
      exact grammar_deri_of_deri_tran ih (grammar_transforms_of_RG_transforms hs)
  · intro h
    induction h with
    | refl => exact RG_deri_self _
    | tail _ hs ih =>
      exact RG_deri_of_deri_tran ih (RG_transforms_of_grammar_transforms hs)

/-- Every right-regular language is recursively enumerable. -/
theorem RG_subclass_RE {L : Language T} (h : is_RG L) : is_RE L := by
  obtain ⟨g, rfl⟩ := is_RG_implies_is_RG_via_rg h
  refine ⟨grammar_of_RG g, ?_⟩
  ext w
  simp only [grammar_language, RG_language]
  exact (RG_derives_iff_grammar_derives g _ _).symm

end
