/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.Linear.Definition

/-! # Linear Language Inclusions

This file proves that every linear language is context-free.

## Main results

- `Linear_subclass_CF` — `Linear ⊆ CF`
-/

open Language List Relation Classical

noncomputable section

variable {T : Type}

/-- A linear output is trivially a valid context-free output (no additional restriction). -/
theorem grammar_context_free_of_linear {g : grammar T}
    (hg : grammar_linear g) : grammar_context_free g := by
  intro r hr
  exact ⟨(hg r hr).1, (hg r hr).2.1⟩

/-- Every linear language is context-free. -/
theorem is_CF_of_is_Linear {L : Language T} (h : is_Linear L) : is_CF L := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g, grammar_context_free_of_linear hg, rfl⟩

/-- The class of linear languages is a subclass of the context-free languages. -/
theorem Linear_subclass_CF :
    (Linear : Set (Language T)) ⊆ (CF : Set (Language T)) := by
  intro L hL
  exact is_CF_of_is_Linear hL
