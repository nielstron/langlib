/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammars.Automata.DetPushdown.ClosureProperties.Complement
import Grammars.Classes.ContextFree.ClosureProperties.Complement
import Grammars.Classes.ContextFree.ClosureProperties.Intersection
import Grammars.Classes.ContextFree.ClosureProperties.IntersectionRegular
import Grammars.Classes.DetContextFree.Basics.DCF

/-! # Complement Properties of DCFs

This file collects complement-closure results and consequences for deterministic
context-free languages.
-/

open PDA

variable {T : Type} [Fintype T]

/-- **DCF Complement Closure**: The class of deterministic context-free languages is
    closed under complementation. -/
theorem is_DCF_compl {L : Language T} (h : is_DCF L) : is_DCF Lᶜ := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  obtain ⟨Q', S', _, _, M', hM'_lang, hM'_total⟩ := DPDA.exists_total_dpda M
  exact ⟨Q', S', _, _, M'.complement,
    by rw [DPDA.complement_acceptsByFinalState M' hM'_total, hM'_lang]⟩
