/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.DeterministicContextFree.Definition

/-! # DCFs are a strict subset of CFLs

This file shows that DCFs are a subset of the CFLs
and that they are a subset

--/

-- ============================================================================
-- DCF inclusion into CFL
-- ============================================================================

theorem is_CF_of_is_DCF {T : Type} [Fintype T] {L : Language T} (h : is_DCF L) : is_CF L := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  exact is_CF_of_is_PDA M.is_PDA_acceptsByFinalState

/-- The class of deterministic context-free languages is contained in the class of
    context-free languages. -/
theorem DCF_subclass_CF {T : Type} [Fintype T] : (DCF : Set (Language T)) ⊆ CF :=
  fun _ h => is_CF_of_is_DCF h
