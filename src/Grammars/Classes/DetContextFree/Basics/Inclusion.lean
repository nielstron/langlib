/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Classes.DetContextFree.Basics.DCFL

/-! # DCFLs are a strict subset of CFLs

This file shows that DCFLs are a subset of the CFLs
and that they are a subset

--/

-- ============================================================================
-- DCFL inclusion into CFL
-- ============================================================================

theorem is_CF_of_is_DCFL {T : Type} [Fintype T] {L : Language T} (h : is_DCFL L) : is_CF L := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  exact is_CF_of_is_PDA M.is_PDA_acceptsByFinalState
