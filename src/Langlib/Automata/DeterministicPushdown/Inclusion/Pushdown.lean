/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlib.Automata.DeterministicPushdown.Definition
import Langlib.Automata.Pushdown.Basics.FinalStateEmptyStackEquiv

open PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

namespace DPDA

/-- Every language accepted by a DPDA via final-state acceptance is accepted by some PDA
    via empty-stack acceptance. -/
theorem is_PDA_acceptsByFinalState (M : DPDA Q T S) : is_PDA M.acceptsByFinalState :=
  PDA_FS_subset_ES M.toPDA

end DPDA

/-- The class of DPDA-recognizable languages is contained in the class of PDA-recognizable
    languages. -/
theorem DPDA_subclass_PDA {T : Type} [Fintype T] : (DPDA.Class : Set (Language T)) ⊆ PDA.Class := by
  intro L hL
  obtain ⟨Q, S, _, _, M, rfl⟩ := hL
  exact M.is_PDA_acceptsByFinalState
