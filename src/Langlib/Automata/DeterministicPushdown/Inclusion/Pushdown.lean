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
