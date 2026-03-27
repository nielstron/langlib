import Mathlib
import Grammars.Classes.Regular.ClosureProperties.Complement
import Grammars.Classes.Regular.Decidability.Emptiness

/-! # Decidability of Universality

This file proves that universality is decidable for
regular languages.

## Main results

- `regular_universality_decidable` – universality of a regular language is decidable
-/

section Regular

variable {α : Type*}

/-- Universality of a regular language is decidable. -/
noncomputable def regular_universality_decidable
    [Fintype α] [DecidableEq α] (L : Language α) (hL : L.IsRegular) :
    Decidable (L = (⊤ : Set (List α))) := by
  change Decidable (L = (Set.univ : Set (List α)))
  rw [← Set.compl_empty_iff]
  exact regular_emptiness_decidable Lᶜ hL.compl

end Regular
