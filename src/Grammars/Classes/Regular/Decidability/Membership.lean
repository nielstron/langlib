import Mathlib
import Grammars.Classes.ContextFree.Basics.Inclusion
import Grammars.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
import Grammars.Classes.ContextFree.Pumping.ParseTree

/-! # Decidability of Membership

This file proves that membership is decidable for
regular languages
## Main results

- `regular_membership_decidable` – membership in a regular language (DFA) is decidable
-/

open List Relation

/-! ## Part 1: Regular Languages -/

section Regular

variable {α σ : Type*}

/-- Membership in a DFA's accepted language is decidable. -/
noncomputable def regular_membership_decidable
    (M : DFA α σ) [DecidablePred (· ∈ M.accept)] (w : List α) :
    Decidable (w ∈ M.accepts) := by
  unfold DFA.accepts DFA.acceptsFrom
  change Decidable (M.evalFrom M.start w ∈ M.accept)
  infer_instance

end Regular
