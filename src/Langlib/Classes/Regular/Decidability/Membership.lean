import Mathlib
import Langlib.Classes.ContextFree.Basics.Inclusion
import Langlib.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
import Langlib.Classes.ContextFree.Pumping.ParseTree

/-! # Decidability of Membership

This file proves that membership is decidable for
regular languages.
## Main results

- `regular_membership_decidable` – membership in a regular language is decidable
-/

open List Relation

/-! ## Part 1: Regular Languages -/

section Regular

variable {α σ : Type*}

/-- Membership in a DFA's accepted language is decidable. -/
private noncomputable def dfa_membership_decidable
    (M : DFA α σ) [DecidablePred (· ∈ M.accept)] (w : List α) :
    Decidable (w ∈ M.accepts) := by
  unfold DFA.accepts DFA.acceptsFrom
  change Decidable (M.evalFrom M.start w ∈ M.accept)
  infer_instance

/-- Membership in a regular language is decidable. -/
noncomputable def regular_membership_decidable
    (L : Language α) (hL : L.IsRegular) (w : List α) :
    Decidable (w ∈ L) := by
  classical
  let σ := Classical.choose hL
  let hσ := Classical.choose_spec hL
  let _ : Fintype σ := Classical.choose hσ
  let hσ' := Classical.choose_spec hσ
  let M : DFA α σ := Classical.choose hσ'
  let hM : M.accepts = L := Classical.choose_spec hσ'
  rw [← hM]
  exact dfa_membership_decidable M w

end Regular
