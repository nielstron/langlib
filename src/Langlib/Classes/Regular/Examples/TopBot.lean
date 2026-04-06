import Mathlib

/-! # Trivial Regular Examples

This file provides the trivial regular-language witnesses `⊥` and `⊤`.
-/

namespace Language

variable {α : Type*}

/-- The empty language is regular. -/
theorem isRegular_bot : (⊥ : Language α).IsRegular := by
  rw [isRegular_iff]
  exact ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, by
    ext w
    simp [DFA.mem_accepts, DFA.eval]
    exact fun a => a.elim⟩

/-- The universal language is regular. -/
theorem isRegular_top : (⊤ : Language α).IsRegular := by
  rw [isRegular_iff]
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), (), Set.univ⟩, ?_⟩
  ext w
  constructor
  · intro _
    trivial
  · intro _
    simp [DFA.mem_accepts, DFA.eval, Set.mem_univ]

end Language
