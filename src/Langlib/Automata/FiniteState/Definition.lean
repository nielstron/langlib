import Mathlib
import Langlib.Classes.Regular.Definition

/-! We just take over the Mathlib DFA/NFA automaton definition -/

variable {T : Type}

/-- A language is `DFA`-recognizable if it is accepted by some finite-state deterministic
automaton in Mathlib's sense. -/
def is_DFA (L : Language T) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : DFA T σ, M.accepts = L

/-- The class of DFA-recognizable languages.

This lives under `DFA.Class` because the top-level name `DFA` is already used by Mathlib's
automaton type. -/
def DFA.Class : Set (Language T) :=
  setOf is_DFA
