import Langlib.Classes.DeterministicContextFree.Examples.AnBnCm

/-! # The language `{a^n b^n c^n}`

This file defines the diagonal language used as the non-context-free
intersection of the two deterministic context-free examples over `Fin 3`.
-/

/-- The language `{aⁿbⁿcⁿ | n ≥ 0}` over `Fin 3`. -/
def lang_eq_eq : Language (Fin 3) :=
  fun w => ∃ n : ℕ, w = List.replicate n a_ ++ List.replicate n b_ ++ List.replicate n c_
