import Langlib.Examples.AlphabetABC

/-! # The language `{a^n b^n c^n}` -/

/-- The language `{aⁿbⁿcⁿ | n ≥ 0}` over `Fin 3`. -/
def lang_eq_eq : Language (Fin 3) :=
  fun w => ∃ n : ℕ, w = List.replicate n a_ ++ List.replicate n b_ ++ List.replicate n c_
