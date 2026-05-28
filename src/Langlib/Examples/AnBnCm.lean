import Langlib.Examples.AlphabetABC

/-! # The language `{a^n b^n c^m}` -/

/-- The language `{aⁿbⁿcᵐ | n,m ≥ 0}` over `Fin 3`. -/
def lang_eq_any : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n a_ ++ List.replicate n b_ ++ List.replicate m c_
