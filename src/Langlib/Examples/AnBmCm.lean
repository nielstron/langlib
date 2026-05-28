import Langlib.Examples.AlphabetABC

/-! # The language `{a^n b^m c^m}` -/

/-- The language `{aⁿbᵐcᵐ | n,m ≥ 0}` over `Fin 3`. -/
def lang_any_eq : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n a_ ++ List.replicate m b_ ++ List.replicate m c_
