import Langlib.Examples.AnBnCn

/-! # The positive language `{a^n b^n c^n}` -/

/-- The language `{aⁿbⁿcⁿ | n ≥ 1}` over `Fin 3`. -/
def lang_eq_eq_pos : Language (Fin 3) :=
  fun w => ∃ n : ℕ, w = List.replicate (n + 1) (0 : Fin 3) ++
    List.replicate (n + 1) (1 : Fin 3) ++ List.replicate (n + 1) (2 : Fin 3)

/-- The singleton epsilon language over the shared `Fin 3` alphabet. -/
def lang_abc_epsilon : Language (Fin 3) :=
  fun w => w = []
