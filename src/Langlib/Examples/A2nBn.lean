import Mathlib

/-! # The language `{a^(2n)b^n}` -/

/-- The core block language `{a^(2n)b^n | n in N}` over `Bool`,
with `false = a` and `true = b`. -/
def quotientLeftBlockCore : Language Bool :=
  fun w => ∃ n : ℕ, w = List.replicate (2 * n) false ++ List.replicate n true
