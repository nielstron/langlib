import Langlib.Examples.A2nBn

/-! # The positive language `{a^(2n)b^n}` -/

/-- The positive block language `{a^(2n)b^n | n >= 1}` over `Bool`,
with `false = a` and `true = b`. -/
def quotientLeftBlock : Language Bool :=
  fun w => ∃ n : ℕ, w = List.replicate (2 * (n + 1)) false ++ List.replicate (n + 1) true
