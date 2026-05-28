import Langlib.Examples.BnAn

/-! # The positive language `{b^n a^n}` -/

/-- The positive block language `{b^n a^n | n >= 1}` over `Bool`,
with `false = a` and `true = b`. -/
def quotientRightBlock : Language Bool :=
  fun w => ∃ n : ℕ, w = List.replicate (n + 1) true ++ List.replicate (n + 1) false
