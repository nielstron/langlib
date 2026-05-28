import Mathlib

/-! # The language `{b^n a^n}` -/

/-- The core block language `{b^n a^n | n in N}` over `Bool`,
with `false = a` and `true = b`. -/
def quotientRightBlockCore : Language Bool :=
  fun w => ∃ n : ℕ, w = List.replicate n true ++ List.replicate n false
