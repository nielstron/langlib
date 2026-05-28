import Mathlib

/-! # The unary language `{a^(2^(k+1))}` -/

/-- The unary language `{a^(2^(k+1)) | k in N}` over `Bool`, with `false` as `a`. -/
def unaryPow2 : Language Bool :=
  fun w => ∃ k : ℕ, w = List.replicate ((2 : ℕ) ^ (k + 1)) false
