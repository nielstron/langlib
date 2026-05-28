import Mathlib

/-! # The language `{a^n b^n}` -/

/-- The language `{aⁿbⁿ}` over `Bool`, where `false` represents `a` and `true` represents `b`. -/
def anbn : Language Bool :=
  { w | ∃ n : ℕ, w = List.replicate n false ++ List.replicate n true }
