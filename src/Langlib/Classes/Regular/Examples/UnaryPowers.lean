module

public import Langlib.Classes.Regular.Basics.Unary
import Mathlib.Tactic

@[expose]
public section

/-!
# Unary powers of two

The unary language whose accepted lengths are powers of two is not regular.  The proof uses the
ultimate-periodicity characterization of unary regular languages: beyond the threshold, adding a
positive period to a sufficiently large power of two would have to produce another power of two,
but the result lies strictly between two consecutive powers.
-/

namespace Language

/-- The unary language `{ a^(2^k) | k ∈ ℕ }`, represented over `Unit`. -/
public def unaryPowersOfTwo : Language Unit :=
  fun w => ∃ k : ℕ, w = List.replicate (2 ^ k) ()

@[simp]
public theorem replicate_mem_unaryPowersOfTwo_iff (n : ℕ) :
    List.replicate n () ∈ unaryPowersOfTwo ↔ ∃ k : ℕ, n = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, List.replicate_left_injective () hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

/-- The unary powers-of-two language is not regular. -/
public theorem unaryPowersOfTwo_not_isRegular :
    ¬ unaryPowersOfTwo.IsRegular := by
  intro hregular
  obtain ⟨N, p, hp, hperiod⟩ :=
    (isRegular_iff_lengthUltimatelyPeriodic unaryPowersOfTwo).mp hregular
  let k := max N p + 1
  have hkpow : k < 2 ^ k := Nat.lt_two_pow_self
  have hNpow : N ≤ 2 ^ k := by
    have hNk : N < k := by
      dsimp [k]
      omega
    omega
  have hppow : p < 2 ^ k := by
    have hpk : p < k := by
      dsimp [k]
      omega
    omega
  have hpowMem : List.replicate (2 ^ k) () ∈ unaryPowersOfTwo :=
    (replicate_mem_unaryPowersOfTwo_iff _).2 ⟨k, rfl⟩
  have hshiftMem :
      List.replicate (2 ^ k + p) () ∈ unaryPowersOfTwo :=
    (hperiod (2 ^ k) hNpow).1 hpowMem
  obtain ⟨j, hj⟩ :=
    (replicate_mem_unaryPowersOfTwo_iff (2 ^ k + p)).1 hshiftMem
  have hlow : 2 ^ k < 2 ^ j :=
    (Nat.lt_add_of_pos_right hp).trans_eq hj
  have hhigh : 2 ^ j < 2 ^ (k + 1) := by
    calc
      2 ^ j = 2 ^ k + p := hj.symm
      _ < 2 ^ k + 2 ^ k := Nat.add_lt_add_left hppow (2 ^ k)
      _ = 2 ^ (k + 1) := (Nat.two_pow_succ k).symm
  have hkj : k < j :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 hlow
  have hjk : j < k + 1 :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 hhigh
  omega

end Language
