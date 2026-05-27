import Langlib.Classes.ContextFree.Basics.Pumping
import Mathlib

/-! # The unary `{a^(2^(k+1))}` language

This file defines the unary language `{a^(2^(k+1)) | k in N}` over `Bool`,
with `false = a`, and proves it is not context-free.
-/

open Language Set List

/-- The unary language `{a^(2^(k+1)) | k in N}` over `Bool`, with `false` as `a`. -/
def unaryPow2 : Language Bool :=
  fun w => ∃ k : ℕ, w = List.replicate ((2 : ℕ) ^ (k + 1)) false

/-- The unary powers-of-two language is not context-free.

After pumping a word of length `2^(p+2)`, the new length is strictly between consecutive powers
of two. -/
lemma notCF_unaryPow2 : ¬ is_CF unaryPow2 := by
  intro hcf
  rcases CF_pumping hcf with ⟨p, hp⟩
  let k := p + 1
  let w := List.replicate ((2 : ℕ) ^ (k + 1)) false
  have hw : w ∈ unaryPow2 := ⟨k, rfl⟩
  have hlen : w.length ≥ p := by
    have hp_lt : p < (2 : ℕ) ^ (p + 2) := by
      have htmp : p + 2 < (2 : ℕ) ^ (p + 2) := Nat.lt_two_pow_self (n := p + 2)
      omega
    simpa [w, k] using le_of_lt hp_lt
  rcases hp w hw hlen with ⟨u, v, x, y, z, hsplit, hnonempty, hbound, hpump⟩
  let pumped := u ++ List.n_times v 2 ++ x ++ List.n_times y 2 ++ z
  have hpumped_mem : pumped ∈ unaryPow2 := by
    dsimp [pumped]
    simpa [List.n_times, nTimes] using hpump 2
  rcases hpumped_mem with ⟨j, hj⟩
  have hlen_pumped : pumped.length = (2 : ℕ) ^ (j + 1) := by
    rw [hj]
    simp
  have hdelta_pos : 0 < (v ++ y).length := hnonempty
  have hdelta_le : (v ++ y).length ≤ p := by
    calc
      (v ++ y).length ≤ (v ++ x ++ y).length := by simp [List.length_append]
      _ ≤ p := hbound
  have hpumped_len_formula : pumped.length = w.length + (v ++ y).length := by
    dsimp [pumped]
    rw [hsplit]
    simp [List.length_append, List.n_times]
    omega
  have hbetween_low : (2 : ℕ) ^ (k + 1) < (2 : ℕ) ^ (j + 1) := by
    rw [← hlen_pumped, hpumped_len_formula]
    dsimp [w]
    simp
    rw [List.length_append] at hdelta_pos
    omega
  have hbetween_high : (2 : ℕ) ^ (j + 1) < (2 : ℕ) ^ (k + 2) := by
    rw [← hlen_pumped]
    have hp_lt : p < (2 : ℕ) ^ (p + 2) := by
      have htmp : p + 2 < (2 : ℕ) ^ (p + 2) := Nat.lt_two_pow_self (n := p + 2)
      omega
    have hdelta_lt : (v ++ y).length < (2 : ℕ) ^ (p + 2) :=
      lt_of_le_of_lt hdelta_le hp_lt
    have hpow : (2 : ℕ) ^ (p + 3) =
        (2 : ℕ) ^ (p + 2) + (2 : ℕ) ^ (p + 2) := by
      rw [show p + 3 = (p + 2) + 1 by omega, pow_succ]
      ring
    calc
      pumped.length = w.length + (v ++ y).length := hpumped_len_formula
      _ = (2 : ℕ) ^ (p + 2) + (v ++ y).length := by simp [w, k]
      _ < (2 : ℕ) ^ (p + 2) + (2 : ℕ) ^ (p + 2) :=
        Nat.add_lt_add_left hdelta_lt _
      _ = (2 : ℕ) ^ (p + 3) := hpow.symm
      _ = (2 : ℕ) ^ (k + 2) := by simp [k]
  have hj_gt : k + 1 < j + 1 :=
    (pow_lt_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp hbetween_low
  have hj_lt : j + 1 < k + 2 :=
    (pow_lt_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp hbetween_high
  omega
