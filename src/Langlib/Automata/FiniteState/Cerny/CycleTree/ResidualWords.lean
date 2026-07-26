module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.ArithmeticCoverage
public import Langlib.Automata.FiniteState.Cerny.CycleTree.DepthPrefix
import Mathlib.Tactic.Linarith

@[expose]
public section

/-!
# Uniform words on the final residual diagonal

This module records the two five-depth prefixes from the residual proof,
their exact original-letter costs, and the theorem reducing their reset
claims to pointwise prefix-image identities.
-/

namespace DFA.CycleTree

/-- The prefix `V` used on `3X + 2 ≤ L ≤ 5X + 2`. -/
def middlePrefix (X L : ℕ) : List Letter :=
  let P := residualParams X L
  aWord ++ pSquared ++
    wordPow aWord (P.ell - 1) ++ [.s] ++
    wordPow aWord (2 * P.ell) ++ pSquared ++
    wordPow aWord (2 * L - 4 * X - 1) ++ [.p] ++
    wordPow aWord (4 * L - 6 * X) ++ [.p] ++
    wordPow aWord (P.ell - 1) ++ [.s] ++
    wordPow aWord (10 * X + 6 - 2 * L) ++ pSquared

/-- The prefix `U` used on `5X + 3 ≤ L`. -/
def largePrefix (X L : ℕ) : List Letter :=
  let P := residualParams X L
  aWord ++ pSquared ++
    wordPow aWord (P.ell - 1) ++ [.s] ++
    wordPow aWord (4 * X + 4) ++ pSquared ++
    wordPow aWord (2 * L - 4 * X - 1) ++ [.p] ++
    wordPow aWord (P.ell - 1) ++ [.s] ++
    wordPow aWord (8 * X + 7) ++ pSquared ++
    wordPow aWord (2 * L - 8 * X - 4) ++ [.p] ++ sSquared

/-- Exact original-letter cost of the middle-band prefix. -/
theorem length_middlePrefix {X L : ℕ} (hmiddle : Middle X L) :
    (middlePrefix X L).length = 8 * L + 16 * X + 34 := by
  rcases hmiddle with ⟨hlower, hupper⟩
  simp only [middlePrefix, List.length_append, List.length_cons,
    List.length_nil, length_wordPow, length_aWord, length_pSquared,
    Params.ell, residualParams]
  omega

/-- Exact original-letter cost of the large-band prefix. -/
theorem length_largePrefix {X L : ℕ} (hlarge : Large X L) :
    (largePrefix X L).length = 8 * L + 8 * X + 30 := by
  simp only [Large] at hlarge
  simp only [largePrefix, List.length_append, List.length_cons,
    List.length_nil, length_wordPow, length_aWord, length_pSquared,
    length_sSquared, Params.ell, residualParams]
  omega

theorem residual_cycle_sub_five (X L : ℕ) :
    (residualParams X L).cycle - 5 = 4 * L := by
  simp [residualParams, Params.cycle]
  omega

theorem residual_dWord_length (X L : ℕ) :
    (dWord (residualParams X L)).length =
      4 * X + 4 * L + 10 := by
  simp [residualParams, Params.m]
  omega

theorem residual_order_sub_one (X L : ℕ) :
    (residualParams X L).order - 1 = 2 * X + 4 * L + 6 := by
  simp [residualParams, Params.order, Params.ell, Params.cycle]
  omega

/-- The complete middle-band word is strictly inside the Černý bound. -/
theorem middlePrefix_total_length_lt_bound {X L : ℕ}
    (hmiddle : Middle X L) :
    (middlePrefix X L).length +
        ((residualParams X L).cycle - 5) *
          (4 * (residualParams X L).m + 2) <
      ((residualParams X L).order - 1) ^ 2 := by
  rw [length_middlePrefix hmiddle, residual_cycle_sub_five,
    residual_order_sub_one]
  simp only [residualParams, Params.m]
  nlinarith [Nat.zero_le X]

/-- The complete large-band word is strictly inside the Černý bound. -/
theorem largePrefix_total_length_lt_bound {X L : ℕ}
    (hlarge : Large X L) :
    (largePrefix X L).length +
        ((residualParams X L).cycle - 5) *
          (4 * (residualParams X L).m + 2) <
      ((residualParams X L).order - 1) ^ 2 := by
  rw [length_largePrefix hlarge, residual_cycle_sub_five,
    residual_order_sub_one]
  simp only [residualParams, Params.m]
  nlinarith [Nat.zero_le X]

/-- Once the middle prefix-image identity is known, the generic depth
theorem supplies the complete reset proof and bound. -/
theorem middle_satisfiesCerny_of_prefix_image {X L : ℕ}
    (hcoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle)
    (hmiddle : Middle X L)
    (himage :
      PrefixAvoidsDeep (residualParams X L) (middlePrefix X L) 5) :
    (automaton (residualParams X L)).SatisfiesCerny := by
  apply satisfiesCerny_of_prefix_avoidsDeep
    (residualParams X L) hcoprime (middlePrefix X L) 5
  · omega
  · simp only [residualParams, Params.cycle]
    omega
  · exact himage
  · exact Nat.le_of_lt (middlePrefix_total_length_lt_bound hmiddle)

/-- Once the large prefix-image identity is known, the generic depth
theorem supplies the complete reset proof and bound. -/
theorem large_satisfiesCerny_of_prefix_image {X L : ℕ}
    (hcoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle)
    (hlarge : Large X L)
    (himage :
      PrefixAvoidsDeep (residualParams X L) (largePrefix X L) 5) :
    (automaton (residualParams X L)).SatisfiesCerny := by
  apply satisfiesCerny_of_prefix_avoidsDeep
    (residualParams X L) hcoprime (largePrefix X L) 5
  · omega
  · simp only [residualParams, Params.cycle]
    omega
  · exact himage
  · exact Nat.le_of_lt (largePrefix_total_length_lt_bound hlarge)

end DFA.CycleTree
