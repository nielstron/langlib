module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.Definition

@[expose]
public section

/-!
# Kernel-checked finite cycle-tree certificates

The uniform words leave nine small synchronizing points on the residual
diagonal.  This file replays explicit words on the executable coordinate
automata.  It certifies only word validity and the Černý length bound, not
search minimality.
-/

namespace DFA.CycleTree

private def xOnePrefixOne : List Letter :=
  hTwoWord 1 1 ++
    wordPow aWord 6 ++ [.p] ++
    wordPow aWord 7 ++ [.p] ++
    wordPow aWord 8 ++ pSquared

private def xOnePrefixTwo : List Letter :=
  hTwoWord 1 2 ++
    wordPow aWord 3 ++ [.s] ++
    wordPow aWord 2 ++ pSquared ++
    wordPow aWord 3 ++ pSquared ++
    wordPow aWord 3 ++ [.p] ++
    aWord ++ pSquared ++
    wordPow aWord 5 ++ [.p] ++ sSquared

private def xOnePrefixThree : List Letter :=
  hTwoWord 1 3 ++
    wordPow aWord 3 ++ [.s] ++
    wordPow aWord 3 ++ pSquared ++
    wordPow aWord 6 ++ [.p] ++
    wordPow aWord 11 ++ [.p] ++ sSquared

private def xTwoSuffixThree : List Letter :=
  decodeWord
    "spspspspspspspspspspspspspsppspspspspspsspspspppspspspppspspspspsppspsppp"

private def xTwoSuffixFour : List Letter :=
  decodeWord
    "spspspspspsspspppspspspspspppspspspspsppspppspspspspspspspspsppss"

private def xTwoSuffixFive : List Letter :=
  decodeWord
    "spspspspspsspspspspspppspspspspspspspsppspspspspspspspspspspspspspspsppss"

private def xTwoSuffixSix : List Letter :=
  decodeWord
    "spspspspspsspspspppspspspspspspspspspspspsppspspspspspsspspspspspspspspspspspspspsppp"

private def xThreeSuffixEight : List Letter :=
  decodeWord
    "spspspspspspspsspspspspspppspspspspspspspspspspspspspsppspspspspspspspspspspspspspspspspspspspspspspspspsppss"

private def xThreeSuffixNine : List Letter :=
  decodeWord
    "spspspspspspspsspspspppspspspspspspspspspspspspspspspspspsppspspspspspspspsspspspspspspspspspspspspspspspspspsppp"

private def residualPrefix (X L : ℕ) (suffix : List Letter) : List Letter :=
  hTwoWord X L ++ suffix

private def completeResidualWord
    (X L : ℕ) (pre : List Letter) : List Letter :=
  let P := residualParams X L
  pre ++ dPowerWord P (P.cycle - 5)

private def wordXOneOne : List Letter :=
  completeResidualWord 1 1 xOnePrefixOne

private def wordXOneTwo : List Letter :=
  completeResidualWord 1 2 xOnePrefixTwo

private def wordXOneThree : List Letter :=
  completeResidualWord 1 3 xOnePrefixThree

private def wordXTwoThree : List Letter :=
  completeResidualWord 2 3 (residualPrefix 2 3 xTwoSuffixThree)

private def wordXTwoFour : List Letter :=
  completeResidualWord 2 4 (residualPrefix 2 4 xTwoSuffixFour)

private def wordXTwoFive : List Letter :=
  completeResidualWord 2 5 (residualPrefix 2 5 xTwoSuffixFive)

private def wordXTwoSix : List Letter :=
  completeResidualWord 2 6 (residualPrefix 2 6 xTwoSuffixSix)

private def wordXThreeEight : List Letter :=
  completeResidualWord 3 8 (residualPrefix 3 8 xThreeSuffixEight)

private def wordXThreeNine : List Letter :=
  completeResidualWord 3 9 (residualPrefix 3 9 xThreeSuffixNine)

/-!
The longest certificate is split into two independently kernel-checked
transition tables.  This avoids making the kernel normalize a single
2,274-letter fold while retaining a proof of the original word.
-/

private abbrev P39 := residualParams 3 9

private def prefix39 : List Letter :=
  residualPrefix 3 9 xThreeSuffixNine

private def block39 : List Letter :=
  dPowerWord P39 6

private def prefixMap39 (state : State P39) : State P39 :=
  P39.stateOfNat
    ([24, 17, 46, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 1, 30, 46, 32,
      33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 1, 45, 46, 47, 48, 8, 9,
      10, 11, 12, 13, 14, 15, 1, 17, 46, 19, 20, 21, 22, 23].getD state.val 0)

private def blockMap39 (state : State P39) : State P39 :=
  P39.stateOfNat
    ([12, 1, 47, 48, 8, 9, 10, 11, 12, 13, 14, 15, 1, 17, 1, 19, 20, 21,
      22, 23, 24, 25, 26, 27, 28, 1, 30, 1, 32, 33, 34, 35, 36, 37, 38, 39,
      40, 41, 42, 43, 1, 45, 1, 47, 48, 8, 9, 10, 11].getD state.val 0)

private theorem prefixMap39_correct :
    ∀ state,
      (automaton P39).evalFrom state prefix39 = prefixMap39 state := by
  decide +kernel

private theorem blockMap39_correct :
    ∀ state,
      (automaton P39).evalFrom state block39 = blockMap39 state := by
  decide +kernel +revert

private theorem wordXThreeNine_blocks :
    wordXThreeNine = prefix39 ++ wordPow block39 6 := by
  change prefix39 ++ dPowerWord P39 (P39.cycle - 5) =
    prefix39 ++ wordPow block39 6
  apply congrArg (prefix39 ++ ·)
  exact wordPow_mul (dWord P39) 6 6

private theorem reset_x1_l1 :
    (automaton (residualParams 1 1)).IsResetWord wordXOneOne := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x1_l2 :
    (automaton (residualParams 1 2)).IsResetWord wordXOneTwo := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x1_l3 :
    (automaton (residualParams 1 3)).IsResetWord wordXOneThree := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x2_l3 :
    (automaton (residualParams 2 3)).IsResetWord wordXTwoThree := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x2_l4 :
    (automaton (residualParams 2 4)).IsResetWord wordXTwoFour := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x2_l5 :
    (automaton (residualParams 2 5)).IsResetWord wordXTwoFive := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x2_l6 :
    (automaton (residualParams 2 6)).IsResetWord wordXTwoSix := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x3_l8 :
    (automaton (residualParams 3 8)).IsResetWord wordXThreeEight := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x3_l9 :
    (automaton (residualParams 3 9)).IsResetWord wordXThreeNine := by
  refine ⟨P39.stateOfNat 1, ?_⟩
  intro state
  rw [wordXThreeNine_blocks, DFA.evalFrom_of_append, prefixMap39_correct]
  simp only [show (6 : ℕ) = 5 + 1 by omega, wordPow_succ,
    wordPow_zero, DFA.evalFrom_of_append, DFA.evalFrom_nil,
    blockMap39_correct]
  decide +kernel +revert

theorem safe_x1_l1 :
    (automaton (residualParams 1 1)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x1_l1 (by decide +kernel)

theorem safe_x1_l2 :
    (automaton (residualParams 1 2)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x1_l2 (by decide +kernel)

theorem safe_x1_l3 :
    (automaton (residualParams 1 3)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x1_l3 (by decide +kernel)

theorem safe_x2_l3 :
    (automaton (residualParams 2 3)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x2_l3 (by decide +kernel)

theorem safe_x2_l4 :
    (automaton (residualParams 2 4)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x2_l4 (by decide +kernel)

theorem safe_x2_l5 :
    (automaton (residualParams 2 5)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x2_l5 (by decide +kernel)

theorem safe_x2_l6 :
    (automaton (residualParams 2 6)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x2_l6 (by decide +kernel)

theorem safe_x3_l8 :
    (automaton (residualParams 3 8)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x3_l8 (by decide +kernel)

theorem safe_x3_l9 :
    (automaton (residualParams 3 9)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x3_l9 (by decide +kernel)

end DFA.CycleTree
