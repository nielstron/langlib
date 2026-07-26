module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.Definition

@[expose]
public section

/-!
# Kernel-checked certificates on the `X = 0` face

This file replays the five exceptional words from the complementary-cycle
construction on the coordinate automata.  It also records the three literal
boundary certificates at `L = 0`, `R = 0, 1, 2`.

The proofs below use kernel reduction.  They certify the displayed words and
their lengths, but make no claim that the words are shortest.
-/

namespace DFA.CycleTree

/-- Parameters on the face `X = 0`. -/
def xZeroParams (R L : ℕ) : Params :=
  ⟨0, R, L⟩

private def wordXZeroRZeroLZero : List Letter :=
  decodeWord "spppspspppsps"

private def wordXZeroROneLZero : List Letter :=
  decodeWord "spppspspsppspspspsppspsspspppsps"

private def wordXZeroRTwoLZero : List Letter :=
  decodeWord
    "spppspspsppspspspsppspsspspsppspsspspsppspsspspppsps"

private def wordXZeroRThreeLOne : List Letter :=
  decodeWord
    "spppspsppspspspspsppspsspspspppspsppspspppspspsppsppspspspsppspsspspppspspsppspspspspspsppsppspspspppsps"

private def wordXZeroRThreeLTwo : List Letter :=
  decodeWord
    "spppspsspspppspspppspspsppspspspspspspspsppspsppspspppspspspspsppsppspspppspspppspsppspspspspspspsppsppspspppspspspsppsppspspspspspppsps"

private def wordXZeroRFourLOne : List Letter :=
  decodeWord
    "spppspsspspppspspsppspsppspspspspsppspsspspppspspsppspppspspspspsppsppspspspsppspsspspspppspsppspspspspsppsppspspspsppsppspspspppsps"

private def wordXZeroRFourLThree : List Letter :=
  decodeWord
    "spppspsppspspspspppspspspspsppspsspspppspppspspspspppspsppspspspspspspspspsppsppspppspppspspspspspsppsppspspspspspppspspsppspspspspspspspspspsppspsspspppspspspspspspsppsppspspspspppspspspsppsppspspspspspspspppsps"

private def wordXZeroRSixLTwo : List Letter :=
  decodeWord
    "spppspsppspspspspspspsppspsspspppspppspspppspsppspspspspspspsppsppspspspspspsppspsspspppspppspppspspsppspspspspspspspsppspsspspppspspspspsppsppspspppspspspsppsppspspspspspsppspsspspspspspspsppsppspppspspspspsppsppspspspspspsppsppspspspspspppsps"

private theorem length_x0_r0_l0 :
    wordXZeroRZeroLZero.length = 13 := by
  decide +kernel

private theorem length_x0_r1_l0 :
    wordXZeroROneLZero.length = 32 := by
  decide +kernel

private theorem length_x0_r2_l0 :
    wordXZeroRTwoLZero.length = 52 := by
  decide +kernel

private theorem length_x0_r3_l1 :
    wordXZeroRThreeLOne.length = 104 := by
  decide +kernel

private theorem length_x0_r3_l2 :
    wordXZeroRThreeLTwo.length = 136 := by
  decide +kernel

private theorem length_x0_r4_l1 :
    wordXZeroRFourLOne.length = 132 := by
  decide +kernel

private theorem length_x0_r4_l3 :
    wordXZeroRFourLThree.length = 212 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem length_x0_r6_l2 :
    wordXZeroRSixLTwo.length = 244 := by
  decide +kernel

private theorem reset_x0_r0_l0 :
    (automaton (xZeroParams 0 0)).IsResetWord wordXZeroRZeroLZero := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x0_r1_l0 :
    (automaton (xZeroParams 1 0)).IsResetWord wordXZeroROneLZero := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x0_r2_l0 :
    (automaton (xZeroParams 2 0)).IsResetWord wordXZeroRTwoLZero := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x0_r3_l1 :
    (automaton (xZeroParams 3 1)).IsResetWord wordXZeroRThreeLOne := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x0_r3_l2 :
    (automaton (xZeroParams 3 2)).IsResetWord wordXZeroRThreeLTwo := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x0_r4_l1 :
    (automaton (xZeroParams 4 1)).IsResetWord wordXZeroRFourLOne := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem reset_x0_r4_l3 :
    (automaton (xZeroParams 4 3)).IsResetWord wordXZeroRFourLThree := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

set_option maxRecDepth 4096 in
private theorem reset_x0_r6_l2 :
    (automaton (xZeroParams 6 2)).IsResetWord wordXZeroRSixLTwo := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

theorem safe_x0_r0_l0 :
    (automaton (xZeroParams 0 0)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x0_r0_l0 (by
    rw [length_x0_r0_l0]
    decide +kernel)

theorem safe_x0_r1_l0 :
    (automaton (xZeroParams 1 0)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x0_r1_l0 (by
    rw [length_x0_r1_l0]
    decide +kernel)

theorem safe_x0_r2_l0 :
    (automaton (xZeroParams 2 0)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x0_r2_l0 (by
    rw [length_x0_r2_l0]
    decide +kernel)

theorem safe_x0_r3_l1 :
    (automaton (xZeroParams 3 1)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x0_r3_l1 (by
    rw [length_x0_r3_l1]
    decide +kernel)

theorem safe_x0_r3_l2 :
    (automaton (xZeroParams 3 2)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x0_r3_l2 (by
    rw [length_x0_r3_l2]
    decide +kernel)

theorem safe_x0_r4_l1 :
    (automaton (xZeroParams 4 1)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x0_r4_l1 (by
    rw [length_x0_r4_l1]
    decide +kernel)

theorem safe_x0_r4_l3 :
    (automaton (xZeroParams 4 3)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x0_r4_l3 (by
    rw [length_x0_r4_l3]
    decide +kernel)

theorem safe_x0_r6_l2 :
    (automaton (xZeroParams 6 2)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _ reset_x0_r6_l2 (by
    rw [length_x0_r6_l2]
    decide +kernel)

end DFA.CycleTree
