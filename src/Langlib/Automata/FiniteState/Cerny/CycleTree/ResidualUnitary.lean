module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.GeneralDirectCut
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose]
public section

/-!
# A short unitary word on the residual diagonal

This module formalizes the unitary construction on `R = L + 1`.  The
prefix compresses the full state set to the interval `J`; a rank
`cycle - 1` block then deletes the unique deepest point of a cut
rotation, allowing `cycle - 2` loop blocks to finish the reset.
-/

namespace DFA.CycleTree

open Params

/-- The odd chord `b = 2(L-X)+1` of the residual unitary. -/
def residualChord (X L : ℕ) : ℕ :=
  2 * (L - X) + 1

/-- Compression prefix `F_J = A^ell s²`. -/
def residualFJWord (X L : ℕ) : List Letter :=
  let P := residualParams X L
  wordPow aWord P.ell ++ sSquared

/-- The rank-`M-1` unitary `T = p² A^(ell-1) s² C^(ell-1)`. -/
def residualUnitaryBlock (X L : ℕ) : List Letter :=
  let P := residualParams X L
  pSquared ++ wordPow aWord (P.ell - 1) ++ sSquared ++
    wordPow cWord (P.ell - 1)

/-- The cut-loop block `V = C^b T`. -/
def residualLoopBlock (X L : ℕ) : List Letter :=
  wordPow cWord (residualChord X L) ++
    residualUnitaryBlock X L

/-- The loop root, obtained by moving the exceptional index forward by
the unitary chord. -/
def residualRootIndex (X L : ℕ) :
    Fin (residualParams X L).cycle :=
  cycleAdvance (residualParams X L)
    (rhoIndex (residualParams X L)) (residualChord X L)

/-- The complete candidate `F_J T V^(M-2)`. -/
def residualUnitaryWord (X L : ℕ) : List Letter :=
  let P := residualParams X L
  residualFJWord X L ++ residualUnitaryBlock X L ++
    wordPow (residualLoopBlock X L) (P.cycle - 2)

private theorem cycleAdvance_add (P : Params)
    (index : Fin P.cycle) (left right : ℕ) :
    cycleAdvance P (cycleAdvance P index left) right =
      cycleAdvance P index (left + right) := by
  apply Fin.ext
  change
    (((index.val + left) % P.cycle + right) % P.cycle) =
      (index.val + (left + right)) % P.cycle
  conv_lhs =>
    rw [Nat.add_mod]
  simp only [Nat.mod_mod]
  conv_rhs =>
    rw [show index.val + (left + right) =
      (index.val + left) + right by omega, Nat.add_mod]

private theorem evalFrom_pSquared_intervalState (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (intervalState P index) pSquared =
      if index.val = 0 then P.stateOfNat 0
      else if index = rhoIndex P then P.stateOfNat 1
      else intervalState P index := by
  rw [evalFrom_pSquared]
  have hstateVal := intervalState_val P index
  rw [hstateVal]
  have hnotZero : P.ell + index.val ≠ 0 := by
    have := P.ell_pos
    omega
  have hnotOne : P.ell + index.val ≠ 1 := by
    have hellTwo : 2 ≤ P.ell := by simp [Params.ell]
    omega
  rw [if_neg hnotZero, if_neg hnotOne]
  by_cases hindexZero : index.val = 0
  · rw [if_pos hindexZero]
    have hcoordinate : P.ell + index.val = P.ell := by omega
    rw [if_pos hcoordinate]
  · rw [if_neg hindexZero]
    have hnotEll : P.ell + index.val ≠ P.ell := by omega
    rw [if_neg hnotEll]
    by_cases hindexRho : index = rhoIndex P
    · rw [if_pos hindexRho]
      have hcoordinate :
          P.ell + index.val = P.rho := by
        rw [hindexRho]
        exact ell_add_rhoIndex P
      rw [if_pos hcoordinate]
    · rw [if_neg hindexRho]
      have hnotRho : P.ell + index.val ≠ P.rho := by
        intro heq
        apply hindexRho
        apply Fin.ext
        have hrho := ell_add_rhoIndex P
        omega
      rw [if_neg hnotRho]

private theorem residualRootIndex_val {X L : ℕ}
    (hLX : X ≤ L) :
    (residualRootIndex X L).val = 4 * L - 2 * X + 4 := by
  change
    (((rhoIndex (residualParams X L)).val +
      residualChord X L) % (residualParams X L).cycle) =
      4 * L - 2 * X + 4
  rw [rhoIndex_val]
  have hcoordinate :
      2 * (residualParams X L).R + 1 +
          residualChord X L =
        4 * L - 2 * X + 4 := by
    simp [residualParams, residualChord]
    omega
  rw [hcoordinate, Nat.mod_eq_of_lt]
  simp [residualParams, Params.cycle]
  omega

private theorem residualRootIndex_ne_rho {X L : ℕ}
    (hLX : X ≤ L) :
    residualRootIndex X L ≠ rhoIndex (residualParams X L) := by
  intro heq
  have heqVal := congrArg Fin.val heq
  rw [residualRootIndex_val hLX, rhoIndex_val] at heqVal
  simp only [residualParams] at heqVal
  omega

private theorem retreat_ell_pred_zero_eq_root {X L : ℕ}
    (hLX : X ≤ L) :
    (cyclePrev (residualParams X L))^[
        (residualParams X L).ell - 1]
        ⟨0, (residualParams X L).cycle_pos⟩ =
      residualRootIndex X L := by
  let P := residualParams X L
  let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
  have hinjective :
      Function.Injective ((cycleNext P)^[P.ell - 1]) :=
    (show Function.LeftInverse
        ((cyclePrev P)^[P.ell - 1])
        ((cycleNext P)^[P.ell - 1]) from
      fun index => iterate_cyclePrev_cycleNext P index (P.ell - 1)).injective
  apply hinjective
  rw [iterate_cycleNext_cyclePrev P zeroIndex (P.ell - 1)]
  rw [iterate_cycleNext]
  unfold residualRootIndex
  rw [cycleAdvance_add]
  apply Fin.ext
  change
    0 = (((rhoIndex P).val +
      (residualChord X L + (P.ell - 1))) % P.cycle)
  have hsum :
      (rhoIndex P).val +
          (residualChord X L + (P.ell - 1)) =
        P.cycle := by
    dsimp only [P]
    simp only [rhoIndex_val, residualParams, residualChord,
      Params.ell, Params.cycle]
    omega
  rw [hsum]
  simp

/-- Exact action of `T`: it fixes every interval coordinate except
`rhoIndex`, which is moved to `residualRootIndex`. -/
theorem evalFrom_residualUnitaryBlock_intervalState {X L : ℕ}
    (hLX : X ≤ L)
    (index : Fin (residualParams X L).cycle) :
    (automaton (residualParams X L)).evalFrom
        (intervalState (residualParams X L) index)
        (residualUnitaryBlock X L) =
      if index = rhoIndex (residualParams X L)
      then intervalState (residualParams X L)
        (residualRootIndex X L)
      else intervalState (residualParams X L) index := by
  let P := residualParams X L
  let count := P.ell - 1
  have hcountPos : 0 < count := by
    dsimp only [count, P]
    simp [residualParams, Params.ell]
  rw [residualUnitaryBlock]
  simp only [DFA.evalFrom_of_append]
  rw [evalFrom_pSquared_intervalState]
  by_cases hindexRho : index = rhoIndex P
  · have hindexNotZero : index.val ≠ 0 := by
      rw [hindexRho, rhoIndex_val]
      omega
    rw [if_neg hindexNotZero, if_pos hindexRho,
      if_pos hindexRho]
    have honeLt : 1 < P.order := by
      have := P.ell_lt_order
      simp [Params.ell] at this ⊢
      omega
    have honeVal : (P.stateOfNat 1).val = 1 :=
      stateOfNat_val_of_lt P honeLt
    have hbefore :
        (P.stateOfNat 1).val + count < P.order := by
      rw [honeVal]
      dsimp only [count]
      have := P.ell_lt_order
      omega
    rw [evalFrom_aPower_before_wrap P (P.stateOfNat 1)
      count (by rw [honeVal]; omega) hbefore]
    have hcoordinate : 1 + count = P.ell := by
      dsimp only [count]
      have := P.ell_pos
      omega
    rw [honeVal, hcoordinate]
    let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
    change
      (automaton P).evalFrom
          ((automaton P).evalFrom (intervalState P zeroIndex)
            sSquared)
          (wordPow cWord count) =
        intervalState P (residualRootIndex X L)
    rw [evalFrom_sSquared_intervalState,
      evalFrom_cPower_intervalState]
    exact congrArg (intervalState P)
      (retreat_ell_pred_zero_eq_root hLX)
  · rw [if_neg hindexRho]
    by_cases hindexZero : index.val = 0
    · rw [if_pos hindexZero]
      let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
      have hindex : index = zeroIndex := Fin.ext hindexZero
      subst index
      rw [← cycleState_zero P,
        evalFrom_aPower_cycleState,
        evalFrom_sSquared_cycleState,
        evalFrom_cPower_intervalState,
        iterate_cyclePrev_cycleNext]
      have hnot :
          zeroIndex ≠ rhoIndex (residualParams X L) :=
        hindexRho
      rw [if_neg hnot]
    · rw [if_neg hindexZero]
      rw [evalFrom_aPower_intervalState_of_pos P index count
        hcountPos, evalFrom_sSquared_cycleState,
        evalFrom_cPower_intervalState,
        iterate_cyclePrev_cycleNext]
      have hnot :
          index ≠ rhoIndex (residualParams X L) :=
        hindexRho
      rw [if_neg hnot]

/-- The compression prefix sends every state into the invariant interval
`J`. -/
theorem residualFJWord_image_interval {X L : ℕ}
    (hLX : X ≤ L)
    (state : State (residualParams X L)) :
    ∃ index : Fin (residualParams X L).cycle,
      (automaton (residualParams X L)).evalFrom state
          (residualFJWord X L) =
        intervalState (residualParams X L) index := by
  let P := residualParams X L
  rw [residualFJWord, (automaton P).evalFrom_of_append]
  by_cases hzero : state.val = 0
  · let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
    let imageIndex := (cycleNext P)^[P.ell] zeroIndex
    refine ⟨imageIndex, ?_⟩
    have hstate : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    rw [hstate, ← cycleState_zero P,
      evalFrom_aPower_cycleState P zeroIndex P.ell,
      evalFrom_sSquared_cycleState]
  · by_cases htail : state.val < P.ell
    · have hstatePos : 0 < state.val := Nat.pos_of_ne_zero hzero
      have hbefore :
          state.val + P.ell < P.order := by
        have hstateLt :
            state.val < (residualParams X L).order :=
          state.isLt
        change
          state.val + (residualParams X L).ell <
            (residualParams X L).order
        change
          state.val < (residualParams X L).ell at htail
        simp only [residualParams, Params.ell, Params.order,
          Params.cycle] at htail hstateLt ⊢
        omega
      have hindexLt : state.val < P.cycle := by
        change
          state.val < (residualParams X L).cycle
        change
          state.val < (residualParams X L).ell at htail
        simp only [residualParams, Params.ell, Params.cycle]
          at htail ⊢
        omega
      let index : Fin P.cycle := ⟨state.val, hindexLt⟩
      refine ⟨index, ?_⟩
      rw [evalFrom_aPower_before_wrap P state P.ell
        hstatePos hbefore, evalFrom_sSquared]
      have hcoordinateVal :
          (P.stateOfNat (state.val + P.ell)).val =
            state.val + P.ell :=
        stateOfNat_val_of_lt P hbefore
      rw [if_neg (by rw [hcoordinateVal]; omega)]
      unfold intervalState
      dsimp only [index]
      exact congrArg P.stateOfNat
        (Nat.add_comm state.val P.ell)
    · have hinterval : P.ell ≤ state.val := by omega
      obtain ⟨index, hstate⟩ :=
        exists_intervalState_eq P state hinterval
      refine
        ⟨(cycleNext P)^[P.ell] index, ?_⟩
      rw [← hstate]
      have hellPos : 0 < P.ell := P.ell_pos
      rw [evalFrom_aPower_intervalState_of_pos P index P.ell
        hellPos, evalFrom_sSquared_cycleState]

private theorem residual_chord_add_twice_m {X L : ℕ}
    (hLX : X ≤ L) :
    residualChord X L + 2 * (residualParams X L).m =
      (residualParams X L).cycle := by
  simp [residualChord, residualParams, Params.m, Params.cycle]
  omega

private theorem residual_cPower_chord_index {X L : ℕ}
    (hLX : X ≤ L)
    (index : Fin (residualParams X L).cycle) :
    (cyclePrev (residualParams X L))^[residualChord X L] index =
      dIndex (residualParams X L) index := by
  let P := residualParams X L
  let chord := residualChord X L
  apply (cycleNext_injective P).iterate chord
  rw [iterate_cycleNext_cyclePrev P index chord]
  change
    index =
      (cycleNext P)^[chord]
        ((cycleNext P)^[2 * P.m] index)
  rw [← Function.iterate_add_apply]
  have hsum : chord + 2 * P.m = P.cycle := by
    dsimp only [chord, P]
    exact residual_chord_add_twice_m hLX
  rw [hsum]
  simpa using (iterate_cycleNext_multiple_cycle P index 1).symm

private theorem dIndex_residualRootIndex {X L : ℕ}
    (hLX : X ≤ L) :
    dIndex (residualParams X L) (residualRootIndex X L) =
      rhoIndex (residualParams X L) := by
  rw [dIndex_eq_advance]
  unfold residualRootIndex
  rw [cycleAdvance_add]
  apply Fin.ext
  change
    (((rhoIndex (residualParams X L)).val +
      (residualChord X L +
        2 * (residualParams X L).m)) %
        (residualParams X L).cycle) =
      (rhoIndex (residualParams X L)).val
  rw [residual_chord_add_twice_m hLX]
  rw [Nat.add_mod]
  simpa only [Nat.mod_self, Nat.add_zero, Nat.mod_mod] using
    Nat.mod_eq_of_lt
      (rhoIndex (residualParams X L)).isLt

private theorem dIndex_injective (P : Params) :
    Function.Injective (dIndex P) := by
  unfold dIndex
  exact (cycleNext_injective P).iterate (2 * P.m)

private theorem dIndex_period (P : Params)
    (index : Fin P.cycle) :
    (dIndex P)^[P.cycle] index = index := by
  rw [iterate_dIndex]
  apply Fin.ext
  change
    (index.val + P.cycle * (2 * P.m)) % P.cycle =
      index.val
  rw [Nat.add_mod]
  simp [Nat.mod_eq_of_lt index.isLt]

/-- Exact action of `V`: it is the `dIndex` rotation with the outgoing
edge of `residualRootIndex` replaced by a loop. -/
theorem evalFrom_residualLoopBlock_intervalState {X L : ℕ}
    (hLX : X ≤ L)
    (index : Fin (residualParams X L).cycle) :
    (automaton (residualParams X L)).evalFrom
        (intervalState (residualParams X L) index)
        (residualLoopBlock X L) =
      intervalState (residualParams X L)
        (loopCut (dIndex (residualParams X L))
          (residualRootIndex X L) index) := by
  let P := residualParams X L
  rw [residualLoopBlock, (automaton P).evalFrom_of_append,
    evalFrom_cPower_intervalState,
    residual_cPower_chord_index hLX,
    evalFrom_residualUnitaryBlock_intervalState hLX]
  unfold loopCut
  by_cases hroot : index = residualRootIndex X L
  · rw [if_pos hroot, hroot, dIndex_residualRootIndex hLX,
      if_pos rfl]
  · rw [if_neg hroot]
    have hnotRho :
        dIndex P index ≠ rhoIndex P := by
      intro heq
      apply hroot
      apply dIndex_injective P
      rw [heq, dIndex_residualRootIndex hLX]
    rw [if_neg hnotRho]

private theorem evalFrom_residualLoopPower_intervalState {X L : ℕ}
    (hLX : X ≤ L)
    (index : Fin (residualParams X L).cycle)
    (count : ℕ) :
    (automaton (residualParams X L)).evalFrom
        (intervalState (residualParams X L) index)
        (wordPow (residualLoopBlock X L) count) =
      intervalState (residualParams X L)
        ((loopCut (dIndex (residualParams X L))
          (residualRootIndex X L))^[count] index) := by
  induction count generalizing index with
  | zero => simp
  | succ count ih =>
      rw [wordPow_succ, DFA.evalFrom_of_append,
        evalFrom_residualLoopBlock_intervalState hLX,
        ih, Function.iterate_succ_apply]

private theorem residualRotationIsCycle {X L : ℕ}
    (hcoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle)
    (hLX : X ≤ L) :
    ∀ index : Fin (residualParams X L).cycle,
      ∃ count < (residualParams X L).cycle,
        (dIndex (residualParams X L))^[count] index =
          residualRootIndex X L := by
  intro index
  let P := residualParams X L
  obtain ⟨count, hcount, hhit⟩ :=
    exists_dIndex_iterate_eq_rho P hcoprime (dIndex P index)
  have hhitIter :
      (dIndex P)^[count] (dIndex P index) = rhoIndex P := by
    rw [iterate_dIndex]
    exact hhit
  refine ⟨count, hcount, ?_⟩
  apply dIndex_injective P
  calc
    dIndex P ((dIndex P)^[count] index) =
        (dIndex P)^[count + 1] index :=
      (Function.iterate_succ_apply' (dIndex P) count index).symm
    _ = (dIndex P)^[count] (dIndex P index) :=
      Function.iterate_succ_apply (dIndex P) count index
    _ = rhoIndex P := hhitIter
    _ = dIndex P (residualRootIndex X L) :=
      (dIndex_residualRootIndex hLX).symm

private theorem residualUnitaryPrefix_avoids_deepest {X L : ℕ}
    (hLX : X ≤ L)
    (state : State (residualParams X L)) :
    ∃ index : Fin (residualParams X L).cycle,
      index ≠
        dIndex (residualParams X L) (residualRootIndex X L) ∧
      (automaton (residualParams X L)).evalFrom state
          (residualFJWord X L ++ residualUnitaryBlock X L) =
        intervalState (residualParams X L) index := by
  obtain ⟨index, hcompression⟩ :=
    residualFJWord_image_interval hLX state
  rw [DFA.evalFrom_of_append, hcompression,
    evalFrom_residualUnitaryBlock_intervalState hLX]
  by_cases hdeep : index = rhoIndex (residualParams X L)
  · refine ⟨residualRootIndex X L, ?_, by rw [if_pos hdeep]⟩
    rw [dIndex_residualRootIndex hLX]
    exact residualRootIndex_ne_rho hLX
  · refine ⟨index, ?_, by rw [if_neg hdeep]⟩
    rw [dIndex_residualRootIndex hLX]
    exact hdeep

/-- The complete residual-unitary word is a reset word throughout the
coprime residual region `X ≤ L`. -/
theorem residualUnitaryWord_isResetWord {X L : ℕ}
    (hcoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle)
    (hLX : X ≤ L) :
    (automaton (residualParams X L)).IsResetWord
      (residualUnitaryWord X L) := by
  let P := residualParams X L
  let root := residualRootIndex X L
  refine ⟨intervalState P root, ?_⟩
  intro state
  obtain ⟨index, hdeleted, hprefix⟩ :=
    residualUnitaryPrefix_avoids_deepest hLX state
  rw [residualUnitaryWord, DFA.evalFrom_of_append, hprefix,
    evalFrom_residualLoopPower_intervalState hLX]
  congr 1
  apply iterate_loopCut_period_sub_two
    (dIndex P) root index P.cycle
  · simp [P, residualParams, Params.cycle]
  · exact dIndex_injective P
  · exact dIndex_period P root
  · exact residualRotationIsCycle hcoprime hLX
  · exact hdeleted

@[simp]
theorem length_residualFJWord (X L : ℕ) :
    (residualFJWord X L).length = 4 * X + 6 := by
  simp [residualFJWord, residualParams, Params.ell]
  omega

@[simp]
theorem length_residualUnitaryBlock (X L : ℕ) :
    (residualUnitaryBlock X L).length = 8 * X + 8 := by
  simp [residualUnitaryBlock, residualParams, Params.ell]
  omega

@[simp]
theorem length_residualLoopBlock {X L : ℕ}
    (hLX : X ≤ L) :
    (residualLoopBlock X L).length =
      4 * L + 4 * X + 10 := by
  simp [residualLoopBlock, residualChord]
  omega

@[simp]
theorem length_residualUnitaryWord {X L : ℕ}
    (hLX : X ≤ L) :
    (residualUnitaryWord X L).length =
      12 * X + 14 +
        (4 * L + 3) * (4 * L + 4 * X + 10) := by
  simp only [residualUnitaryWord, List.length_append,
    length_wordPow, length_residualFJWord,
    length_residualUnitaryBlock,
    length_residualLoopBlock hLX]
  simp only [residualParams, Params.cycle]
  have hcycleSub :
      2 * (L + 1) + 2 * L + 3 - 2 = 4 * L + 3 := by
    omega
  rw [hcycleSub]
  ring

/-- The residual-unitary word lies within the Černý bound whenever
`L + 2 ≤ X²`, the subtraction-free form of `L ≤ X² - 2`. -/
theorem length_residualUnitaryWord_le_cernyBound {X L : ℕ}
    (hLX : X ≤ L) (hupper : L + 2 ≤ X ^ 2) :
    (residualUnitaryWord X L).length ≤
      (automaton (residualParams X L)).cernyBound := by
  rw [length_residualUnitaryWord hLX]
  simp only [DFA.cernyBound, Fintype.card_fin]
  have horder :
      (residualParams X L).order - 1 =
        2 * X + 4 * L + 6 := by
    simp [residualParams, Params.order, Params.ell,
      Params.cycle]
    omega
  rw [horder]
  nlinarith

/-- Full Černý theorem for the cost-safe residual-unitary region. -/
theorem residualUnitary_satisfiesCerny_of_add_two_le_square
    {X L : ℕ}
    (hcoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle)
    (hLX : X ≤ L) (hupper : L + 2 ≤ X ^ 2) :
    (automaton (residualParams X L)).SatisfiesCerny :=
  DFA.satisfiesCerny_of_resetWord
    (automaton (residualParams X L))
    (residualUnitaryWord_isResetWord hcoprime hLX)
    (length_residualUnitaryWord_le_cernyBound hLX hupper)

/-- The same result in the paper's natural-number formulation
`1 ≤ X`, `X ≤ L`, and `L ≤ X² - 2`. -/
theorem residualUnitary_satisfiesCerny {X L : ℕ}
    (hcoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle)
    (hX : 1 ≤ X) (hLX : X ≤ L)
    (hupper : L ≤ X ^ 2 - 2) :
    (automaton (residualParams X L)).SatisfiesCerny := by
  have hXtwo : 2 ≤ X := by
    by_contra hnot
    have hXone : X = 1 := by omega
    subst X
    norm_num at hupper
    omega
  have hsquareTwo : 2 ≤ X ^ 2 := by
    nlinarith
  have hupper' : L + 2 ≤ X ^ 2 :=
    Nat.add_le_of_le_sub hsquareTwo hupper
  exact residualUnitary_satisfiesCerny_of_add_two_le_square
    hcoprime hLX hupper'

private theorem coprime_residual_complement
    {a b c multiplier : ℕ}
    (hsum : b + c = multiplier * a)
    (hcoprime : Nat.Coprime a b) :
    Nat.Coprime a c := by
  apply Nat.coprime_iff_isRelPrime.mpr
  intro divisor hdivisorA hdivisorC
  rw [Nat.isUnit_iff]
  apply Nat.eq_one_of_dvd_coprimes hcoprime hdivisorA
  have hmultiple : divisor ∣ multiplier * a :=
    dvd_mul_of_dvd_right hdivisorA multiplier
  have hdifference : divisor ∣ multiplier * a - c :=
    Nat.dvd_sub hmultiple hdivisorC
  have hdifference_eq : multiplier * a - c = b := by
    omega
  simpa only [hdifference_eq] using hdifference

/-- Public wrapper using the complementary arithmetic coprimality
`gcd(X+L+2, 4X+3)=1` employed by the residual partition. -/
theorem residualUnitary_satisfiesCerny_arithmetic {X L : ℕ}
    (hcoprime : Nat.Coprime (X + L + 2) (4 * X + 3))
    (hX : 1 ≤ X) (hLX : X ≤ L)
    (hupper : L ≤ X ^ 2 - 2) :
    (automaton (residualParams X L)).SatisfiesCerny := by
  have hcycle :
      Nat.Coprime (X + L + 2) (4 * L + 5) :=
    coprime_residual_complement
      (a := X + L + 2) (b := 4 * X + 3)
      (c := 4 * L + 5) (multiplier := 4)
      (by omega) hcoprime
  have hcycle' :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle := by
    have hm :
        (residualParams X L).m = X + L + 2 := by
      simp [residualParams, Params.m]
      omega
    have hM :
        (residualParams X L).cycle = 4 * L + 5 := by
      simp [residualParams, Params.cycle]
      omega
    rw [hm, hM]
    exact hcycle
  exact residualUnitary_satisfiesCerny
    hcycle' hX hLX hupper

end DFA.CycleTree
