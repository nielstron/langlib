module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.CutRotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose]
public section

/-!
# The complementary direct cut

This module formalizes the second, large-`R` reset construction for the
three-arm cycle-tree automata.  In the notation of the accompanying
mathematical proof, `A = sp`, `C = ps`,

* `B = A^a C^ell`, where `a = 2L + 3`, and
* `Pcut = A^a s² C A C^ell`.

The candidate reset word is `Pcut B^(M-2)`.
-/

namespace DFA.CycleTree

namespace Params

/-- The exponent `a = 2L + 3` in the direct-cut construction. -/
def directExponent (P : Params) : ℕ := 2 * P.L + 3

/-- A nonnegative representative of the signed rotation step
`a - ell (mod M)`.  The deliberately large representative avoids
integer-valued coordinates in the executable development. -/
def directStep (P : Params) : ℕ :=
  P.directExponent + P.cycle * (P.ell + 1) - P.ell

theorem directExponent_pos (P : Params) : 0 < P.directExponent := by
  simp [directExponent]

theorem directExponent_le_cycle (P : Params) :
    P.directExponent ≤ P.cycle := by
  simp [directExponent, cycle]

theorem ell_le_directExponent_add_cycle_mul (P : Params) :
    P.ell ≤ P.directExponent + P.cycle * (P.ell + 1) := by
  have hcycle : 1 ≤ P.cycle := P.cycle_pos
  have hell :
      P.ell ≤ P.cycle * P.ell := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right P.ell hcycle
  have hmul :
      P.cycle * P.ell ≤ P.cycle * (P.ell + 1) :=
    Nat.mul_le_mul_left P.cycle (Nat.le_add_right P.ell 1)
  omega

theorem directStep_add_ell (P : Params) :
    P.directStep + P.ell =
      P.directExponent + P.cycle * (P.ell + 1) := by
  unfold directStep
  exact Nat.sub_add_cancel (P.ell_le_directExponent_add_cycle_mul)

theorem directExponent_add_twice_m (P : Params) :
    P.directExponent + 2 * P.m = P.cycle + P.ell := by
  simp [directExponent, cycle, m, ell]
  omega

theorem directStep_add_twice_m (P : Params) :
    P.directStep + 2 * P.m = (P.ell + 2) * P.cycle := by
  have hstep := P.directStep_add_ell
  have hexponent := P.directExponent_add_twice_m
  have hring :
      P.cycle * (P.ell + 1) + P.cycle =
        (P.ell + 2) * P.cycle := by ring
  omega

/-- The fixed point of the direct-cut block in local `J` coordinates. -/
def directAlpha (P : Params) : Fin P.cycle :=
  ⟨2 * P.R, by
    simp [cycle]
    omega⟩

@[simp]
theorem directAlpha_val (P : Params) :
    P.directAlpha.val = 2 * P.R :=
  rfl

/-- The maximal domain on which the direct prefix removes one state. -/
def DirectDomain (P : Params) : Prop :=
  P.X ≤ P.R + 2 * P.L + 1

end Params

/-- Replace the outgoing edge of `root` in a permutation by a loop.  This
is the abstract functional core shared by direct-cut constructions. -/
def loopCut {State : Type*} [DecidableEq State]
    (rotation : State → State) (root : State) (state : State) : State :=
  if state = root then root else rotation state

@[simp]
theorem loopCut_root {State : Type*} [DecidableEq State]
    (rotation : State → State) (root : State) :
    loopCut rotation root root = root := by
  simp [loopCut]

theorem iterate_loopCut_of_rotation_hit
    {State : Type*} [DecidableEq State]
    (rotation : State → State) (root state : State) (count : ℕ)
    (hhit : rotation^[count] state = root) :
    (loopCut rotation root)^[count] state = root := by
  induction count generalizing state with
  | zero =>
      simpa only [Function.iterate_zero_apply] using hhit
  | succ count ih =>
      rw [Function.iterate_succ_apply] at hhit ⊢
      by_cases hroot : state = root
      · subst state
        rw [loopCut_root]
        exact Function.iterate_fixed (loopCut_root rotation root) count
      · rw [loopCut, if_neg hroot]
        exact ih (rotation state) hhit

theorem iterate_loopCut_eq_of_hit_le
    {State : Type*} [DecidableEq State]
    (rotation : State → State) (root state : State)
    (hit total : ℕ) (hle : hit ≤ total)
    (hhit : rotation^[hit] state = root) :
    (loopCut rotation root)^[total] state = root := by
  have hdecompose : total = (total - hit) + hit := by
    omega
  rw [hdecompose, Function.iterate_add_apply,
    iterate_loopCut_of_rotation_hit rotation root state hit hhit]
  exact Function.iterate_fixed (loopCut_root rotation root) _

/-- A reusable "one arc cut" collapse lemma.  If `rotation` is an
injective `period`-cycle and every state reaches `root` in fewer than
`period` steps, then deleting `rotation root` leaves depth at most
`period - 2`. -/
theorem iterate_loopCut_period_sub_two
    {State : Type*} [DecidableEq State]
    (rotation : State → State) (root state : State) (period : ℕ)
    (hperiodTwo : 2 ≤ period)
    (hinjective : Function.Injective rotation)
    (hperiod : rotation^[period] root = root)
    (hhit : ∀ state, ∃ count < period,
      rotation^[count] state = root)
    (hdeleted : state ≠ rotation root) :
    (loopCut rotation root)^[period - 2] state = root := by
  obtain ⟨count, hcount, hcountHit⟩ := hhit state
  have hcountBound : count ≤ period - 2 := by
    by_contra hnotBound
    have hcountLast : count = period - 1 := by omega
    have hrootFromSuccessor :
        rotation^[period - 1] (rotation root) = root := by
      rw [← Function.iterate_succ_apply]
      have hsucc : (period - 1).succ = period := by omega
      rw [hsucc, hperiod]
    apply hdeleted
    apply (hinjective.iterate (period - 1))
    rw [hcountLast] at hcountHit
    exact hcountHit.trans hrootFromSuccessor.symm
  exact iterate_loopCut_eq_of_hit_le rotation root state count
    (period - 2) hcountBound hcountHit

/-- Predecessor on the local `M`-cycle. -/
def cyclePrev (P : Params) (index : Fin P.cycle) : Fin P.cycle :=
  if hzero : index.val = 0
  then ⟨P.cycle - 1, by omega⟩
  else ⟨index.val - 1, by omega⟩

theorem cyclePrev_of_zero (P : Params) (index : Fin P.cycle)
    (hzero : index.val = 0) :
    cyclePrev P index = ⟨P.cycle - 1, by omega⟩ := by
  simp [cyclePrev, hzero]

theorem cyclePrev_of_ne_zero (P : Params) (index : Fin P.cycle)
    (hzero : index.val ≠ 0) :
    cyclePrev P index = ⟨index.val - 1, by omega⟩ := by
  simp [cyclePrev, hzero]

theorem cycleNext_cyclePrev (P : Params) (index : Fin P.cycle) :
    cycleNext P (cyclePrev P index) = index := by
  by_cases hzero : index.val = 0
  · apply Fin.ext
    rw [cyclePrev_of_zero P index hzero]
    rw [cycleNext_of_not_lt]
    · exact hzero.symm
    · simp
      omega
  · apply Fin.ext
    rw [cyclePrev_of_ne_zero P index hzero]
    rw [cycleNext_of_lt]
    · simp
      omega
    · simp
      omega

theorem cyclePrev_cycleNext (P : Params) (index : Fin P.cycle) :
    cyclePrev P (cycleNext P index) = index := by
  by_cases hnext : index.val + 1 < P.cycle
  · rw [cycleNext_of_lt P index hnext, cyclePrev_of_ne_zero]
    · apply Fin.ext
      simp
    · simp
  · have hlast : index.val + 1 = P.cycle := by omega
    rw [cycleNext_of_not_lt P index hnext,
      cyclePrev_of_zero P _ rfl]
    apply Fin.ext
    simp
    omega

theorem iterate_cyclePrev_cycleNext (P : Params)
    (index : Fin P.cycle) (count : ℕ) :
    (cyclePrev P)^[count] ((cycleNext P)^[count] index) = index := by
  exact
    (show Function.LeftInverse (cyclePrev P) (cycleNext P) from
      cyclePrev_cycleNext P).iterate count index

theorem iterate_cycleNext_cyclePrev (P : Params)
    (index : Fin P.cycle) (count : ℕ) :
    (cycleNext P)^[count] ((cyclePrev P)^[count] index) = index := by
  exact
    (show Function.LeftInverse (cycleNext P) (cyclePrev P) from
      cycleNext_cyclePrev P).iterate count index

/-- On the interval `J`, `C = ps` is exactly cyclic predecessor. -/
theorem evalFrom_cWord_intervalState (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (intervalState P index) cWord =
      intervalState P (cyclePrev P index) := by
  simp only [cWord, DFA.evalFrom_cons, DFA.evalFrom_nil,
    automaton_step_p, automaton_step_s]
  by_cases hzero : index.val = 0
  · have hindexEq : index = ⟨0, P.cycle_pos⟩ := Fin.ext hzero
    subst index
    have hellVal :
        (intervalState P ⟨0, P.cycle_pos⟩).val = P.ell := by
      simp
    rw [pMap_at_ell P _ hellVal]
    have hrhoVal :
        (P.stateOfNat P.rho).val = P.rho :=
      stateOfNat_val_of_lt P P.rho_lt_order
    rw [sMap_at_or_after_rho P _ (by rw [hrhoVal])]
    rw [hrhoVal]
    have hcoordinate :
        P.rho + P.order - 1 - P.rho = P.order - 1 := by
      omega
    rw [hcoordinate]
    apply Fin.ext
    rw [stateOfNat_val_of_lt P (by omega), intervalState_val]
    rw [cyclePrev_of_zero P _ rfl]
    simp [Params.order]
    omega
  · have hindexPos : 0 < index.val := Nat.pos_of_ne_zero hzero
    have hstateVal := intervalState_val P index
    by_cases hbeforeRho : index.val < 2 * P.R + 1
    · have hellState : P.ell < (intervalState P index).val := by
        rw [hstateVal]
        omega
      have hrhoState : (intervalState P index).val < P.rho := by
        rw [hstateVal, P.rho_eq]
        omega
      rw [pMap_between_ell_rho P _ hellState hrhoState]
      rw [hstateVal]
      have hpCoordinate :
          P.ell + P.rho - (P.ell + index.val) =
            P.rho - index.val := by
        omega
      rw [hpCoordinate]
      have hpVal :
          (P.stateOfNat (P.rho - index.val)).val =
            P.rho - index.val := by
        apply stateOfNat_val_of_lt
        exact (Nat.sub_le P.rho index.val).trans_lt P.rho_lt_order
      have hpAfterEll :
          P.ell <
            (P.stateOfNat (P.rho - index.val)).val := by
        rw [hpVal, P.rho_eq]
        omega
      have hpBeforeRho :
          (P.stateOfNat (P.rho - index.val)).val <
            P.rho := by
        rw [hpVal]
        omega
      rw [sMap_between_ell_rho P _ hpAfterEll hpBeforeRho]
      rw [hpVal]
      have hcoordinate :
          P.ell + P.rho - 1 - (P.rho - index.val) =
            P.ell + (index.val - 1) := by
        rw [P.rho_eq]
        omega
      rw [hcoordinate, cyclePrev_of_ne_zero P index hzero]
      rfl
    · by_cases hatRho : index.val = 2 * P.R + 1
      · have hstateRho :
            (intervalState P index).val = P.rho := by
          rw [hstateVal, hatRho, P.rho_eq]
          omega
        rw [pMap_at_rho P _ hstateRho]
        have hzeroVal : (P.stateOfNat 0).val = 0 :=
          stateOfNat_val_of_lt P P.order_pos
        rw [sMap_at_zero P _ hzeroVal]
        apply Fin.ext
        rw [stateOfNat_val_of_lt P (by omega), intervalState_val]
        have hprevVal :
            (cyclePrev P index).val = index.val - 1 := by
          rw [cyclePrev_of_ne_zero P index hzero]
        rw [hprevVal, hatRho, P.rho_eq]
        omega
      · have hafterRho : P.rho < (intervalState P index).val := by
          rw [hstateVal, P.rho_eq]
          omega
        rw [pMap_after_rho P _ hafterRho]
        rw [hstateVal]
        have hpCoordinate :
            P.rho + P.order - (P.ell + index.val) =
              P.rho + P.cycle - index.val := by
          rw [Params.order]
          omega
        rw [hpCoordinate]
        have hpVal :
            (P.stateOfNat
                (P.rho + P.cycle - index.val)).val =
              P.rho + P.cycle - index.val := by
          apply stateOfNat_val_of_lt
          simp [Params.order]
          omega
        have hpAtRho :
            P.rho ≤
              (P.stateOfNat
                (P.rho + P.cycle - index.val)).val := by
          rw [hpVal]
          omega
        rw [sMap_at_or_after_rho P _ hpAtRho]
        rw [hpVal]
        have hcoordinate :
            P.rho + P.order - 1 -
                (P.rho + P.cycle - index.val) =
              P.ell + (index.val - 1) := by
          rw [Params.order, P.rho_eq]
          omega
        rw [hcoordinate, cyclePrev_of_ne_zero P index hzero]
        rfl

/-- Powers of `C` remain in `J` and iterate cyclic predecessor. -/
theorem evalFrom_cPower_intervalState (P : Params)
    (index : Fin P.cycle) (count : ℕ) :
    (automaton P).evalFrom (intervalState P index)
        (wordPow cWord count) =
      intervalState P ((cyclePrev P)^[count] index) := by
  induction count generalizing index with
  | zero => simp
  | succ count ih =>
      rw [wordPow_succ, (automaton P).evalFrom_of_append,
        evalFrom_cWord_intervalState, ih]
      rw [Function.iterate_succ_apply]

theorem sMap_rho_sub_one (P : Params) :
    sMap P (P.stateOfNat (P.rho - 1)) =
      P.stateOfNat P.ell := by
  have hrhoPredLt : P.rho - 1 < P.order := by
    have := P.rho_lt_order
    omega
  have hrhoPredVal :
      (P.stateOfNat (P.rho - 1)).val = P.rho - 1 :=
    stateOfNat_val_of_lt P hrhoPredLt
  by_cases hR : P.R = 0
  · have hrhoEq : P.rho = P.ell + 1 := by
      simp [Params.rho, Params.m, Params.ell, hR]
      omega
    have hrhoPredEq : P.rho - 1 = P.ell := by omega
    rw [sMap_at_ell P _]
    · rw [hrhoEq]
      congr 1
    · rw [hrhoPredVal, hrhoPredEq]
  · have hRPos : 0 < P.R := Nat.pos_of_ne_zero hR
    have hafterEll : P.ell < P.rho - 1 := by
      rw [P.rho_eq]
      omega
    have hbeforeRho : P.rho - 1 < P.rho := by omega
    rw [sMap_between_ell_rho P _]
    · rw [hrhoPredVal]
      congr 1
      omega
    · rw [hrhoPredVal]
      exact hafterEll
    · rw [hrhoPredVal]
      exact hbeforeRho

/-- The square of `s` maps the unique exceptional coordinate `0` to
`ell` and fixes every other state. -/
theorem evalFrom_sSquared (P : Params) (state : State P) :
    (automaton P).evalFrom state sSquared =
      if state.val = 0 then P.stateOfNat P.ell else state := by
  simp only [sSquared, DFA.evalFrom_cons, DFA.evalFrom_nil,
    automaton_step_s]
  by_cases hzero : state.val = 0
  · rw [sMap_at_zero P state hzero, sMap_rho_sub_one]
    simp [hzero]
  by_cases hell : state.val = P.ell
  · rw [sMap_at_ell P state hell, sMap_rho_sub_one]
    rw [if_neg hzero]
    rw [← hell]
    exact stateOfNat_state_val P state
  by_cases hbeforeEll : state.val < P.ell
  · have hstatePos : 0 < state.val := Nat.pos_of_ne_zero hzero
    rw [sMap_between_zero_ell P state hstatePos hbeforeEll]
    let reflected := P.ell - state.val
    have hreflectedPos : 0 < reflected := by
      dsimp [reflected]
      omega
    have hreflectedLt : reflected < P.ell := by
      dsimp [reflected]
      omega
    have hreflectedOrder : reflected < P.order :=
      hreflectedLt.trans P.ell_lt_order
    have hreflectedVal :
        (P.stateOfNat reflected).val = reflected :=
      stateOfNat_val_of_lt P hreflectedOrder
    change
      sMap P (P.stateOfNat reflected) =
        (if state.val = 0 then P.stateOfNat P.ell else state)
    rw [sMap_between_zero_ell P _]
    · rw [hreflectedVal]
      rw [if_neg hzero]
      have hcoordinate :
          P.ell - reflected = state.val := by
        dsimp [reflected]
        omega
      rw [hcoordinate]
      exact stateOfNat_state_val P state
    · rw [hreflectedVal]
      exact hreflectedPos
    · rw [hreflectedVal]
      exact hreflectedLt
  · by_cases hbeforeRho : state.val < P.rho
    · have hafterEll : P.ell < state.val := by omega
      rw [sMap_between_ell_rho P state hafterEll hbeforeRho]
      let reflected := P.ell + P.rho - 1 - state.val
      have hreflectedEll : P.ell ≤ reflected := by
        dsimp [reflected]
        omega
      have hreflectedRho : reflected < P.rho := by
        dsimp [reflected]
        omega
      have hreflectedOrder : reflected < P.order :=
        hreflectedRho.trans P.rho_lt_order
      have hreflectedVal :
          (P.stateOfNat reflected).val = reflected :=
        stateOfNat_val_of_lt P hreflectedOrder
      change
        sMap P (P.stateOfNat reflected) =
          (if state.val = 0 then P.stateOfNat P.ell else state)
      by_cases hreflectedEq : reflected = P.ell
      · rw [sMap_at_ell P _]
        · rw [if_neg hzero]
          have hstateEq : state.val = P.rho - 1 := by
            dsimp [reflected] at hreflectedEq
            omega
          rw [← hstateEq]
          exact stateOfNat_state_val P state
        · rw [hreflectedVal]
          exact hreflectedEq
      · have hreflectedAfter : P.ell < reflected := by omega
        rw [sMap_between_ell_rho P _]
        · rw [hreflectedVal]
          rw [if_neg hzero]
          have hcoordinate :
              P.ell + P.rho - 1 - reflected = state.val := by
            dsimp [reflected]
            omega
          rw [hcoordinate]
          exact stateOfNat_state_val P state
        · rw [hreflectedVal]
          exact hreflectedAfter
        · rw [hreflectedVal]
          exact hreflectedRho
    · have hatOrAfterRho : P.rho ≤ state.val := by omega
      rw [sMap_at_or_after_rho P state hatOrAfterRho]
      let reflected := P.rho + P.order - 1 - state.val
      have hreflectedRho : P.rho ≤ reflected := by
        dsimp [reflected]
        omega
      have hreflectedOrder : reflected < P.order := by
        dsimp [reflected]
        omega
      have hreflectedVal :
          (P.stateOfNat reflected).val = reflected :=
        stateOfNat_val_of_lt P hreflectedOrder
      change
        sMap P (P.stateOfNat reflected) =
          (if state.val = 0 then P.stateOfNat P.ell else state)
      rw [sMap_at_or_after_rho P _]
      · rw [hreflectedVal]
        rw [if_neg hzero]
        have hcoordinate :
            P.rho + P.order - 1 - reflected = state.val := by
          dsimp [reflected]
          omega
        rw [hcoordinate]
        exact stateOfNat_state_val P state
      · rw [hreflectedVal]
        exact hreflectedRho

theorem evalFrom_sSquared_cycleState (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (cycleState P index) sSquared =
      intervalState P index := by
  rw [evalFrom_sSquared]
  by_cases hzero : index.val = 0
  · have hindex : index = ⟨0, P.cycle_pos⟩ := Fin.ext hzero
    subst index
    rw [cycleState_zero]
    have hstateZero : (P.stateOfNat 0).val = 0 :=
      stateOfNat_val_of_lt P P.order_pos
    rw [if_pos hstateZero]
    rfl
  · have hcycleVal := cycleState_val_of_ne_zero P index hzero
    rw [if_neg (by rw [hcycleVal]; omega)]
    exact cycleState_of_ne_zero P index hzero

theorem evalFrom_sSquared_intervalState (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (intervalState P index) sSquared =
      intervalState P index := by
  rw [evalFrom_sSquared]
  rw [if_neg (by
    rw [intervalState_val]
    have := P.ell_pos
    omega)]

theorem evalFrom_sSquared_tail (P : Params) (coordinate : ℕ)
    (hcoordinatePos : 0 < coordinate)
    (hcoordinate : coordinate < P.ell) :
    (automaton P).evalFrom (P.stateOfNat coordinate) sSquared =
      P.stateOfNat coordinate := by
  rw [evalFrom_sSquared]
  have hcoordinateOrder := hcoordinate.trans P.ell_lt_order
  have hcoordinateVal :
      (P.stateOfNat coordinate).val = coordinate :=
    stateOfNat_val_of_lt P hcoordinateOrder
  rw [if_neg (by rw [hcoordinateVal]; omega)]

/-- After `A^a s²`, every state is either in `J`, or is a tail state
whose coordinate is at least `a + 1`. -/
theorem after_aPower_sSquared_interval_or_tail
    (P : Params) (state : State P) :
    (∃ index : Fin P.cycle,
      (automaton P).evalFrom state
          (wordPow aWord P.directExponent ++ sSquared) =
        intervalState P index) ∨
    (∃ coordinate : ℕ,
      P.directExponent + 1 ≤ coordinate ∧ coordinate < P.ell ∧
      (automaton P).evalFrom state
          (wordPow aWord P.directExponent ++ sSquared) =
        P.stateOfNat coordinate) := by
  by_cases hzero : state.val = 0
  · left
    have hstateEq : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
    refine
      ⟨(cycleNext P)^[P.directExponent] zeroIndex, ?_⟩
    rw [(automaton P).evalFrom_of_append, hstateEq,
      ← cycleState_zero,
      evalFrom_aPower_cycleState,
      evalFrom_sSquared_cycleState]
  · by_cases htail : state.val < P.ell
    · have hstatePos : 0 < state.val := Nat.pos_of_ne_zero hzero
      have hbefore :
          state.val + P.directExponent < P.order := by
        have ha := P.directExponent_le_cycle
        simp only [Params.order]
        omega
      rw [(automaton P).evalFrom_of_append,
        evalFrom_aPower_before_wrap P state P.directExponent
          hstatePos hbefore]
      let coordinate := state.val + P.directExponent
      have hcoordinatePos : 0 < coordinate := by
        dsimp [coordinate]
        omega
      by_cases hcoordinate : coordinate < P.ell
      · right
        refine
          ⟨coordinate, by
            dsimp [coordinate]
            omega,
            hcoordinate, ?_⟩
        exact evalFrom_sSquared_tail P coordinate
          hcoordinatePos hcoordinate
      · left
        have hcoordinateOrder : coordinate < P.order := by
          dsimp [coordinate]
          exact hbefore
        have hcoordinateVal :
            (P.stateOfNat coordinate).val = coordinate :=
          stateOfNat_val_of_lt P hcoordinateOrder
        have hcoordinateEll :
            P.ell ≤ (P.stateOfNat coordinate).val := by
          rw [hcoordinateVal]
          omega
        obtain ⟨index, hindex⟩ :=
          exists_intervalState_eq P (P.stateOfNat coordinate)
            hcoordinateEll
        refine ⟨index, ?_⟩
        rw [← hindex]
        exact evalFrom_sSquared_intervalState P index
    · left
      have hinterval : P.ell ≤ state.val := by omega
      obtain ⟨index, hstateEq⟩ :=
        exists_intervalState_eq P state hinterval
      refine
        ⟨(cycleNext P)^[P.directExponent] index, ?_⟩
      rw [(automaton P).evalFrom_of_append, ← hstateEq,
        evalFrom_aPower_intervalState_of_pos P index
          P.directExponent P.directExponent_pos,
        evalFrom_sSquared_cycleState]

/-- On `J`, the composite `CA` restores the hidden-cycle state with the
same local index.  In particular, local index zero becomes global zero. -/
theorem evalFrom_cWord_aWord_intervalState
    (P : Params) (index : Fin P.cycle) :
    (automaton P).evalFrom (intervalState P index)
        (cWord ++ aWord) =
      cycleState P index := by
  rw [(automaton P).evalFrom_of_append,
    evalFrom_cWord_intervalState,
    evalFrom_aWord_intervalState,
    cycleNext_cyclePrev]

theorem evalFrom_cWord_zero (P : Params) :
    (automaton P).evalFrom (P.stateOfNat 0) cWord =
      P.stateOfNat (P.ell - 1) := by
  simp only [cWord, DFA.evalFrom_cons, DFA.evalFrom_nil,
    automaton_step_p, automaton_step_s]
  have hzeroVal : (P.stateOfNat 0).val = 0 :=
    stateOfNat_val_of_lt P P.order_pos
  rw [pMap_at_zero P _ hzeroVal]
  have honeLt : 1 < P.order := by
    have := P.ell_pos
    have := P.ell_lt_order
    omega
  have honeVal : (P.stateOfNat 1).val = 1 :=
    stateOfNat_val_of_lt P honeLt
  rw [sMap_between_zero_ell P _ (by rw [honeVal]; omega)
    (by rw [honeVal]; simp [Params.ell])]
  rw [honeVal]

theorem evalFrom_cWord_one (P : Params) :
    (automaton P).evalFrom (P.stateOfNat 1) cWord =
      P.stateOfNat (P.rho - 1) := by
  simp only [cWord, DFA.evalFrom_cons, DFA.evalFrom_nil,
    automaton_step_p, automaton_step_s]
  have honeLt : 1 < P.order := by
    have := P.ell_pos
    have := P.ell_lt_order
    omega
  have honeVal : (P.stateOfNat 1).val = 1 :=
    stateOfNat_val_of_lt P honeLt
  rw [pMap_at_one P _ honeVal]
  have hellVal : (P.stateOfNat P.ell).val = P.ell :=
    stateOfNat_val_of_lt P P.ell_lt_order
  rw [sMap_at_ell P _ hellVal]

theorem evalFrom_cWord_tail (P : Params) (coordinate : ℕ)
    (htwo : 2 ≤ coordinate) (hcoordinate : coordinate < P.ell) :
    (automaton P).evalFrom (P.stateOfNat coordinate) cWord =
      P.stateOfNat (coordinate - 1) := by
  simp only [cWord, DFA.evalFrom_cons, DFA.evalFrom_nil,
    automaton_step_p, automaton_step_s]
  have hcoordinateOrder : coordinate < P.order :=
    hcoordinate.trans P.ell_lt_order
  have hcoordinateVal :
      (P.stateOfNat coordinate).val = coordinate :=
    stateOfNat_val_of_lt P hcoordinateOrder
  rw [pMap_before_ell P _ (by rw [hcoordinateVal]; exact htwo)
    (by rw [hcoordinateVal]; exact hcoordinate)]
  rw [hcoordinateVal]
  have hreflectedVal :
      (P.stateOfNat (P.ell + 1 - coordinate)).val =
        P.ell + 1 - coordinate := by
    apply stateOfNat_val_of_lt
    have hreflectedLt : P.ell + 1 - coordinate < P.ell := by
      omega
    exact hreflectedLt.trans P.ell_lt_order
  have hreflectedPos :
      0 < (P.stateOfNat (P.ell + 1 - coordinate)).val := by
    rw [hreflectedVal]
    omega
  have hreflectedBeforeEll :
      (P.stateOfNat (P.ell + 1 - coordinate)).val < P.ell := by
    rw [hreflectedVal]
    omega
  rw [sMap_between_zero_ell P _ hreflectedPos
    hreflectedBeforeEll, hreflectedVal]
  congr 1
  omega

/-- The composite `CA` fixes the portion of the tail relevant to the
direct prefix. -/
theorem evalFrom_cWord_aWord_tail
    (P : Params) (coordinate : ℕ)
    (hcoordinate : P.directExponent + 1 ≤ coordinate)
    (hcoordinateEll : coordinate < P.ell) :
    (automaton P).evalFrom (P.stateOfNat coordinate)
        (cWord ++ aWord) =
      P.stateOfNat coordinate := by
  have htwo : 2 ≤ coordinate := by
    have := P.directExponent_pos
    omega
  rw [(automaton P).evalFrom_of_append,
    evalFrom_cWord_tail P coordinate htwo hcoordinateEll,
    evalFrom_aWord]
  have hpredOrder : coordinate - 1 < P.order :=
    (Nat.sub_le coordinate 1).trans_lt
      (hcoordinateEll.trans P.ell_lt_order)
  have hpredVal :
      (P.stateOfNat (coordinate - 1)).val = coordinate - 1 :=
    stateOfNat_val_of_lt P hpredOrder
  rw [hpredVal, if_neg (by omega)]
  congr 1
  omega

/-- Repeated `C` descends monotonically along the tail as long as it has
not yet passed coordinate `1`. -/
theorem evalFrom_cPower_tail (P : Params) (coordinate count : ℕ)
    (hcoordinatePos : 0 < coordinate)
    (hcoordinate : coordinate < P.ell)
    (hcount : count ≤ coordinate - 1) :
    (automaton P).evalFrom (P.stateOfNat coordinate)
        (wordPow cWord count) =
      P.stateOfNat (coordinate - count) := by
  induction count generalizing coordinate with
  | zero => simp
  | succ count ih =>
      have hcoordinateTwo : 2 ≤ coordinate := by omega
      rw [wordPow_succ, (automaton P).evalFrom_of_append,
        evalFrom_cWord_tail P coordinate hcoordinateTwo hcoordinate]
      rw [ih (coordinate := coordinate - 1)]
      · congr 1
        omega
      · omega
      · omega
      · omega

/-- The exceptional cycle state `0` is sent by `C^ell` to local
coordinate `alpha = 2R`. -/
theorem evalFrom_cPower_ell_zero (P : Params) :
    (automaton P).evalFrom (P.stateOfNat 0)
        (wordPow cWord P.ell) =
      intervalState P P.directAlpha := by
  have hellTwo : 2 ≤ P.ell := by simp [Params.ell]
  have hellPredPos : 0 < P.ell - 1 := by omega
  have hellPredLt : P.ell - 1 < P.ell := by omega
  have htail :
      (automaton P).evalFrom (P.stateOfNat (P.ell - 1))
          (wordPow cWord (P.ell - 2)) =
        P.stateOfNat 1 := by
    have h :=
      evalFrom_cPower_tail P (P.ell - 1) (P.ell - 2)
        hellPredPos hellPredLt (by omega)
    have hcoordinate :
        (P.ell - 1) - (P.ell - 2) = 1 := by omega
    rw [hcoordinate] at h
    exact h
  have hellDecompose :
      P.ell = 1 + (P.ell - 2) + 1 := by omega
  calc
    (automaton P).evalFrom (P.stateOfNat 0)
        (wordPow cWord P.ell) =
      (automaton P).evalFrom (P.stateOfNat 0)
        (wordPow cWord 1 ++
          wordPow cWord (P.ell - 2) ++ wordPow cWord 1) := by
            conv_lhs =>
              rw [hellDecompose, wordPow_add, wordPow_add]
    _ = P.stateOfNat (P.rho - 1) := by
      simp only [(automaton P).evalFrom_of_append]
      rw [show wordPow cWord 1 = cWord by simp,
        evalFrom_cWord_zero, htail, evalFrom_cWord_one]
    _ = intervalState P P.directAlpha := by
      unfold intervalState
      congr 1
      rw [P.rho_eq]
      simp

theorem evalFrom_cWord_one_eq_intervalAlpha (P : Params) :
    (automaton P).evalFrom (P.stateOfNat 1) cWord =
      intervalState P P.directAlpha := by
  rw [evalFrom_cWord_one]
  unfold intervalState
  congr 1
  rw [P.rho_eq]
  simp

/-- Starting at a positive tail coordinate `x`, exactly `x` copies of
`C` enter `J` at `alpha`. -/
theorem evalFrom_cPower_tail_to_intervalAlpha
    (P : Params) (coordinate : ℕ)
    (hcoordinatePos : 0 < coordinate)
    (hcoordinate : coordinate < P.ell) :
    (automaton P).evalFrom (P.stateOfNat coordinate)
        (wordPow cWord coordinate) =
      intervalState P P.directAlpha := by
  have htail :
      (automaton P).evalFrom (P.stateOfNat coordinate)
          (wordPow cWord (coordinate - 1)) =
        P.stateOfNat 1 := by
    have h :=
      evalFrom_cPower_tail P coordinate (coordinate - 1)
        hcoordinatePos hcoordinate (by omega)
    have hresult : coordinate - (coordinate - 1) = 1 := by omega
    rw [hresult] at h
    exact h
  have hdecompose : coordinate = (coordinate - 1) + 1 := by omega
  have hword :
      wordPow cWord coordinate =
        wordPow cWord (coordinate - 1) ++ wordPow cWord 1 := by
    calc
      wordPow cWord coordinate =
          wordPow cWord ((coordinate - 1) + 1) :=
        congrArg (wordPow cWord) hdecompose
      _ = wordPow cWord (coordinate - 1) ++
          wordPow cWord 1 :=
        wordPow_add cWord (coordinate - 1) 1
  rw [hword,
    (automaton P).evalFrom_of_append, htail]
  rw [show wordPow cWord 1 = cWord by simp,
    evalFrom_cWord_one_eq_intervalAlpha]

/-- Closed form for the final `C^ell` factor on the surviving tail
interval. -/
theorem evalFrom_cPower_ell_tail
    (P : Params) (coordinate : ℕ)
    (hcoordinatePos : 0 < coordinate)
    (hcoordinate : coordinate < P.ell) :
    (automaton P).evalFrom (P.stateOfNat coordinate)
        (wordPow cWord P.ell) =
      intervalState P
        ((cyclePrev P)^[P.ell - coordinate] P.directAlpha) := by
  have hdecompose :
      P.ell = coordinate + (P.ell - coordinate) := by omega
  have hword :
      wordPow cWord P.ell =
        wordPow cWord coordinate ++
          wordPow cWord (P.ell - coordinate) := by
    calc
      wordPow cWord P.ell =
          wordPow cWord
            (coordinate + (P.ell - coordinate)) :=
        congrArg (wordPow cWord) hdecompose
      _ = wordPow cWord coordinate ++
          wordPow cWord (P.ell - coordinate) :=
        wordPow_add cWord coordinate (P.ell - coordinate)
  rw [hword,
    (automaton P).evalFrom_of_append,
    evalFrom_cPower_tail_to_intervalAlpha P coordinate
      hcoordinatePos hcoordinate,
    evalFrom_cPower_intervalState]

/-- Exact local transition of the direct block.  It is deliberately
defined only in terms of the reusable cyclic successor/predecessor maps. -/
def directRotation (P : Params) (index : Fin P.cycle) : Fin P.cycle :=
  (cyclePrev P)^[P.ell]
    ((cycleNext P)^[P.directExponent] index)

/-- The modular transitivity fact required by the direct cut. -/
def DirectRotationIsCycle (P : Params) : Prop :=
  ∀ index : Fin P.cycle, ∃ count < P.cycle,
    (directRotation P)^[count] index = P.directAlpha

/-- Exact local transition of the direct block. -/
def directBlockIndex (P : Params) (index : Fin P.cycle) : Fin P.cycle :=
  let advanced := (cycleNext P)^[P.directExponent] index
  if advanced.val = 0
  then P.directAlpha
  else (cyclePrev P)^[P.ell] advanced

/-- The direct-cut block `B = A^a C^ell`. -/
def directBlockWord (P : Params) : List Letter :=
  wordPow aWord P.directExponent ++ wordPow cWord P.ell

/-- Exact `B = A^a C^ell` action on the invariant interval `J`. -/
theorem evalFrom_directBlockWord_intervalState (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (intervalState P index)
        (directBlockWord P) =
      intervalState P (directBlockIndex P index) := by
  rw [directBlockWord, (automaton P).evalFrom_of_append]
  have haPos := P.directExponent_pos
  rw [evalFrom_aPower_intervalState_of_pos P index
    P.directExponent haPos]
  let advanced := (cycleNext P)^[P.directExponent] index
  change
    (automaton P).evalFrom (cycleState P advanced)
        (wordPow cWord P.ell) =
      intervalState P
        (if advanced.val = 0
          then P.directAlpha
          else (cyclePrev P)^[P.ell] advanced)
  by_cases hadvanced : advanced.val = 0
  · have hadvancedEq :
        advanced = ⟨0, P.cycle_pos⟩ := Fin.ext hadvanced
    rw [if_pos hadvanced, hadvancedEq, cycleState_zero,
      evalFrom_cPower_ell_zero]
  · rw [if_neg hadvanced,
      cycleState_of_ne_zero P advanced hadvanced,
      ← intervalState, evalFrom_cPower_intervalState]

theorem directAlpha_advances_to_zero (P : Params) :
    (cycleNext P)^[P.directExponent] P.directAlpha =
      ⟨0, P.cycle_pos⟩ := by
  rw [iterate_cycleNext]
  apply Fin.ext
  change
    (2 * P.R + P.directExponent) % P.cycle = 0
  have hsum :
      2 * P.R + P.directExponent = P.cycle := by
    simp [Params.directExponent, Params.cycle]
    omega
  rw [hsum]
  simp

theorem direct_advance_eq_zero_iff (P : Params)
    (index : Fin P.cycle) :
    ((cycleNext P)^[P.directExponent] index).val = 0 ↔
      index = P.directAlpha := by
  have hinjective :
      Function.Injective ((cycleNext P)^[P.directExponent]) :=
    (show Function.LeftInverse
        ((cyclePrev P)^[P.directExponent])
        ((cycleNext P)^[P.directExponent]) from
      fun index =>
        iterate_cyclePrev_cycleNext P index P.directExponent).injective
  constructor
  · intro hzero
    apply hinjective
    rw [directAlpha_advances_to_zero P]
    apply Fin.ext
    exact hzero
  · rintro rfl
    rw [directAlpha_advances_to_zero]

/-- Boxed form of the block action: `alpha` is fixed and every other
coordinate follows the uncut rotation `C^ell ∘ A^a`. -/
theorem evalFrom_directBlockWord_intervalState_eq_cut (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (intervalState P index)
        (directBlockWord P) =
      if index = P.directAlpha
      then intervalState P P.directAlpha
      else intervalState P
        ((cyclePrev P)^[P.ell]
          ((cycleNext P)^[P.directExponent] index)) := by
  rw [evalFrom_directBlockWord_intervalState]
  unfold directBlockIndex
  by_cases hindex : index = P.directAlpha
  · rw [if_pos hindex, hindex, directAlpha_advances_to_zero]
    simp
  · rw [if_neg hindex]
    have hadvance :
        ((cycleNext P)^[P.directExponent] index).val ≠ 0 := by
      rw [ne_eq, direct_advance_eq_zero_iff]
      exact hindex
    rw [if_neg hadvance]

theorem directBlockIndex_eq_loopCut (P : Params)
    (index : Fin P.cycle) :
    directBlockIndex P index =
      loopCut (directRotation P) P.directAlpha index := by
  unfold directBlockIndex directRotation loopCut
  by_cases hindex : index = P.directAlpha
  · subst index
    rw [directAlpha_advances_to_zero]
    simp
  · have hadvance :
        ((cycleNext P)^[P.directExponent] index).val ≠ 0 := by
      rw [ne_eq, direct_advance_eq_zero_iff]
      exact hindex
    rw [if_neg hadvance, if_neg hindex]

theorem cycleNext_injective (P : Params) :
    Function.Injective (cycleNext P) :=
  (show Function.LeftInverse (cyclePrev P) (cycleNext P) from
    cyclePrev_cycleNext P).injective

theorem cyclePrev_injective (P : Params) :
    Function.Injective (cyclePrev P) :=
  (show Function.LeftInverse (cycleNext P) (cyclePrev P) from
    cycleNext_cyclePrev P).injective

/-- The distinguished zero in local cycle coordinates. -/
def cycleZeroIndex (P : Params) : Fin P.cycle :=
  ⟨0, P.cycle_pos⟩

@[simp]
theorem cycleZeroIndex_val (P : Params) :
    (cycleZeroIndex P).val = 0 :=
  rfl

theorem directAlpha_eq_iterate_cyclePrev_zero (P : Params) :
    (cyclePrev P)^[P.directExponent] (cycleZeroIndex P) =
      P.directAlpha := by
  apply (cycleNext_injective P).iterate P.directExponent
  rw [iterate_cycleNext_cyclePrev,
    directAlpha_advances_to_zero]
  rfl

theorem directRotation_alpha_eq_iterate_cyclePrev_zero (P : Params) :
    directRotation P P.directAlpha =
      (cyclePrev P)^[P.ell] (cycleZeroIndex P) := by
  unfold directRotation
  rw [directAlpha_advances_to_zero]
  rfl

theorem iterate_cyclePrev_zero_ne_zero (P : Params) (count : ℕ)
    (hcountPos : 0 < count) (hcountLt : count < P.cycle) :
    (cyclePrev P)^[count] (cycleZeroIndex P) ≠
      cycleZeroIndex P := by
  intro heq
  have himage := congrArg ((cycleNext P)^[count]) heq
  rw [iterate_cycleNext_cyclePrev] at himage
  rw [iterate_cycleNext] at himage
  have hval := congrArg Fin.val himage
  change 0 = (0 + count) % P.cycle at hval
  simp only [zero_add] at hval
  rw [Nat.mod_eq_of_lt hcountLt] at hval
  omega

/-- On the exact direct-prefix domain, the exceptional image `alpha`
does not fill the deleted deepest point `rotation alpha`. -/
theorem directAlpha_ne_directRotation_alpha_of_domain (P : Params)
    (hdomain : P.DirectDomain) :
    P.directAlpha ≠ directRotation P P.directAlpha := by
  have hparity : P.ell ≠ P.directExponent := by
    simp [Params.ell, Params.directExponent]
    omega
  have hdomainDiff :
      P.ell - P.directExponent < P.cycle := by
    simp only [Params.DirectDomain, Params.ell,
      Params.directExponent, Params.cycle] at hdomain ⊢
    omega
  intro heq
  rw [directRotation_alpha_eq_iterate_cyclePrev_zero] at heq
  rw [← directAlpha_eq_iterate_cyclePrev_zero] at heq
  by_cases hexponentLe :
      P.directExponent ≤ P.ell
  · have hstrict : P.directExponent < P.ell := by omega
    let difference := P.ell - P.directExponent
    have hdifferencePos : 0 < difference := by
      dsimp [difference]
      omega
    have hdifferenceLt : difference < P.cycle := by
      dsimp [difference]
      exact hdomainDiff
    have hell :
        P.ell = P.directExponent + difference := by
      dsimp [difference]
      omega
    have heq' :
        (cyclePrev P)^[P.directExponent] (cycleZeroIndex P) =
          (cyclePrev P)^[P.directExponent]
            ((cyclePrev P)^[difference] (cycleZeroIndex P)) := by
      rw [← Function.iterate_add_apply, ← hell]
      exact heq
    have hzero :=
      ((cyclePrev_injective P).iterate P.directExponent) heq'
    exact
      (iterate_cyclePrev_zero_ne_zero P difference
        hdifferencePos hdifferenceLt) hzero.symm
  · have hellLt : P.ell < P.directExponent := by omega
    let difference := P.directExponent - P.ell
    have hdifferencePos : 0 < difference := by
      dsimp [difference]
      omega
    have hdifferenceLt : difference < P.cycle := by
      dsimp [difference]
      have := P.directExponent_le_cycle
      have := P.ell_pos
      omega
    have hexponent :
        P.directExponent = P.ell + difference := by
      dsimp [difference]
      omega
    have heq' :
        (cyclePrev P)^[P.ell]
            ((cyclePrev P)^[difference] (cycleZeroIndex P)) =
          (cyclePrev P)^[P.ell] (cycleZeroIndex P) := by
      rw [← Function.iterate_add_apply, ← hexponent]
      exact heq
    have hzero :=
      ((cyclePrev_injective P).iterate P.ell) heq'
    exact
      (iterate_cyclePrev_zero_ne_zero P difference
        hdifferencePos hdifferenceLt) hzero

/-- No surviving tail coordinate fills the deepest point after the final
`C^ell` factor. -/
theorem tail_finalIndex_ne_directRotation_alpha_of_domain
    (P : Params) (coordinate : ℕ)
    (hcoordinate :
      P.directExponent + 1 ≤ coordinate)
    (hcoordinateEll : coordinate < P.ell)
    (hdomain : P.DirectDomain) :
    (cyclePrev P)^[P.ell - coordinate] P.directAlpha ≠
      directRotation P P.directAlpha := by
  have hexponentLt : P.directExponent < coordinate := by omega
  have hdomainDiff :
      P.ell - P.directExponent < P.cycle := by
    simp only [Params.DirectDomain, Params.ell,
      Params.directExponent, Params.cycle] at hdomain ⊢
    omega
  let difference := coordinate - P.directExponent
  have hdifferencePos : 0 < difference := by
    dsimp [difference]
    omega
  have hdifferenceLt : difference < P.cycle := by
    dsimp [difference]
    omega
  intro heq
  rw [directRotation_alpha_eq_iterate_cyclePrev_zero] at heq
  rw [← directAlpha_eq_iterate_cyclePrev_zero] at heq
  have heqCombined :
      (cyclePrev P)^[
          P.ell - coordinate + P.directExponent]
          (cycleZeroIndex P) =
        (cyclePrev P)^[P.ell] (cycleZeroIndex P) := by
    rw [Function.iterate_add_apply]
    exact heq
  have hellDecompose :
      P.ell =
        (P.ell - coordinate + P.directExponent) +
          difference := by
    dsimp [difference]
    omega
  have heq' :
      (cyclePrev P)^[
          P.ell - coordinate + P.directExponent]
          (cycleZeroIndex P) =
        (cyclePrev P)^[
          P.ell - coordinate + P.directExponent]
          ((cyclePrev P)^[difference] (cycleZeroIndex P)) := by
    calc
      (cyclePrev P)^[
          P.ell - coordinate + P.directExponent]
          (cycleZeroIndex P) =
        (cyclePrev P)^[P.ell] (cycleZeroIndex P) :=
          heqCombined
      _ =
        (cyclePrev P)^[
          (P.ell - coordinate + P.directExponent) +
            difference] (cycleZeroIndex P) := by
              rw [← hellDecompose]
      _ =
        (cyclePrev P)^[
          P.ell - coordinate + P.directExponent]
          ((cyclePrev P)^[difference] (cycleZeroIndex P)) :=
            Function.iterate_add_apply _ _ _ _
  have hzero :=
    ((cyclePrev_injective P).iterate
      (P.ell - coordinate + P.directExponent)) heq'
  exact
    (iterate_cyclePrev_zero_ne_zero P difference
      hdifferencePos hdifferenceLt) hzero.symm

theorem directRotation_injective (P : Params) :
    Function.Injective (directRotation P) := by
  unfold directRotation
  exact
    (cyclePrev_injective P).iterate P.ell |>.comp
      ((cycleNext_injective P).iterate P.directExponent)

theorem iterate_cycleNext_multiple_cycle (P : Params)
    (index : Fin P.cycle) (multiple : ℕ) :
    (cycleNext P)^[multiple * P.cycle] index = index := by
  rw [iterate_cycleNext]
  apply Fin.ext
  simp [cycleAdvance, Nat.add_mod, Nat.mod_eq_of_lt index.isLt]

theorem iterate_cyclePrev_multiple_cycle (P : Params)
    (index : Fin P.cycle) (multiple : ℕ) :
    (cyclePrev P)^[multiple * P.cycle] index = index := by
  have hinverse :=
    iterate_cyclePrev_cycleNext P index (multiple * P.cycle)
  rw [iterate_cycleNext_multiple_cycle] at hinverse
  exact hinverse

theorem directRotation_eq_cycleNext_directStep (P : Params)
    (index : Fin P.cycle) :
    directRotation P index =
      (cycleNext P)^[P.directStep] index := by
  apply (cycleNext_injective P).iterate P.ell
  unfold directRotation
  rw [iterate_cycleNext_cyclePrev]
  have hsum :
      P.ell + P.directStep =
        P.directExponent + (P.ell + 1) * P.cycle := by
    rw [Nat.add_comm P.ell P.directStep, P.directStep_add_ell]
    rw [Nat.mul_comm P.cycle (P.ell + 1)]
  rw [← Function.iterate_add_apply, hsum,
    Function.iterate_add_apply,
    iterate_cycleNext_multiple_cycle]

theorem directStep_coprime_cycle (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle) :
    Nat.Coprime P.directStep P.cycle := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let common := Nat.gcd P.directStep P.cycle
  have hcommonStep : common ∣ P.directStep :=
    Nat.gcd_dvd_left _ _
  have hcommonCycle : common ∣ P.cycle :=
    Nat.gcd_dvd_right _ _
  have hcommonSum :
      common ∣ P.directStep + 2 * P.m := by
    rw [P.directStep_add_twice_m]
    exact dvd_mul_of_dvd_right hcommonCycle (P.ell + 2)
  have hcommonTwice : common ∣ 2 * P.m :=
    (Nat.dvd_add_iff_right hcommonStep).2 hcommonSum
  have hcommonGcd :
      common ∣ Nat.gcd (2 * P.m) P.cycle :=
    Nat.dvd_gcd hcommonTwice hcommonCycle
  rw [(twice_m_coprime_cycle P hcoprime).gcd_eq_one] at hcommonGcd
  exact Nat.dvd_one.mp hcommonGcd

theorem directRotationIsCycle_of_coprime (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle) :
    DirectRotationIsCycle P := by
  intro index
  obtain ⟨count, hcount, hhit⟩ :=
    exists_modular_hit P.cycle_pos
      (directStep_coprime_cycle P hcoprime)
      (start := index.val) (target := P.directAlpha.val)
  rw [Nat.mod_eq_of_lt P.directAlpha.isLt] at hhit
  refine ⟨count, hcount, ?_⟩
  apply Fin.ext
  have hfunction :
      directRotation P = (cycleNext P)^[P.directStep] := by
    funext localIndex
    exact directRotation_eq_cycleNext_directStep P localIndex
  rw [hfunction, ← Function.iterate_mul]
  rw [Nat.mul_comm P.directStep count,
    iterate_cycleNext]
  exact hhit

theorem directRotation_period (P : Params) (index : Fin P.cycle) :
    (directRotation P)^[P.cycle] index = index := by
  let previous := (cyclePrev P)^[P.ell]
  let next := (cycleNext P)^[P.directExponent]
  have hcommute : Function.Commute previous next := by
    dsimp [previous, next]
    exact
      (show Function.Commute (cyclePrev P) (cycleNext P) from
        fun localIndex => by
          rw [cyclePrev_cycleNext, cycleNext_cyclePrev]
      ).iterate_iterate P.ell P.directExponent
  change (previous ∘ next)^[P.cycle] index = index
  rw [hcommute.comp_iterate]
  change
    ((cyclePrev P)^[P.ell])^[P.cycle]
        (((cycleNext P)^[P.directExponent])^[P.cycle] index) =
      index
  rw [← Function.iterate_mul, ← Function.iterate_mul]
  rw [iterate_cycleNext_multiple_cycle,
    iterate_cyclePrev_multiple_cycle]

theorem evalFrom_directBlockPower_intervalState (P : Params)
    (index : Fin P.cycle) (count : ℕ) :
    (automaton P).evalFrom (intervalState P index)
        (wordPow (directBlockWord P) count) =
      intervalState P ((directBlockIndex P)^[count] index) := by
  induction count generalizing index with
  | zero => simp
  | succ count ih =>
      rw [wordPow_succ, (automaton P).evalFrom_of_append,
        evalFrom_directBlockWord_intervalState, ih,
        Function.iterate_succ_apply]

/-- The first four factors `A^a s² C A` of the direct prefix. -/
def directCoreWord (P : Params) : List Letter :=
  (wordPow aWord P.directExponent ++ sSquared) ++
    (cWord ++ aWord)

/-- The direct prefix `Pcut = A^a s² C A C^ell`. -/
def directPrefixWord (P : Params) : List Letter :=
  directCoreWord P ++ wordPow cWord P.ell

/-- The full complementary candidate `Pcut B^(M-2)`. -/
def generalDirectCutWord (P : Params) : List Letter :=
  directPrefixWord P ++
    wordPow (directBlockWord P) (P.cycle - 2)

/-- The exact prefix obligation used by the cut-path argument: every
prefix image lies in `J` and avoids the unique deepest point
`rotation alpha`. -/
def DirectPrefixAvoidsDeepest (P : Params) : Prop :=
  ∀ state : State P, ∃ index : Fin P.cycle,
    index ≠ directRotation P P.directAlpha ∧
    (automaton P).evalFrom state (directPrefixWord P) =
      intervalState P index

/-- Exact pointwise form of the fourth line of equation (11): after
`A^a s² C A`, an image is global zero, is a nonzero local point of `J`,
or remains in the tail interval `[a+1, ell-1]`. -/
theorem evalFrom_directCoreWord_range (P : Params) (state : State P) :
    (automaton P).evalFrom state (directCoreWord P) =
        P.stateOfNat 0 ∨
    (∃ index : Fin P.cycle,
      index.val ≠ 0 ∧
      (automaton P).evalFrom state (directCoreWord P) =
        intervalState P index) ∨
    (∃ coordinate : ℕ,
      P.directExponent + 1 ≤ coordinate ∧ coordinate < P.ell ∧
      (automaton P).evalFrom state (directCoreWord P) =
        P.stateOfNat coordinate) := by
  rcases after_aPower_sSquared_interval_or_tail P state with
    ⟨index, hindex⟩ | ⟨coordinate, hcoordinate, hcoordinateEll,
      htail⟩
  · have hcore :
        (automaton P).evalFrom state (directCoreWord P) =
          cycleState P index := by
      rw [directCoreWord, (automaton P).evalFrom_of_append,
        hindex, evalFrom_cWord_aWord_intervalState]
    by_cases hzero : index.val = 0
    · left
      rw [hcore]
      have hindexZero :
          index = ⟨0, P.cycle_pos⟩ := Fin.ext hzero
      rw [hindexZero, cycleState_zero]
    · right
      left
      exact ⟨index, hzero, by
        rw [hcore]
        exact cycleState_of_ne_zero P index hzero⟩
  · right
    right
    refine ⟨coordinate, hcoordinate, hcoordinateEll, ?_⟩
    rw [directCoreWord, (automaton P).evalFrom_of_append,
      htail,
      evalFrom_cWord_aWord_tail P coordinate hcoordinate
        hcoordinateEll]

/-- The pointwise content of equations (11)--(15): throughout the
maximal prefix domain, `Pcut` sends every state into `J` and omits the
deepest point needed by the one-arc-cut collapse argument. -/
theorem directPrefix_avoidsDeepest_of_domain (P : Params)
    (hdomain : P.DirectDomain) :
    DirectPrefixAvoidsDeepest P := by
  intro state
  rcases evalFrom_directCoreWord_range P state with
    hzero | ⟨index, hindex, hinterval⟩ |
      ⟨coordinate, hcoordinate, hcoordinateEll, htail⟩
  · refine
      ⟨P.directAlpha,
        directAlpha_ne_directRotation_alpha_of_domain P hdomain,
        ?_⟩
    rw [directPrefixWord,
      (automaton P).evalFrom_of_append, hzero,
      evalFrom_cPower_ell_zero]
  · let finalIndex :=
      (cyclePrev P)^[P.ell] index
    have hfinal :
        finalIndex ≠ directRotation P P.directAlpha := by
      intro heq
      rw [directRotation_alpha_eq_iterate_cyclePrev_zero] at heq
      have hindexEq :
          index = cycleZeroIndex P :=
        ((cyclePrev_injective P).iterate P.ell) heq
      apply hindex
      have hval := congrArg Fin.val hindexEq
      simpa using hval
    refine ⟨finalIndex, hfinal, ?_⟩
    rw [directPrefixWord,
      (automaton P).evalFrom_of_append, hinterval,
      evalFrom_cPower_intervalState]
  · let finalIndex :=
      (cyclePrev P)^[P.ell - coordinate] P.directAlpha
    have hfinal :
        finalIndex ≠ directRotation P P.directAlpha :=
      tail_finalIndex_ne_directRotation_alpha_of_domain
        P coordinate hcoordinate hcoordinateEll hdomain
    refine ⟨finalIndex, hfinal, ?_⟩
    rw [directPrefixWord,
      (automaton P).evalFrom_of_append, htail,
      evalFrom_cPower_ell_tail P coordinate
        (by
          have := P.directExponent_pos
          omega)
        hcoordinateEll]

@[simp]
theorem length_directBlockWord (P : Params) :
    (directBlockWord P).length =
      2 * (P.directExponent + P.ell) := by
  simp [directBlockWord]
  omega

@[simp]
theorem length_directPrefixWord (P : Params) :
    (directPrefixWord P).length =
      2 * (P.directExponent + P.ell + 3) := by
  simp [directPrefixWord, directCoreWord]
  omega

@[simp]
theorem length_generalDirectCutWord (P : Params) :
    (generalDirectCutWord P).length =
      6 + 4 * (P.R + P.L + 1) * (2 * P.X + 2 * P.L + 5) := by
  simp [generalDirectCutWord, Params.directExponent, Params.ell,
    Params.cycle]
  ring

/-- Arithmetic form of the maximal prefix domain `ell - a < M`. -/
theorem directDomain_iff_ell_sub_exponent_lt_cycle (P : Params) :
    P.DirectDomain ↔
      P.ell - P.directExponent < P.cycle := by
  simp only [Params.DirectDomain, Params.ell, Params.directExponent,
    Params.cycle]
  omega

/-- The integral cost condition `f_W ≥ 3`, written without integer
subtraction. -/
def DirectSafe (P : Params) : Prop :=
  P.L ^ 2 + 3 * P.L + P.R + 3 ≤
    P.X ^ 2 + P.R ^ 2 + 2 * P.X

/-- The exact cost criterion for the complementary direct-cut word. -/
theorem length_generalDirectCutWord_le_cernyBound_iff (P : Params) :
    (generalDirectCutWord P).length ≤
        (automaton P).cernyBound ↔
      DirectSafe P := by
  simp only [length_generalDirectCutWord, DFA.cernyBound,
    Fintype.card_fin]
  rw [P.order_eq]
  have horder :
      2 * (P.X + P.R + P.L) + 5 - 1 =
        2 * (P.X + P.R + P.L) + 4 := by omega
  rw [horder]
  have hcost :
      6 + 4 * (P.R + P.L + 1) *
          (2 * P.X + 2 * P.L + 5) ≤
          (2 * (P.X + P.R + P.L) + 4) ^ 2 ↔
        10 + 4 * (P.L ^ 2 + 3 * P.L + P.R) ≤
          4 * (P.X ^ 2 + P.R ^ 2 + 2 * P.X) := by
    constructor <;> intro h <;> nlinarith
  rw [hcost]
  unfold DirectSafe
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem length_generalDirectCutWord_le_cernyBound (P : Params)
    (hsafe : DirectSafe P) :
    (generalDirectCutWord P).length ≤
      (automaton P).cernyBound :=
  (length_generalDirectCutWord_le_cernyBound_iff P).2 hsafe

/-- The complete reset argument, factored into its two mathematical
obligations: the modular rotation is one cycle, and the prefix deletes
its deepest point.  The graph-theoretic collapse itself is discharged by
`iterate_loopCut_period_sub_two`. -/
theorem generalDirectCut_isResetWord_of_dynamics (P : Params)
    (hcycle : DirectRotationIsCycle P)
    (hprefix : DirectPrefixAvoidsDeepest P) :
    (automaton P).IsResetWord (generalDirectCutWord P) := by
  refine ⟨intervalState P P.directAlpha, ?_⟩
  intro state
  obtain ⟨index, hdeleted, hprefixImage⟩ := hprefix state
  rw [generalDirectCutWord, (automaton P).evalFrom_of_append,
    hprefixImage, evalFrom_directBlockPower_intervalState]
  have hblockFunction :
      directBlockIndex P =
        loopCut (directRotation P) P.directAlpha := by
    funext localIndex
    exact directBlockIndex_eq_loopCut P localIndex
  rw [hblockFunction]
  congr 1
  exact iterate_loopCut_period_sub_two
    (directRotation P) P.directAlpha index P.cycle
    (by simp [Params.cycle])
    (directRotation_injective P)
    (directRotation_period P P.directAlpha) hcycle hdeleted

theorem generalDirectCut_isResetWord_of_coprime_of_prefix (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (hprefix : DirectPrefixAvoidsDeepest P) :
    (automaton P).IsResetWord (generalDirectCutWord P) :=
  generalDirectCut_isResetWord_of_dynamics P
    (directRotationIsCycle_of_coprime P hcoprime) hprefix

/-- The complementary direct word resets throughout its exact prefix
domain whenever the synchronization residue is coprime. -/
theorem generalDirectCut_isResetWord (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (hdomain : P.DirectDomain) :
    (automaton P).IsResetWord (generalDirectCutWord P) :=
  generalDirectCut_isResetWord_of_coprime_of_prefix P hcoprime
    (directPrefix_avoidsDeepest_of_domain P hdomain)

/-- A full usable Černý theorem once the two explicit symbolic dynamics
obligations above have been supplied. -/
theorem satisfiesCerny_of_generalDirectCut_dynamics (P : Params)
    (hcycle : DirectRotationIsCycle P)
    (hprefix : DirectPrefixAvoidsDeepest P)
    (hsafe : DirectSafe P) :
    (automaton P).SatisfiesCerny :=
  DFA.satisfiesCerny_of_resetWord (automaton P)
    (generalDirectCut_isResetWord_of_dynamics P
      hcycle hprefix)
    (length_generalDirectCutWord_le_cernyBound P hsafe)

theorem satisfiesCerny_of_generalDirectCut_coprime_of_prefix
    (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (hprefix : DirectPrefixAvoidsDeepest P)
    (hsafe : DirectSafe P) :
    (automaton P).SatisfiesCerny :=
  DFA.satisfiesCerny_of_resetWord (automaton P)
    (generalDirectCut_isResetWord_of_coprime_of_prefix P
      hcoprime hprefix)
    (length_generalDirectCutWord_le_cernyBound P hsafe)

/-- Full direct-cut Černý theorem: coprimality supplies the single
rotation cycle, `DirectDomain` supplies the deleted deepest point, and
`DirectSafe` is exactly the word-length condition. -/
theorem satisfiesCerny_of_generalDirectCut
    (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (hdomain : P.DirectDomain)
    (hsafe : DirectSafe P) :
    (automaton P).SatisfiesCerny :=
  DFA.satisfiesCerny_of_resetWord (automaton P)
    (generalDirectCut_isResetWord P hcoprime hdomain)
    (length_generalDirectCutWord_le_cernyBound P hsafe)

/-- Once the symbolic image/collapse argument establishes that the
displayed word resets, the exact cost lemma immediately yields the Černý
conclusion. -/
theorem satisfiesCerny_of_generalDirectCut_reset (P : Params)
    (hreset :
      (automaton P).IsResetWord (generalDirectCutWord P))
    (hsafe : DirectSafe P) :
    (automaton P).SatisfiesCerny :=
  DFA.satisfiesCerny_of_resetWord (automaton P) hreset
    (length_generalDirectCutWord_le_cernyBound P hsafe)

end DFA.CycleTree
