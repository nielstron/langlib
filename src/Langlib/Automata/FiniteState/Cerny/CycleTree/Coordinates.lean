module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.Definition

@[expose]
public section

/-!
# Coordinate lemmas for cycle-tree automata

The executable definitions in `Definition` use total modulo constructors.
This module records their mathematical behavior on the canonical interval.
These lemmas are the bridge between finite certificate replay and the
symbolic cut-rotation arguments.
-/

namespace DFA.CycleTree

open Params

@[simp]
theorem stateOfNat_val (P : Params) (coordinate : ℕ) :
    (P.stateOfNat coordinate).val = coordinate % P.order :=
  rfl

theorem stateOfNat_val_of_lt (P : Params) {coordinate : ℕ}
    (hcoordinate : coordinate < P.order) :
    (P.stateOfNat coordinate).val = coordinate := by
  simp [Params.stateOfNat, Nat.mod_eq_of_lt hcoordinate]

theorem stateOfNat_eq_of_lt (P : Params) {left right : ℕ}
    (hleft : left < P.order) (hright : right < P.order) :
    P.stateOfNat left = P.stateOfNat right ↔ left = right := by
  constructor
  · intro h
    have := congrArg Fin.val h
    change left % P.order = right % P.order at this
    rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at this
    exact this
  · exact congrArg P.stateOfNat

@[simp]
theorem stateOfNat_state_val (P : Params) (state : State P) :
    P.stateOfNat state.val = state := by
  apply Fin.ext
  simp [Params.stateOfNat, Nat.mod_eq_of_lt state.isLt]

@[simp]
theorem automaton_step_p (P : Params) (state : State P) :
    (automaton P).step state .p = pMap P state :=
  rfl

@[simp]
theorem automaton_step_s (P : Params) (state : State P) :
    (automaton P).step state .s = sMap P state :=
  rfl

theorem pMap_at_zero (P : Params) (state : State P)
    (hstate : state.val = 0) :
    pMap P state = P.stateOfNat 1 := by
  simp [pMap, hstate]

theorem pMap_at_one (P : Params) (state : State P)
    (hstate : state.val = 1) :
    pMap P state = P.stateOfNat P.ell := by
  have hone : (1 : ℕ) ≠ 0 := by omega
  simp [pMap, hstate, hone]

theorem pMap_at_ell (P : Params) (state : State P)
    (hstate : state.val = P.ell) :
    pMap P state = P.stateOfNat P.rho := by
  have hell0 : P.ell ≠ 0 := Nat.ne_of_gt P.ell_pos
  have hell1 : P.ell ≠ 1 := by simp [Params.ell]
  simp [pMap, hstate, hell0, hell1]

theorem pMap_at_rho (P : Params) (state : State P)
    (hstate : state.val = P.rho) :
    pMap P state = P.stateOfNat 0 := by
  have hrho0 : P.rho ≠ 0 := by simp [Params.rho, Params.m]
  have hrho1 : P.rho ≠ 1 := by simp [Params.rho, Params.m]
  have hrhoell : P.rho ≠ P.ell := by
    simp [Params.rho, Params.m, Params.ell]
    omega
  simp [pMap, hstate, hrho0, hrho1, hrhoell]

theorem pMap_before_ell (P : Params) (state : State P)
    (htwo : 2 ≤ state.val) (hstate : state.val < P.ell) :
    pMap P state = P.stateOfNat (P.ell + 1 - state.val) := by
  have hzero : state.val ≠ 0 := by omega
  have hone : state.val ≠ 1 := by omega
  have hell : state.val ≠ P.ell := by omega
  have hrho : state.val ≠ P.rho := by
    have := P.rho_eq
    omega
  simp [pMap, hzero, hone, hell, hrho, hstate]

theorem pMap_between_ell_rho (P : Params) (state : State P)
    (hell : P.ell < state.val) (hrho : state.val < P.rho) :
    pMap P state = P.stateOfNat (P.ell + P.rho - state.val) := by
  have hzero : state.val ≠ 0 := by omega
  have hone : state.val ≠ 1 := by
    have := P.ell_pos
    omega
  have hnell : state.val ≠ P.ell := by omega
  have hnrho : state.val ≠ P.rho := by omega
  have hnBeforeEll : ¬state.val < P.ell := by omega
  simp [pMap, hzero, hone, hnell, hnrho, hnBeforeEll, hrho]

theorem pMap_after_rho (P : Params) (state : State P)
    (hrho : P.rho < state.val) :
    pMap P state = P.stateOfNat (P.rho + P.order - state.val) := by
  have hrhoOne : 1 < P.rho := by simp [Params.rho, Params.m]
  have hzero : state.val ≠ 0 := by omega
  have hone : state.val ≠ 1 := by omega
  have hell : state.val ≠ P.ell := by
    have := P.rho_eq
    omega
  have hnrho : state.val ≠ P.rho := by omega
  have hnBeforeEll : ¬state.val < P.ell := by
    have := P.rho_eq
    omega
  have hnBeforeRho : ¬state.val < P.rho := by omega
  simp [pMap, hzero, hone, hell, hnrho, hnBeforeEll, hnBeforeRho]

theorem sMap_at_zero (P : Params) (state : State P)
    (hstate : state.val = 0) :
    sMap P state = P.stateOfNat (P.rho - 1) := by
  simp [sMap, hstate]

theorem sMap_at_ell (P : Params) (state : State P)
    (hstate : state.val = P.ell) :
    sMap P state = P.stateOfNat (P.rho - 1) := by
  have hell0 : P.ell ≠ 0 := Nat.ne_of_gt P.ell_pos
  simp [sMap, hstate, hell0]

theorem sMap_between_zero_ell (P : Params) (state : State P)
    (hzero : 0 < state.val) (hell : state.val < P.ell) :
    sMap P state = P.stateOfNat (P.ell - state.val) := by
  have hnzero : state.val ≠ 0 := by omega
  have hnell : state.val ≠ P.ell := by omega
  simp [sMap, hnzero, hnell, hell]

theorem sMap_between_ell_rho (P : Params) (state : State P)
    (hell : P.ell < state.val) (hrho : state.val < P.rho) :
    sMap P state =
      P.stateOfNat (P.ell + P.rho - 1 - state.val) := by
  have hnzero : state.val ≠ 0 := by omega
  have hnell : state.val ≠ P.ell := by omega
  have hnBeforeEll : ¬state.val < P.ell := by omega
  simp [sMap, hnzero, hnell, hnBeforeEll, hrho]

theorem sMap_at_or_after_rho (P : Params) (state : State P)
    (hrho : P.rho ≤ state.val) :
    sMap P state =
      P.stateOfNat (P.rho + P.order - 1 - state.val) := by
  have hrhoPos : 0 < P.rho := by simp [Params.rho, Params.m]
  have hnzero : state.val ≠ 0 := by omega
  have hnell : state.val ≠ P.ell := by
    have := P.rho_eq
    omega
  have hnBeforeEll : ¬state.val < P.ell := by
    have := P.rho_eq
    omega
  have hnBeforeRho : ¬state.val < P.rho := by omega
  simp [sMap, hnzero, hnell, hnBeforeEll, hnBeforeRho]

theorem pMap_twice_of_regular (P : Params) (state : State P)
    (hzero : state.val ≠ 0) (hone : state.val ≠ 1)
    (hell : state.val ≠ P.ell) (hrho : state.val ≠ P.rho) :
    pMap P (pMap P state) = state := by
  by_cases hBeforeEll : state.val < P.ell
  · have htwo : 2 ≤ state.val := by omega
    let reflected := P.ell + 1 - state.val
    have hreflectedTwo : 2 ≤ reflected := by
      dsimp [reflected]
      omega
    have hreflectedEll : reflected < P.ell := by
      dsimp [reflected]
      omega
    have hreflectedOrder : reflected < P.order :=
      hreflectedEll.trans P.ell_lt_order
    have hreflectedVal :
        (P.stateOfNat reflected).val = reflected :=
      stateOfNat_val_of_lt P hreflectedOrder
    rw [pMap_before_ell P state htwo hBeforeEll]
    rw [pMap_before_ell P (P.stateOfNat reflected)]
    · have hcoordinate :
          P.ell + 1 - reflected = state.val := by
        dsimp [reflected]
        omega
      rw [hreflectedVal, hcoordinate]
      exact stateOfNat_state_val P state
    · rw [hreflectedVal]
      exact hreflectedTwo
    · rw [hreflectedVal]
      exact hreflectedEll
  · by_cases hBeforeRho : state.val < P.rho
    · have hAfterEll : P.ell < state.val := by omega
      let reflected := P.ell + P.rho - state.val
      have hreflectedEll : P.ell < reflected := by
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
      rw [pMap_between_ell_rho P state hAfterEll hBeforeRho]
      rw [pMap_between_ell_rho P (P.stateOfNat reflected)]
      · have hcoordinate :
            P.ell + P.rho - reflected = state.val := by
          dsimp [reflected]
          omega
        rw [hreflectedVal, hcoordinate]
        exact stateOfNat_state_val P state
      · rw [hreflectedVal]
        exact hreflectedEll
      · rw [hreflectedVal]
        exact hreflectedRho
    · have hAfterRho : P.rho < state.val := by omega
      let reflected := P.rho + P.order - state.val
      have hreflectedRho : P.rho < reflected := by
        dsimp [reflected]
        omega
      have hreflectedOrder : reflected < P.order := by
        dsimp [reflected]
        omega
      have hreflectedVal :
          (P.stateOfNat reflected).val = reflected :=
        stateOfNat_val_of_lt P hreflectedOrder
      rw [pMap_after_rho P state hAfterRho]
      rw [pMap_after_rho P (P.stateOfNat reflected)]
      · have hcoordinate :
            P.rho + P.order - reflected = state.val := by
          dsimp [reflected]
          omega
        rw [hreflectedVal, hcoordinate]
        exact stateOfNat_state_val P state
      · rw [hreflectedVal]
        exact hreflectedRho

theorem pMap_rho_sub_one (P : Params) :
    pMap P (P.stateOfNat (P.rho - 1)) =
      P.stateOfNat (P.ell + 1) := by
  have hrhoPos : 0 < P.rho := by simp [Params.rho, Params.m]
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
    rw [pMap_at_ell P _]
    · rw [hrhoEq]
    · rw [hrhoPredVal, hrhoPredEq]
  · have hRPos : 0 < P.R := Nat.pos_of_ne_zero hR
    have hellPred : P.ell < P.rho - 1 := by
      rw [P.rho_eq]
      omega
    have hpredRho : P.rho - 1 < P.rho := by omega
    rw [pMap_between_ell_rho P _]
    · congr 1
      rw [hrhoPredVal]
      omega
    · rw [hrhoPredVal]
      exact hellPred
    · rw [hrhoPredVal]
      exact hpredRho

/-- The defect-one macro `A = sp` follows the hidden full cycle on every
nonzero state; the excluded coordinate `0` is redirected to `ell + 1`. -/
theorem evalFrom_aWord (P : Params) (state : State P) :
    (automaton P).evalFrom state aWord =
      if state.val = 0
      then P.stateOfNat (P.ell + 1)
      else P.stateOfNat (state.val + 1) := by
  simp only [aWord, DFA.evalFrom_cons, DFA.evalFrom_nil,
    automaton_step_s, automaton_step_p]
  by_cases hzero : state.val = 0
  · rw [sMap_at_zero P state hzero, pMap_rho_sub_one P]
    simp [hzero]
  by_cases hell : state.val = P.ell
  · rw [sMap_at_ell P state hell, pMap_rho_sub_one P]
    simp [hell]
  by_cases hBeforeEll : state.val < P.ell
  · have hstatePos : 0 < state.val := Nat.pos_of_ne_zero hzero
    let reflected := P.ell - state.val
    have hreflectedPos : 0 < reflected := by
      dsimp [reflected]
      omega
    have hreflectedEll : reflected < P.ell := by
      dsimp [reflected]
      omega
    have hreflectedOrder : reflected < P.order :=
      hreflectedEll.trans P.ell_lt_order
    have hreflectedVal :
        (P.stateOfNat reflected).val = reflected :=
      stateOfNat_val_of_lt P hreflectedOrder
    rw [sMap_between_zero_ell P state hstatePos hBeforeEll]
    by_cases hreflectedOne : reflected = 1
    · rw [pMap_at_one P _]
      · have hcoordinate : state.val + 1 = P.ell := by
          dsimp [reflected] at hreflectedOne
          omega
        simp [hzero, hcoordinate]
      · rw [hreflectedVal]
        exact hreflectedOne
    · have hreflectedTwo : 2 ≤ reflected := by omega
      rw [pMap_before_ell P _]
      · have hcoordinate :
            P.ell + 1 - reflected = state.val + 1 := by
          dsimp [reflected]
          omega
        rw [hreflectedVal, hcoordinate]
        simp [hzero]
      · rw [hreflectedVal]
        exact hreflectedTwo
      · rw [hreflectedVal]
        exact hreflectedEll
  by_cases hBeforeRho : state.val < P.rho
  · have hAfterEll : P.ell < state.val := by omega
    let reflected := P.ell + P.rho - 1 - state.val
    have hreflectedEllLe : P.ell ≤ reflected := by
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
    rw [sMap_between_ell_rho P state hAfterEll hBeforeRho]
    by_cases hreflectedEll : reflected = P.ell
    · rw [pMap_at_ell P _]
      · have hcoordinate : state.val + 1 = P.rho := by
          dsimp [reflected] at hreflectedEll
          omega
        simp [hzero, hcoordinate]
      · rw [hreflectedVal]
        exact hreflectedEll
    · have hAfterReflectedEll : P.ell < reflected := by omega
      rw [pMap_between_ell_rho P _]
      · have hcoordinate :
            P.ell + P.rho - reflected = state.val + 1 := by
          dsimp [reflected]
          omega
        rw [hreflectedVal, hcoordinate]
        simp [hzero]
      · rw [hreflectedVal]
        exact hAfterReflectedEll
      · rw [hreflectedVal]
        exact hreflectedRho
  · have hAtOrAfterRho : P.rho ≤ state.val := by omega
    let reflected := P.rho + P.order - 1 - state.val
    have hreflectedRhoLe : P.rho ≤ reflected := by
      dsimp [reflected]
      omega
    have hreflectedOrder : reflected < P.order := by
      dsimp [reflected]
      omega
    have hreflectedVal :
        (P.stateOfNat reflected).val = reflected :=
      stateOfNat_val_of_lt P hreflectedOrder
    rw [sMap_at_or_after_rho P state hAtOrAfterRho]
    by_cases hreflectedRho : reflected = P.rho
    · rw [pMap_at_rho P _]
      · have hlast : state.val + 1 = P.order := by
          dsimp [reflected] at hreflectedRho
          omega
        simp [hzero, hlast, Params.stateOfNat]
      · rw [hreflectedVal]
        exact hreflectedRho
    · have hAfterReflectedRho : P.rho < reflected := by omega
      rw [pMap_after_rho P _]
      · have hcoordinate :
            P.rho + P.order - reflected = state.val + 1 := by
          dsimp [reflected]
          omega
        rw [hreflectedVal, hcoordinate]
        simp [hzero]
      · rw [hreflectedVal]
        exact hAfterReflectedRho

theorem evalFrom_aPower_before_wrap (P : Params) (state : State P)
    (count : ℕ) (hstatePos : 0 < state.val)
    (hBeforeWrap : state.val + count < P.order) :
    (automaton P).evalFrom state (wordPow aWord count) =
      P.stateOfNat (state.val + count) := by
  induction count generalizing state with
  | zero =>
      simp
  | succ count ih =>
      rw [wordPow_succ, (automaton P).evalFrom_of_append, evalFrom_aWord]
      have hstateNe : state.val ≠ 0 := Nat.ne_of_gt hstatePos
      rw [if_neg hstateNe]
      have hnextLt : state.val + 1 < P.order := by omega
      have hnextVal :
          (P.stateOfNat (state.val + 1)).val = state.val + 1 :=
        stateOfNat_val_of_lt P hnextLt
      rw [ih]
      · congr 1
        rw [hnextVal]
        omega
      · rw [hnextVal]
        omega
      · rw [hnextVal]
        omega

theorem evalFrom_aPower_at_wrap (P : Params) (state : State P)
    (count : ℕ) (hstatePos : 0 < state.val)
    (hwrap : state.val + count = P.order) :
    (automaton P).evalFrom state (wordPow aWord count) =
      P.stateOfNat 0 := by
  have hcountPos : 0 < count := by
    have := state.isLt
    omega
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcountPos)
  have hBeforeFinal : state.val + previous < P.order := by omega
  rw [wordPow_succ_right, (automaton P).evalFrom_of_append,
    evalFrom_aPower_before_wrap P state previous hstatePos hBeforeFinal]
  have hcoordinateLt : state.val + previous < P.order := hBeforeFinal
  have hcoordinateVal :
      (P.stateOfNat (state.val + previous)).val =
        state.val + previous :=
    stateOfNat_val_of_lt P hcoordinateLt
  rw [evalFrom_aWord]
  have hcoordinatePos : 0 < state.val + previous := by omega
  have hcoordinateNe :
      (P.stateOfNat (state.val + previous)).val ≠ 0 := by
    rw [hcoordinateVal]
    omega
  rw [if_neg hcoordinateNe]
  have hsum : state.val + previous + 1 = P.order := by omega
  rw [hcoordinateVal]
  apply Fin.ext
  change (state.val + previous + 1) % P.order = 0 % P.order
  rw [hsum]
  simp

/-- Decode a coordinate on the `M = cycle`-point cycle of `A = sp`.
Index zero is the distinguished state `0`; positive indices `i` are the
global coordinates `ell + i`. -/
def cycleState (P : Params) (index : Fin P.cycle) : State P :=
  if index.val = 0
  then P.stateOfNat 0
  else P.stateOfNat (P.ell + index.val)

@[simp]
theorem cycleState_zero (P : Params) :
    cycleState P ⟨0, P.cycle_pos⟩ = P.stateOfNat 0 := by
  simp [cycleState]

theorem cycleState_of_ne_zero (P : Params) (index : Fin P.cycle)
    (hindex : index.val ≠ 0) :
    cycleState P index = P.stateOfNat (P.ell + index.val) := by
  simp [cycleState, hindex]

theorem cycleState_val_of_ne_zero (P : Params) (index : Fin P.cycle)
    (hindex : index.val ≠ 0) :
    (cycleState P index).val = P.ell + index.val := by
  rw [cycleState_of_ne_zero P index hindex]
  apply stateOfNat_val_of_lt
  simp [Params.order]

theorem cycleState_injective (P : Params) :
    Function.Injective (cycleState P) := by
  intro left right heq
  by_cases hleft : left.val = 0
  · have hleftEq : left = ⟨0, P.cycle_pos⟩ := Fin.ext hleft
    subst left
    by_cases hright : right.val = 0
    · exact Fin.ext hright.symm
    · have hrightVal := cycleState_val_of_ne_zero P right hright
      have hzeroVal :
          (cycleState P ⟨0, P.cycle_pos⟩).val = 0 := by
        rw [cycleState_zero]
        exact stateOfNat_val_of_lt P P.order_pos
      have heqVal := congrArg Fin.val heq
      rw [hzeroVal, hrightVal] at heqVal
      omega
  · by_cases hright : right.val = 0
    · have hleftVal := cycleState_val_of_ne_zero P left hleft
      have heqVal := congrArg Fin.val heq
      have hrightEq : right = ⟨0, P.cycle_pos⟩ := Fin.ext hright
      subst right
      have hzeroVal :
          (cycleState P ⟨0, P.cycle_pos⟩).val = 0 := by
        rw [cycleState_zero]
        exact stateOfNat_val_of_lt P P.order_pos
      rw [hleftVal, hzeroVal] at heqVal
      omega
    · apply Fin.ext
      have hleftVal := cycleState_val_of_ne_zero P left hleft
      have hrightVal := cycleState_val_of_ne_zero P right hright
      have heqVal := congrArg Fin.val heq
      omega

/-- Successor on the `cycle` coordinates, with explicit wrap at `M`. -/
def cycleNext (P : Params) (index : Fin P.cycle) : Fin P.cycle :=
  if hnext : index.val + 1 < P.cycle
  then ⟨index.val + 1, hnext⟩
  else ⟨0, P.cycle_pos⟩

theorem cycleNext_of_lt (P : Params) (index : Fin P.cycle)
    (hnext : index.val + 1 < P.cycle) :
    cycleNext P index = ⟨index.val + 1, hnext⟩ := by
  simp [cycleNext, hnext]

theorem cycleNext_of_not_lt (P : Params) (index : Fin P.cycle)
    (hnext : ¬index.val + 1 < P.cycle) :
    cycleNext P index = ⟨0, P.cycle_pos⟩ := by
  simp [cycleNext, hnext]

/-- Advance a local cycle coordinate by an arbitrary natural offset. -/
def cycleAdvance (P : Params) (index : Fin P.cycle)
    (count : ℕ) : Fin P.cycle :=
  ⟨(index.val + count) % P.cycle,
    Nat.mod_lt _ P.cycle_pos⟩

@[simp]
theorem cycleAdvance_zero (P : Params) (index : Fin P.cycle) :
    cycleAdvance P index 0 = index := by
  apply Fin.ext
  simp [cycleAdvance, Nat.mod_eq_of_lt index.isLt]

theorem cycleNext_cycleAdvance (P : Params)
    (index : Fin P.cycle) (count : ℕ) :
    cycleNext P (cycleAdvance P index count) =
      cycleAdvance P index (count + 1) := by
  let remainder := (index.val + count) % P.cycle
  have hremainderLt : remainder < P.cycle :=
    Nat.mod_lt _ P.cycle_pos
  have honeLt : 1 < P.cycle := by
    simp [Params.cycle]
  have hadvanceVal :
      (cycleAdvance P index count).val = remainder := rfl
  by_cases hnext : remainder + 1 < P.cycle
  · rw [cycleNext_of_lt P _ (by
      rw [hadvanceVal]
      exact hnext)]
    apply Fin.ext
    change remainder + 1 = (index.val + (count + 1)) % P.cycle
    rw [show index.val + (count + 1) =
      (index.val + count) + 1 by omega, Nat.add_mod]
    simp [Nat.mod_eq_of_lt honeLt, Nat.mod_eq_of_lt hnext,
      remainder]
  · have hlast : remainder + 1 = P.cycle := by omega
    rw [cycleNext_of_not_lt P _ (by
      rw [hadvanceVal]
      exact hnext)]
    apply Fin.ext
    change 0 = (index.val + (count + 1)) % P.cycle
    rw [show index.val + (count + 1) =
      (index.val + count) + 1 by omega, Nat.add_mod]
    simp [Nat.mod_eq_of_lt honeLt, remainder, hlast]

theorem iterate_cycleNext (P : Params) (index : Fin P.cycle)
    (count : ℕ) :
    (cycleNext P)^[count] index = cycleAdvance P index count := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, cycleNext_cycleAdvance]

/-- `A = sp` is successor on its `M`-cycle. -/
theorem evalFrom_aWord_cycleState (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (cycleState P index) aWord =
      cycleState P (cycleNext P index) := by
  by_cases hindex : index.val = 0
  · have hindexEq : index = ⟨0, P.cycle_pos⟩ := Fin.ext hindex
    subst index
    have honeLt : 0 + 1 < P.cycle := by
      simp [Params.cycle]
    rw [cycleState_zero, evalFrom_aWord]
    have hzeroVal : (P.stateOfNat 0).val = 0 :=
      stateOfNat_val_of_lt P P.order_pos
    rw [hzeroVal, if_pos rfl, cycleNext_of_lt P _ honeLt]
    have hnextNe :
        (⟨(⟨0, P.cycle_pos⟩ : Fin P.cycle).val + 1, honeLt⟩ :
          Fin P.cycle).val ≠ 0 := by
      simp
    rw [cycleState_of_ne_zero P _ hnextNe]
  · rw [cycleState_of_ne_zero P index hindex, evalFrom_aWord]
    have hstateVal :
        (P.stateOfNat (P.ell + index.val)).val =
          P.ell + index.val := by
      apply stateOfNat_val_of_lt
      simp [Params.order]
    rw [hstateVal, if_neg (by
      have := P.ell_pos
      omega)]
    by_cases hnext : index.val + 1 < P.cycle
    · rw [cycleNext_of_lt P index hnext]
      have hnextNe :
          (⟨index.val + 1, hnext⟩ : Fin P.cycle).val ≠ 0 := by
        simp
      rw [cycleState_of_ne_zero P _ hnextNe]
      congr 1
    · have hlast : index.val + 1 = P.cycle := by omega
      rw [cycleNext_of_not_lt P index hnext, cycleState_zero]
      have hsum : P.ell + index.val + 1 = P.order := by
        simp [Params.order]
        omega
      apply Fin.ext
      change (P.ell + index.val + 1) % P.order = 0 % P.order
      rw [hsum]
      simp

theorem evalFrom_aPower_cycleState (P : Params)
    (index : Fin P.cycle) (count : ℕ) :
    (automaton P).evalFrom (cycleState P index)
        (wordPow aWord count) =
      cycleState P ((cycleNext P)^[count] index) := by
  induction count generalizing index with
  | zero => simp
  | succ count ih =>
      rw [wordPow_succ, (automaton P).evalFrom_of_append,
        evalFrom_aWord_cycleState, ih]
      rfl

/-- Decode a coordinate on the interval `J = {ell, ..., order - 1}`. -/
def intervalState (P : Params) (index : Fin P.cycle) : State P :=
  P.stateOfNat (P.ell + index.val)

@[simp]
theorem intervalState_val (P : Params) (index : Fin P.cycle) :
    (intervalState P index).val = P.ell + index.val := by
  apply stateOfNat_val_of_lt
  simp [Params.order]

theorem intervalState_injective (P : Params) :
    Function.Injective (intervalState P) := by
  intro left right heq
  apply Fin.ext
  have heqVal := congrArg Fin.val heq
  simp only [intervalState_val] at heqVal
  omega

theorem exists_intervalState_eq (P : Params) (state : State P)
    (hstate : P.ell ≤ state.val) :
    ∃ index : Fin P.cycle, intervalState P index = state := by
  have hindex : state.val - P.ell < P.cycle := by
    apply (Nat.sub_lt_iff_lt_add' hstate).2
    exact state.isLt
  let index : Fin P.cycle := ⟨state.val - P.ell, hindex⟩
  refine ⟨index, ?_⟩
  unfold intervalState
  have hcoordinate : P.ell + index.val = state.val := by
    dsimp [index]
    exact Nat.add_sub_of_le hstate
  rw [hcoordinate]
  exact stateOfNat_state_val P state

theorem evalFrom_aWord_intervalState (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (intervalState P index) aWord =
      cycleState P (cycleNext P index) := by
  rw [evalFrom_aWord]
  have hintervalVal := intervalState_val P index
  rw [hintervalVal, if_neg (by
    have := P.ell_pos
    omega)]
  rw [← evalFrom_aWord_cycleState]
  rw [evalFrom_aWord]
  by_cases hindex : index.val = 0
  · have hindexEq : index = ⟨0, P.cycle_pos⟩ := Fin.ext hindex
    subst index
    rw [cycleState_zero]
    have hzeroVal : (P.stateOfNat 0).val = 0 :=
      stateOfNat_val_of_lt P P.order_pos
    rw [hzeroVal, if_pos rfl]
    rfl
  · rw [cycleState_of_ne_zero P index hindex]
    have hcoordinateVal :
        (P.stateOfNat (P.ell + index.val)).val =
          P.ell + index.val := by
      apply stateOfNat_val_of_lt
      simp [Params.order]
    rw [hcoordinateVal, if_neg (by
      have := P.ell_pos
      omega)]

theorem evalFrom_aPower_intervalState (P : Params)
    (index : Fin P.cycle) (count : ℕ) :
    (automaton P).evalFrom (intervalState P index)
        (wordPow aWord (count + 1)) =
      cycleState P ((cycleNext P)^[count + 1] index) := by
  rw [wordPow_succ, (automaton P).evalFrom_of_append,
    evalFrom_aWord_intervalState, evalFrom_aPower_cycleState]
  rfl

theorem evalFrom_aPower_intervalState_of_pos (P : Params)
    (index : Fin P.cycle) (count : ℕ) (hcount : 0 < count) :
    (automaton P).evalFrom (intervalState P index)
        (wordPow aWord count) =
      cycleState P ((cycleNext P)^[count] index) := by
  obtain ⟨previous, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcount)
  exact evalFrom_aPower_intervalState P index previous

def cycleOneIndex (P : Params) : Fin P.cycle :=
  ⟨1, by
    simp [Params.cycle]⟩

@[simp]
theorem cycleOneIndex_val (P : Params) :
    (cycleOneIndex P).val = 1 :=
  rfl

theorem cycleState_oneIndex (P : Params) :
    cycleState P (cycleOneIndex P) =
      P.stateOfNat (P.ell + 1) := by
  have honeNe : (cycleOneIndex P).val ≠ 0 := by
    rw [cycleOneIndex_val]
    omega
  rw [cycleState_of_ne_zero P _ honeNe, cycleOneIndex_val]

/-- Every nonzero tail coordinate has entered the `A`-cycle by time
`2m`. -/
theorem exists_aPower_twom_cycleState_of_tail (P : Params)
    (state : State P) (hstatePos : 0 < state.val)
    (hstateTail : state.val < P.ell) :
    ∃ index : Fin P.cycle,
      (automaton P).evalFrom state (wordPow aWord (2 * P.m)) =
        cycleState P index := by
  let entry := P.ell + 1 - state.val
  let remaining := 2 * P.m - entry
  have htwom : 2 * P.m = P.ell + 2 * P.R := by
    simp [Params.m, Params.ell]
    omega
  have hentryPos : 0 < entry := by
    dsimp [entry]
    omega
  have hentryLe : entry ≤ 2 * P.m := by
    dsimp [entry]
    omega
  have hsum : entry + remaining = 2 * P.m := by
    dsimp [remaining]
    exact Nat.add_sub_of_le hentryLe
  have hcoordinate : state.val + entry = P.ell + 1 := by
    dsimp [entry]
    omega
  have hellOneLt : P.ell + 1 < P.order := by
    simp [Params.order, Params.cycle]
  refine
    ⟨(cycleNext P)^[remaining] (cycleOneIndex P), ?_⟩
  calc
    (automaton P).evalFrom state (wordPow aWord (2 * P.m)) =
      (automaton P).evalFrom state
        (wordPow aWord entry ++ wordPow aWord remaining) := by
          rw [← wordPow_add, hsum]
    _ = (automaton P).evalFrom
        ((automaton P).evalFrom state (wordPow aWord entry))
        (wordPow aWord remaining) := by
          rw [(automaton P).evalFrom_of_append]
    _ = (automaton P).evalFrom
        (cycleState P (cycleOneIndex P))
        (wordPow aWord remaining) := by
          rw [evalFrom_aPower_before_wrap P state entry hstatePos]
          · rw [hcoordinate, cycleState_oneIndex]
          · rw [hcoordinate]
            exact hellOneLt
    _ = cycleState P
        ((cycleNext P)^[remaining] (cycleOneIndex P)) :=
      evalFrom_aPower_cycleState P (cycleOneIndex P) remaining

/-- After `ell` copies of `A`, every state has entered the hidden
`cycle`-state encoding. -/
theorem exists_aPower_ell_cycleState (P : Params) (state : State P) :
    ∃ index : Fin P.cycle,
      (automaton P).evalFrom state (wordPow aWord P.ell) =
        cycleState P index := by
  by_cases hzero : state.val = 0
  · have hstateEq : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
    refine ⟨(cycleNext P)^[P.ell] zeroIndex, ?_⟩
    rw [hstateEq, ← cycleState_zero]
    exact evalFrom_aPower_cycleState P zeroIndex P.ell
  · have hstatePos : 0 < state.val := Nat.pos_of_ne_zero hzero
    by_cases hbefore : state.val + P.ell < P.order
    · have hindex : state.val < P.cycle := by
        simp [Params.order] at hbefore
        omega
      let index : Fin P.cycle := ⟨state.val, hindex⟩
      refine ⟨index, ?_⟩
      rw [evalFrom_aPower_before_wrap P state P.ell
        hstatePos hbefore]
      rw [cycleState_of_ne_zero P index (by
        dsimp [index]
        exact hzero)]
      congr 1
      dsimp [index]
      omega
    · by_cases hwrap : state.val + P.ell = P.order
      · let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
        refine ⟨zeroIndex, ?_⟩
        rw [evalFrom_aPower_at_wrap P state P.ell hstatePos hwrap,
          cycleState_zero]
      · have hafter : P.order < state.val + P.ell := by omega
        let entry := P.order - state.val
        let remaining := P.ell - entry
        have hentryPos : 0 < entry := by
          dsimp [entry]
          exact Nat.sub_pos_of_lt state.isLt
        have hentryLe : entry ≤ P.ell := by
          dsimp [entry]
          omega
        have hsum : entry + remaining = P.ell := by
          dsimp [remaining]
          exact Nat.add_sub_of_le hentryLe
        have hwrapEntry : state.val + entry = P.order := by
          dsimp [entry]
          exact Nat.add_sub_of_le (Nat.le_of_lt state.isLt)
        let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
        refine ⟨(cycleNext P)^[remaining] zeroIndex, ?_⟩
        calc
          (automaton P).evalFrom state (wordPow aWord P.ell) =
              (automaton P).evalFrom state
                (wordPow aWord entry ++
                  wordPow aWord remaining) := by
                    rw [← wordPow_add, hsum]
          _ = (automaton P).evalFrom
                ((automaton P).evalFrom state
                  (wordPow aWord entry))
                (wordPow aWord remaining) := by
                  rw [(automaton P).evalFrom_of_append]
          _ = (automaton P).evalFrom
                (cycleState P zeroIndex)
                (wordPow aWord remaining) := by
                  rw [evalFrom_aPower_at_wrap P state entry
                    hstatePos hwrapEntry, cycleState_zero]
          _ = cycleState P
                ((cycleNext P)^[remaining] zeroIndex) :=
              evalFrom_aPower_cycleState P zeroIndex remaining

/-- Local `J`-coordinate of the distinguished global state `rho`. -/
def rhoIndex (P : Params) : Fin P.cycle :=
  ⟨2 * P.R + 1, by
    simp [Params.cycle]
    omega⟩

@[simp]
theorem rhoIndex_val (P : Params) :
    (rhoIndex P).val = 2 * P.R + 1 :=
  rfl

theorem ell_add_rhoIndex (P : Params) :
    P.ell + (rhoIndex P).val = P.rho := by
  rw [P.rho_eq]
  simp
  omega

theorem intervalState_rhoIndex (P : Params) :
    intervalState P (rhoIndex P) = P.stateOfNat P.rho := by
  unfold intervalState
  rw [ell_add_rhoIndex]

/-- The square of `p` consists of the two central transpositions
`0 ↔ ell` and `1 ↔ rho`, and fixes every other coordinate. -/
theorem evalFrom_pSquared (P : Params) (state : State P) :
    (automaton P).evalFrom state pSquared =
      if state.val = 0 then P.stateOfNat P.ell
      else if state.val = P.ell then P.stateOfNat 0
      else if state.val = 1 then P.stateOfNat P.rho
      else if state.val = P.rho then P.stateOfNat 1
      else state := by
  have hellZero : P.ell ≠ 0 := Nat.ne_of_gt P.ell_pos
  have hellOne : P.ell ≠ 1 := by simp [Params.ell]
  have honeEll : (1 : ℕ) ≠ P.ell := Ne.symm hellOne
  have hrhoZero : P.rho ≠ 0 := by simp [Params.rho, Params.m]
  have hrhoOne : P.rho ≠ 1 := by simp [Params.rho, Params.m]
  have hrhoEll : P.rho ≠ P.ell := by
    simp [Params.rho, Params.m, Params.ell]
    omega
  simp only [pSquared, DFA.evalFrom_cons, DFA.evalFrom_nil, automaton_step_p]
  by_cases hzero : state.val = 0
  · rw [pMap_at_zero P state hzero]
    have honeVal : (P.stateOfNat 1).val = 1 := by
      apply stateOfNat_val_of_lt
      simp [Params.order, Params.ell, Params.cycle]
      omega
    rw [pMap_at_one P _ honeVal]
    simp [hzero]
  by_cases hell : state.val = P.ell
  · rw [pMap_at_ell P state hell]
    have hrhoVal : (P.stateOfNat P.rho).val = P.rho :=
      stateOfNat_val_of_lt P P.rho_lt_order
    rw [pMap_at_rho P _ hrhoVal]
    simp [hell, hellZero]
  by_cases hone : state.val = 1
  · rw [pMap_at_one P state hone]
    have hellVal : (P.stateOfNat P.ell).val = P.ell :=
      stateOfNat_val_of_lt P P.ell_lt_order
    rw [pMap_at_ell P _ hellVal]
    simp [hone, honeEll]
  by_cases hrho : state.val = P.rho
  · rw [pMap_at_rho P state hrho]
    have hzeroVal : (P.stateOfNat 0).val = 0 := by
      apply stateOfNat_val_of_lt
      exact P.order_pos
    rw [pMap_at_zero P _ hzeroVal]
    simp [hrho, hrhoZero, hrhoOne, hrhoEll]
  rw [pMap_twice_of_regular P state hzero hone hell hrho]
  simp [hzero, hell, hone, hrho]

theorem evalFrom_pSquared_cycleState (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (cycleState P index) pSquared =
      if index = rhoIndex P
      then P.stateOfNat 1
      else intervalState P index := by
  rw [evalFrom_pSquared]
  by_cases hindexZero : index.val = 0
  · have hindexEq :
        index = ⟨0, P.cycle_pos⟩ := Fin.ext hindexZero
    rw [hindexEq, cycleState_zero]
    have hzeroVal : (P.stateOfNat 0).val = 0 :=
      stateOfNat_val_of_lt P P.order_pos
    have hzeroNeRho :
        (⟨0, P.cycle_pos⟩ : Fin P.cycle) ≠ rhoIndex P := by
      intro heq
      have heqVal := congrArg Fin.val heq
      simp at heqVal
    rw [hzeroVal, if_pos rfl, if_neg hzeroNeRho]
    rfl
  · have hindexVal :=
      cycleState_val_of_ne_zero P index hindexZero
    rw [hindexVal]
    have hnotZero : P.ell + index.val ≠ 0 := by
      have := P.ell_pos
      omega
    have hnotEll : P.ell + index.val ≠ P.ell := by omega
    have hnotOne : P.ell + index.val ≠ 1 := by
      have hellTwo : 2 ≤ P.ell := by simp [Params.ell]
      omega
    rw [if_neg hnotZero, if_neg hnotEll, if_neg hnotOne]
    by_cases hindexRho : index = rhoIndex P
    · rw [if_pos hindexRho]
      have hcoordinate : P.ell + index.val = P.rho := by
        rw [hindexRho]
        exact ell_add_rhoIndex P
      rw [if_pos hcoordinate]
    · rw [if_neg hindexRho]
      have hcoordinate : P.ell + index.val ≠ P.rho := by
        intro heq
        apply hindexRho
        apply Fin.ext
        have hrho := ell_add_rhoIndex P
        omega
      rw [if_neg hcoordinate]
      exact cycleState_of_ne_zero P index hindexZero

/-- Local rotation coordinate reached by the `A^(2m)` part of `D`. -/
def dIndex (P : Params) (index : Fin P.cycle) : Fin P.cycle :=
  (cycleNext P)^[2 * P.m] index

theorem dIndex_eq_advance (P : Params) (index : Fin P.cycle) :
    dIndex P index = cycleAdvance P index (2 * P.m) := by
  exact iterate_cycleNext P index (2 * P.m)

/-- On `J`, the macro `D = A^(2m)p²` is a cyclic advance with one
distinguished image redirected to the sink `1`. -/
theorem evalFrom_dWord_intervalState (P : Params)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (intervalState P index) (dWord P) =
      if dIndex P index = rhoIndex P
      then P.stateOfNat 1
      else intervalState P (dIndex P index) := by
  have htwomPos : 0 < 2 * P.m := by
    simp [Params.m]
  rw [dWord, (automaton P).evalFrom_of_append,
    evalFrom_aPower_intervalState_of_pos P index (2 * P.m) htwomPos,
    evalFrom_pSquared]
  let advanced := dIndex P index
  change
    (if (cycleState P advanced).val = 0 then P.stateOfNat P.ell
    else if (cycleState P advanced).val = P.ell then P.stateOfNat 0
    else if (cycleState P advanced).val = 1 then P.stateOfNat P.rho
    else if (cycleState P advanced).val = P.rho then P.stateOfNat 1
    else cycleState P advanced) =
      if advanced = rhoIndex P
      then P.stateOfNat 1
      else intervalState P advanced
  by_cases hadvancedZero : advanced.val = 0
  · have hadvancedEq :
        advanced = ⟨0, P.cycle_pos⟩ := Fin.ext hadvancedZero
    rw [hadvancedEq, cycleState_zero]
    have hzeroVal : (P.stateOfNat 0).val = 0 :=
      stateOfNat_val_of_lt P P.order_pos
    have hzeroNeRho :
        (⟨0, P.cycle_pos⟩ : Fin P.cycle) ≠ rhoIndex P := by
      intro heq
      have heqVal := congrArg Fin.val heq
      simp at heqVal
    rw [hzeroVal, if_pos rfl, if_neg hzeroNeRho]
    rfl
  · have hadvancedVal :=
      cycleState_val_of_ne_zero P advanced hadvancedZero
    rw [hadvancedVal]
    have hnotZero : P.ell + advanced.val ≠ 0 := by
      have := P.ell_pos
      omega
    have hnotEll : P.ell + advanced.val ≠ P.ell := by omega
    have hnotOne : P.ell + advanced.val ≠ 1 := by
      have hellTwo : 2 ≤ P.ell := by simp [Params.ell]
      omega
    rw [if_neg hnotZero, if_neg hnotEll, if_neg hnotOne]
    by_cases hadvancedRho : advanced = rhoIndex P
    · rw [if_pos hadvancedRho]
      have hcoordinate : P.ell + advanced.val = P.rho := by
        rw [hadvancedRho]
        exact ell_add_rhoIndex P
      rw [if_pos hcoordinate]
    · rw [if_neg hadvancedRho]
      have hcoordinate : P.ell + advanced.val ≠ P.rho := by
        intro heq
        apply hadvancedRho
        apply Fin.ext
        have hrho := ell_add_rhoIndex P
        omega
      rw [if_neg hcoordinate]
      exact cycleState_of_ne_zero P advanced hadvancedZero

/-- The sink coordinate `1` is fixed by the macro `D`. -/
theorem evalFrom_dWord_one (P : Params) :
    (automaton P).evalFrom (P.stateOfNat 1) (dWord P) =
      P.stateOfNat 1 := by
  have honeLt : 1 < P.order := by
    simp [Params.order, Params.ell, Params.cycle]
    omega
  have honeVal : (P.stateOfNat 1).val = 1 :=
    stateOfNat_val_of_lt P honeLt
  have hcoordinate : 1 + 2 * P.m = P.rho := by
    simp [Params.rho]
    omega
  have hbefore : (P.stateOfNat 1).val + 2 * P.m < P.order := by
    rw [honeVal, hcoordinate]
    exact P.rho_lt_order
  rw [dWord, (automaton P).evalFrom_of_append,
    evalFrom_aPower_before_wrap P (P.stateOfNat 1) (2 * P.m)
      (by rw [honeVal]; omega) hbefore, honeVal, hcoordinate,
    evalFrom_pSquared]
  have hrhoVal : (P.stateOfNat P.rho).val = P.rho :=
    stateOfNat_val_of_lt P P.rho_lt_order
  have hrhoZero : P.rho ≠ 0 := by simp [Params.rho, Params.m]
  have hrhoOne : P.rho ≠ 1 := by simp [Params.rho, Params.m]
  have hrhoEll : P.rho ≠ P.ell := by
    rw [P.rho_eq]
    omega
  rw [hrhoVal]
  simp [hrhoZero, hrhoOne, hrhoEll]

theorem evalFrom_dWord_of_aPower_cycleState (P : Params)
    (state : State P) (index : Fin P.cycle)
    (himage :
      (automaton P).evalFrom state (wordPow aWord (2 * P.m)) =
        cycleState P index) :
    (automaton P).evalFrom state (dWord P) =
      if index = rhoIndex P
      then P.stateOfNat 1
      else intervalState P index := by
  rw [dWord, (automaton P).evalFrom_of_append, himage,
    evalFrom_pSquared_cycleState]

/-- One application of `D` sends every state either to its fixed sink or
into the interval `J`. -/
theorem dWord_image_sink_or_interval (P : Params) (state : State P) :
    (automaton P).evalFrom state (dWord P) = P.stateOfNat 1 ∨
      ∃ index : Fin P.cycle,
        index ≠ rhoIndex P ∧
        (automaton P).evalFrom state (dWord P) =
          intervalState P index := by
  by_cases hzero : state.val = 0
  · have hstateEq : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
    have himage :
        (automaton P).evalFrom state
            (wordPow aWord (2 * P.m)) =
          cycleState P ((cycleNext P)^[2 * P.m] zeroIndex) := by
      rw [hstateEq, ← cycleState_zero]
      exact evalFrom_aPower_cycleState P zeroIndex (2 * P.m)
    let imageIndex := (cycleNext P)^[2 * P.m] zeroIndex
    by_cases hcut : imageIndex = rhoIndex P
    · left
      rw [evalFrom_dWord_of_aPower_cycleState P state imageIndex
        himage, if_pos hcut]
    · right
      exact ⟨imageIndex, hcut, by
        rw [evalFrom_dWord_of_aPower_cycleState P state imageIndex
          himage, if_neg hcut]⟩
  · by_cases hone : state.val = 1
    · left
      have hstateEq : state = P.stateOfNat 1 := by
        rw [← hone]
        exact (stateOfNat_state_val P state).symm
      rw [hstateEq, evalFrom_dWord_one]
    · by_cases htail : state.val < P.ell
      · have hstatePos : 0 < state.val := Nat.pos_of_ne_zero hzero
        obtain ⟨imageIndex, himage⟩ :=
          exists_aPower_twom_cycleState_of_tail P state
            hstatePos htail
        by_cases hcut : imageIndex = rhoIndex P
        · left
          rw [evalFrom_dWord_of_aPower_cycleState P state imageIndex
            himage, if_pos hcut]
        · right
          exact ⟨imageIndex, hcut, by
            rw [evalFrom_dWord_of_aPower_cycleState P state imageIndex
              himage, if_neg hcut]⟩
      · have hinterval : P.ell ≤ state.val := by omega
        obtain ⟨index, hstateEq⟩ :=
          exists_intervalState_eq P state hinterval
        by_cases hcut : dIndex P index = rhoIndex P
        · left
          rw [← hstateEq, evalFrom_dWord_intervalState, if_pos hcut]
        · right
          exact ⟨dIndex P index, hcut, by
            rw [← hstateEq, evalFrom_dWord_intervalState, if_neg hcut]⟩

end DFA.CycleTree
