module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.ResidualWords

@[expose]
public section

/-!
# The large-band five-depth prefix

This file verifies the parameter-uniform prefix `largePrefix`.  The proof
follows the fifteen-row image-complement calculation from the residual
large-band argument, but records each row as a pointwise invariant.  This
is sufficient for `PrefixAvoidsDeep` and avoids introducing finite-set
enumerations whose cardinality depends on the parameters.
-/

namespace DFA.CycleTree

open Params

private theorem evalFrom_aPower_zero_of_pos_lt_cycle
    (P : Params) (count : ℕ) (hcountPos : 0 < count)
    (hcountLt : count < P.cycle) :
    (automaton P).evalFrom (P.stateOfNat 0)
        (wordPow aWord count) =
      P.stateOfNat (P.ell + count) := by
  let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
  rw [← cycleState_zero P,
    evalFrom_aPower_cycleState P zeroIndex count,
    iterate_cycleNext]
  have hadvanceVal :
      (cycleAdvance P zeroIndex count).val = count := by
    change (0 + count) % P.cycle = count
    simpa using Nat.mod_eq_of_lt hcountLt
  have hadvanceNe :
      (cycleAdvance P zeroIndex count).val ≠ 0 := by
    rw [hadvanceVal]
    omega
  rw [cycleState_of_ne_zero P _ hadvanceNe, hadvanceVal]

private theorem evalFrom_aPower_after_wrap
    (P : Params) (state : State P) (count : ℕ)
    (hstatePos : 0 < state.val)
    (hafter : P.order < state.val + count)
    (hbeforeSecond : state.val + count < P.order + P.cycle) :
    (automaton P).evalFrom state (wordPow aWord count) =
      P.stateOfNat
        (P.ell + (state.val + count - P.order)) := by
  let toWrap := P.order - state.val
  let remaining := count - toWrap
  have hstateLe : state.val ≤ P.order := Nat.le_of_lt state.isLt
  have hwrap : state.val + toWrap = P.order := by
    dsimp [toWrap]
    omega
  have htoWrapLe : toWrap ≤ count := by
    dsimp [toWrap]
    omega
  have hsplit : toWrap + remaining = count := by
    dsimp [remaining]
    exact Nat.add_sub_of_le htoWrapLe
  have hremainingPos : 0 < remaining := by
    dsimp [remaining, toWrap]
    omega
  have hremainingLt : remaining < P.cycle := by
    dsimp [remaining, toWrap]
    omega
  have hremaining :
      remaining = state.val + count - P.order := by
    dsimp [remaining, toWrap]
    omega
  calc
    (automaton P).evalFrom state (wordPow aWord count) =
        (automaton P).evalFrom state
          (wordPow aWord toWrap ++
            wordPow aWord remaining) := by
              rw [← wordPow_add, hsplit]
    _ = (automaton P).evalFrom
          ((automaton P).evalFrom state
            (wordPow aWord toWrap))
          (wordPow aWord remaining) := by
            rw [(automaton P).evalFrom_of_append]
    _ = (automaton P).evalFrom (P.stateOfNat 0)
          (wordPow aWord remaining) := by
            rw [evalFrom_aPower_at_wrap P state toWrap
              hstatePos hwrap]
    _ = P.stateOfNat (P.ell + remaining) :=
      evalFrom_aPower_zero_of_pos_lt_cycle P remaining
        hremainingPos hremainingLt
    _ = P.stateOfNat
          (P.ell + (state.val + count - P.order)) := by
            rw [hremaining]

/-- Exhaustive coordinate behavior of a short positive power of `A`.
All powers occurring in the large-prefix table are shorter than `cycle`,
so at most one wrap needs to be considered. -/
private theorem evalFrom_aPower_val_cases
    (P : Params) (state : State P) (count : ℕ)
    (hcountPos : 0 < count) (hcountLt : count < P.cycle) :
    let target :=
      (automaton P).evalFrom state (wordPow aWord count)
    (state.val = 0 ∧ target.val = P.ell + count) ∨
    (0 < state.val ∧ state.val + count < P.order ∧
      target.val = state.val + count) ∨
    (0 < state.val ∧ state.val + count = P.order ∧
      target.val = 0) ∨
    (0 < state.val ∧ P.order < state.val + count ∧
      target.val =
        P.ell + (state.val + count - P.order)) := by
  dsimp only
  by_cases hzero : state.val = 0
  · left
    refine ⟨hzero, ?_⟩
    have hstate :
        state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    rw [hstate,
      evalFrom_aPower_zero_of_pos_lt_cycle P count
        hcountPos hcountLt]
    apply stateOfNat_val_of_lt
    simp [Params.order]
    exact hcountLt
  have hstatePos : 0 < state.val := Nat.pos_of_ne_zero hzero
  by_cases hbefore : state.val + count < P.order
  · right; left
    refine ⟨hstatePos, hbefore, ?_⟩
    rw [evalFrom_aPower_before_wrap P state count
      hstatePos hbefore]
    exact stateOfNat_val_of_lt P hbefore
  by_cases hwrap : state.val + count = P.order
  · right; right; left
    refine ⟨hstatePos, hwrap, ?_⟩
    rw [evalFrom_aPower_at_wrap P state count
      hstatePos hwrap]
    exact stateOfNat_val_of_lt P P.order_pos
  · right; right; right
    have hafter : P.order < state.val + count := by omega
    have hbeforeSecond :
        state.val + count < P.order + P.cycle := by
      have := state.isLt
      omega
    refine ⟨hstatePos, hafter, ?_⟩
    rw [evalFrom_aPower_after_wrap P state count
      hstatePos hafter hbeforeSecond]
    apply stateOfNat_val_of_lt
    have hremainder :
        state.val + count - P.order < P.cycle := by
      omega
    simpa [Params.order] using
      Nat.add_lt_add_left hremainder P.ell

private theorem evalFrom_pSquared_val_cases
    (P : Params) (state : State P) :
    let target := (automaton P).evalFrom state pSquared
    (state.val = 0 ∧ target.val = P.ell) ∨
    (state.val = P.ell ∧ target.val = 0) ∨
    (state.val = 1 ∧ target.val = P.rho) ∨
    (state.val = P.rho ∧ target.val = 1) ∨
    (state.val ≠ 0 ∧ state.val ≠ P.ell ∧
      state.val ≠ 1 ∧ state.val ≠ P.rho ∧
      target.val = state.val) := by
  dsimp only
  rw [evalFrom_pSquared]
  by_cases hzero : state.val = 0
  · left
    refine ⟨hzero, ?_⟩
    rw [if_pos hzero]
    exact stateOfNat_val_of_lt P P.ell_lt_order
  rw [if_neg hzero]
  by_cases hell : state.val = P.ell
  · right; left
    refine ⟨hell, ?_⟩
    rw [if_pos hell]
    exact stateOfNat_val_of_lt P P.order_pos
  rw [if_neg hell]
  by_cases hone : state.val = 1
  · right; right; left
    refine ⟨hone, ?_⟩
    rw [if_pos hone]
    exact stateOfNat_val_of_lt P P.rho_lt_order
  rw [if_neg hone]
  by_cases hrho : state.val = P.rho
  · right; right; right; left
    refine ⟨hrho, ?_⟩
    rw [if_pos hrho]
    apply stateOfNat_val_of_lt
    have := P.ell_lt_order
    omega
  · right; right; right; right
    simp [hzero, hell, hone, hrho]

private theorem pMap_val_cases (P : Params) (state : State P) :
    let target := pMap P state
    (state.val = 0 ∧ target.val = 1) ∨
    (state.val = 1 ∧ target.val = P.ell) ∨
    (state.val = P.ell ∧ target.val = P.rho) ∨
    (state.val = P.rho ∧ target.val = 0) ∨
    (2 ≤ state.val ∧ state.val < P.ell ∧
      target.val = P.ell + 1 - state.val) ∨
    (P.ell < state.val ∧ state.val < P.rho ∧
      target.val = P.ell + P.rho - state.val) ∨
    (P.rho < state.val ∧
      target.val = P.rho + P.order - state.val) := by
  dsimp only
  by_cases hzero : state.val = 0
  · left
    refine ⟨hzero, ?_⟩
    rw [pMap_at_zero P state hzero]
    apply stateOfNat_val_of_lt
    exact (show 1 < P.ell by simp [Params.ell]).trans
      P.ell_lt_order
  by_cases hone : state.val = 1
  · right; left
    refine ⟨hone, ?_⟩
    rw [pMap_at_one P state hone]
    exact stateOfNat_val_of_lt P P.ell_lt_order
  by_cases hell : state.val = P.ell
  · right; right; left
    refine ⟨hell, ?_⟩
    rw [pMap_at_ell P state hell]
    exact stateOfNat_val_of_lt P P.rho_lt_order
  by_cases hrho : state.val = P.rho
  · right; right; right; left
    refine ⟨hrho, ?_⟩
    rw [pMap_at_rho P state hrho]
    exact stateOfNat_val_of_lt P P.order_pos
  by_cases hbeforeEll : state.val < P.ell
  · right; right; right; right; left
    have htwo : 2 ≤ state.val := by omega
    refine ⟨htwo, hbeforeEll, ?_⟩
    rw [pMap_before_ell P state htwo hbeforeEll]
    apply stateOfNat_val_of_lt
    have := P.ell_lt_order
    omega
  by_cases hbeforeRho : state.val < P.rho
  · right; right; right; right; right; left
    have hafterEll : P.ell < state.val := by omega
    refine ⟨hafterEll, hbeforeRho, ?_⟩
    rw [pMap_between_ell_rho P state hafterEll hbeforeRho]
    apply stateOfNat_val_of_lt
    have := P.rho_lt_order
    omega
  · right; right; right; right; right; right
    have hafterRho : P.rho < state.val := by omega
    refine ⟨hafterRho, ?_⟩
    rw [pMap_after_rho P state hafterRho]
    apply stateOfNat_val_of_lt
    have := P.rho_lt_order
    have := state.isLt
    omega

private theorem sMap_val_cases (P : Params) (state : State P) :
    let target := sMap P state
    (state.val = 0 ∧ target.val = P.rho - 1) ∨
    (state.val = P.ell ∧ target.val = P.rho - 1) ∨
    (0 < state.val ∧ state.val < P.ell ∧
      target.val = P.ell - state.val) ∨
    (P.ell < state.val ∧ state.val < P.rho ∧
      target.val = P.ell + P.rho - 1 - state.val) ∨
    (P.rho ≤ state.val ∧
      target.val = P.rho + P.order - 1 - state.val) := by
  dsimp only
  by_cases hzero : state.val = 0
  · left
    refine ⟨hzero, ?_⟩
    rw [sMap_at_zero P state hzero]
    apply stateOfNat_val_of_lt
    have := P.rho_lt_order
    omega
  by_cases hell : state.val = P.ell
  · right; left
    refine ⟨hell, ?_⟩
    rw [sMap_at_ell P state hell]
    apply stateOfNat_val_of_lt
    have := P.rho_lt_order
    omega
  by_cases hbeforeEll : state.val < P.ell
  · right; right; left
    have hstatePos : 0 < state.val := by omega
    refine ⟨hstatePos, hbeforeEll, ?_⟩
    rw [sMap_between_zero_ell P state hstatePos hbeforeEll]
    apply stateOfNat_val_of_lt
    have := P.ell_lt_order
    omega
  by_cases hbeforeRho : state.val < P.rho
  · right; right; right; left
    have hafterEll : P.ell < state.val := by omega
    refine ⟨hafterEll, hbeforeRho, ?_⟩
    rw [sMap_between_ell_rho P state hafterEll hbeforeRho]
    apply stateOfNat_val_of_lt
    have := P.rho_lt_order
    omega
  · right; right; right; right
    have hatRho : P.rho ≤ state.val := by omega
    refine ⟨hatRho, ?_⟩
    rw [sMap_at_or_after_rho P state hatRho]
    apply stateOfNat_val_of_lt
    have := state.isLt
    have := P.rho_lt_order
    omega

private def LargeRow1 (P : Params) (state : State P) : Prop :=
  state.val ≠ 1

private def LargeRow2 (P : Params) (state : State P) : Prop :=
  state.val ≠ P.rho

private def LargeRow3 (P : Params) (state : State P) : Prop :=
  ¬(1 ≤ state.val ∧ state.val ≤ P.ell - 1) ∧
  state.val ≠ P.rho + P.ell - 1

private def LargeRow4 (P : Params) (state : State P) : Prop :=
  ¬(state.val ≤ P.ell - 1) ∧
  state.val ≠ P.cycle

private def LargeRow5 (P : Params) (state : State P) : Prop :=
  ¬(1 ≤ state.val ∧ state.val ≤ P.ell) ∧
  state.val ≠ 2 * P.ell

private def LargeRow6 (P : Params) (state : State P) : Prop :=
  state.val ≠ 0 ∧
  ¬(2 ≤ state.val ∧ state.val ≤ P.ell - 1) ∧
  state.val ≠ 2 * P.ell ∧ state.val ≠ P.rho

private def LargeRow7 (P : Params) (X L : ℕ)
    (state : State P) : Prop :=
  ¬(1 ≤ state.val ∧ state.val ≤ P.ell) ∧
  state.val ≠ 2 * L + 3 ∧
  state.val ≠ 4 * L - 2 * X + 4

private def LargeRow8 (P : Params) (X L : ℕ)
    (state : State P) : Prop :=
  ¬(2 ≤ state.val ∧ state.val ≤ P.ell) ∧
  state.val ≠ 2 * P.ell ∧ state.val ≠ P.rho ∧
  state.val ≠ 2 * L + 6 * X + 8

private def LargeRow9 (P : Params) (X L : ℕ)
    (state : State P) : Prop :=
  ¬(1 ≤ state.val ∧ state.val ≤ P.ell - 1) ∧
  state.val ≠ 6 * X + 5 ∧
  state.val ≠ P.rho + P.ell - 1 ∧
  state.val ≠ 2 * L + 8 * X + 9

private def LargeRow10 (P : Params) (X L : ℕ)
    (state : State P) : Prop :=
  ¬(state.val ≤ P.ell - 1) ∧
  state.val ≠ 2 * L - 2 * X + 1 ∧
  state.val ≠ 4 * L - 4 * X + 2 ∧
  state.val ≠ P.cycle

private def LargeRow11 (P : Params) (X L : ℕ)
    (state : State P) : Prop :=
  ¬(1 ≤ state.val ∧ state.val ≤ P.ell) ∧
  state.val ≠ 2 * P.ell ∧
  state.val ≠ 8 * X + 7 ∧
  state.val ≠ 2 * L + 6 * X + 8

private def LargeRow12 (P : Params) (X L : ℕ)
    (state : State P) : Prop :=
  state.val ≠ 0 ∧
  ¬(2 ≤ state.val ∧ state.val ≤ P.ell - 1) ∧
  state.val ≠ 2 * P.ell ∧
  state.val ≠ 8 * X + 7 ∧
  state.val ≠ P.rho ∧
  state.val ≠ 2 * L + 6 * X + 8

private def LargeRow13 (P : Params) (X L : ℕ)
    (state : State P) : Prop :=
  ¬(1 ≤ state.val ∧ state.val ≤ P.ell) ∧
  state.val ≠ 2 * L - 4 * X ∧
  state.val ≠ 2 * L + 3 ∧
  state.val ≠ 4 * L - 6 * X + 1 ∧
  state.val ≠ 4 * L - 2 * X + 4

private def LargeRow14 (P : Params) (X L : ℕ)
    (state : State P) : Prop :=
  ¬(2 ≤ state.val ∧ state.val ≤ P.ell) ∧
  state.val ≠ 2 * P.ell ∧
  state.val ≠ 8 * X + 7 ∧
  state.val ≠ P.rho ∧
  state.val ≠ 2 * L + 6 * X + 8 ∧
  state.val ≠ 2 * L + 10 * X + 11

private def LargeRow15 (P : Params) (X L : ℕ)
    (state : State P) : Prop :=
  state.val ≠ 0 ∧
  ¬(2 ≤ state.val ∧ state.val ≤ P.ell - 1) ∧
  state.val ≠ 2 * P.ell ∧
  state.val ≠ 8 * X + 7 ∧
  state.val ≠ P.rho ∧
  state.val ≠ 2 * L + 6 * X + 8 ∧
  state.val ≠ 2 * L + 10 * X + 11

private theorem largeRow1_of_aWord (X L : ℕ)
    (state : State (residualParams X L)) :
    LargeRow1 (residualParams X L)
      ((automaton (residualParams X L)).evalFrom state aWord) := by
  have hcases :=
    evalFrom_aPower_val_cases (residualParams X L) state 1
      (by omega) (by
        simp [residualParams, Params.cycle])
  simp [wordPow] at hcases
  simp only [LargeRow1]
  simp only [residualParams, Params.ell, Params.order,
    Params.cycle] at hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ <;> omega

private theorem largeRow2_of_pSquared {X L : ℕ}
    {state : State (residualParams X L)}
    (hstate : LargeRow1 (residualParams X L) state) :
    LargeRow2 (residualParams X L)
      ((automaton (residualParams X L)).evalFrom state pSquared) := by
  have hcases :=
    evalFrom_pSquared_val_cases (residualParams X L) state
  simp only [LargeRow1] at hstate
  simp only [LargeRow2]
  simp only [residualParams, Params.ell, Params.m, Params.rho]
    at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, _, _, _, htarget⟩ <;> omega

private theorem largeRow3_of_aPower {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow2 (residualParams X L) state) :
    LargeRow3 (residualParams X L)
      ((automaton (residualParams X L)).evalFrom state
        (wordPow aWord ((residualParams X L).ell - 1))) := by
  have hcountPos : 0 < (residualParams X L).ell - 1 := by
    simp [residualParams, Params.ell]
  have hcountLt :
      (residualParams X L).ell - 1 <
        (residualParams X L).cycle := by
    simp only [Large] at hlarge
    simp [residualParams, Params.ell, Params.cycle]
    omega
  have hcases :=
    evalFrom_aPower_val_cases (residualParams X L) state
      ((residualParams X L).ell - 1) hcountPos hcountLt
  simp only [LargeRow2] at hstate
  simp only [LargeRow3]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ <;> omega

private theorem largeRow4_of_sMap {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow3 (residualParams X L) state) :
    LargeRow4 (residualParams X L)
      (sMap (residualParams X L) state) := by
  have hcases := sMap_val_cases (residualParams X L) state
  simp only [LargeRow3] at hstate
  simp only [LargeRow4]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, htarget⟩ <;> omega

private theorem largeRow5_of_aPower {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow4 (residualParams X L) state) :
    LargeRow5 (residualParams X L)
      ((automaton (residualParams X L)).evalFrom state
        (wordPow aWord (4 * X + 4))) := by
  have hcountPos : 0 < 4 * X + 4 := by omega
  have hcountLt :
      4 * X + 4 < (residualParams X L).cycle := by
    simp only [Large] at hlarge
    simp [residualParams, Params.cycle]
    omega
  have hcases :=
    evalFrom_aPower_val_cases (residualParams X L) state
      (4 * X + 4) hcountPos hcountLt
  simp only [LargeRow4] at hstate
  simp only [LargeRow5]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.cycle,
    Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ <;> omega

private theorem largeRow6_of_pSquared {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow5 (residualParams X L) state) :
    LargeRow6 (residualParams X L)
      ((automaton (residualParams X L)).evalFrom state pSquared) := by
  have hcases :=
    evalFrom_pSquared_val_cases (residualParams X L) state
  simp only [LargeRow5] at hstate
  simp only [LargeRow6]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, _, _, _, htarget⟩ <;> omega

private theorem largeRow7_of_aPower {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow6 (residualParams X L) state) :
    LargeRow7 (residualParams X L) X L
      ((automaton (residualParams X L)).evalFrom state
        (wordPow aWord (2 * L - 4 * X - 1))) := by
  have hcountPos : 0 < 2 * L - 4 * X - 1 := by
    simp only [Large] at hlarge
    omega
  have hcountLt :
      2 * L - 4 * X - 1 <
        (residualParams X L).cycle := by
    simp [residualParams, Params.cycle]
    omega
  have hcases :=
    evalFrom_aPower_val_cases (residualParams X L) state
      (2 * L - 4 * X - 1) hcountPos hcountLt
  simp only [LargeRow6] at hstate
  simp only [LargeRow7]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ <;> omega

private theorem largeRow8_of_pMap {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow7 (residualParams X L) X L state) :
    LargeRow8 (residualParams X L) X L
      (pMap (residualParams X L) state) := by
  have hcases := pMap_val_cases (residualParams X L) state
  simp only [LargeRow7] at hstate
  simp only [LargeRow8]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, htarget⟩ <;> omega

private theorem largeRow9_of_aPower {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow8 (residualParams X L) X L state) :
    LargeRow9 (residualParams X L) X L
      ((automaton (residualParams X L)).evalFrom state
        (wordPow aWord ((residualParams X L).ell - 1))) := by
  have hcountPos : 0 < (residualParams X L).ell - 1 := by
    simp [residualParams, Params.ell]
  have hcountLt :
      (residualParams X L).ell - 1 <
        (residualParams X L).cycle := by
    simp only [Large] at hlarge
    simp [residualParams, Params.ell, Params.cycle]
    omega
  have hcases :=
    evalFrom_aPower_val_cases (residualParams X L) state
      ((residualParams X L).ell - 1) hcountPos hcountLt
  simp only [LargeRow8] at hstate
  simp only [LargeRow9]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ <;> omega

private theorem largeRow10_of_sMap {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow9 (residualParams X L) X L state) :
    LargeRow10 (residualParams X L) X L
      (sMap (residualParams X L) state) := by
  have hcases := sMap_val_cases (residualParams X L) state
  simp only [LargeRow9] at hstate
  simp only [LargeRow10]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, htarget⟩ <;> omega

private theorem largeRow11_of_aPower {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow10 (residualParams X L) X L state) :
    LargeRow11 (residualParams X L) X L
      ((automaton (residualParams X L)).evalFrom state
        (wordPow aWord (8 * X + 7))) := by
  have hcountPos : 0 < 8 * X + 7 := by omega
  have hcountLt :
      8 * X + 7 < (residualParams X L).cycle := by
    simp only [Large] at hlarge
    simp [residualParams, Params.cycle]
    omega
  have hcases :=
    evalFrom_aPower_val_cases (residualParams X L) state
      (8 * X + 7) hcountPos hcountLt
  simp only [LargeRow10] at hstate
  simp only [LargeRow11]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.cycle,
    Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ <;> omega

private theorem largeRow12_of_pSquared {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow11 (residualParams X L) X L state) :
    LargeRow12 (residualParams X L) X L
      ((automaton (residualParams X L)).evalFrom state pSquared) := by
  have hcases :=
    evalFrom_pSquared_val_cases (residualParams X L) state
  simp only [LargeRow11] at hstate
  simp only [LargeRow12]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, _, _, _, htarget⟩ <;> omega

private theorem largeRow13_of_aPower {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow12 (residualParams X L) X L state) :
    LargeRow13 (residualParams X L) X L
      ((automaton (residualParams X L)).evalFrom state
        (wordPow aWord (2 * L - 8 * X - 4))) := by
  have hcountPos : 0 < 2 * L - 8 * X - 4 := by
    simp only [Large] at hlarge
    omega
  have hcountLt :
      2 * L - 8 * X - 4 <
        (residualParams X L).cycle := by
    simp [residualParams, Params.cycle]
    omega
  have hcases :=
    evalFrom_aPower_val_cases (residualParams X L) state
      (2 * L - 8 * X - 4) hcountPos hcountLt
  simp only [LargeRow12] at hstate
  simp only [LargeRow13]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ <;> omega

private theorem largeRow14_of_pMap {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow13 (residualParams X L) X L state) :
    LargeRow14 (residualParams X L) X L
      (pMap (residualParams X L) state) := by
  have hcases := pMap_val_cases (residualParams X L) state
  simp only [LargeRow13] at hstate
  simp only [LargeRow14]
  simp only [Large] at hlarge
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hcases ⊢
  rcases hcases with
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, htarget⟩ <;> omega

private theorem largeRow15_of_sSquared {X L : ℕ}
    (hlarge : Large X L)
    {state : State (residualParams X L)}
    (hstate : LargeRow14 (residualParams X L) X L state) :
    LargeRow15 (residualParams X L) X L
      ((automaton (residualParams X L)).evalFrom state sSquared) := by
  let first := sMap (residualParams X L) state
  have hfirst := sMap_val_cases (residualParams X L) state
  have hsecond := sMap_val_cases (residualParams X L) first
  change LargeRow15 (residualParams X L) X L
    (sMap (residualParams X L)
      (sMap (residualParams X L) state))
  simp only [LargeRow14] at hstate
  simp only [LargeRow15]
  simp only [Large] at hlarge
  dsimp only [first] at hsecond
  simp only [residualParams, Params.ell, Params.m, Params.rho,
    Params.cycle, Params.order] at hstate hfirst hsecond ⊢
  rcases hfirst with
    ⟨_, hfirstTarget⟩ |
    ⟨_, hfirstTarget⟩ |
    ⟨_, _, hfirstTarget⟩ |
    ⟨_, _, hfirstTarget⟩ |
    ⟨_, hfirstTarget⟩ <;>
  rcases hsecond with
    ⟨_, htarget⟩ |
    ⟨_, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, _, htarget⟩ |
    ⟨_, htarget⟩ <;> omega

private theorem evalFrom_largePrefix_largeRow15 {X L : ℕ}
    (hlarge : Large X L)
    (state : State (residualParams X L)) :
    LargeRow15 (residualParams X L) X L
      ((automaton (residualParams X L)).evalFrom state
        (largePrefix X L)) := by
  let P := residualParams X L
  let q1 := (automaton P).evalFrom state aWord
  let q2 := (automaton P).evalFrom q1 pSquared
  let q3 := (automaton P).evalFrom q2
    (wordPow aWord (P.ell - 1))
  let q4 := sMap P q3
  let q5 := (automaton P).evalFrom q4
    (wordPow aWord (4 * X + 4))
  let q6 := (automaton P).evalFrom q5 pSquared
  let q7 := (automaton P).evalFrom q6
    (wordPow aWord (2 * L - 4 * X - 1))
  let q8 := pMap P q7
  let q9 := (automaton P).evalFrom q8
    (wordPow aWord (P.ell - 1))
  let q10 := sMap P q9
  let q11 := (automaton P).evalFrom q10
    (wordPow aWord (8 * X + 7))
  let q12 := (automaton P).evalFrom q11 pSquared
  let q13 := (automaton P).evalFrom q12
    (wordPow aWord (2 * L - 8 * X - 4))
  let q14 := pMap P q13
  let q15 := (automaton P).evalFrom q14 sSquared
  have h1 : LargeRow1 P q1 := by
    dsimp only [P, q1]
    exact largeRow1_of_aWord X L state
  have h2 : LargeRow2 P q2 := by
    dsimp only [P, q2]
    exact largeRow2_of_pSquared h1
  have h3 : LargeRow3 P q3 := by
    dsimp only [P, q3]
    exact largeRow3_of_aPower hlarge h2
  have h4 : LargeRow4 P q4 := by
    dsimp only [P, q4]
    exact largeRow4_of_sMap hlarge h3
  have h5 : LargeRow5 P q5 := by
    dsimp only [P, q5]
    exact largeRow5_of_aPower hlarge h4
  have h6 : LargeRow6 P q6 := by
    dsimp only [P, q6]
    exact largeRow6_of_pSquared hlarge h5
  have h7 : LargeRow7 P X L q7 := by
    dsimp only [P, q7]
    exact largeRow7_of_aPower hlarge h6
  have h8 : LargeRow8 P X L q8 := by
    dsimp only [P, q8]
    exact largeRow8_of_pMap hlarge h7
  have h9 : LargeRow9 P X L q9 := by
    dsimp only [P, q9]
    exact largeRow9_of_aPower hlarge h8
  have h10 : LargeRow10 P X L q10 := by
    dsimp only [P, q10]
    exact largeRow10_of_sMap hlarge h9
  have h11 : LargeRow11 P X L q11 := by
    dsimp only [P, q11]
    exact largeRow11_of_aPower hlarge h10
  have h12 : LargeRow12 P X L q12 := by
    dsimp only [P, q12]
    exact largeRow12_of_pSquared hlarge h11
  have h13 : LargeRow13 P X L q13 := by
    dsimp only [P, q13]
    exact largeRow13_of_aPower hlarge h12
  have h14 : LargeRow14 P X L q14 := by
    dsimp only [P, q14]
    exact largeRow14_of_pMap hlarge h13
  have h15 : LargeRow15 P X L q15 := by
    dsimp only [P, q15]
    exact largeRow15_of_sSquared hlarge h14
  simpa only [largePrefix, P, q1, q2, q3, q4, q5, q6, q7,
    q8, q9, q10, q11, q12, q13, q14, q15,
    DFA.evalFrom_of_append, DFA.evalFrom_cons, DFA.evalFrom_nil,
    automaton_step_p, automaton_step_s] using h15

private theorem residual_deep_five_values {X L : ℕ}
    (hlarge : Large X L)
    {index : Fin (residualParams X L).cycle}
    (hdeep : IsDeepIndex (residualParams X L) 5 index) :
    (residualParams X L).ell + index.val =
        (residualParams X L).rho ∨
    (residualParams X L).ell + index.val =
        2 * (residualParams X L).ell ∨
    (residualParams X L).ell + index.val =
        2 * L + 6 * X + 8 ∨
    (residualParams X L).ell + index.val =
        8 * X + 7 ∨
    (residualParams X L).ell + index.val =
        2 * L + 10 * X + 11 := by
  rcases hdeep with ⟨offset, hoffset, rfl⟩
  have hoffsetCases :
      offset = 0 ∨ offset = 1 ∨ offset = 2 ∨
        offset = 3 ∨ offset = 4 := by
    omega
  rcases hoffsetCases with
    rfl | rfl | rfl | rfl | rfl
  · left
    simp only [Function.iterate_zero_apply]
    exact ell_add_rhoIndex (residualParams X L)
  · right; left
    have hval :
        ((dIndex (residualParams X L))^[1]
          (rhoIndex (residualParams X L))).val =
          2 * X + 2 := by
      rw [iterate_dIndex]
      change
        (((rhoIndex (residualParams X L)).val +
          1 * (2 * (residualParams X L).m)) %
            (residualParams X L).cycle) =
          2 * X + 2
      rw [rhoIndex_val]
      have hdecomp :
          2 * (residualParams X L).R + 1 +
              1 * (2 * (residualParams X L).m) =
            (residualParams X L).cycle + (2 * X + 2) := by
        simp [residualParams, Params.m, Params.cycle]
        omega
      have hremainder :
          2 * X + 2 < (residualParams X L).cycle := by
        simp only [Large] at hlarge
        simp [residualParams, Params.cycle]
        omega
      rw [hdecomp, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hremainder]
    rw [hval]
    simp [residualParams, Params.ell]
    omega
  · right; right; left
    have hval :
        ((dIndex (residualParams X L))^[2]
          (rhoIndex (residualParams X L))).val =
          4 * X + 2 * L + 6 := by
      rw [iterate_dIndex]
      change
        (((rhoIndex (residualParams X L)).val +
          2 * (2 * (residualParams X L).m)) %
            (residualParams X L).cycle) =
          4 * X + 2 * L + 6
      rw [rhoIndex_val]
      have hdecomp :
          2 * (residualParams X L).R + 1 +
              2 * (2 * (residualParams X L).m) =
            (residualParams X L).cycle +
              (4 * X + 2 * L + 6) := by
        simp [residualParams, Params.m, Params.cycle]
        omega
      have hremainder :
          4 * X + 2 * L + 6 <
            (residualParams X L).cycle := by
        simp only [Large] at hlarge
        simp [residualParams, Params.cycle]
        omega
      rw [hdecomp, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hremainder]
    rw [hval]
    simp [residualParams, Params.ell]
    omega
  · right; right; right; left
    have hval :
        ((dIndex (residualParams X L))^[3]
          (rhoIndex (residualParams X L))).val =
          6 * X + 5 := by
      rw [iterate_dIndex]
      change
        (((rhoIndex (residualParams X L)).val +
          3 * (2 * (residualParams X L).m)) %
            (residualParams X L).cycle) =
          6 * X + 5
      rw [rhoIndex_val]
      have hdecomp :
          2 * (residualParams X L).R + 1 +
              3 * (2 * (residualParams X L).m) =
            2 * (residualParams X L).cycle +
              (6 * X + 5) := by
        simp [residualParams, Params.m, Params.cycle]
        omega
      have hremainder :
          6 * X + 5 < (residualParams X L).cycle := by
        simp only [Large] at hlarge
        simp [residualParams, Params.cycle]
        omega
      rw [hdecomp, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hremainder]
    rw [hval]
    simp [residualParams, Params.ell]
    omega
  · right; right; right; right
    have hval :
        ((dIndex (residualParams X L))^[4]
          (rhoIndex (residualParams X L))).val =
          8 * X + 2 * L + 9 := by
      rw [iterate_dIndex]
      change
        (((rhoIndex (residualParams X L)).val +
          4 * (2 * (residualParams X L).m)) %
            (residualParams X L).cycle) =
          8 * X + 2 * L + 9
      rw [rhoIndex_val]
      have hdecomp :
          2 * (residualParams X L).R + 1 +
              4 * (2 * (residualParams X L).m) =
            2 * (residualParams X L).cycle +
              (8 * X + 2 * L + 9) := by
        simp [residualParams, Params.m, Params.cycle]
        omega
      have hremainder :
          8 * X + 2 * L + 9 <
            (residualParams X L).cycle := by
        simp only [Large] at hlarge
        simp [residualParams, Params.cycle]
        omega
      rw [hdecomp, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hremainder]
    rw [hval]
    simp [residualParams, Params.ell]
    omega

/-- The uniform large-band prefix deletes the first five points of the
cut-rotation path. -/
theorem largePrefix_avoidsDeep {X L : ℕ}
    (hlarge : Large X L) :
    PrefixAvoidsDeep (residualParams X L) (largePrefix X L) 5 := by
  intro state
  let target :=
    (automaton (residualParams X L)).evalFrom state
      (largePrefix X L)
  have hrow : LargeRow15 (residualParams X L) X L target := by
    dsimp only [target]
    exact evalFrom_largePrefix_largeRow15 hlarge state
  by_cases hone : target.val = 1
  · left
    calc
      target = (residualParams X L).stateOfNat target.val :=
        (stateOfNat_state_val (residualParams X L) target).symm
      _ = (residualParams X L).stateOfNat 1 := by rw [hone]
  · right
    have hell : (residualParams X L).ell ≤ target.val := by
      simp only [LargeRow15] at hrow
      have hellTwo : 2 ≤ (residualParams X L).ell := by
        simp [residualParams, Params.ell]
      omega
    obtain ⟨index, hindex⟩ :=
      exists_intervalState_eq (residualParams X L) target hell
    refine ⟨index, ?_, hindex.symm⟩
    intro hdeep
    have hvalues :=
      residual_deep_five_values hlarge hdeep
    have hcoordinate :
        (residualParams X L).ell + index.val = target.val := by
      have := congrArg Fin.val hindex
      simpa only [intervalState_val] using this
    simp only [LargeRow15] at hrow
    rcases hvalues with
      hvalue | hvalue | hvalue | hvalue | hvalue <;> omega

/-- Consequently, the large residual band satisfies the Černý bound
whenever the exact synchronization coprimality condition holds. -/
theorem large_satisfiesCerny {X L : ℕ}
    (hcoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle)
    (hlarge : Large X L) :
    (automaton (residualParams X L)).SatisfiesCerny :=
  large_satisfiesCerny_of_prefix_image hcoprime hlarge
    (largePrefix_avoidsDeep hlarge)

end DFA.CycleTree
