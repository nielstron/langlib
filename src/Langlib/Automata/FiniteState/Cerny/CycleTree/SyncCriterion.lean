module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.CutRotation
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

@[expose]
public section

/-!
# Exact synchronization criterion

The cut-rotation construction proves that coprimality of `m` and `cycle`
is sufficient for synchronization.  This module proves the converse.

If `d > 1` divides both parameters, color coordinate `0` by `ell` and
every other coordinate by its residue modulo `d`.  Both input letters act
on these colors by reflections, hence by permutations.  A reset word
cannot exist because two distinct quotient colors can never merge.
-/

namespace DFA.CycleTree

/-- The residue coloring used for the nonsynchronization quotient.

Coordinate `0` receives the same color as `ell`; every positive coordinate
keeps its residue. -/
def quotientColor (P : Params) (d : ℕ) (state : State P) : ZMod d :=
  if state.val = 0 then P.ell else state.val

@[simp]
theorem quotientColor_of_val_zero (P : Params) (d : ℕ)
    (state : State P) (hstate : state.val = 0) :
    quotientColor P d state = (P.ell : ZMod d) := by
  simp [quotientColor, hstate]

theorem quotientColor_of_val_ne_zero (P : Params) (d : ℕ)
    (state : State P) (hstate : state.val ≠ 0) :
    quotientColor P d state = (state.val : ZMod d) := by
  simp [quotientColor, hstate]

theorem quotientColor_stateOfNat_of_lt_of_ne_zero
    (P : Params) (d coordinate : ℕ)
    (hcoordinate : coordinate < P.order) (hzero : coordinate ≠ 0) :
    quotientColor P d (P.stateOfNat coordinate) =
      (coordinate : ZMod d) := by
  rw [quotientColor_of_val_ne_zero]
  · rw [stateOfNat_val_of_lt P hcoordinate]
  · rw [stateOfNat_val_of_lt P hcoordinate]
    exact hzero

theorem quotientColor_stateOfNat_zero (P : Params) (d : ℕ) :
    quotientColor P d (P.stateOfNat 0) = (P.ell : ZMod d) := by
  apply quotientColor_of_val_zero
  exact stateOfNat_val_of_lt P P.order_pos

private theorem quotient_rho_cast (P : Params) (d : ℕ)
    (hdm : d ∣ P.m) :
    (P.rho : ZMod d) = 1 := by
  have hm : (P.m : ZMod d) = 0 :=
    (ZMod.natCast_eq_zero_iff P.m d).2 hdm
  simp [Params.rho, hm]

private theorem quotient_order_cast (P : Params) (d : ℕ)
    (hdcycle : d ∣ P.cycle) :
    (P.order : ZMod d) = (P.ell : ZMod d) := by
  have hcycle : (P.cycle : ZMod d) = 0 :=
    (ZMod.natCast_eq_zero_iff P.cycle d).2 hdcycle
  simp [Params.order, hcycle]

/-- On every common-divisor quotient, `p` is the reflection
`color ↦ ell + 1 - color`. -/
theorem quotientColor_pMap (P : Params) (d : ℕ)
    (hdm : d ∣ P.m) (hdcycle : d ∣ P.cycle)
    (state : State P) :
    quotientColor P d (pMap P state) =
      (P.ell : ZMod d) + 1 - quotientColor P d state := by
  have hrho := quotient_rho_cast P d hdm
  have horder := quotient_order_cast P d hdcycle
  by_cases hzero : state.val = 0
  · rw [pMap_at_zero P state hzero,
      quotientColor_stateOfNat_of_lt_of_ne_zero]
    · rw [quotientColor_of_val_zero P d state hzero]
      ring
    · exact (show 1 < P.ell by
        simp [Params.ell]).trans P.ell_lt_order
    · omega
  by_cases hone : state.val = 1
  · rw [pMap_at_one P state hone,
      quotientColor_stateOfNat_of_lt_of_ne_zero]
    · rw [quotientColor_of_val_ne_zero P d state hzero, hone]
      ring
    · exact P.ell_lt_order
    · exact Nat.ne_of_gt P.ell_pos
  by_cases hell : state.val = P.ell
  · rw [pMap_at_ell P state hell,
      quotientColor_stateOfNat_of_lt_of_ne_zero]
    · rw [quotientColor_of_val_ne_zero P d state hzero, hell, hrho]
      ring
    · exact P.rho_lt_order
    · simp [Params.rho, Params.m]
  by_cases hrhoState : state.val = P.rho
  · rw [pMap_at_rho P state hrhoState,
      quotientColor_stateOfNat_zero,
      quotientColor_of_val_ne_zero P d state hzero, hrhoState, hrho]
    ring
  by_cases hBeforeEll : state.val < P.ell
  · have htwo : 2 ≤ state.val := by omega
    have hcoordinatePos : 0 < P.ell + 1 - state.val := by omega
    have hcoordinateLt : P.ell + 1 - state.val < P.order := by
      have := P.ell_lt_order
      omega
    rw [pMap_before_ell P state htwo hBeforeEll,
      quotientColor_stateOfNat_of_lt_of_ne_zero
        P d _ hcoordinateLt (Nat.ne_of_gt hcoordinatePos),
      quotientColor_of_val_ne_zero P d state hzero]
    rw [Nat.cast_sub (by omega : state.val ≤ P.ell + 1),
      Nat.cast_add, Nat.cast_one]
  by_cases hBeforeRho : state.val < P.rho
  · have hAfterEll : P.ell < state.val := by omega
    have hcoordinatePos : 0 < P.ell + P.rho - state.val := by omega
    have hcoordinateLt :
        P.ell + P.rho - state.val < P.order := by
      have := P.rho_lt_order
      omega
    rw [pMap_between_ell_rho P state hAfterEll hBeforeRho,
      quotientColor_stateOfNat_of_lt_of_ne_zero
        P d _ hcoordinateLt (Nat.ne_of_gt hcoordinatePos),
      quotientColor_of_val_ne_zero P d state hzero]
    rw [Nat.cast_sub (by omega : state.val ≤ P.ell + P.rho),
      Nat.cast_add, hrho]
  · have hAfterRho : P.rho < state.val := by omega
    have hcoordinatePos : 0 < P.rho + P.order - state.val := by
      have := state.isLt
      omega
    have hcoordinateLt :
        P.rho + P.order - state.val < P.order := by
      have := P.rho_lt_order
      omega
    rw [pMap_after_rho P state hAfterRho,
      quotientColor_stateOfNat_of_lt_of_ne_zero
        P d _ hcoordinateLt (Nat.ne_of_gt hcoordinatePos),
      quotientColor_of_val_ne_zero P d state hzero]
    rw [Nat.cast_sub (by
      have := state.isLt
      omega : state.val ≤ P.rho + P.order),
      Nat.cast_add, hrho, horder]
    ring

/-- On every common-divisor quotient, `s` is the reflection
`color ↦ ell - color`. -/
theorem quotientColor_sMap (P : Params) (d : ℕ)
    (hdm : d ∣ P.m) (hdcycle : d ∣ P.cycle)
    (state : State P) :
    quotientColor P d (sMap P state) =
      (P.ell : ZMod d) - quotientColor P d state := by
  have hrho := quotient_rho_cast P d hdm
  have horder := quotient_order_cast P d hdcycle
  by_cases hzero : state.val = 0
  · have hcoordinatePos : 0 < P.rho - 1 := by
      simp [Params.rho, Params.m]
    have hcoordinateLt : P.rho - 1 < P.order := by
      have := P.rho_lt_order
      omega
    rw [sMap_at_zero P state hzero,
      quotientColor_stateOfNat_of_lt_of_ne_zero
        P d _ hcoordinateLt (Nat.ne_of_gt hcoordinatePos),
      quotientColor_of_val_zero P d state hzero]
    rw [Nat.cast_sub (by
      simp [Params.rho, Params.m] : 1 ≤ P.rho), hrho]
    ring
  by_cases hell : state.val = P.ell
  · have hcoordinatePos : 0 < P.rho - 1 := by
      simp [Params.rho, Params.m]
    have hcoordinateLt : P.rho - 1 < P.order := by
      have := P.rho_lt_order
      omega
    rw [sMap_at_ell P state hell,
      quotientColor_stateOfNat_of_lt_of_ne_zero
        P d _ hcoordinateLt (Nat.ne_of_gt hcoordinatePos),
      quotientColor_of_val_ne_zero P d state hzero, hell]
    rw [Nat.cast_sub (by
      simp [Params.rho, Params.m] : 1 ≤ P.rho), hrho]
    ring
  by_cases hBeforeEll : state.val < P.ell
  · have hstatePos : 0 < state.val := Nat.pos_of_ne_zero hzero
    have hcoordinatePos : 0 < P.ell - state.val := by omega
    have hcoordinateLt : P.ell - state.val < P.order := by
      have := P.ell_lt_order
      omega
    rw [sMap_between_zero_ell P state hstatePos hBeforeEll,
      quotientColor_stateOfNat_of_lt_of_ne_zero
        P d _ hcoordinateLt (Nat.ne_of_gt hcoordinatePos),
      quotientColor_of_val_ne_zero P d state hzero]
    rw [Nat.cast_sub (by omega : state.val ≤ P.ell)]
  by_cases hBeforeRho : state.val < P.rho
  · have hAfterEll : P.ell < state.val := by omega
    have hcoordinatePos :
        0 < P.ell + P.rho - 1 - state.val := by
      have := P.ell_pos
      omega
    have hcoordinateLt :
        P.ell + P.rho - 1 - state.val < P.order := by
      have := P.rho_lt_order
      omega
    rw [sMap_between_ell_rho P state hAfterEll hBeforeRho,
      quotientColor_stateOfNat_of_lt_of_ne_zero
        P d _ hcoordinateLt (Nat.ne_of_gt hcoordinatePos),
      quotientColor_of_val_ne_zero P d state hzero]
    rw [show P.ell + P.rho - 1 - state.val =
      (P.ell + (P.rho - 1)) - state.val by omega,
      Nat.cast_sub (by omega : state.val ≤ P.ell + (P.rho - 1)),
      Nat.cast_add,
      Nat.cast_sub (by
        simp [Params.rho, Params.m] : 1 ≤ P.rho),
      hrho]
    ring
  · have hAtOrAfterRho : P.rho ≤ state.val := by omega
    have hcoordinatePos :
        0 < P.rho + P.order - 1 - state.val := by
      have := state.isLt
      have hrhoOne : 1 < P.rho := by
        simp [Params.rho, Params.m]
      omega
    have hcoordinateLt :
        P.rho + P.order - 1 - state.val < P.order := by
      have := P.rho_lt_order
      omega
    rw [sMap_at_or_after_rho P state hAtOrAfterRho,
      quotientColor_stateOfNat_of_lt_of_ne_zero
        P d _ hcoordinateLt (Nat.ne_of_gt hcoordinatePos),
      quotientColor_of_val_ne_zero P d state hzero]
    rw [show P.rho + P.order - 1 - state.val =
      ((P.rho - 1) + P.order) - state.val by
        have hrhoOne : 1 ≤ P.rho := by
          simp [Params.rho, Params.m]
        omega,
      Nat.cast_sub (by
        have := state.isLt
        omega : state.val ≤ (P.rho - 1) + P.order),
      Nat.cast_add,
      Nat.cast_sub (by
        simp [Params.rho, Params.m] : 1 ≤ P.rho),
      hrho, horder]
    ring

theorem quotientColor_step_eq_iff (P : Params) (d : ℕ)
    (hdm : d ∣ P.m) (hdcycle : d ∣ P.cycle)
    (letter : Letter) (left right : State P) :
    quotientColor P d ((automaton P).step left letter) =
        quotientColor P d ((automaton P).step right letter) ↔
      quotientColor P d left = quotientColor P d right := by
  cases letter with
  | p =>
      simp only [automaton_step_p,
        quotientColor_pMap P d hdm hdcycle]
      exact sub_right_inj
  | s =>
      simp only [automaton_step_s,
        quotientColor_sMap P d hdm hdcycle]
      exact sub_right_inj

theorem quotientColor_evalFrom_eq_iff (P : Params) (d : ℕ)
    (hdm : d ∣ P.m) (hdcycle : d ∣ P.cycle)
    (word : List Letter) (left right : State P) :
    quotientColor P d ((automaton P).evalFrom left word) =
        quotientColor P d ((automaton P).evalFrom right word) ↔
      quotientColor P d left = quotientColor P d right := by
  induction word generalizing left right with
  | nil => simp
  | cons letter word ih =>
      rw [(automaton P).evalFrom_cons, (automaton P).evalFrom_cons,
        ih, quotientColor_step_eq_iff P d hdm hdcycle]

/-- A nontrivial common divisor gives a permutation quotient, obstructing
every reset word. -/
theorem not_synchronizing_of_common_divisor (P : Params) (d : ℕ)
    (hone : 1 < d) (hdm : d ∣ P.m) (hdcycle : d ∣ P.cycle) :
    ¬(automaton P).Synchronizing := by
  intro hsync
  obtain ⟨word, target, htarget⟩ := hsync
  have hdPos : 0 < d := by omega
  have hdLeCycle : d ≤ P.cycle :=
    Nat.le_of_dvd P.cycle_pos hdcycle
  have hdLtOrder : d < P.order :=
    lt_of_le_of_lt hdLeCycle (by
      simp [Params.order, Params.ell])
  have honeLtOrder : 1 < P.order :=
    (show 1 < P.ell by
      simp [Params.ell]).trans P.ell_lt_order
  let stateZeroColor : State P := P.stateOfNat d
  let stateOneColor : State P := P.stateOfNat 1
  have hcolors :
      quotientColor P d stateZeroColor =
        quotientColor P d stateOneColor := by
    apply (quotientColor_evalFrom_eq_iff P d hdm hdcycle
      word stateZeroColor stateOneColor).1
    rw [htarget stateZeroColor, htarget stateOneColor]
  have hzeroColor :
      quotientColor P d stateZeroColor = 0 := by
    dsimp [stateZeroColor]
    rw [quotientColor_stateOfNat_of_lt_of_ne_zero
      P d d hdLtOrder (Nat.ne_of_gt hdPos)]
    exact ZMod.natCast_self d
  have honeColor :
      quotientColor P d stateOneColor = 1 := by
    dsimp [stateOneColor]
    rw [quotientColor_stateOfNat_of_lt_of_ne_zero
      P d 1 honeLtOrder (by omega)]
    exact Nat.cast_one
  haveI : Nontrivial (ZMod d) :=
    ZMod.nontrivial_iff.mpr (by omega)
  rw [hzeroColor, honeColor] at hcolors
  exact zero_ne_one hcolors

/-- Synchronization forces the exact coprimality condition. -/
theorem coprime_of_synchronizing (P : Params)
    (hsync : (automaton P).Synchronizing) :
    Nat.Coprime P.m P.cycle := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  have hmPos : 0 < P.m := by
    simp [Params.m]
  have hgcdPos : 0 < P.m.gcd P.cycle :=
    Nat.gcd_pos_of_pos_left P.cycle hmPos
  have hgcdOne : 1 < P.m.gcd P.cycle := by omega
  exact not_synchronizing_of_common_divisor P
    (P.m.gcd P.cycle) hgcdOne
    (Nat.gcd_dvd_left P.m P.cycle)
    (Nat.gcd_dvd_right P.m P.cycle) hsync

/-- The coordinate DFA synchronizes exactly in the coprime regime. -/
theorem synchronizing_iff_coprime (P : Params) :
    (automaton P).Synchronizing ↔ Nat.Coprime P.m P.cycle :=
  ⟨coprime_of_synchronizing P, synchronizing_of_coprime P⟩

/-- Every synchronizing parameter triple in the cut-safe arithmetic region
satisfies the Černý bound via the explicit word `D^M`. -/
theorem satisfiesCerny_of_synchronizing_of_cutSafe (P : Params)
    (hsynchronizing : (automaton P).Synchronizing)
    (hsafe : CutSafe P) :
    (automaton P).SatisfiesCerny :=
  satisfiesCerny_of_coprime_of_cutSafe P
    (coprime_of_synchronizing P hsynchronizing) hsafe

end DFA.CycleTree
