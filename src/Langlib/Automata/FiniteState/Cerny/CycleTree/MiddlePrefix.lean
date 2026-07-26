module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.ResidualWords

@[expose]
public section

/-!
# The five-depth middle-band prefix

This module supplies the parameter-uniform coordinate calculation for
`middlePrefix`.  The prefix calculation itself does not use coprimality;
coprimality is needed only later, when `DepthPrefix` iterates the cut
rotation.
-/

namespace DFA.CycleTree

/-- The fifth omitted coordinate has two affine representatives, according
to whether its local cycle coordinate wraps three or two times. -/
def middleZ (X L : ℕ) : ℕ :=
  if L ≤ 4 * X + 2
  then 10 * X + 6 - 2 * L
  else 2 * L + 10 * X + 11

/-- The reflected coordinate in the twelfth table row. -/
def middleR (X L : ℕ) : ℕ :=
  if L ≤ 4 * X + 1
  then 6 * L - 6 * X + 3
  else 2 * L - 6 * X - 2

/-- The five global coordinates removed by the middle-band prefix. -/
def IsMiddleForbidden (X L coordinate : ℕ) : Prop :=
  coordinate = (residualParams X L).rho ∨
  coordinate = 2 * (residualParams X L).ell ∨
  coordinate = 2 * L + 6 * X + 8 ∨
  coordinate = 8 * X + 7 ∨
  coordinate = middleZ X L

private theorem residual_deep_index_val_zero (X L : ℕ) :
    (((dIndex (residualParams X L))^[0]
      (rhoIndex (residualParams X L))).val) = 2 * L + 3 := by
  simp [rhoIndex, residualParams]
  omega

private theorem residual_deep_index_val_one {X L : ℕ}
    (hmiddle : Middle X L) :
    (((dIndex (residualParams X L))^[1]
      (rhoIndex (residualParams X L))).val) = 2 * X + 2 := by
  rw [iterate_dIndex]
  change
    ((2 * (L + 1) + 1 + 1 * (2 * (X + (L + 1) + 1))) %
      (2 * (L + 1) + 2 * L + 3)) = 2 * X + 2
  rw [Nat.mod_eq_sub_mod (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  rw [Nat.mod_eq_of_lt (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  omega

private theorem residual_deep_index_val_two {X L : ℕ}
    (hmiddle : Middle X L) :
    (((dIndex (residualParams X L))^[2]
      (rhoIndex (residualParams X L))).val) = 2 * L + 4 * X + 6 := by
  rw [iterate_dIndex]
  change
    ((2 * (L + 1) + 1 + 2 * (2 * (X + (L + 1) + 1))) %
      (2 * (L + 1) + 2 * L + 3)) = 2 * L + 4 * X + 6
  rw [Nat.mod_eq_sub_mod (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  rw [Nat.mod_eq_of_lt (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  omega

private theorem residual_deep_index_val_three {X L : ℕ}
    (hmiddle : Middle X L) :
    (((dIndex (residualParams X L))^[3]
      (rhoIndex (residualParams X L))).val) = 6 * X + 5 := by
  rw [iterate_dIndex]
  change
    ((2 * (L + 1) + 1 + 3 * (2 * (X + (L + 1) + 1))) %
      (2 * (L + 1) + 2 * L + 3)) = 6 * X + 5
  rw [Nat.mod_eq_sub_mod (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  rw [Nat.mod_eq_sub_mod (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  rw [Nat.mod_eq_of_lt (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  omega

private theorem residual_deep_index_val_four_low {X L : ℕ}
    (hmiddle : Middle X L) (hlow : L ≤ 4 * X + 2) :
    (((dIndex (residualParams X L))^[4]
      (rhoIndex (residualParams X L))).val) = 8 * X + 4 - 2 * L := by
  rw [iterate_dIndex]
  change
    ((2 * (L + 1) + 1 + 4 * (2 * (X + (L + 1) + 1))) %
      (2 * (L + 1) + 2 * L + 3)) = 8 * X + 4 - 2 * L
  rw [Nat.mod_eq_sub_mod (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  rw [Nat.mod_eq_sub_mod (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  rw [Nat.mod_eq_sub_mod (by omega)]
  rw [Nat.mod_eq_of_lt (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  omega

private theorem residual_deep_index_val_four_high {X L : ℕ}
    (hmiddle : Middle X L) (hhigh : 4 * X + 3 ≤ L) :
    (((dIndex (residualParams X L))^[4]
      (rhoIndex (residualParams X L))).val) = 2 * L + 8 * X + 9 := by
  rw [iterate_dIndex]
  change
    ((2 * (L + 1) + 1 + 4 * (2 * (X + (L + 1) + 1))) %
      (2 * (L + 1) + 2 * L + 3)) = 2 * L + 8 * X + 9
  rw [Nat.mod_eq_sub_mod (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  rw [Nat.mod_eq_sub_mod (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  rw [Nat.mod_eq_of_lt (by rcases hmiddle with ⟨h₁, h₂⟩; omega)]
  omega

private theorem residual_deep_index_val_four {X L : ℕ}
    (hmiddle : Middle X L) :
    (residualParams X L).ell +
        (((dIndex (residualParams X L))^[4]
          (rhoIndex (residualParams X L))).val) =
      middleZ X L := by
  by_cases hlow : L ≤ 4 * X + 2
  · rw [residual_deep_index_val_four_low hmiddle hlow]
    simp [middleZ, hlow, residualParams, Params.ell]
    omega
  · have hhigh : 4 * X + 3 ≤ L := by omega
    rw [residual_deep_index_val_four_high hmiddle hhigh]
    simp [middleZ, hlow, residualParams, Params.ell]
    omega

/-- On the middle band, the first five deep local indices are exactly the
five affine coordinates displayed in the factor-table calculation. -/
theorem isDeepIndex_five_iff_middleForbidden {X L : ℕ}
    (hmiddle : Middle X L) (index : Fin (residualParams X L).cycle) :
    IsDeepIndex (residualParams X L) 5 index ↔
      IsMiddleForbidden X L
        ((residualParams X L).ell + index.val) := by
  constructor
  · rintro ⟨offset, hoffset, rfl⟩
    have hoffsetCases :
        offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨ offset = 4 := by
      omega
    rcases hoffsetCases with rfl | rfl | rfl | rfl | rfl
    · left
      rw [residual_deep_index_val_zero]
      simp [residualParams, Params.ell, Params.rho, Params.m]
      omega
    · right; left
      rw [residual_deep_index_val_one hmiddle]
      simp [residualParams, Params.ell]
      omega
    · right; right; left
      rw [residual_deep_index_val_two hmiddle]
      simp [residualParams, Params.ell]
      omega
    · right; right; right; left
      rw [residual_deep_index_val_three hmiddle]
      simp [residualParams, Params.ell]
      omega
    · right; right; right; right
      exact residual_deep_index_val_four hmiddle
  · intro hforbidden
    rcases hforbidden with hrho | htwoEll | hthird | hfourth | hz
    · refine ⟨0, by omega, ?_⟩
      apply Fin.ext
      have hrhoValue := residual_deep_index_val_zero X L
      simp only [Function.iterate_zero_apply] at hrhoValue ⊢
      simp [residualParams, Params.ell, Params.rho, Params.m] at hrho
      omega
    · refine ⟨1, by omega, ?_⟩
      apply Fin.ext
      have hone := residual_deep_index_val_one hmiddle
      simp [residualParams, Params.ell] at htwoEll
      omega
    · refine ⟨2, by omega, ?_⟩
      apply Fin.ext
      have htwo := residual_deep_index_val_two hmiddle
      simp [residualParams, Params.ell] at hthird
      omega
    · refine ⟨3, by omega, ?_⟩
      apply Fin.ext
      have hthree := residual_deep_index_val_three hmiddle
      simp [residualParams, Params.ell] at hfourth
      omega
    · refine ⟨4, by omega, ?_⟩
      apply Fin.ext
      have hfour := residual_deep_index_val_four hmiddle
      exact Nat.add_left_cancel (hz.trans hfour.symm)

/-- A pointwise way to record a row of an image-complement table. -/
def ImageAvoids (P : Params) (word : List Letter)
    (hole : ℕ → Prop) : Prop :=
  ∀ state, ¬hole ((automaton P).evalFrom state word).val

/-- Image-complement rows compose by checking the inverse image of the
new holes under the appended factor. -/
theorem imageAvoids_append {P : Params} {word factor : List Letter}
    {oldHole newHole : ℕ → Prop}
    (hword : ImageAvoids P word oldHole)
    (hfactor : ∀ state,
      newHole ((automaton P).evalFrom state factor).val →
        oldHole state.val) :
    ImageAvoids P (word ++ factor) newHole := by
  intro state hnew
  rw [(automaton P).evalFrom_of_append] at hnew
  exact hword _ (hfactor _ hnew)

/-- The complement in the last row of the middle-prefix factor table. -/
def MiddleFinalHole (X L coordinate : ℕ) : Prop :=
  coordinate = 0 ∨
  (2 ≤ coordinate ∧ coordinate < (residualParams X L).ell) ∨
  IsMiddleForbidden X L coordinate

/-- The exact last-row avoidance statement is sufficient for the abstract
five-depth prefix interface. -/
theorem prefixAvoidsDeep_of_middleFinalHole {X L : ℕ}
    (hmiddle : Middle X L)
    (himage :
      ImageAvoids (residualParams X L) (middlePrefix X L)
        (MiddleFinalHole X L)) :
    PrefixAvoidsDeep (residualParams X L) (middlePrefix X L) 5 := by
  let P := residualParams X L
  intro state
  let output := (automaton P).evalFrom state (middlePrefix X L)
  have hnotHole : ¬MiddleFinalHole X L output.val := himage state
  by_cases hone : output.val = 1
  · left
    change output = P.stateOfNat 1
    rw [← hone]
    exact (stateOfNat_state_val P output).symm
  · right
    have hell : P.ell ≤ output.val := by
      by_contra hnot
      have hlt : output.val < P.ell := by omega
      have hzero : output.val ≠ 0 := by
        intro h
        exact hnotHole (Or.inl h)
      exact hnotHole (Or.inr (Or.inl ⟨by omega, hlt⟩))
    obtain ⟨index, hindex⟩ := exists_intervalState_eq P output hell
    refine ⟨index, ?_, ?_⟩
    · intro hdeep
      have hforbidden :
          IsMiddleForbidden X L (P.ell + index.val) :=
        (isDeepIndex_five_iff_middleForbidden hmiddle index).mp hdeep
      apply hnotHole
      right
      right
      have hout : output.val = P.ell + index.val := by
        rw [← hindex, intervalState_val]
      rw [hout]
      exact hforbidden
    · exact hindex.symm

/-- A generalized version of tail entry into the hidden `A`-cycle. -/
theorem evalFrom_aPower_tail_after_entry (P : Params)
    (state : State P) (count : ℕ)
    (hstatePos : 0 < state.val) (hstateTail : state.val < P.ell)
    (hentry : P.ell + 1 - state.val ≤ count) :
    (automaton P).evalFrom state (wordPow aWord count) =
      cycleState P
        ((cycleNext P)^[count - (P.ell + 1 - state.val)]
          (cycleOneIndex P)) := by
  let entry := P.ell + 1 - state.val
  let remaining := count - entry
  have hentryPos : 0 < entry := by
    dsimp [entry]
    omega
  have hsum : entry + remaining = count := by
    dsimp [remaining, entry]
    exact Nat.add_sub_of_le hentry
  have hcoordinate : state.val + entry = P.ell + 1 := by
    dsimp [entry]
    omega
  have hellOneLt : P.ell + 1 < P.order := by
    simp [Params.order, Params.cycle]
  calc
    (automaton P).evalFrom state (wordPow aWord count) =
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

theorem evalFrom_aPower_zero (P : Params) (count : ℕ) :
    (automaton P).evalFrom (P.stateOfNat 0) (wordPow aWord count) =
      cycleState P
        ((cycleNext P)^[count] ⟨0, P.cycle_pos⟩) := by
  rw [← cycleState_zero]
  exact evalFrom_aPower_cycleState P ⟨0, P.cycle_pos⟩ count

theorem evalFrom_aPower_of_interval (P : Params) (state : State P)
    (count : ℕ) (hcount : 0 < count) (hstate : P.ell ≤ state.val) :
    ∃ index : Fin P.cycle,
      (automaton P).evalFrom state (wordPow aWord count) =
        cycleState P ((cycleNext P)^[count] index) := by
  obtain ⟨index, hindex⟩ := exists_intervalState_eq P state hstate
  refine ⟨index, ?_⟩
  rw [← hindex]
  exact evalFrom_aPower_intervalState_of_pos P index count hcount

/-- Once at least `ell` copies of `A` have been read, every state has
entered the hidden cycle. -/
theorem exists_cycleState_aPower_of_ell_le (P : Params)
    (state : State P) (count : ℕ) (hcount : P.ell ≤ count) :
    ∃ index : Fin P.cycle,
      (automaton P).evalFrom state (wordPow aWord count) =
        cycleState P index := by
  have hcountPos : 0 < count := P.ell_pos.trans_le hcount
  by_cases hzero : state.val = 0
  · have hstate : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    refine ⟨(cycleNext P)^[count] ⟨0, P.cycle_pos⟩, ?_⟩
    rw [hstate, evalFrom_aPower_zero]
  · by_cases htail : state.val < P.ell
    · refine
        ⟨((cycleNext P)^[count - (P.ell + 1 - state.val)]
          (cycleOneIndex P)), ?_⟩
      apply evalFrom_aPower_tail_after_entry P state count
        (Nat.pos_of_ne_zero hzero) htail
      omega
    · have hinterval : P.ell ≤ state.val := by omega
      obtain ⟨index, himage⟩ :=
        evalFrom_aPower_of_interval P state count hcountPos hinterval
      exact ⟨(cycleNext P)^[count] index, himage⟩

/-- The defect-one macro `A` omits exactly the coordinate `1`; only the
avoidance direction is needed for the factor-table induction. -/
theorem imageAvoids_aWord_one (P : Params) :
    ImageAvoids P aWord (fun coordinate => coordinate = 1) := by
  intro state hone
  rw [evalFrom_aWord] at hone
  by_cases hzero : state.val = 0
  · rw [if_pos hzero] at hone
    have hvalue :
        (P.stateOfNat (P.ell + 1)).val = P.ell + 1 := by
      apply stateOfNat_val_of_lt
      simp [Params.order, Params.cycle]
    rw [hvalue] at hone
    have := P.ell_pos
    omega
  · rw [if_neg hzero] at hone
    by_cases hnowrap : state.val + 1 < P.order
    · rw [stateOfNat_val_of_lt P hnowrap] at hone
      omega
    · have hwrap : state.val + 1 = P.order := by
        omega
      change (state.val + 1) % P.order = 1 at hone
      rw [hwrap] at hone
      simp at hone

/-- The only preimage of `rho` under `p²` is `1`. -/
theorem pSquared_preimage_rho (P : Params) (state : State P)
    (himage :
      ((automaton P).evalFrom state pSquared).val = P.rho) :
    state.val = 1 := by
  rw [evalFrom_pSquared] at himage
  by_cases hzero : state.val = 0
  · rw [if_pos hzero] at himage
    rw [stateOfNat_val_of_lt P P.ell_lt_order] at himage
    have := P.rho_eq
    omega
  · rw [if_neg hzero] at himage
    by_cases hell : state.val = P.ell
    · rw [if_pos hell] at himage
      rw [stateOfNat_val_of_lt P P.order_pos] at himage
      have := P.rho_eq
      omega
    · rw [if_neg hell] at himage
      by_cases hone : state.val = 1
      · exact hone
      · rw [if_neg hone] at himage
        by_cases hrho : state.val = P.rho
        · rw [if_pos hrho] at himage
          have honeLt : 1 < P.order := by
            simp [Params.order, Params.ell, Params.cycle]
            omega
          rw [stateOfNat_val_of_lt P honeLt] at himage
          have := P.rho_eq
          omega
        · rw [if_neg hrho] at himage
          exact (hrho himage).elim

/-- The only preimage of `ell` under `p²` is `0`. -/
theorem pSquared_preimage_ell (P : Params) (state : State P)
    (himage :
      ((automaton P).evalFrom state pSquared).val = P.ell) :
    state.val = 0 := by
  rw [evalFrom_pSquared] at himage
  by_cases hzero : state.val = 0
  · exact hzero
  · rw [if_neg hzero] at himage
    by_cases hell : state.val = P.ell
    · rw [if_pos hell] at himage
      rw [stateOfNat_val_of_lt P P.order_pos] at himage
      have := P.ell_pos
      omega
    · rw [if_neg hell] at himage
      by_cases hone : state.val = 1
      · rw [if_pos hone] at himage
        rw [stateOfNat_val_of_lt P P.rho_lt_order] at himage
        have := P.rho_eq
        omega
      · rw [if_neg hone] at himage
        by_cases hrho : state.val = P.rho
        · rw [if_pos hrho] at himage
          have honeLt : 1 < P.order := by
            simp [Params.order, Params.ell, Params.cycle]
            omega
          rw [stateOfNat_val_of_lt P honeLt] at himage
          have hellTwo : 2 ≤ P.ell := by simp [Params.ell]
          omega
        · rw [if_neg hrho] at himage
          exact (hell himage).elim

/-- Away from its four exceptional coordinates, `p²` has the state itself
as its unique preimage. -/
theorem pSquared_preimage_regular (P : Params) (state : State P)
    (target : ℕ)
    (htargetZero : target ≠ 0) (htargetEll : target ≠ P.ell)
    (htargetOne : target ≠ 1) (htargetRho : target ≠ P.rho)
    (himage :
      ((automaton P).evalFrom state pSquared).val = target) :
    state.val = target := by
  rw [evalFrom_pSquared] at himage
  by_cases hzero : state.val = 0
  · rw [if_pos hzero] at himage
    rw [stateOfNat_val_of_lt P P.ell_lt_order] at himage
    exact (htargetEll himage.symm).elim
  · rw [if_neg hzero] at himage
    by_cases hell : state.val = P.ell
    · rw [if_pos hell] at himage
      rw [stateOfNat_val_of_lt P P.order_pos] at himage
      exact (htargetZero himage.symm).elim
    · rw [if_neg hell] at himage
      by_cases hone : state.val = 1
      · rw [if_pos hone] at himage
        rw [stateOfNat_val_of_lt P P.rho_lt_order] at himage
        exact (htargetRho himage.symm).elim
      · rw [if_neg hone] at himage
        by_cases hrho : state.val = P.rho
        · rw [if_pos hrho] at himage
          have honeLt : 1 < P.order := by
            simp [Params.order, Params.ell, Params.cycle]
            omega
          rw [stateOfNat_val_of_lt P honeLt] at himage
          exact (htargetOne himage.symm).elim
        · rw [if_neg hrho] at himage
          exact himage

/-- The first two rows of the middle factor table:
`H(A) = {1}` and `H(Ap²) = {rho}`. -/
theorem imageAvoids_aWord_pSquared_rho (P : Params) :
    ImageAvoids P (aWord ++ pSquared)
      (fun coordinate => coordinate = P.rho) := by
  apply imageAvoids_append (imageAvoids_aWord_one P)
  intro state h
  exact pSquared_preimage_rho P state h

/-- Cycle states are either the distinguished coordinate `0` or lie
strictly above `ell`. -/
theorem cycleState_val_zero_or_above_ell (P : Params)
    (index : Fin P.cycle) :
    (cycleState P index).val = 0 ∨
      P.ell < (cycleState P index).val := by
  by_cases hzero : index.val = 0
  · left
    have hindex : index = ⟨0, P.cycle_pos⟩ := Fin.ext hzero
    rw [hindex, cycleState_zero]
    exact stateOfNat_val_of_lt P P.order_pos
  · right
    rw [cycleState_val_of_ne_zero P index hzero]
    omega

theorem cycleState_val_eq_ell_add_iff (P : Params)
    (index : Fin P.cycle) {target : ℕ}
    (htargetPos : 0 < target) (htargetLt : target < P.cycle) :
    (cycleState P index).val = P.ell + target ↔
      index.val = target := by
  constructor
  · intro h
    by_cases hzero : index.val = 0
    · have hindex : index = ⟨0, P.cycle_pos⟩ := Fin.ext hzero
      subst index
      rw [cycleState_zero,
        stateOfNat_val_of_lt P P.order_pos] at h
      have := P.ell_pos
      omega
    · rw [cycleState_val_of_ne_zero P index hzero] at h
      omega
  · intro h
    have hzero : index.val ≠ 0 := by omega
    rw [cycleState_of_ne_zero P index hzero]
    have hcoordinateLt : P.ell + index.val < P.order := by
      rw [h]
      simpa [Params.order] using Nat.add_lt_add_left htargetLt P.ell
    rw [stateOfNat_val_of_lt P hcoordinateLt, h]

/-- After `ell - 1` copies of `A`, no state remains in the open low
interval `{1, ..., ell - 1}`. -/
theorem aEllPred_avoids_low (P : Params) (state : State P) :
    ¬(1 ≤
        ((automaton P).evalFrom state
          (wordPow aWord (P.ell - 1))).val ∧
      ((automaton P).evalFrom state
          (wordPow aWord (P.ell - 1))).val < P.ell) := by
  intro hlow
  have hcountPos : 0 < P.ell - 1 := by
    simp [Params.ell]
  by_cases hzero : state.val = 0
  · have hstate : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    rw [hstate, evalFrom_aPower_zero] at hlow
    rcases cycleState_val_zero_or_above_ell P
      ((cycleNext P)^[P.ell - 1] ⟨0, P.cycle_pos⟩) with hz | habove
    · omega
    · omega
  · by_cases hone : state.val = 1
    · have hbefore : state.val + (P.ell - 1) < P.order := by
        rw [hone]
        have := P.ell_lt_order
        omega
      rw [evalFrom_aPower_before_wrap P state (P.ell - 1)
        (by omega) hbefore] at hlow
      rw [stateOfNat_val_of_lt P (by
        rw [hone]
        have := P.ell_lt_order
        omega)] at hlow
      rw [hone] at hlow
      omega
    · by_cases htail : state.val < P.ell
      · have hentry : P.ell + 1 - state.val ≤ P.ell - 1 := by
          omega
        rw [evalFrom_aPower_tail_after_entry P state (P.ell - 1)
          (by omega) htail hentry] at hlow
        rcases cycleState_val_zero_or_above_ell P
          ((cycleNext P)^[(P.ell - 1) -
              (P.ell + 1 - state.val)] (cycleOneIndex P)) with
          hz | habove
        · omega
        · omega
      · have hinterval : P.ell ≤ state.val := by omega
        obtain ⟨index, himage⟩ :=
          evalFrom_aPower_of_interval P state (P.ell - 1)
            hcountPos hinterval
        rw [himage] at hlow
        rcases cycleState_val_zero_or_above_ell P
          ((cycleNext P)^[P.ell - 1] index) with hz | habove
        · omega
        · omega

/-- On the residual middle band, the unique preimage of
`rho + ell - 1` under `A^(ell-1)` is `rho`. -/
theorem aEllPred_preimage_rho_add {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      ((automaton (residualParams X L)).evalFrom state
        (wordPow aWord ((residualParams X L).ell - 1))).val =
          (residualParams X L).rho +
            (residualParams X L).ell - 1) :
    state.val = (residualParams X L).rho := by
  let P := residualParams X L
  change State P at state
  change
    ((automaton P).evalFrom state
      (wordPow aWord (P.ell - 1))).val =
        P.rho + P.ell - 1 at himage
  change state.val = P.rho
  have hrhoPos : 0 < P.rho := by
    simp [P, residualParams, Params.rho, Params.m]
  have hrhoPredPos : 0 < P.rho - 1 := by
    simp [P, residualParams, Params.rho, Params.m]
  have hrhoPredLt : P.rho - 1 < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, residualParams, Params.rho, Params.m, Params.cycle]
    omega
  have htarget :
      P.rho + P.ell - 1 = P.ell + (P.rho - 1) := by
    omega
  by_cases hzero : state.val = 0
  · have hstate : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    rw [hstate, evalFrom_aPower_zero, htarget] at himage
    have hadvance :=
      (cycleState_val_eq_ell_add_iff P
        ((cycleNext P)^[P.ell - 1] ⟨0, P.cycle_pos⟩)
        hrhoPredPos hrhoPredLt).mp himage
    rw [iterate_cycleNext] at hadvance
    change ((0 + (P.ell - 1)) % P.cycle) = P.rho - 1 at hadvance
    have hcountLt : P.ell - 1 < P.cycle := by
      rcases hmiddle with ⟨hlower, hupper⟩
      simp [P, residualParams, Params.ell, Params.cycle]
      omega
    rw [Nat.mod_eq_of_lt (by simpa using hcountLt)] at hadvance
    simp [P, residualParams, Params.ell, Params.rho, Params.m] at hadvance
    rcases hmiddle with ⟨hlower, hupper⟩
    omega
  · by_cases hone : state.val = 1
    · have hbefore : state.val + (P.ell - 1) < P.order := by
        rw [hone]
        have := P.ell_lt_order
        omega
      rw [evalFrom_aPower_before_wrap P state (P.ell - 1)
        (by omega) hbefore] at himage
      rw [stateOfNat_val_of_lt P (by
        rw [hone]
        have := P.ell_lt_order
        omega)] at himage
      rw [hone] at himage
      have := P.rho_eq
      omega
    · by_cases htail : state.val < P.ell
      · have hentry : P.ell + 1 - state.val ≤ P.ell - 1 := by
          omega
        rw [evalFrom_aPower_tail_after_entry P state (P.ell - 1)
          (by omega) htail hentry, htarget] at himage
        have hadvance :=
          (cycleState_val_eq_ell_add_iff P
            ((cycleNext P)^[(P.ell - 1) -
                (P.ell + 1 - state.val)] (cycleOneIndex P))
            hrhoPredPos hrhoPredLt).mp himage
        rw [iterate_cycleNext] at hadvance
        change
          ((1 + ((P.ell - 1) -
            (P.ell + 1 - state.val))) % P.cycle) =
              P.rho - 1 at hadvance
        have hsumLt :
            1 + ((P.ell - 1) -
              (P.ell + 1 - state.val)) < P.cycle := by
          rcases hmiddle with ⟨hlower, hupper⟩
          simp [P, residualParams, Params.ell, Params.cycle] at *
          omega
        rw [Nat.mod_eq_of_lt hsumLt] at hadvance
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [P, residualParams, Params.ell, Params.rho, Params.m] at *
        omega
      · have hinterval : P.ell ≤ state.val := by omega
        obtain ⟨index, hindex⟩ :=
          exists_intervalState_eq P state hinterval
        have hpower :
            (automaton P).evalFrom state
                (wordPow aWord (P.ell - 1)) =
              cycleState P ((cycleNext P)^[P.ell - 1] index) := by
          rw [← hindex]
          exact evalFrom_aPower_intervalState_of_pos P index
            (P.ell - 1) (by simp [Params.ell])
        rw [hpower, htarget] at himage
        have hadvance :=
          (cycleState_val_eq_ell_add_iff P
            ((cycleNext P)^[P.ell - 1] index)
            hrhoPredPos hrhoPredLt).mp himage
        rw [iterate_cycleNext] at hadvance
        change
          ((index.val + (P.ell - 1)) % P.cycle) =
            P.rho - 1 at hadvance
        have hellPredLt : P.ell - 1 < P.cycle := by
          rcases hmiddle with ⟨hlower, hupper⟩
          simp [P, residualParams, Params.ell, Params.cycle]
          omega
        have hsumTwo :
            index.val + (P.ell - 1) < P.cycle + P.cycle := by
          omega
        have hindexValue : index.val = (rhoIndex P).val := by
          by_cases hsum : index.val + (P.ell - 1) < P.cycle
          · rw [Nat.mod_eq_of_lt hsum] at hadvance
            simp [P, residualParams, Params.ell, Params.rho,
              Params.m, rhoIndex] at *
            omega
          · rw [Nat.mod_eq_sub_mod (by omega)] at hadvance
            rw [Nat.mod_eq_of_lt (by omega)] at hadvance
            simp [P, residualParams, Params.ell, Params.rho,
              Params.m, Params.cycle, rhoIndex] at *
            omega
        have hstateValue : state.val = P.ell + index.val := by
          rw [← hindex, intervalState_val]
        rw [hstateValue, hindexValue, ell_add_rhoIndex]

/-- General interval inversion for the short power `A^(ell-1)`, above
all transient phases. -/
theorem aEllPred_preimage_cycle_of_count_lt_target (P : Params)
    (state : State P) (target : ℕ)
    (hcountTarget : P.ell - 1 < target)
    (htarget : target < P.cycle)
    (himage :
      ((automaton P).evalFrom state
        (wordPow aWord (P.ell - 1))).val = P.ell + target) :
    state.val = P.ell + (target - (P.ell - 1)) := by
  have hcountPos : 0 < P.ell - 1 := by simp [Params.ell]
  have htargetPos : 0 < target := by omega
  by_cases hzero : state.val = 0
  · have hstate : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    rw [hstate, evalFrom_aPower_zero] at himage
    have hadvance :=
      (cycleState_val_eq_ell_add_iff P
        ((cycleNext P)^[P.ell - 1] ⟨0, P.cycle_pos⟩)
        htargetPos htarget).mp himage
    rw [iterate_cycleNext] at hadvance
    change ((0 + (P.ell - 1)) % P.cycle) = target at hadvance
    have hcountCycle : P.ell - 1 < P.cycle :=
      hcountTarget.trans htarget
    rw [Nat.mod_eq_of_lt (by simpa using hcountCycle)] at hadvance
    omega
  · by_cases hone : state.val = 1
    · have hbefore : state.val + (P.ell - 1) < P.order := by
        rw [hone]
        have := P.ell_lt_order
        omega
      rw [evalFrom_aPower_before_wrap P state (P.ell - 1)
        (by omega) hbefore] at himage
      rw [stateOfNat_val_of_lt P (by
        rw [hone]
        have := P.ell_lt_order
        omega)] at himage
      rw [hone] at himage
      omega
    · by_cases htail : state.val < P.ell
      · have hentry : P.ell + 1 - state.val ≤ P.ell - 1 := by
          omega
        rw [evalFrom_aPower_tail_after_entry P state (P.ell - 1)
          (by omega) htail hentry] at himage
        have hadvance :=
          (cycleState_val_eq_ell_add_iff P
            ((cycleNext P)^[(P.ell - 1) -
                (P.ell + 1 - state.val)] (cycleOneIndex P))
            htargetPos htarget).mp himage
        rw [iterate_cycleNext] at hadvance
        change
          ((1 + ((P.ell - 1) -
            (P.ell + 1 - state.val))) % P.cycle) =
              target at hadvance
        have hphaseTarget :
            1 + ((P.ell - 1) -
              (P.ell + 1 - state.val)) < target := by
          omega
        rw [Nat.mod_eq_of_lt (hphaseTarget.trans htarget)] at hadvance
        omega
      · have hinterval : P.ell ≤ state.val := by omega
        obtain ⟨index, hindex⟩ :=
          exists_intervalState_eq P state hinterval
        have hpower :
            (automaton P).evalFrom state
                (wordPow aWord (P.ell - 1)) =
              cycleState P ((cycleNext P)^[P.ell - 1] index) := by
          rw [← hindex]
          exact evalFrom_aPower_intervalState_of_pos P index
            (P.ell - 1) hcountPos
        rw [hpower] at himage
        have hadvance :=
          (cycleState_val_eq_ell_add_iff P
            ((cycleNext P)^[P.ell - 1] index)
            htargetPos htarget).mp himage
        rw [iterate_cycleNext] at hadvance
        change
          ((index.val + (P.ell - 1)) % P.cycle) = target at hadvance
        have hsumTwo :
            index.val + (P.ell - 1) < P.cycle + P.cycle := by
          omega
        have hindexValue :
            index.val = target - (P.ell - 1) := by
          by_cases hsum : index.val + (P.ell - 1) < P.cycle
          · rw [Nat.mod_eq_of_lt hsum] at hadvance
            omega
          · rw [Nat.mod_eq_sub_mod (by omega)] at hadvance
            rw [Nat.mod_eq_of_lt (by omega)] at hadvance
            omega
        have hstateValue : state.val = P.ell + index.val := by
          rw [← hindex, intervalState_val]
        rw [hstateValue, hindexValue]

/-- Third factor-table row. -/
theorem imageAvoids_middle_third_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1))
      (fun coordinate =>
        (1 ≤ coordinate ∧
          coordinate < (residualParams X L).ell) ∨
        coordinate =
          (residualParams X L).rho +
            (residualParams X L).ell - 1) := by
  apply imageAvoids_append
    (imageAvoids_aWord_pSquared_rho (residualParams X L))
  intro state hnew
  rcases hnew with hlow | hspecial
  · exact (aEllPred_avoids_low (residualParams X L) state hlow).elim
  · exact aEllPred_preimage_rho_add hmiddle state hspecial

/-- On the residual middle band, a state mapped by `s` below `ell` was
already in the open low interval. -/
theorem sMap_preimage_below_ell_middle {X L : ℕ}
    (state : State (residualParams X L))
    (himage :
      (sMap (residualParams X L) state).val <
        (residualParams X L).ell) :
    1 ≤ state.val ∧ state.val < (residualParams X L).ell := by
  let P := residualParams X L
  change State P at state
  change (sMap P state).val < P.ell at himage
  change 1 ≤ state.val ∧ state.val < P.ell
  by_cases hzero : state.val = 0
  · rw [sMap_at_zero P state hzero] at himage
    rw [stateOfNat_val_of_lt P (by
      have := P.rho_lt_order
      omega)] at himage
    have := P.rho_eq
    omega
  · by_cases hell : state.val = P.ell
    · rw [sMap_at_ell P state hell] at himage
      rw [stateOfNat_val_of_lt P (by
        have := P.rho_lt_order
        omega)] at himage
      have := P.rho_eq
      omega
    · by_cases hbeforeEll : state.val < P.ell
      · exact ⟨by omega, hbeforeEll⟩
      · have hafterEll : P.ell < state.val := by omega
        by_cases hbeforeRho : state.val < P.rho
        · rw [sMap_between_ell_rho P state hafterEll hbeforeRho] at himage
          have hcoordinateLt :
              P.ell + P.rho - 1 - state.val < P.order := by
            have := P.rho_lt_order
            omega
          rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
          omega
        · have hatRho : P.rho ≤ state.val := by omega
          rw [sMap_at_or_after_rho P state hatRho] at himage
          have hcoordinateLt :
              P.rho + P.order - 1 - state.val < P.order := by
            have hrhoPos : 0 < P.rho := by
              simp [Params.rho, Params.m]
            have := P.rho_lt_order
            omega
          rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
          have := P.rho_eq
          omega

/-- The unique preimage of the displayed coordinate `M = cycle` under
`s` is `rho + ell - 1`. -/
theorem sMap_preimage_cycle_middle {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      (sMap (residualParams X L) state).val =
        (residualParams X L).cycle) :
    state.val =
      (residualParams X L).rho +
        (residualParams X L).ell - 1 := by
  let P := residualParams X L
  change State P at state
  change (sMap P state).val = P.cycle at himage
  change state.val = P.rho + P.ell - 1
  by_cases hzero : state.val = 0
  · rw [sMap_at_zero P state hzero] at himage
    rw [stateOfNat_val_of_lt P (by
      have := P.rho_lt_order
      omega)] at himage
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, residualParams, Params.rho, Params.m,
      Params.cycle] at himage
    omega
  · by_cases hell : state.val = P.ell
    · rw [sMap_at_ell P state hell] at himage
      rw [stateOfNat_val_of_lt P (by
        have := P.rho_lt_order
        omega)] at himage
      rcases hmiddle with ⟨hlower, hupper⟩
      simp [P, residualParams, Params.rho, Params.m,
        Params.cycle] at himage
      omega
    · by_cases hbeforeEll : state.val < P.ell
      · rw [sMap_between_zero_ell P state (by omega) hbeforeEll] at himage
        have hcoordinateLt : P.ell - state.val < P.order := by
          have := P.ell_lt_order
          omega
        rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [P, residualParams, Params.ell, Params.cycle] at himage
        omega
      · have hafterEll : P.ell < state.val := by omega
        by_cases hbeforeRho : state.val < P.rho
        · rw [sMap_between_ell_rho P state hafterEll hbeforeRho] at himage
          have hcoordinateLt :
              P.ell + P.rho - 1 - state.val < P.order := by
            have := P.rho_lt_order
            omega
          rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
          rcases hmiddle with ⟨hlower, hupper⟩
          simp [P, residualParams, Params.ell, Params.rho,
            Params.m, Params.cycle] at himage
          omega
        · have hatRho : P.rho ≤ state.val := by omega
          rw [sMap_at_or_after_rho P state hatRho] at himage
          have hcoordinateLt :
              P.rho + P.order - 1 - state.val < P.order := by
            have hrhoPos : 0 < P.rho := by
              simp [Params.rho, Params.m]
            have := P.rho_lt_order
            omega
          rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
          simp [P, residualParams, Params.order, Params.ell,
            Params.cycle, Params.rho, Params.m] at himage ⊢
          omega

/-- Inversion of `s` for a target strictly inside the middle reflection
interval. -/
theorem sMap_preimage_middle_target (P : Params)
    (state : State P) (target : ℕ)
    (htargetEll : P.ell ≤ target)
    (htargetRho : target < P.rho - 1)
    (himage : (sMap P state).val = target) :
    state.val = P.ell + P.rho - 1 - target := by
  by_cases hzero : state.val = 0
  · rw [sMap_at_zero P state hzero] at himage
    rw [stateOfNat_val_of_lt P (by
      have := P.rho_lt_order
      omega)] at himage
    have hrhoPred : P.rho - 1 < P.rho := by
      simp [Params.rho, Params.m]
    omega
  · by_cases hell : state.val = P.ell
    · rw [sMap_at_ell P state hell] at himage
      rw [stateOfNat_val_of_lt P (by
        have := P.rho_lt_order
        omega)] at himage
      have hrhoPred : P.rho - 1 < P.rho := by
        simp [Params.rho, Params.m]
      omega
    · by_cases hbeforeEll : state.val < P.ell
      · rw [sMap_between_zero_ell P state (by omega) hbeforeEll] at himage
        have hcoordinateLt : P.ell - state.val < P.order := by
          have := P.ell_lt_order
          omega
        rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
        omega
      · have hafterEll : P.ell < state.val := by omega
        by_cases hbeforeRho : state.val < P.rho
        · rw [sMap_between_ell_rho P state hafterEll hbeforeRho] at himage
          have hcoordinateLt :
              P.ell + P.rho - 1 - state.val < P.order := by
            have := P.rho_lt_order
            omega
          rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
          have hle : state.val ≤ P.ell + P.rho - 1 := by
            omega
          have hsum :
              P.ell + P.rho - 1 = target + state.val :=
            (Nat.sub_eq_iff_eq_add hle).mp himage
          omega
        · have hatRho : P.rho ≤ state.val := by omega
          rw [sMap_at_or_after_rho P state hatRho] at himage
          have hcoordinateLt :
              P.rho + P.order - 1 - state.val < P.order := by
            have hrhoPos : 0 < P.rho := by
              simp [Params.rho, Params.m]
            have := P.rho_lt_order
            omega
          rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
          omega

/-- Inversion of `s` on the final reflection interval. -/
theorem sMap_preimage_after_target (P : Params)
    (state : State P) (target : ℕ)
    (htargetRho : P.rho ≤ target)
    (htargetOrder : target < P.order)
    (himage : (sMap P state).val = target) :
    state.val = P.rho + P.order - 1 - target := by
  by_cases hzero : state.val = 0
  · rw [sMap_at_zero P state hzero] at himage
    rw [stateOfNat_val_of_lt P (by
      have := P.rho_lt_order
      omega)] at himage
    have hrhoPred : P.rho - 1 < P.rho := by
      simp [Params.rho, Params.m]
    omega
  · by_cases hell : state.val = P.ell
    · rw [sMap_at_ell P state hell] at himage
      rw [stateOfNat_val_of_lt P (by
        have := P.rho_lt_order
        omega)] at himage
      have hrhoPred : P.rho - 1 < P.rho := by
        simp [Params.rho, Params.m]
      omega
    · by_cases hbeforeEll : state.val < P.ell
      · rw [sMap_between_zero_ell P state (by omega) hbeforeEll] at himage
        have hcoordinateLt : P.ell - state.val < P.order := by
          have := P.ell_lt_order
          omega
        rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
        have := P.rho_eq
        omega
      · have hafterEll : P.ell < state.val := by omega
        by_cases hbeforeRho : state.val < P.rho
        · rw [sMap_between_ell_rho P state hafterEll hbeforeRho] at himage
          have hcoordinateLt :
              P.ell + P.rho - 1 - state.val < P.order := by
            have := P.rho_lt_order
            omega
          rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
          omega
        · have hatRho : P.rho ≤ state.val := by omega
          rw [sMap_at_or_after_rho P state hatRho] at himage
          have hcoordinateLt :
              P.rho + P.order - 1 - state.val < P.order := by
            have hrhoPos : 0 < P.rho := by
              simp [Params.rho, Params.m]
            have := P.rho_lt_order
            omega
          rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
          have hle : state.val ≤ P.rho + P.order - 1 := by
            omega
          have hsum :
              P.rho + P.order - 1 = target + state.val :=
            (Nat.sub_eq_iff_eq_add hle).mp himage
          omega

/-- Fourth factor-table row. -/
theorem imageAvoids_middle_fourth_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s])
      (fun coordinate =>
        coordinate < (residualParams X L).ell ∨
        coordinate = (residualParams X L).cycle) := by
  apply imageAvoids_append (imageAvoids_middle_third_row hmiddle)
  intro state hnew
  simp only [DFA.evalFrom_cons, DFA.evalFrom_nil, automaton_step_s] at hnew
  rcases hnew with hlow | hcycle
  · left
    exact sMap_preimage_below_ell_middle state hlow
  · right
    exact sMap_preimage_cycle_middle hmiddle state hcycle

/-- Inverse-image calculation for the `A^(2ell)` factor. -/
theorem aTwoEll_preimage_fifth_hole {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      (1 ≤
          ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord
              (2 * (residualParams X L).ell))).val ∧
        ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord
              (2 * (residualParams X L).ell))).val ≤
          (residualParams X L).ell) ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord
            (2 * (residualParams X L).ell))).val =
        2 * (residualParams X L).ell) :
    state.val < (residualParams X L).ell ∨
      state.val = (residualParams X L).cycle := by
  let P := residualParams X L
  change State P at state
  change
    (1 ≤
        ((automaton P).evalFrom state
          (wordPow aWord (2 * P.ell))).val ∧
      ((automaton P).evalFrom state
          (wordPow aWord (2 * P.ell))).val ≤ P.ell) ∨
    ((automaton P).evalFrom state
      (wordPow aWord (2 * P.ell))).val = 2 * P.ell at himage
  change state.val < P.ell ∨ state.val = P.cycle
  rcases himage with hlow | hspecial
  · obtain ⟨index, hcycle⟩ :=
      exists_cycleState_aPower_of_ell_le P state (2 * P.ell)
        (by omega)
    rw [hcycle] at hlow
    rcases cycleState_val_zero_or_above_ell P index with hz | habove
    · omega
    · omega
  · by_cases htail : state.val < P.ell
    · exact Or.inl htail
    · right
      have hinterval : P.ell ≤ state.val := by omega
      obtain ⟨index, hindex⟩ :=
        exists_intervalState_eq P state hinterval
      have hpower :
          (automaton P).evalFrom state
              (wordPow aWord (2 * P.ell)) =
            cycleState P ((cycleNext P)^[2 * P.ell] index) := by
        rw [← hindex]
        exact evalFrom_aPower_intervalState_of_pos P index
          (2 * P.ell) (by have := P.ell_pos; omega)
      rw [hpower] at hspecial
      have hellLtCycle : P.ell < P.cycle := by
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [P, residualParams, Params.ell, Params.cycle]
        omega
      have htarget : 2 * P.ell = P.ell + P.ell := by omega
      have hspecial' :
          (cycleState P
            ((cycleNext P)^[2 * P.ell] index)).val =
              P.ell + P.ell := by
        rw [← htarget]
        exact hspecial
      have hadvance :=
        (cycleState_val_eq_ell_add_iff P
          ((cycleNext P)^[2 * P.ell] index)
          P.ell_pos hellLtCycle).mp hspecial'
      rw [iterate_cycleNext] at hadvance
      change ((index.val + 2 * P.ell) % P.cycle) = P.ell at hadvance
      have htwoEllLt : 2 * P.ell < P.cycle := by
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [P, residualParams, Params.ell, Params.cycle]
        omega
      have hsumTwo :
          index.val + 2 * P.ell < P.cycle + P.cycle := by
        omega
      have hsum : P.cycle ≤ index.val + 2 * P.ell := by
        by_contra hnot
        have hlt : index.val + 2 * P.ell < P.cycle := by omega
        rw [Nat.mod_eq_of_lt hlt] at hadvance
        have := P.ell_pos
        omega
      rw [Nat.mod_eq_sub_mod hsum] at hadvance
      rw [Nat.mod_eq_of_lt (by omega)] at hadvance
      have hstateValue : state.val = P.ell + index.val := by
        rw [← hindex, intervalState_val]
      simp [Params.order] at *
      omega

/-- Fifth factor-table row. -/
theorem imageAvoids_middle_fifth_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell))
      (fun coordinate =>
        (1 ≤ coordinate ∧
          coordinate ≤ (residualParams X L).ell) ∨
        coordinate = 2 * (residualParams X L).ell) := by
  apply imageAvoids_append (imageAvoids_middle_fourth_row hmiddle)
  intro state hnew
  exact aTwoEll_preimage_fifth_hole hmiddle state hnew

/-- Inverse-image calculation for the second `p²` factor. -/
theorem pSquared_preimage_sixth_hole {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      ((automaton (residualParams X L)).evalFrom state pSquared).val = 0 ∨
      (2 ≤ ((automaton (residualParams X L)).evalFrom state
          pSquared).val ∧
        ((automaton (residualParams X L)).evalFrom state
          pSquared).val <
            (residualParams X L).ell) ∨
      ((automaton (residualParams X L)).evalFrom state
          pSquared).val =
        2 * (residualParams X L).ell ∨
      ((automaton (residualParams X L)).evalFrom state
          pSquared).val =
        (residualParams X L).rho) :
    (1 ≤ state.val ∧
      state.val ≤ (residualParams X L).ell) ∨
    state.val = 2 * (residualParams X L).ell := by
  let P := residualParams X L
  change State P at state
  change
    ((automaton P).evalFrom state pSquared).val = 0 ∨
    (2 ≤ ((automaton P).evalFrom state pSquared).val ∧
      ((automaton P).evalFrom state pSquared).val < P.ell) ∨
    ((automaton P).evalFrom state pSquared).val = 2 * P.ell ∨
    ((automaton P).evalFrom state pSquared).val = P.rho at himage
  change (1 ≤ state.val ∧ state.val ≤ P.ell) ∨
    state.val = 2 * P.ell
  rw [evalFrom_pSquared] at himage
  have hellVal : (P.stateOfNat P.ell).val = P.ell :=
    stateOfNat_val_of_lt P P.ell_lt_order
  have hzeroVal : (P.stateOfNat 0).val = 0 :=
    stateOfNat_val_of_lt P P.order_pos
  have hrhoVal : (P.stateOfNat P.rho).val = P.rho :=
    stateOfNat_val_of_lt P P.rho_lt_order
  have honeLt : 1 < P.order := by
    simp [Params.order, Params.ell, Params.cycle]
    omega
  have honeVal : (P.stateOfNat 1).val = 1 :=
    stateOfNat_val_of_lt P honeLt
  have hrhoBeyondTwoEll : 2 * P.ell < P.rho := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, residualParams, Params.ell, Params.rho, Params.m]
    omega
  by_cases hzero : state.val = 0
  · rw [if_pos hzero, hellVal] at himage
    have := P.ell_pos
    rcases himage with h | h | h | h <;> omega
  · rw [if_neg hzero] at himage
    by_cases hell : state.val = P.ell
    · left
      exact ⟨by rw [hell]; have := P.ell_pos; omega, hell.le⟩
    · rw [if_neg hell] at himage
      by_cases hone : state.val = 1
      · left
        rw [hone]
        exact ⟨by omega, by simp [Params.ell]⟩
      · rw [if_neg hone] at himage
        by_cases hrho : state.val = P.rho
        · rw [if_pos hrho, honeVal] at himage
          rcases himage with h | h | h | h <;> omega
        · rw [if_neg hrho] at himage
          rcases himage with hzeroImage | hlow | htwoEll | hrhoImage
          · exact (hzero hzeroImage).elim
          · left
            exact ⟨by omega, by omega⟩
          · exact Or.inr htwoEll
          · exact (hrho hrhoImage).elim

/-- Sixth factor-table row. -/
theorem imageAvoids_middle_sixth_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell) ++ pSquared)
      (fun coordinate =>
        coordinate = 0 ∨
        (2 ≤ coordinate ∧
          coordinate < (residualParams X L).ell) ∨
        coordinate = 2 * (residualParams X L).ell ∨
        coordinate = (residualParams X L).rho) := by
  apply imageAvoids_append (imageAvoids_middle_fifth_row hmiddle)
  intro state hnew
  exact pSquared_preimage_sixth_hole hmiddle state hnew

/-- If a long `A`-power advances by fewer local coordinates than a positive
target, that target has the expected unique interval preimage. -/
theorem aPower_preimage_cycle_of_count_lt_target (P : Params)
    (state : State P) (count target : ℕ)
    (hcount : P.ell ≤ count) (hcountTarget : count < target)
    (htarget : target < P.cycle)
    (himage :
      ((automaton P).evalFrom state
        (wordPow aWord count)).val = P.ell + target) :
    state.val = P.ell + (target - count) := by
  have hcountPos : 0 < count := P.ell_pos.trans_le hcount
  have htargetPos : 0 < target := by omega
  by_cases hzero : state.val = 0
  · have hstate : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    rw [hstate, evalFrom_aPower_zero] at himage
    have hadvance :=
      (cycleState_val_eq_ell_add_iff P
        ((cycleNext P)^[count] ⟨0, P.cycle_pos⟩)
        htargetPos htarget).mp himage
    rw [iterate_cycleNext] at hadvance
    change ((0 + count) % P.cycle) = target at hadvance
    simp only [zero_add] at hadvance
    rw [Nat.mod_eq_of_lt (hcountTarget.trans htarget)] at hadvance
    omega
  · by_cases htail : state.val < P.ell
    · have hentry : P.ell + 1 - state.val ≤ count := by
        omega
      rw [evalFrom_aPower_tail_after_entry P state count
        (Nat.pos_of_ne_zero hzero) htail hentry] at himage
      have hadvance :=
        (cycleState_val_eq_ell_add_iff P
          ((cycleNext P)^[count - (P.ell + 1 - state.val)]
            (cycleOneIndex P))
          htargetPos htarget).mp himage
      rw [iterate_cycleNext] at hadvance
      change
        ((1 + (count - (P.ell + 1 - state.val))) % P.cycle) =
          target at hadvance
      have hphaseLt :
          1 + (count - (P.ell + 1 - state.val)) < target := by
        omega
      rw [Nat.mod_eq_of_lt (hphaseLt.trans htarget)] at hadvance
      omega
    · have hinterval : P.ell ≤ state.val := by omega
      obtain ⟨index, hindex⟩ :=
        exists_intervalState_eq P state hinterval
      have hpower :
          (automaton P).evalFrom state (wordPow aWord count) =
            cycleState P ((cycleNext P)^[count] index) := by
        rw [← hindex]
        exact evalFrom_aPower_intervalState_of_pos P index count hcountPos
      rw [hpower] at himage
      have hadvance :=
        (cycleState_val_eq_ell_add_iff P
          ((cycleNext P)^[count] index)
          htargetPos htarget).mp himage
      rw [iterate_cycleNext] at hadvance
      change ((index.val + count) % P.cycle) = target at hadvance
      have hsumTwo :
          index.val + count < P.cycle + P.cycle := by
        omega
      have hindexValue : index.val = target - count := by
        by_cases hsum : index.val + count < P.cycle
        · rw [Nat.mod_eq_of_lt hsum] at hadvance
          omega
        · rw [Nat.mod_eq_sub_mod (by omega)] at hadvance
          rw [Nat.mod_eq_of_lt (by omega)] at hadvance
          omega
      have hstateValue : state.val = P.ell + index.val := by
        rw [← hindex, intervalState_val]
      rw [hstateValue, hindexValue]

/-- Complementary long-power inversion when the target lies far enough
behind the advance that only a wrapped interval preimage can reach it. -/
theorem aPower_preimage_cycle_of_target_add_ell_le_count (P : Params)
    (state : State P) (count target : ℕ)
    (hcount : P.ell ≤ count) (htargetPos : 0 < target)
    (htargetPhase : target + P.ell ≤ count)
    (hcountCycle : count < P.cycle)
    (himage :
      ((automaton P).evalFrom state
        (wordPow aWord count)).val = P.ell + target) :
    state.val = P.ell + (P.cycle + target - count) := by
  have hcountPos : 0 < count := P.ell_pos.trans_le hcount
  have htargetCount : target < count := by
    have := P.ell_pos
    omega
  have htargetCycle : target < P.cycle :=
    htargetCount.trans hcountCycle
  by_cases hzero : state.val = 0
  · have hstate : state = P.stateOfNat 0 := by
      rw [← hzero]
      exact (stateOfNat_state_val P state).symm
    rw [hstate, evalFrom_aPower_zero] at himage
    have hadvance :=
      (cycleState_val_eq_ell_add_iff P
        ((cycleNext P)^[count] ⟨0, P.cycle_pos⟩)
        htargetPos htargetCycle).mp himage
    rw [iterate_cycleNext] at hadvance
    change ((0 + count) % P.cycle) = target at hadvance
    simp only [zero_add] at hadvance
    rw [Nat.mod_eq_of_lt hcountCycle] at hadvance
    omega
  · by_cases htail : state.val < P.ell
    · have hentry : P.ell + 1 - state.val ≤ count := by
        omega
      rw [evalFrom_aPower_tail_after_entry P state count
        (Nat.pos_of_ne_zero hzero) htail hentry] at himage
      have hadvance :=
        (cycleState_val_eq_ell_add_iff P
          ((cycleNext P)^[count - (P.ell + 1 - state.val)]
            (cycleOneIndex P))
          htargetPos htargetCycle).mp himage
      rw [iterate_cycleNext] at hadvance
      change
        ((1 + (count - (P.ell + 1 - state.val))) % P.cycle) =
          target at hadvance
      have hphaseAbove :
          target <
            1 + (count - (P.ell + 1 - state.val)) := by
        omega
      have hphaseCycle :
          1 + (count - (P.ell + 1 - state.val)) < P.cycle := by
        omega
      rw [Nat.mod_eq_of_lt hphaseCycle] at hadvance
      omega
    · have hinterval : P.ell ≤ state.val := by omega
      obtain ⟨index, hindex⟩ :=
        exists_intervalState_eq P state hinterval
      have hpower :
          (automaton P).evalFrom state (wordPow aWord count) =
            cycleState P ((cycleNext P)^[count] index) := by
        rw [← hindex]
        exact evalFrom_aPower_intervalState_of_pos P index count hcountPos
      rw [hpower] at himage
      have hadvance :=
        (cycleState_val_eq_ell_add_iff P
          ((cycleNext P)^[count] index)
          htargetPos htargetCycle).mp himage
      rw [iterate_cycleNext] at hadvance
      change ((index.val + count) % P.cycle) = target at hadvance
      have hsumTwo :
          index.val + count < P.cycle + P.cycle := by
        omega
      have hsum : P.cycle ≤ index.val + count := by
        by_contra hnot
        have hlt : index.val + count < P.cycle := by omega
        rw [Nat.mod_eq_of_lt hlt] at hadvance
        omega
      rw [Nat.mod_eq_sub_mod hsum] at hadvance
      rw [Nat.mod_eq_of_lt (by omega)] at hadvance
      have hindexValue : index.val = P.cycle + target - count := by
        omega
      have hstateValue : state.val = P.ell + index.val := by
        rw [← hindex, intervalState_val]
      rw [hstateValue, hindexValue]

/-- Inverse-image calculation for the first parameter-dependent long
`A`-power. -/
theorem aFirstLong_preimage_seventh_hole {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      (1 ≤
          ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord (2 * L - 4 * X - 1))).val ∧
        ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord (2 * L - 4 * X - 1))).val ≤
          (residualParams X L).ell) ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (2 * L - 4 * X - 1))).val =
        2 * L + 3 ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (2 * L - 4 * X - 1))).val =
        4 * L - 2 * X + 4) :
    state.val = 0 ∨
    (2 ≤ state.val ∧
      state.val < (residualParams X L).ell) ∨
    state.val = 2 * (residualParams X L).ell ∨
    state.val = (residualParams X L).rho := by
  let P := residualParams X L
  let count := 2 * L - 4 * X - 1
  let targetOne := 2 * L - 2 * X + 1
  let targetTwo := 4 * L - 4 * X + 2
  change State P at state
  change
    (1 ≤ ((automaton P).evalFrom state
        (wordPow aWord count)).val ∧
      ((automaton P).evalFrom state
        (wordPow aWord count)).val ≤ P.ell) ∨
    ((automaton P).evalFrom state
      (wordPow aWord count)).val = 2 * L + 3 ∨
    ((automaton P).evalFrom state
      (wordPow aWord count)).val = 4 * L - 2 * X + 4 at himage
  change state.val = 0 ∨
    (2 ≤ state.val ∧ state.val < P.ell) ∨
    state.val = 2 * P.ell ∨ state.val = P.rho
  have hcount : P.ell ≤ count := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, count, residualParams, Params.ell]
    omega
  have hcountOne : count < targetOne := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [count, targetOne]
    omega
  have hcountTwo : count < targetTwo := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [count, targetTwo]
    omega
  have htargetOneCycle : targetOne < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetOne, residualParams, Params.cycle]
    omega
  have htargetTwoCycle : targetTwo < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetTwo, residualParams, Params.cycle]
    omega
  have hglobalOne : 2 * L + 3 = P.ell + targetOne := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetOne, residualParams, Params.ell]
    omega
  have hglobalTwo : 4 * L - 2 * X + 4 = P.ell + targetTwo := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetTwo, residualParams, Params.ell]
    omega
  rcases himage with hlow | hone | htwo
  · obtain ⟨index, hcycle⟩ :=
      exists_cycleState_aPower_of_ell_le P state count hcount
    rw [hcycle] at hlow
    rcases cycleState_val_zero_or_above_ell P index with hz | habove
    · omega
    · omega
  · have hlocal :
        ((automaton P).evalFrom state
          (wordPow aWord count)).val = P.ell + targetOne := by
      rw [← hglobalOne]
      exact hone
    have hpreimage :=
      aPower_preimage_cycle_of_count_lt_target P state count targetOne
        hcount hcountOne htargetOneCycle hlocal
    right
    right
    left
    simp [P, count, targetOne, residualParams, Params.ell] at hpreimage ⊢
    omega
  · have hlocal :
        ((automaton P).evalFrom state
          (wordPow aWord count)).val = P.ell + targetTwo := by
      rw [← hglobalTwo]
      exact htwo
    have hpreimage :=
      aPower_preimage_cycle_of_count_lt_target P state count targetTwo
        hcount hcountTwo htargetTwoCycle hlocal
    right
    right
    right
    simp [P, count, targetTwo, residualParams, Params.ell,
      Params.rho, Params.m] at hpreimage ⊢
    omega

/-- Seventh factor-table row. -/
theorem imageAvoids_middle_seventh_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell) ++ pSquared ++
        wordPow aWord (2 * L - 4 * X - 1))
      (fun coordinate =>
        (1 ≤ coordinate ∧
          coordinate ≤ (residualParams X L).ell) ∨
        coordinate = 2 * L + 3 ∨
        coordinate = 4 * L - 2 * X + 4) := by
  apply imageAvoids_append (imageAvoids_middle_sixth_row hmiddle)
  intro state hnew
  exact aFirstLong_preimage_seventh_hole hmiddle state hnew

/-- Inverse-image calculation for the first single `p`. -/
theorem pMap_preimage_eighth_hole {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      (2 ≤ (pMap (residualParams X L) state).val ∧
        (pMap (residualParams X L) state).val ≤
          (residualParams X L).ell) ∨
      (pMap (residualParams X L) state).val =
        2 * (residualParams X L).ell ∨
      (pMap (residualParams X L) state).val =
        (residualParams X L).rho ∨
      (pMap (residualParams X L) state).val =
        2 * L + 6 * X + 8) :
    (1 ≤ state.val ∧
      state.val ≤ (residualParams X L).ell) ∨
    state.val = 2 * L + 3 ∨
    state.val = 4 * L - 2 * X + 4 := by
  let P := residualParams X L
  change State P at state
  change
    (2 ≤ (pMap P state).val ∧ (pMap P state).val ≤ P.ell) ∨
    (pMap P state).val = 2 * P.ell ∨
    (pMap P state).val = P.rho ∨
    (pMap P state).val = 2 * L + 6 * X + 8 at himage
  change (1 ≤ state.val ∧ state.val ≤ P.ell) ∨
    state.val = 2 * L + 3 ∨
    state.val = 4 * L - 2 * X + 4
  have hrhoBeyondTwoEll : 2 * P.ell < P.rho := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, residualParams, Params.ell, Params.rho, Params.m]
    omega
  have hlastBeyondRho : P.rho < 2 * L + 6 * X + 8 := by
    simp [P, residualParams, Params.rho, Params.m]
    omega
  by_cases hzero : state.val = 0
  · rw [pMap_at_zero P state hzero] at himage
    have honeLt : 1 < P.order := by
      simp [Params.order, Params.ell, Params.cycle]
      omega
    rw [stateOfNat_val_of_lt P honeLt] at himage
    have := P.ell_pos
    rcases himage with h | h | h | h <;> omega
  · by_cases hone : state.val = 1
    · left
      rw [hone]
      exact ⟨by omega, by simp [Params.ell]⟩
    · by_cases hell : state.val = P.ell
      · left
        exact ⟨by rw [hell]; have := P.ell_pos; omega, hell.le⟩
      · by_cases hrho : state.val = P.rho
        · rw [pMap_at_rho P state hrho] at himage
          rw [stateOfNat_val_of_lt P P.order_pos] at himage
          rcases hmiddle with ⟨hlower, hupper⟩
          simp [P, residualParams, Params.ell, Params.rho,
            Params.m] at himage
        · by_cases hbeforeEll : state.val < P.ell
          · have htwo : 2 ≤ state.val := by omega
            left
            exact ⟨by omega, hbeforeEll.le⟩
          · have hafterEll : P.ell < state.val := by omega
            by_cases hbeforeRho : state.val < P.rho
            · rw [pMap_between_ell_rho P state
                hafterEll hbeforeRho] at himage
              have hcoordinateLt :
                  P.ell + P.rho - state.val < P.order := by
                have := P.rho_lt_order
                omega
              rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
              rcases himage with hlow | htwoEll | hrhoImage | hlast
              · omega
              · right
                left
                simp [P, residualParams, Params.ell,
                  Params.rho, Params.m] at htwoEll ⊢
                omega
              · omega
              · omega
            · have hafterRho : P.rho < state.val := by omega
              rw [pMap_after_rho P state hafterRho] at himage
              have hcoordinateLt :
                  P.rho + P.order - state.val < P.order := by
                have := P.rho_lt_order
                omega
              rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
              rcases himage with hlow | htwoEll | hrhoImage | hlast
              · omega
              · omega
              · omega
              · right
                right
                have hle :
                    state.val ≤ P.rho + P.order := by omega
                have hsum :
                    P.rho + P.order =
                      (2 * L + 6 * X + 8) + state.val :=
                  (Nat.sub_eq_iff_eq_add hle).mp hlast
                have horder : P.order = 2 * X + 4 * L + 7 := by
                  simp [P, residualParams, Params.order, Params.ell,
                    Params.cycle]
                  omega
                have hrhoValue : P.rho = 2 * X + 2 * L + 5 := by
                  simp [P, residualParams, Params.rho, Params.m]
                  omega
                have hsum' :
                    (2 * X + 2 * L + 5) +
                        (2 * X + 4 * L + 7) =
                      (2 * L + 6 * X + 8) + state.val := by
                  calc
                    (2 * X + 2 * L + 5) +
                        (2 * X + 4 * L + 7) =
                      P.rho + P.order := by
                        rw [hrhoValue, horder]
                    _ = (2 * L + 6 * X + 8) + state.val := hsum
                omega

/-- Eighth factor-table row. -/
theorem imageAvoids_middle_eighth_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell) ++ pSquared ++
        wordPow aWord (2 * L - 4 * X - 1) ++ [.p])
      (fun coordinate =>
        (2 ≤ coordinate ∧
          coordinate ≤ (residualParams X L).ell) ∨
        coordinate = 2 * (residualParams X L).ell ∨
        coordinate = (residualParams X L).rho ∨
        coordinate = 2 * L + 6 * X + 8) := by
  apply imageAvoids_append (imageAvoids_middle_seventh_row hmiddle)
  intro state hnew
  simp only [DFA.evalFrom_cons, DFA.evalFrom_nil, automaton_step_p] at hnew
  exact pMap_preimage_eighth_hole hmiddle state hnew

/-- Inverse-image calculation for the second long `A`-power. -/
theorem aSecondLong_preimage_ninth_hole {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      (1 ≤
          ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord (4 * L - 6 * X))).val ∧
        ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord (4 * L - 6 * X))).val ≤
          (residualParams X L).ell) ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (4 * L - 6 * X))).val =
        2 * L - 4 * X ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (4 * L - 6 * X))).val =
        2 * L + 3 ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (4 * L - 6 * X))).val =
        4 * L - 2 * X + 4) :
    (2 ≤ state.val ∧
      state.val ≤ (residualParams X L).ell) ∨
    state.val = 2 * (residualParams X L).ell ∨
    state.val = (residualParams X L).rho ∨
    state.val = 2 * L + 6 * X + 8 := by
  let P := residualParams X L
  let count := 4 * L - 6 * X
  let targetOne := 2 * L - 6 * X - 2
  let targetTwo := 2 * L - 2 * X + 1
  let targetThree := 4 * L - 4 * X + 2
  change State P at state
  change
    (1 ≤ ((automaton P).evalFrom state
        (wordPow aWord count)).val ∧
      ((automaton P).evalFrom state
        (wordPow aWord count)).val ≤ P.ell) ∨
    ((automaton P).evalFrom state
      (wordPow aWord count)).val = 2 * L - 4 * X ∨
    ((automaton P).evalFrom state
      (wordPow aWord count)).val = 2 * L + 3 ∨
    ((automaton P).evalFrom state
      (wordPow aWord count)).val = 4 * L - 2 * X + 4 at himage
  change (2 ≤ state.val ∧ state.val ≤ P.ell) ∨
    state.val = 2 * P.ell ∨ state.val = P.rho ∨
    state.val = 2 * L + 6 * X + 8
  have hcount : P.ell ≤ count := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, count, residualParams, Params.ell]
    omega
  have hcountCycle : count < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, count, residualParams, Params.cycle]
    omega
  have htargetOnePos : 0 < targetOne := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [targetOne]
    omega
  have htargetTwoPos : 0 < targetTwo := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [targetTwo]
  have htargetOnePhase : targetOne + P.ell ≤ count := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetOne, count, residualParams, Params.ell]
    omega
  have htargetTwoPhase : targetTwo + P.ell ≤ count := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetTwo, count, residualParams, Params.ell]
    omega
  have hcountThree : count < targetThree := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [count, targetThree]
    omega
  have htargetThreeCycle : targetThree < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetThree, residualParams, Params.cycle]
    omega
  have hglobalOne : 2 * L - 4 * X = P.ell + targetOne := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetOne, residualParams, Params.ell]
    omega
  have hglobalTwo : 2 * L + 3 = P.ell + targetTwo := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetTwo, residualParams, Params.ell]
    omega
  have hglobalThree :
      4 * L - 2 * X + 4 = P.ell + targetThree := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetThree, residualParams, Params.ell]
    omega
  rcases himage with hlow | hone | htwo | hthree
  · obtain ⟨index, hcycle⟩ :=
      exists_cycleState_aPower_of_ell_le P state count hcount
    rw [hcycle] at hlow
    rcases cycleState_val_zero_or_above_ell P index with hz | habove
    · omega
    · omega
  · have hlocal :
        ((automaton P).evalFrom state
          (wordPow aWord count)).val = P.ell + targetOne := by
      rw [← hglobalOne]
      exact hone
    have hpreimage :=
      aPower_preimage_cycle_of_target_add_ell_le_count P state
        count targetOne hcount htargetOnePos htargetOnePhase
        hcountCycle hlocal
    right
    right
    left
    simp [P, count, targetOne, residualParams, Params.ell,
      Params.cycle, Params.rho, Params.m] at hpreimage ⊢
    omega
  · have hlocal :
        ((automaton P).evalFrom state
          (wordPow aWord count)).val = P.ell + targetTwo := by
      rw [← hglobalTwo]
      exact htwo
    have hpreimage :=
      aPower_preimage_cycle_of_target_add_ell_le_count P state
        count targetTwo hcount htargetTwoPos htargetTwoPhase
        hcountCycle hlocal
    right
    right
    right
    simp [P, count, targetTwo, residualParams, Params.ell,
      Params.cycle] at hpreimage ⊢
    omega
  · have hlocal :
        ((automaton P).evalFrom state
          (wordPow aWord count)).val = P.ell + targetThree := by
      rw [← hglobalThree]
      exact hthree
    have hpreimage :=
      aPower_preimage_cycle_of_count_lt_target P state count targetThree
        hcount hcountThree htargetThreeCycle hlocal
    right
    left
    simp [P, count, targetThree, residualParams, Params.ell] at hpreimage ⊢
    omega

/-- Ninth factor-table row. -/
theorem imageAvoids_middle_ninth_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell) ++ pSquared ++
        wordPow aWord (2 * L - 4 * X - 1) ++ [.p] ++
        wordPow aWord (4 * L - 6 * X))
      (fun coordinate =>
        (1 ≤ coordinate ∧
          coordinate ≤ (residualParams X L).ell) ∨
        coordinate = 2 * L - 4 * X ∨
        coordinate = 2 * L + 3 ∨
        coordinate = 4 * L - 2 * X + 4) := by
  apply imageAvoids_append (imageAvoids_middle_eighth_row hmiddle)
  intro state hnew
  exact aSecondLong_preimage_ninth_hole hmiddle state hnew

/-- The extra reflected point in the second single-`p` row. -/
theorem pMap_preimage_eightX_seven {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      (pMap (residualParams X L) state).val = 8 * X + 7) :
    state.val = 2 * L - 4 * X := by
  let P := residualParams X L
  change State P at state
  change (pMap P state).val = 8 * X + 7 at himage
  change state.val = 2 * L - 4 * X
  have htargetAfterEll : P.ell < 8 * X + 7 := by
    simp [P, residualParams, Params.ell]
    omega
  have htargetBeforeRho : 8 * X + 7 < P.rho := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, residualParams, Params.rho, Params.m]
    omega
  by_cases hzero : state.val = 0
  · rw [pMap_at_zero P state hzero] at himage
    have honeLt : 1 < P.order := by
      simp [Params.order, Params.ell, Params.cycle]
      omega
    rw [stateOfNat_val_of_lt P honeLt] at himage
    omega
  · by_cases hone : state.val = 1
    · rw [pMap_at_one P state hone] at himage
      rw [stateOfNat_val_of_lt P P.ell_lt_order] at himage
      omega
    · by_cases hell : state.val = P.ell
      · rw [pMap_at_ell P state hell] at himage
        rw [stateOfNat_val_of_lt P P.rho_lt_order] at himage
        omega
      · by_cases hrho : state.val = P.rho
        · rw [pMap_at_rho P state hrho] at himage
          rw [stateOfNat_val_of_lt P P.order_pos] at himage
          omega
        · by_cases hbeforeEll : state.val < P.ell
          · rw [pMap_before_ell P state (by omega) hbeforeEll] at himage
            have hcoordinateLt :
                P.ell + 1 - state.val < P.order := by
              have := P.ell_lt_order
              omega
            rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
            omega
          · have hafterEll : P.ell < state.val := by omega
            by_cases hbeforeRho : state.val < P.rho
            · rw [pMap_between_ell_rho P state
                hafterEll hbeforeRho] at himage
              have hcoordinateLt :
                  P.ell + P.rho - state.val < P.order := by
                have := P.rho_lt_order
                omega
              rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
              simp [P, residualParams, Params.ell, Params.rho,
                Params.m] at himage ⊢
              omega
            · have hafterRho : P.rho < state.val := by omega
              rw [pMap_after_rho P state hafterRho] at himage
              have hcoordinateLt :
                  P.rho + P.order - state.val < P.order := by
                have := P.rho_lt_order
                omega
              rw [stateOfNat_val_of_lt P hcoordinateLt] at himage
              omega

/-- Tenth factor-table row. -/
theorem imageAvoids_middle_tenth_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell) ++ pSquared ++
        wordPow aWord (2 * L - 4 * X - 1) ++ [.p] ++
        wordPow aWord (4 * L - 6 * X) ++ [.p])
      (fun coordinate =>
        (2 ≤ coordinate ∧
          coordinate ≤ (residualParams X L).ell) ∨
        coordinate = 2 * (residualParams X L).ell ∨
        coordinate = 8 * X + 7 ∨
        coordinate = (residualParams X L).rho ∨
        coordinate = 2 * L + 6 * X + 8) := by
  apply imageAvoids_append (imageAvoids_middle_ninth_row hmiddle)
  intro state hnew
  simp only [DFA.evalFrom_cons, DFA.evalFrom_nil, automaton_step_p] at hnew
  rcases hnew with hlow | htwoEll | heightX | hrho | hlast
  · have hpre := pMap_preimage_eighth_hole hmiddle state
      (Or.inl hlow)
    rcases hpre with hpre | hpre | hpre
    · exact Or.inl hpre
    · exact Or.inr (Or.inr (Or.inl hpre))
    · exact Or.inr (Or.inr (Or.inr hpre))
  · have hpre := pMap_preimage_eighth_hole hmiddle state
      (Or.inr (Or.inl htwoEll))
    rcases hpre with hpre | hpre | hpre
    · exact Or.inl hpre
    · exact Or.inr (Or.inr (Or.inl hpre))
    · exact Or.inr (Or.inr (Or.inr hpre))
  · exact Or.inr (Or.inl
      (pMap_preimage_eightX_seven hmiddle state heightX))
  · have hpre := pMap_preimage_eighth_hole hmiddle state
      (Or.inr (Or.inr (Or.inl hrho)))
    rcases hpre with hpre | hpre | hpre
    · exact Or.inl hpre
    · exact Or.inr (Or.inr (Or.inl hpre))
    · exact Or.inr (Or.inr (Or.inr hpre))
  · have hpre := pMap_preimage_eighth_hole hmiddle state
      (Or.inr (Or.inr (Or.inr hlast)))
    rcases hpre with hpre | hpre | hpre
    · exact Or.inl hpre
    · exact Or.inr (Or.inr (Or.inl hpre))
    · exact Or.inr (Or.inr (Or.inr hpre))

/-- Inverse-image calculation for the second `A^(ell-1)` factor. -/
theorem aEllPred_preimage_eleventh_hole {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      (1 ≤
          ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord
              ((residualParams X L).ell - 1))).val ∧
        ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord
              ((residualParams X L).ell - 1))).val <
          (residualParams X L).ell) ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord
            ((residualParams X L).ell - 1))).val = 6 * X + 5 ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord
            ((residualParams X L).ell - 1))).val = 10 * X + 8 ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord
            ((residualParams X L).ell - 1))).val =
        (residualParams X L).rho +
          (residualParams X L).ell - 1 ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord
            ((residualParams X L).ell - 1))).val =
        2 * L + 8 * X + 9) :
    (2 ≤ state.val ∧
      state.val ≤ (residualParams X L).ell) ∨
    state.val = 2 * (residualParams X L).ell ∨
    state.val = 8 * X + 7 ∨
    state.val = (residualParams X L).rho ∨
    state.val = 2 * L + 6 * X + 8 := by
  let P := residualParams X L
  let targetOne := 4 * X + 3
  let targetTwo := 8 * X + 6
  let targetThree := P.rho - 1
  let targetFour := 2 * L + 6 * X + 7
  change State P at state
  change
    (1 ≤ ((automaton P).evalFrom state
        (wordPow aWord (P.ell - 1))).val ∧
      ((automaton P).evalFrom state
        (wordPow aWord (P.ell - 1))).val < P.ell) ∨
    ((automaton P).evalFrom state
      (wordPow aWord (P.ell - 1))).val = 6 * X + 5 ∨
    ((automaton P).evalFrom state
      (wordPow aWord (P.ell - 1))).val = 10 * X + 8 ∨
    ((automaton P).evalFrom state
      (wordPow aWord (P.ell - 1))).val = P.rho + P.ell - 1 ∨
    ((automaton P).evalFrom state
      (wordPow aWord (P.ell - 1))).val = 2 * L + 8 * X + 9 at himage
  change (2 ≤ state.val ∧ state.val ≤ P.ell) ∨
    state.val = 2 * P.ell ∨ state.val = 8 * X + 7 ∨
    state.val = P.rho ∨ state.val = 2 * L + 6 * X + 8
  have htargetOneCycle : targetOne < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetOne, residualParams, Params.cycle]
    omega
  have htargetTwoCycle : targetTwo < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetTwo, residualParams, Params.cycle]
    omega
  have htargetThreeCycle : targetThree < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetThree, residualParams, Params.rho, Params.m,
      Params.cycle]
    omega
  have htargetFourCycle : targetFour < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetFour, residualParams, Params.cycle]
    omega
  have hcountOne : P.ell - 1 < targetOne := by
    simp [P, targetOne, residualParams, Params.ell]
    omega
  have hcountTwo : P.ell - 1 < targetTwo := by
    simp [P, targetTwo, residualParams, Params.ell]
    omega
  have hcountThree : P.ell - 1 < targetThree := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, targetThree, residualParams, Params.ell,
      Params.rho, Params.m]
    omega
  have hcountFour : P.ell - 1 < targetFour := by
    simp [P, targetFour, residualParams, Params.ell]
    omega
  have hglobalOne : 6 * X + 5 = P.ell + targetOne := by
    simp [P, targetOne, residualParams, Params.ell]
    omega
  have hglobalTwo : 10 * X + 8 = P.ell + targetTwo := by
    simp [P, targetTwo, residualParams, Params.ell]
    omega
  have hglobalThree :
      P.rho + P.ell - 1 = P.ell + targetThree := by
    simp [targetThree]
    have hrhoPos : 0 < P.rho := by simp [Params.rho, Params.m]
    omega
  have hglobalFour :
      2 * L + 8 * X + 9 = P.ell + targetFour := by
    simp [P, targetFour, residualParams, Params.ell]
    omega
  rcases himage with hlow | hone | htwo | hthree | hfour
  · exact (aEllPred_avoids_low P state hlow).elim
  · have hlocal :
        ((automaton P).evalFrom state
          (wordPow aWord (P.ell - 1))).val = P.ell + targetOne := by
      rw [← hglobalOne]
      exact hone
    have hpreimage :=
      aEllPred_preimage_cycle_of_count_lt_target P state targetOne
        hcountOne htargetOneCycle hlocal
    right
    left
    simp [P, targetOne, residualParams, Params.ell] at hpreimage ⊢
    omega
  · have hlocal :
        ((automaton P).evalFrom state
          (wordPow aWord (P.ell - 1))).val = P.ell + targetTwo := by
      rw [← hglobalTwo]
      exact htwo
    have hpreimage :=
      aEllPred_preimage_cycle_of_count_lt_target P state targetTwo
        hcountTwo htargetTwoCycle hlocal
    right
    right
    left
    simp [P, targetTwo, residualParams, Params.ell] at hpreimage ⊢
    omega
  · have hlocal :
        ((automaton P).evalFrom state
          (wordPow aWord (P.ell - 1))).val =
            P.ell + targetThree := by
      rw [← hglobalThree]
      exact hthree
    have hpreimage :=
      aEllPred_preimage_cycle_of_count_lt_target P state targetThree
        hcountThree htargetThreeCycle hlocal
    right
    right
    right
    left
    simp [P, targetThree, residualParams, Params.ell,
      Params.rho, Params.m] at hpreimage ⊢
    omega
  · have hlocal :
        ((automaton P).evalFrom state
          (wordPow aWord (P.ell - 1))).val = P.ell + targetFour := by
      rw [← hglobalFour]
      exact hfour
    have hpreimage :=
      aEllPred_preimage_cycle_of_count_lt_target P state targetFour
        hcountFour htargetFourCycle hlocal
    right
    right
    right
    right
    simp [P, targetFour, residualParams, Params.ell] at hpreimage ⊢
    omega

/-- Eleventh factor-table row. -/
theorem imageAvoids_middle_eleventh_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell) ++ pSquared ++
        wordPow aWord (2 * L - 4 * X - 1) ++ [.p] ++
        wordPow aWord (4 * L - 6 * X) ++ [.p] ++
        wordPow aWord ((residualParams X L).ell - 1))
      (fun coordinate =>
        (1 ≤ coordinate ∧
          coordinate < (residualParams X L).ell) ∨
        coordinate = 6 * X + 5 ∨
        coordinate = 10 * X + 8 ∨
        coordinate =
          (residualParams X L).rho +
            (residualParams X L).ell - 1 ∨
        coordinate = 2 * L + 8 * X + 9) := by
  apply imageAvoids_append (imageAvoids_middle_tenth_row hmiddle)
  intro state hnew
  exact aEllPred_preimage_eleventh_hole hmiddle state hnew

/-- Inverse-image calculation for the second single `s`. -/
theorem sMap_preimage_twelfth_hole {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      (sMap (residualParams X L) state).val <
          (residualParams X L).ell ∨
      (sMap (residualParams X L) state).val = 2 * L - 2 * X + 1 ∨
      (sMap (residualParams X L) state).val = middleR X L ∨
      (sMap (residualParams X L) state).val = 4 * L - 4 * X + 2 ∨
      (sMap (residualParams X L) state).val =
        (residualParams X L).cycle) :
    (1 ≤ state.val ∧
      state.val < (residualParams X L).ell) ∨
    state.val = 6 * X + 5 ∨
    state.val = 10 * X + 8 ∨
    state.val =
      (residualParams X L).rho +
        (residualParams X L).ell - 1 ∨
    state.val = 2 * L + 8 * X + 9 := by
  let P := residualParams X L
  change State P at state
  change
    (sMap P state).val < P.ell ∨
    (sMap P state).val = 2 * L - 2 * X + 1 ∨
    (sMap P state).val = middleR X L ∨
    (sMap P state).val = 4 * L - 4 * X + 2 ∨
    (sMap P state).val = P.cycle at himage
  change (1 ≤ state.val ∧ state.val < P.ell) ∨
    state.val = 6 * X + 5 ∨ state.val = 10 * X + 8 ∨
    state.val = P.rho + P.ell - 1 ∨
    state.val = 2 * L + 8 * X + 9
  rcases himage with hlow | hfirst | hreflected | hthird | hcycle
  · exact Or.inl (sMap_preimage_below_ell_middle state hlow)
  · have htargetEll : P.ell ≤ 2 * L - 2 * X + 1 := by
      rcases hmiddle with ⟨hlower, hupper⟩
      simp [P, residualParams, Params.ell]
      omega
    have htargetRho :
        2 * L - 2 * X + 1 < P.rho - 1 := by
      rcases hmiddle with ⟨hlower, hupper⟩
      simp [P, residualParams, Params.rho, Params.m]
      omega
    have hpreimage :=
      sMap_preimage_middle_target P state (2 * L - 2 * X + 1)
        htargetEll htargetRho hfirst
    right
    left
    rw [hpreimage]
    have hell : P.ell = 2 * X + 2 := by
      simp [P, residualParams, Params.ell]
    have hrho : P.rho = 2 * X + 2 * L + 5 := by
      simp [P, residualParams, Params.rho, Params.m]
      omega
    rw [hell, hrho]
    omega
  · right
    right
    left
    by_cases hlowSide : L ≤ 4 * X + 1
    · have hr :
          (sMap P state).val = 6 * L - 6 * X + 3 := by
        simpa [middleR, hlowSide] using hreflected
      have htargetRho : P.rho ≤ 6 * L - 6 * X + 3 := by
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [P, residualParams, Params.rho, Params.m]
        omega
      have htargetOrder : 6 * L - 6 * X + 3 < P.order := by
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [P, residualParams, Params.order, Params.ell,
          Params.cycle]
        omega
      have hpreimage :=
        sMap_preimage_after_target P state (6 * L - 6 * X + 3)
          htargetRho htargetOrder hr
      have horder : P.order = 2 * X + 4 * L + 7 := by
        simp [P, residualParams, Params.order, Params.ell,
          Params.cycle]
        omega
      have hrho : P.rho = 2 * X + 2 * L + 5 := by
        simp [P, residualParams, Params.rho, Params.m]
        omega
      have hsum :
          state.val = 10 * X + 8 := by
        rw [hpreimage]
        rw [horder, hrho]
        omega
      exact hsum
    · have hhighSide : 4 * X + 2 ≤ L := by omega
      have hr :
          (sMap P state).val = 2 * L - 6 * X - 2 := by
        simpa [middleR, hlowSide] using hreflected
      have htargetEll : P.ell ≤ 2 * L - 6 * X - 2 := by
        simp [P, residualParams, Params.ell]
        omega
      have htargetRho : 2 * L - 6 * X - 2 < P.rho - 1 := by
        simp [P, residualParams, Params.rho, Params.m]
        omega
      have hpreimage :=
        sMap_preimage_middle_target P state (2 * L - 6 * X - 2)
          htargetEll htargetRho hr
      simp [P, residualParams, Params.ell, Params.rho,
        Params.m] at hpreimage ⊢
      omega
  · have htargetRho : P.rho ≤ 4 * L - 4 * X + 2 := by
      rcases hmiddle with ⟨hlower, hupper⟩
      simp [P, residualParams, Params.rho, Params.m]
      omega
    have htargetOrder : 4 * L - 4 * X + 2 < P.order := by
      simp [P, residualParams, Params.order, Params.ell, Params.cycle]
      omega
    have hpreimage :=
      sMap_preimage_after_target P state (4 * L - 4 * X + 2)
        htargetRho htargetOrder hthird
    right
    right
    right
    right
    have horder : P.order = 2 * X + 4 * L + 7 := by
      simp [P, residualParams, Params.order, Params.ell, Params.cycle]
      omega
    have hrho : P.rho = 2 * X + 2 * L + 5 := by
      simp [P, residualParams, Params.rho, Params.m]
      omega
    rw [hpreimage, horder, hrho]
    omega
  · right
    right
    right
    left
    exact sMap_preimage_cycle_middle hmiddle state hcycle

/-- Twelfth factor-table row. -/
theorem imageAvoids_middle_twelfth_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell) ++ pSquared ++
        wordPow aWord (2 * L - 4 * X - 1) ++ [.p] ++
        wordPow aWord (4 * L - 6 * X) ++ [.p] ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s])
      (fun coordinate =>
        coordinate < (residualParams X L).ell ∨
        coordinate = 2 * L - 2 * X + 1 ∨
        coordinate = middleR X L ∨
        coordinate = 4 * L - 4 * X + 2 ∨
        coordinate = (residualParams X L).cycle) := by
  apply imageAvoids_append (imageAvoids_middle_eleventh_row hmiddle)
  intro state hnew
  simp only [DFA.evalFrom_cons, DFA.evalFrom_nil, automaton_step_s] at hnew
  exact sMap_preimage_twelfth_hole hmiddle state hnew

/-- Rotation inversion on `J` when the advance does not pass the target. -/
theorem aPower_interval_preimage_of_count_le_target (P : Params)
    (state : State P) (count target : ℕ)
    (hstate : P.ell ≤ state.val) (hcountPos : 0 < count)
    (hcountTarget : count ≤ target) (htarget : target < P.cycle)
    (himage :
      ((automaton P).evalFrom state
        (wordPow aWord count)).val = P.ell + target) :
    state.val = P.ell + (target - count) := by
  obtain ⟨index, hindex⟩ :=
    exists_intervalState_eq P state hstate
  have hpower :
      (automaton P).evalFrom state (wordPow aWord count) =
        cycleState P ((cycleNext P)^[count] index) := by
    rw [← hindex]
    exact evalFrom_aPower_intervalState_of_pos P index count hcountPos
  rw [hpower] at himage
  have htargetPos : 0 < target := hcountPos.trans_le hcountTarget
  have hadvance :=
    (cycleState_val_eq_ell_add_iff P
      ((cycleNext P)^[count] index)
      htargetPos htarget).mp himage
  rw [iterate_cycleNext] at hadvance
  change ((index.val + count) % P.cycle) = target at hadvance
  have hcountCycle : count < P.cycle := hcountTarget.trans_lt htarget
  have hsumTwo : index.val + count < P.cycle + P.cycle := by
    omega
  have hindexValue : index.val = target - count := by
    by_cases hsum : index.val + count < P.cycle
    · rw [Nat.mod_eq_of_lt hsum] at hadvance
      omega
    · rw [Nat.mod_eq_sub_mod (by omega)] at hadvance
      rw [Nat.mod_eq_of_lt (by omega)] at hadvance
      omega
  have hstateValue : state.val = P.ell + index.val := by
    rw [← hindex, intervalState_val]
  rw [hstateValue, hindexValue]

/-- Rotation inversion on `J` when the advance wraps past the target. -/
theorem aPower_interval_preimage_of_target_lt_count (P : Params)
    (state : State P) (count target : ℕ)
    (hstate : P.ell ≤ state.val) (htargetCount : target < count)
    (hcountCycle : count < P.cycle)
    (htargetPos : 0 < target)
    (himage :
      ((automaton P).evalFrom state
        (wordPow aWord count)).val = P.ell + target) :
    state.val = P.ell + (P.cycle + target - count) := by
  obtain ⟨index, hindex⟩ :=
    exists_intervalState_eq P state hstate
  have hpower :
      (automaton P).evalFrom state (wordPow aWord count) =
        cycleState P ((cycleNext P)^[count] index) := by
    rw [← hindex]
    exact evalFrom_aPower_intervalState_of_pos P index count
      (by omega)
  rw [hpower] at himage
  have htargetCycle : target < P.cycle :=
    htargetCount.trans hcountCycle
  have hadvance :=
    (cycleState_val_eq_ell_add_iff P
      ((cycleNext P)^[count] index)
      htargetPos htargetCycle).mp himage
  rw [iterate_cycleNext] at hadvance
  change ((index.val + count) % P.cycle) = target at hadvance
  have hsumTwo : index.val + count < P.cycle + P.cycle := by
    omega
  have hsum : P.cycle ≤ index.val + count := by
    by_contra hnot
    have hlt : index.val + count < P.cycle := by omega
    rw [Nat.mod_eq_of_lt hlt] at hadvance
    omega
  rw [Nat.mod_eq_sub_mod hsum] at hadvance
  rw [Nat.mod_eq_of_lt (by omega)] at hadvance
  have hindexValue : index.val = P.cycle + target - count := by
    omega
  have hstateValue : state.val = P.ell + index.val := by
    rw [← hindex, intervalState_val]
  rw [hstateValue, hindexValue]

theorem cycleState_val_eq_zero_iff (P : Params)
    (index : Fin P.cycle) :
    (cycleState P index).val = 0 ↔ index.val = 0 := by
  constructor
  · intro h
    by_cases hindex : index.val = 0
    · exact hindex
    · rw [cycleState_val_of_ne_zero P index hindex] at h
      have := P.ell_pos
      omega
  · intro hindex
    have hfin : index = ⟨0, P.cycle_pos⟩ := Fin.ext hindex
    rw [hfin, cycleState_zero,
      stateOfNat_val_of_lt P P.order_pos]

/-- The unique interval preimage of cycle coordinate `0`. -/
theorem aPower_interval_preimage_zero (P : Params)
    (state : State P) (count : ℕ)
    (hstate : P.ell ≤ state.val) (hcountPos : 0 < count)
    (hcountCycle : count < P.cycle)
    (himage :
      ((automaton P).evalFrom state
        (wordPow aWord count)).val = 0) :
    state.val = P.ell + (P.cycle - count) := by
  obtain ⟨index, hindex⟩ :=
    exists_intervalState_eq P state hstate
  have hpower :
      (automaton P).evalFrom state (wordPow aWord count) =
        cycleState P ((cycleNext P)^[count] index) := by
    rw [← hindex]
    exact evalFrom_aPower_intervalState_of_pos P index count hcountPos
  rw [hpower] at himage
  have hadvance :=
    (cycleState_val_eq_zero_iff P
      ((cycleNext P)^[count] index)).mp himage
  rw [iterate_cycleNext] at hadvance
  change ((index.val + count) % P.cycle) = 0 at hadvance
  have hsumTwo : index.val + count < P.cycle + P.cycle := by
    omega
  have hsum : P.cycle ≤ index.val + count := by
    by_contra hnot
    have hlt : index.val + count < P.cycle := by omega
    rw [Nat.mod_eq_of_lt hlt] at hadvance
    omega
  rw [Nat.mod_eq_sub_mod hsum] at hadvance
  rw [Nat.mod_eq_of_lt (by omega)] at hadvance
  have hindexValue : index.val = P.cycle - count := by omega
  have hstateValue : state.val = P.ell + index.val := by
    rw [← hindex, intervalState_val]
  rw [hstateValue, hindexValue]

/-- Inverse-image calculation for the final `A`-power, including the
`L = 4X + 2` wrap collision. -/
theorem aFinal_preimage_thirteenth_hole {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      (L = 4 * X + 2 ∧
        ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (10 * X + 6 - 2 * L))).val = 0) ∨
      (1 ≤
          ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord (10 * X + 6 - 2 * L))).val ∧
        ((automaton (residualParams X L)).evalFrom state
            (wordPow aWord (10 * X + 6 - 2 * L))).val ≤
          (residualParams X L).ell) ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (10 * X + 6 - 2 * L))).val =
        2 * (residualParams X L).ell ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (10 * X + 6 - 2 * L))).val =
        8 * X + 7 ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (10 * X + 6 - 2 * L))).val =
        2 * L + 6 * X + 8 ∨
      ((automaton (residualParams X L)).evalFrom state
          (wordPow aWord (10 * X + 6 - 2 * L))).val =
        middleZ X L) :
    state.val < (residualParams X L).ell ∨
    state.val = 2 * L - 2 * X + 1 ∨
    state.val = middleR X L ∨
    state.val = 4 * L - 4 * X + 2 ∨
    state.val = (residualParams X L).cycle := by
  let P := residualParams X L
  let count := 10 * X + 6 - 2 * L
  change State P at state
  change
    (L = 4 * X + 2 ∧
      ((automaton P).evalFrom state
        (wordPow aWord count)).val = 0) ∨
    (1 ≤ ((automaton P).evalFrom state
        (wordPow aWord count)).val ∧
      ((automaton P).evalFrom state
        (wordPow aWord count)).val ≤ P.ell) ∨
    ((automaton P).evalFrom state
      (wordPow aWord count)).val = 2 * P.ell ∨
    ((automaton P).evalFrom state
      (wordPow aWord count)).val = 8 * X + 7 ∨
    ((automaton P).evalFrom state
      (wordPow aWord count)).val = 2 * L + 6 * X + 8 ∨
    ((automaton P).evalFrom state
      (wordPow aWord count)).val = middleZ X L at himage
  change state.val < P.ell ∨
    state.val = 2 * L - 2 * X + 1 ∨
    state.val = middleR X L ∨
    state.val = 4 * L - 4 * X + 2 ∨
    state.val = P.cycle
  have hcountPos : 0 < count := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [count]
    omega
  have hcountCycle : count < P.cycle := by
    rcases hmiddle with ⟨hlower, hupper⟩
    simp [P, count, residualParams, Params.cycle]
    omega
  rcases himage with hzero | hlow | htwoEll | heightX | hlast | hz
  · rcases hzero with ⟨hboundary, hzero⟩
    by_cases htail : state.val < P.ell
    · exact Or.inl htail
    · right
      right
      right
      right
      have hpreimage :=
        aPower_interval_preimage_zero P state count
          (by omega) hcountPos hcountCycle hzero
      rw [hpreimage]
      subst L
      simp [P, count, residualParams, Params.ell, Params.cycle]
      omega
  · by_cases htail : state.val < P.ell
    · exact Or.inl htail
    · have hstate : P.ell ≤ state.val := by omega
      obtain ⟨index, hindex⟩ :=
        exists_intervalState_eq P state hstate
      have hpower :
          (automaton P).evalFrom state (wordPow aWord count) =
            cycleState P ((cycleNext P)^[count] index) := by
        rw [← hindex]
        exact evalFrom_aPower_intervalState_of_pos P index count hcountPos
      rw [hpower] at hlow
      rcases cycleState_val_zero_or_above_ell P
        ((cycleNext P)^[count] index) with hzero | habove
      · omega
      · omega
  · by_cases htail : state.val < P.ell
    · exact Or.inl htail
    · right
      right
      left
      have hstate : P.ell ≤ state.val := by omega
      have htarget :
          2 * P.ell = P.ell + P.ell := by omega
      have hlocal :
          ((automaton P).evalFrom state
            (wordPow aWord count)).val = P.ell + P.ell := by
        rw [← htarget]
        exact htwoEll
      by_cases hlowSide : L ≤ 4 * X + 1
      · have hellCount : P.ell < count := by
          simp [P, count, residualParams, Params.ell]
          omega
        have hpreimage :=
          aPower_interval_preimage_of_target_lt_count P state
            count P.ell hstate hellCount hcountCycle P.ell_pos hlocal
        rw [hpreimage]
        have hell : P.ell = 2 * X + 2 := by
          simp [P, residualParams, Params.ell]
        have hcycle : P.cycle = 4 * L + 5 := by
          simp [P, residualParams, Params.cycle]
          omega
        rw [hell, hcycle]
        simp [count, middleR, hlowSide]
        omega
      · have hhighSide : 4 * X + 2 ≤ L := by omega
        have hcountEll : count ≤ P.ell := by
          simp [P, count, residualParams, Params.ell]
          omega
        have hpreimage :=
          aPower_interval_preimage_of_count_le_target P state
            count P.ell hstate hcountPos hcountEll
            (by
              rcases hmiddle with ⟨hlower, hupper⟩
              simp [P, residualParams, Params.ell, Params.cycle]
              omega) hlocal
        rw [hpreimage]
        simp [P, count, middleR, hlowSide, residualParams,
          Params.ell]
        omega
  · by_cases htail : state.val < P.ell
    · exact Or.inl htail
    · right
      left
      have hstate : P.ell ≤ state.val := by omega
      let target := 6 * X + 5
      have hglobal : 8 * X + 7 = P.ell + target := by
        simp [P, target, residualParams, Params.ell]
        omega
      have hlocal :
          ((automaton P).evalFrom state
            (wordPow aWord count)).val = P.ell + target := by
        rw [← hglobal]
        exact heightX
      have hcountTarget : count ≤ target := by
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [count, target]
        omega
      have htargetCycle : target < P.cycle := by
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [P, target, residualParams, Params.cycle]
        omega
      have hpreimage :=
        aPower_interval_preimage_of_count_le_target P state
          count target hstate hcountPos hcountTarget htargetCycle hlocal
      rw [hpreimage]
      simp [P, count, target, residualParams, Params.ell]
      omega
  · by_cases htail : state.val < P.ell
    · exact Or.inl htail
    · right
      right
      right
      left
      have hstate : P.ell ≤ state.val := by omega
      let target := 2 * L + 4 * X + 6
      have hglobal : 2 * L + 6 * X + 8 = P.ell + target := by
        simp [P, target, residualParams, Params.ell]
        omega
      have hlocal :
          ((automaton P).evalFrom state
            (wordPow aWord count)).val = P.ell + target := by
        rw [← hglobal]
        exact hlast
      have hcountTarget : count ≤ target := by
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [count, target]
        omega
      have htargetCycle : target < P.cycle := by
        rcases hmiddle with ⟨hlower, hupper⟩
        simp [P, target, residualParams, Params.cycle]
        omega
      have hpreimage :=
        aPower_interval_preimage_of_count_le_target P state
          count target hstate hcountPos hcountTarget htargetCycle hlocal
      rw [hpreimage]
      simp [P, count, target, residualParams, Params.ell]
      omega
  · by_cases htail : state.val < P.ell
    · exact Or.inl htail
    · right
      right
      right
      right
      have hstate : P.ell ≤ state.val := by omega
      by_cases hlowSide : L ≤ 4 * X + 2
      · by_cases hboundary : L = 4 * X + 2
        · subst L
          have hzEll : middleZ X (4 * X + 2) = P.ell := by
            simp [middleZ, P, residualParams, Params.ell]
            omega
          rw [hzEll] at hz
          obtain ⟨index, hindex⟩ :=
            exists_intervalState_eq P state hstate
          have hpower :
              (automaton P).evalFrom state (wordPow aWord count) =
                cycleState P ((cycleNext P)^[count] index) := by
            rw [← hindex]
            exact evalFrom_aPower_intervalState_of_pos P index count
              hcountPos
          rw [hpower] at hz
          rcases cycleState_val_zero_or_above_ell P
            ((cycleNext P)^[count] index) with hzero | habove
          · rw [hz] at hzero
            exact (Nat.ne_of_gt P.ell_pos hzero).elim
          · rw [hz] at habove
            exact (Nat.lt_irrefl _ habove).elim
        · have hstrict : L ≤ 4 * X + 1 := by omega
          let target := 8 * X + 4 - 2 * L
          have htargetPos : 0 < target := by
            simp [target]
            omega
          have htargetCount : target < count := by
            rcases hmiddle with ⟨hlower, hupper⟩
            simp [target, count]
            omega
          have hglobal :
              middleZ X L = P.ell + target := by
            simp [middleZ, hlowSide, P, target, residualParams,
              Params.ell]
            omega
          have hlocal :
              ((automaton P).evalFrom state
                (wordPow aWord count)).val = P.ell + target := by
            rw [← hglobal]
            exact hz
          have hpreimage :=
            aPower_interval_preimage_of_target_lt_count P state
              count target hstate htargetCount hcountCycle htargetPos hlocal
          rw [hpreimage]
          have hell : P.ell = 2 * X + 2 := by
            simp [P, residualParams, Params.ell]
          have hcycle : P.cycle = 4 * L + 5 := by
            simp [P, residualParams, Params.cycle]
            omega
          rw [hell, hcycle]
          simp [count, target]
          omega
      · have hhighSide : 4 * X + 3 ≤ L := by omega
        let target := 2 * L + 8 * X + 9
        have hglobal : middleZ X L = P.ell + target := by
          simp [middleZ, hlowSide, P, target, residualParams,
            Params.ell]
          omega
        have hlocal :
            ((automaton P).evalFrom state
              (wordPow aWord count)).val = P.ell + target := by
          rw [← hglobal]
          exact hz
        have hcountTarget : count ≤ target := by
          simp [count, target]
          omega
        have htargetCycle : target < P.cycle := by
          rcases hmiddle with ⟨hlower, hupper⟩
          simp [P, target, residualParams, Params.cycle]
          omega
        have hpreimage :=
          aPower_interval_preimage_of_count_le_target P state
            count target hstate hcountPos hcountTarget htargetCycle hlocal
        rw [hpreimage]
        simp [P, count, target, residualParams, Params.ell,
          Params.cycle]
        omega

/-- Thirteenth factor-table row, with its exact boundary collision. -/
theorem imageAvoids_middle_thirteenth_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell) ++ pSquared ++
        wordPow aWord (2 * L - 4 * X - 1) ++ [.p] ++
        wordPow aWord (4 * L - 6 * X) ++ [.p] ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (10 * X + 6 - 2 * L))
      (fun coordinate =>
        (L = 4 * X + 2 ∧ coordinate = 0) ∨
        (1 ≤ coordinate ∧
          coordinate ≤ (residualParams X L).ell) ∨
        coordinate = 2 * (residualParams X L).ell ∨
        coordinate = 8 * X + 7 ∨
        coordinate = 2 * L + 6 * X + 8 ∨
        coordinate = middleZ X L) := by
  apply imageAvoids_append (imageAvoids_middle_twelfth_row hmiddle)
  intro state hnew
  exact aFinal_preimage_thirteenth_hole hmiddle state hnew

/-- Inverse-image calculation for the final `p²`. -/
theorem pSquared_preimage_middleFinalHole {X L : ℕ}
    (hmiddle : Middle X L)
    (state : State (residualParams X L))
    (himage :
      MiddleFinalHole X L
        ((automaton (residualParams X L)).evalFrom state pSquared).val) :
    (L = 4 * X + 2 ∧ state.val = 0) ∨
    (1 ≤ state.val ∧
      state.val ≤ (residualParams X L).ell) ∨
    state.val = 2 * (residualParams X L).ell ∨
    state.val = 8 * X + 7 ∨
    state.val = 2 * L + 6 * X + 8 ∨
    state.val = middleZ X L := by
  let P := residualParams X L
  change State P at state
  change
    ((automaton P).evalFrom state pSquared).val = 0 ∨
    (2 ≤ ((automaton P).evalFrom state pSquared).val ∧
      ((automaton P).evalFrom state pSquared).val < P.ell) ∨
    IsMiddleForbidden X L
      ((automaton P).evalFrom state pSquared).val at himage
  change (L = 4 * X + 2 ∧ state.val = 0) ∨
    (1 ≤ state.val ∧ state.val ≤ P.ell) ∨
    state.val = 2 * P.ell ∨ state.val = 8 * X + 7 ∨
    state.val = 2 * L + 6 * X + 8 ∨
    state.val = middleZ X L
  rcases himage with hzero | hlow |
      hrho | htwoEll | hlast | heightX | hz
  · have hpre :=
      pSquared_preimage_sixth_hole hmiddle state (Or.inl hzero)
    rcases hpre with hpre | hpre
    · exact Or.inr (Or.inl hpre)
    · exact Or.inr (Or.inr (Or.inl hpre))
  · have hpre :=
      pSquared_preimage_sixth_hole hmiddle state
        (Or.inr (Or.inl hlow))
    rcases hpre with hpre | hpre
    · exact Or.inr (Or.inl hpre)
    · exact Or.inr (Or.inr (Or.inl hpre))
  · have hpre :=
      pSquared_preimage_sixth_hole hmiddle state
        (Or.inr (Or.inr (Or.inr hrho)))
    rcases hpre with hpre | hpre
    · exact Or.inr (Or.inl hpre)
    · exact Or.inr (Or.inr (Or.inl hpre))
  · have hpre :=
      pSquared_preimage_sixth_hole hmiddle state
        (Or.inr (Or.inr (Or.inl htwoEll)))
    rcases hpre with hpre | hpre
    · exact Or.inr (Or.inl hpre)
    · exact Or.inr (Or.inr (Or.inl hpre))
  · have htargetZero : 2 * L + 6 * X + 8 ≠ 0 := by omega
    have htargetEll : 2 * L + 6 * X + 8 ≠ P.ell := by
      rcases hmiddle with ⟨hlower, hupper⟩
      simp [P, residualParams, Params.ell]
      omega
    have htargetOne : 2 * L + 6 * X + 8 ≠ 1 := by omega
    have htargetRho : 2 * L + 6 * X + 8 ≠ P.rho := by
      simp [P, residualParams, Params.rho, Params.m]
      omega
    have hpre :=
      pSquared_preimage_regular P state (2 * L + 6 * X + 8)
        htargetZero htargetEll htargetOne htargetRho hlast
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpre))))
  · have htargetZero : 8 * X + 7 ≠ 0 := by omega
    have htargetEll : 8 * X + 7 ≠ P.ell := by
      simp [P, residualParams, Params.ell]
      omega
    have htargetOne : 8 * X + 7 ≠ 1 := by omega
    have htargetRho : 8 * X + 7 ≠ P.rho := by
      rcases hmiddle with ⟨hlower, hupper⟩
      simp [P, residualParams, Params.rho, Params.m]
      omega
    have hpre :=
      pSquared_preimage_regular P state (8 * X + 7)
        htargetZero htargetEll htargetOne htargetRho heightX
    exact Or.inr (Or.inr (Or.inr (Or.inl hpre)))
  · by_cases hboundary : L = 4 * X + 2
    · left
      refine ⟨hboundary, ?_⟩
      have hzEll : middleZ X L = P.ell := by
        subst L
        simp [middleZ, P, residualParams, Params.ell]
        omega
      rw [hzEll] at hz
      exact pSquared_preimage_ell P state hz
    · right
      right
      right
      right
      right
      have htargetZero : middleZ X L ≠ 0 := by
        by_cases hlowSide : L ≤ 4 * X + 2
        · have hstrict : L ≤ 4 * X + 1 := by omega
          simp [middleZ, hlowSide]
          omega
        · simp [middleZ, hlowSide]
      have htargetEll : middleZ X L ≠ P.ell := by
        by_cases hlowSide : L ≤ 4 * X + 2
        · have hstrict : L ≤ 4 * X + 1 := by omega
          rcases hmiddle with ⟨hlower, hupper⟩
          simp [middleZ, hlowSide, P, residualParams, Params.ell]
          omega
        · rcases hmiddle with ⟨hlower, hupper⟩
          simp [middleZ, hlowSide, P, residualParams, Params.ell]
          omega
      have htargetOne : middleZ X L ≠ 1 := by
        by_cases hlowSide : L ≤ 4 * X + 2
        · have hstrict : L ≤ 4 * X + 1 := by omega
          simp [middleZ, hlowSide]
          omega
        · simp [middleZ, hlowSide]
      have htargetRho : middleZ X L ≠ P.rho := by
        by_cases hlowSide : L ≤ 4 * X + 2
        · have hstrict : L ≤ 4 * X + 1 := by omega
          rcases hmiddle with ⟨hlower, hupper⟩
          simp [middleZ, hlowSide, P, residualParams,
            Params.rho, Params.m]
          omega
        · simp [middleZ, hlowSide, P, residualParams,
            Params.rho, Params.m]
          omega
      exact pSquared_preimage_regular P state (middleZ X L)
        htargetZero htargetEll htargetOne htargetRho hz

/-- The full last row of the middle-prefix complement table. -/
theorem imageAvoids_middle_fourteenth_row {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L)
      (aWord ++ pSquared ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (2 * (residualParams X L).ell) ++ pSquared ++
        wordPow aWord (2 * L - 4 * X - 1) ++ [.p] ++
        wordPow aWord (4 * L - 6 * X) ++ [.p] ++
        wordPow aWord ((residualParams X L).ell - 1) ++ [.s] ++
        wordPow aWord (10 * X + 6 - 2 * L) ++ pSquared)
      (MiddleFinalHole X L) := by
  apply imageAvoids_append (imageAvoids_middle_thirteenth_row hmiddle)
  intro state hnew
  exact pSquared_preimage_middleFinalHole hmiddle state hnew

/-- Parameter-uniform last-row identity for the displayed middle prefix. -/
theorem middlePrefix_image_avoids_finalHole {X L : ℕ}
    (hmiddle : Middle X L) :
    ImageAvoids (residualParams X L) (middlePrefix X L)
      (MiddleFinalHole X L) := by
  simpa [middlePrefix] using imageAvoids_middle_fourteenth_row hmiddle

/-- The middle-band prefix deletes the five deepest cut-rotation points. -/
theorem middlePrefix_avoidsDeep {X L : ℕ}
    (hmiddle : Middle X L) :
    PrefixAvoidsDeep (residualParams X L) (middlePrefix X L) 5 :=
  prefixAvoidsDeep_of_middleFinalHole hmiddle
    (middlePrefix_image_avoids_finalHole hmiddle)

/-- The complete uniform middle-band Černý theorem. -/
theorem middle_satisfiesCerny {X L : ℕ}
    (hcoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle)
    (hmiddle : Middle X L) :
    (automaton (residualParams X L)).SatisfiesCerny :=
  middle_satisfiesCerny_of_prefix_image hcoprime hmiddle
    (middlePrefix_avoidsDeep hmiddle)

end DFA.CycleTree
