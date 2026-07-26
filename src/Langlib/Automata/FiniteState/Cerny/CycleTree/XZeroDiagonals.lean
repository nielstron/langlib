module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.GeneralDirectCut
public import Langlib.Automata.FiniteState.Cerny.CycleTree.XZeroCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose]
public section

/-!
# Auxiliary `F/E/G` coordinates on `X = 0`

This module records reusable definitions and initial action lemmas for the
older `F/E/G` cone construction.  The final theorem does not depend on
this auxiliary route: `XZeroFace` closes the two diagonals with shorter
cut words.
-/

namespace DFA.CycleTree

def xzeroConeParams (R L : ℕ) : Params :=
  ⟨0, R, L⟩

def xzeroSmallCycle (R : ℕ) : ℕ := R + 1

theorem xzeroSmallCycle_pos (R : ℕ) :
    0 < xzeroSmallCycle R := by
  simp [xzeroSmallCycle]

/-- Embed a local index of the small cycle as the odd local coordinate
`2i+1` of the hidden `A`-cycle. -/
def xzeroHIndex (R L : ℕ)
    (index : Fin (xzeroSmallCycle R)) :
    Fin (xzeroConeParams R L).cycle :=
  ⟨2 * index.val + 1, by
    simp [xzeroConeParams, xzeroSmallCycle, Params.cycle]
    omega⟩

/-- The small-cycle state `hᵢ = 2i+3`. -/
def xzeroHState (R L : ℕ)
    (index : Fin (xzeroSmallCycle R)) :
    State (xzeroConeParams R L) :=
  intervalState (xzeroConeParams R L)
    (xzeroHIndex R L index)

@[simp]
theorem xzeroHState_val (R L : ℕ)
    (index : Fin (xzeroSmallCycle R)) :
    (xzeroHState R L index).val = 2 * index.val + 3 := by
  simp [xzeroHState, xzeroHIndex, xzeroConeParams, Params.ell]
  omega

theorem xzeroHState_injective (R L : ℕ) :
    Function.Injective (xzeroHState R L) := by
  intro left right heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simp only [xzeroHState_val] at hval
  omega

/-- Rotation on the `R+1` small-cycle indices. -/
def xzeroHNext (R : ℕ)
    (index : Fin (xzeroSmallCycle R)) :
    Fin (xzeroSmallCycle R) :=
  ⟨(index.val + 1) % (xzeroSmallCycle R),
    Nat.mod_lt _ (xzeroSmallCycle_pos R)⟩

def xzeroHPrev (R : ℕ)
    (index : Fin (xzeroSmallCycle R)) :
    Fin (xzeroSmallCycle R) :=
  if hzero : index.val = 0
  then ⟨R, by simp [xzeroSmallCycle]⟩
  else ⟨index.val - 1, by
    simp [xzeroSmallCycle]
    omega⟩

theorem xzeroHPrev_next (R : ℕ)
    (index : Fin (xzeroSmallCycle R)) :
    xzeroHPrev R (xzeroHNext R index) = index := by
  apply Fin.ext
  by_cases hlast : index.val = R
  · have hindex : index.val + 1 = R + 1 := by omega
    have hmod :
        (index.val + 1) % xzeroSmallCycle R = 0 := by
      rw [hindex]
      simp [xzeroSmallCycle]
    simp [xzeroHPrev, xzeroHNext, xzeroSmallCycle, hlast]
  · have hlt : index.val + 1 < xzeroSmallCycle R := by
      simp [xzeroSmallCycle]
      omega
    simp [xzeroHPrev, xzeroHNext,
      Nat.mod_eq_of_lt hlt]

theorem xzeroHNext_prev (R : ℕ)
    (index : Fin (xzeroSmallCycle R)) :
    xzeroHNext R (xzeroHPrev R index) = index := by
  apply Fin.ext
  by_cases hzero : index.val = 0
  · simp [xzeroHPrev, xzeroHNext, hzero,
      xzeroSmallCycle]
  · have hlt : index.val - 1 + 1 < xzeroSmallCycle R := by
      simp [xzeroSmallCycle]
      omega
    simp [xzeroHPrev, xzeroHNext, hzero,
      Nat.mod_eq_of_lt hlt]
    omega

theorem xzeroHNext_injective (R : ℕ) :
    Function.Injective (xzeroHNext R) :=
  (show Function.LeftInverse (xzeroHPrev R) (xzeroHNext R) from
    xzeroHPrev_next R).injective

theorem xzeroHPrev_injective (R : ℕ) :
    Function.Injective (xzeroHPrev R) :=
  (show Function.LeftInverse (xzeroHNext R) (xzeroHPrev R) from
    xzeroHNext_prev R).injective

def xzeroFWord : List Letter :=
  pSquared ++ wordPow aWord 2

def xzeroJWord : List Letter :=
  [.p] ++ aWord ++ [.p] ++ aWord ++ pSquared

def xzeroEWord (_R L : ℕ) : List Letter :=
  wordPow aWord 2 ++ wordPow xzeroFWord L ++
    xzeroJWord ++
    wordPow aWord 2 ++ wordPow xzeroFWord L

def xzeroGWord : List Letter :=
  [.p, .s, .p, .p, .p, .s, .p, .p]

def xzeroConeCompression (R L : ℕ) : List Letter :=
  wordPow aWord 2 ++
    wordPow xzeroFWord (R + 2 * L + 2)

def xzeroConeGamma (R L : ℕ) : ℕ :=
  (2 * L + 2) % (R + 1)

def xzeroConeWord (R L : ℕ) : List Letter :=
  xzeroConeCompression R L ++ xzeroEWord R L ++
    wordPow (xzeroGWord ++ xzeroEWord R L) (R - 1) ++
    wordPow xzeroGWord (xzeroConeGamma R L)

@[simp]
theorem length_xzeroFWord : xzeroFWord.length = 6 := by
  simp [xzeroFWord]

@[simp]
theorem length_xzeroJWord : xzeroJWord.length = 8 := by
  simp [xzeroJWord]

@[simp]
theorem length_xzeroEWord (R L : ℕ) :
    (xzeroEWord R L).length = 12 * L + 16 := by
  simp [xzeroEWord]
  omega

@[simp]
theorem length_xzeroGWord : xzeroGWord.length = 8 := by
  decide

@[simp]
theorem length_xzeroConeCompression (R L : ℕ) :
    (xzeroConeCompression R L).length =
      6 * R + 12 * L + 16 := by
  simp [xzeroConeCompression]
  omega

theorem length_xzeroConeWord {R L : ℕ} (hR : 1 ≤ R) :
    (xzeroConeWord R L).length =
      12 * R * L + 30 * R + 12 * L +
        8 * xzeroConeGamma R L + 8 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hR
  simp [xzeroConeWord]
  ring

theorem xzeroConeGamma_upper {L : ℕ} (hL : 1 ≤ L) :
    xzeroConeGamma (L + 2) L = L - 1 := by
  have hsum :
      2 * L + 2 = (L + 3) + (L - 1) := by
    omega
  have hremainder : L - 1 < L + 3 := by omega
  rw [xzeroConeGamma, hsum, Nat.add_mod]
  simp [Nat.mod_eq_of_lt hremainder]

theorem length_xzeroConeWord_upper {L : ℕ} (hL : 1 ≤ L) :
    (xzeroConeWord (L + 2) L).length =
      12 * L ^ 2 + 74 * L + 60 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hL
  rw [length_xzeroConeWord (by omega),
    xzeroConeGamma_upper (by omega)]
  simp
  ring

/-- The index action of `F` on the hidden `A`-cycle. -/
def xzeroFIndex (R L : ℕ)
    (index : Fin (xzeroConeParams R L).cycle) :
    Fin (xzeroConeParams R L).cycle :=
  if index = rhoIndex (xzeroConeParams R L)
  then xzeroHIndex R L ⟨0, xzeroSmallCycle_pos R⟩
  else (cycleNext (xzeroConeParams R L))^[2] index

theorem evalFrom_xzeroFWord_cycleState (R L : ℕ)
    (index : Fin (xzeroConeParams R L).cycle) :
    (automaton (xzeroConeParams R L)).evalFrom
        (cycleState (xzeroConeParams R L) index)
        xzeroFWord =
      cycleState (xzeroConeParams R L)
        (xzeroFIndex R L index) := by
  let P := xzeroConeParams R L
  rw [xzeroFWord, (automaton P).evalFrom_of_append,
    evalFrom_pSquared_cycleState]
  by_cases hindex : index = rhoIndex P
  · rw [if_pos hindex]
    have honeLt : 1 < P.order := by
      simp [P, xzeroConeParams, Params.order,
        Params.ell, Params.cycle]
      omega
    have honeVal : (P.stateOfNat 1).val = 1 :=
      stateOfNat_val_of_lt P honeLt
    have hbefore : (P.stateOfNat 1).val + 2 < P.order := by
      rw [honeVal]
      simp [P, xzeroConeParams, Params.order,
        Params.ell, Params.cycle]
      omega
    rw [evalFrom_aPower_before_wrap P (P.stateOfNat 1) 2
      (by rw [honeVal]; omega) hbefore]
    unfold xzeroFIndex
    rw [if_pos hindex]
    rw [honeVal]
    have hzero :
        (⟨0, xzeroSmallCycle_pos R⟩ :
          Fin (xzeroSmallCycle R)).val = 0 := rfl
    have hnonzero :
        (xzeroHIndex R L
          (⟨0, xzeroSmallCycle_pos R⟩ :
            Fin (xzeroSmallCycle R))).val ≠ 0 := by
      change 2 * 0 + 1 ≠ 0
      omega
    rw [cycleState_of_ne_zero _ _ hnonzero]
    congr 1
  · rw [if_neg hindex,
      evalFrom_aPower_intervalState_of_pos P index 2 (by omega)]
    unfold xzeroFIndex
    rw [if_neg hindex]

end DFA.CycleTree
