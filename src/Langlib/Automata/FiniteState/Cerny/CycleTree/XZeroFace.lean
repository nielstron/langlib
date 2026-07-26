module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.GeneralDirectCut
public import Langlib.Automata.FiniteState.Cerny.CycleTree.ShortenedCut
public import Langlib.Automata.FiniteState.Cerny.CycleTree.MiddlePrefix
public import Langlib.Automata.FiniteState.Cerny.CycleTree.LargePrefix
import Mathlib.Tactic.Linarith

@[expose]
public section

/-!
# The face `X = 0`

This module assembles the generic cut constructions on the complete
two-parameter face `Params.mk 0 R L` and formalizes the remaining
small-cycle construction.
-/

namespace DFA.CycleTree

open Params

private theorem xzero_directDomain (R L : ℕ) :
    (Params.mk 0 R L).DirectDomain := by
  simp [Params.DirectDomain]

/-- On `X=0`, the direct prefix always deletes the unique deepest
point of the direct rotation. -/
theorem xzero_directPrefix_avoidsDeepest (R L : ℕ) :
    DirectPrefixAvoidsDeepest ⟨0, R, L⟩ :=
  directPrefix_avoidsDeepest_of_domain ⟨0, R, L⟩
    (xzero_directDomain R L)

/-- The complementary direct cut is a complete Černý construction on
its cost-safe part of the `X=0` face. -/
theorem xzero_satisfiesCerny_of_directSafe {R L : ℕ}
    (hsynchronizing : (automaton ⟨0, R, L⟩).Synchronizing)
    (hsafe : DirectSafe ⟨0, R, L⟩) :
    (automaton ⟨0, R, L⟩).SatisfiesCerny := by
  apply satisfiesCerny_of_generalDirectCut
    ⟨0, R, L⟩
  · exact coprime_of_synchronizing ⟨0, R, L⟩ hsynchronizing
  · exact xzero_directDomain R L
  · exact hsafe

/-- The shortened cut covers the upper half-plane `R < L`. -/
theorem xzero_satisfiesCerny_of_R_lt_L {R L : ℕ}
    (hsynchronizing : (automaton ⟨0, R, L⟩).Synchronizing)
    (hRL : R < L) :
    (automaton ⟨0, R, L⟩).SatisfiesCerny := by
  apply satisfiesCerny_of_synchronizing_of_shortenedCutSafe
    ⟨0, R, L⟩ hsynchronizing
  simp only [ShortenedCutSafe]
  nlinarith

/-- The direct cut covers the lower cone `L + 3 ≤ R`. -/
theorem xzero_satisfiesCerny_of_L_add_three_le_R {R L : ℕ}
    (hsynchronizing : (automaton ⟨0, R, L⟩).Synchronizing)
    (hLR : L + 3 ≤ R) :
    (automaton ⟨0, R, L⟩).SatisfiesCerny := by
  apply xzero_satisfiesCerny_of_directSafe hsynchronizing
  simp only [DirectSafe]
  nlinarith

/-- Existing generic words reduce the unfinished `X=0` face exactly to
the three adjacent diagonals `R=L,L+1,L+2`. -/
theorem xzero_satisfiesCerny_or_three_diagonals (R L : ℕ)
    (hsynchronizing : (automaton ⟨0, R, L⟩).Synchronizing) :
    (automaton ⟨0, R, L⟩).SatisfiesCerny ∨
      R = L ∨ R = L + 1 ∨ R = L + 2 := by
  by_cases hRL : R < L
  · exact Or.inl
      (xzero_satisfiesCerny_of_R_lt_L hsynchronizing hRL)
  by_cases hLR : L + 3 ≤ R
  · exact Or.inl
      (xzero_satisfiesCerny_of_L_add_three_le_R
        hsynchronizing hLR)
  right
  omega

/-!
## The balanced diagonal

The usual one-depth prefix `A²p²` is two letters too long when `R=L`.
On `X=0`, the shorter lead `Ap²` has one exceptional image at global
zero.  One additional `D` block absorbs that exception while preserving
two deleted points of the cut path.  Thus `Ap²D · D^(cycle-2)` has exactly
the Černý-bound length on the balanced diagonal.
-/

def xzeroLeadWord : List Letter :=
  aWord ++ pSquared

private theorem evalFrom_aWord_ne_one_xzero
    (R L : ℕ) (state : State ⟨0, R, L⟩) :
    ((automaton ⟨0, R, L⟩).evalFrom state aWord).val ≠ 1 := by
  let P : Params := ⟨0, R, L⟩
  change ((automaton P).evalFrom state aWord).val ≠ 1
  dsimp only [P]
  rw [evalFrom_aWord]
  by_cases hzero : state.val = 0
  · rw [if_pos hzero]
    have hellPlusOne :
        (Params.mk 0 R L).ell + 1 = 3 := by
      simp [Params.ell]
    rw [hellPlusOne]
    have hthree : 3 < (Params.mk 0 R L).order := by
      simp [Params.order, Params.ell, Params.cycle]
      omega
    rw [stateOfNat_val_of_lt _ hthree]
    omega
  · rw [if_neg hzero, stateOfNat_val]
    have hstatePos : 0 < state.val := Nat.pos_of_ne_zero hzero
    have hsumLe :
        state.val + 1 ≤ (Params.mk 0 R L).order :=
      Nat.succ_le_iff.mpr state.isLt
    by_cases hsumLt :
        state.val + 1 < (Params.mk 0 R L).order
    · rw [Nat.mod_eq_of_lt hsumLt]
      omega
    · have hsum :
          state.val + 1 = (Params.mk 0 R L).order := by
        omega
      rw [hsum]
      simp

private theorem xzeroLeadWord_range
    (R L : ℕ) (state : State ⟨0, R, L⟩) :
    let P : Params := ⟨0, R, L⟩
    (automaton P).evalFrom state xzeroLeadWord =
        P.stateOfNat 0 ∨
    (automaton P).evalFrom state xzeroLeadWord =
        P.stateOfNat 1 ∨
    ∃ index : Fin P.cycle,
      index ≠ rhoIndex P ∧
      (automaton P).evalFrom state xzeroLeadWord =
        intervalState P index := by
  dsimp only
  let P : Params := ⟨0, R, L⟩
  let middle := (automaton P).evalFrom state aWord
  have hmiddleOne : middle.val ≠ 1 :=
    evalFrom_aWord_ne_one_xzero R L state
  have hell : P.ell = 2 := by
    simp [P, Params.ell]
  rw [xzeroLeadWord, (automaton P).evalFrom_of_append,
    evalFrom_pSquared]
  by_cases hzero : middle.val = 0
  · rw [if_pos hzero]
    right
    right
    let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
    refine ⟨zeroIndex, ?_, ?_⟩
    · intro heq
      have heqVal := congrArg Fin.val heq
      simp [zeroIndex, rhoIndex] at heqVal
    · unfold intervalState
      simp [P, zeroIndex]
  rw [if_neg hzero]
  by_cases hmiddleEll : middle.val = P.ell
  · rw [if_pos hmiddleEll]
    exact Or.inl rfl
  rw [if_neg hmiddleEll, if_neg hmiddleOne]
  by_cases hmiddleRho : middle.val = P.rho
  · rw [if_pos hmiddleRho]
    exact Or.inr (Or.inl rfl)
  rw [if_neg hmiddleRho]
  right
  right
  have hmiddleInterval : P.ell ≤ middle.val := by
    rw [hell]
    omega
  obtain ⟨index, hindex⟩ :=
    exists_intervalState_eq P middle hmiddleInterval
  refine ⟨index, ?_, hindex.symm⟩
  intro hindexRho
  subst index
  rw [intervalState_rhoIndex] at hindex
  have hval := congrArg Fin.val hindex
  rw [stateOfNat_val_of_lt P P.rho_lt_order] at hval
  exact hmiddleRho hval.symm

def xzeroBalancedPrefix (P : Params) : List Letter :=
  xzeroLeadWord ++ dWord P

private theorem dIndex_zero_ne_rho_xzero (R L : ℕ) :
    let P : Params := ⟨0, R, L⟩
    dIndex P ⟨0, P.cycle_pos⟩ ≠ rhoIndex P := by
  dsimp only
  let P : Params := ⟨0, R, L⟩
  intro heq
  have heqVal := congrArg Fin.val heq
  rw [dIndex_eq_advance] at heqVal
  change
    (0 + 2 * P.m) % P.cycle = 2 * P.R + 1 at heqVal
  have hstep : 2 * P.m < P.cycle := by
    simp [P, Params.m, Params.cycle]
    omega
  rw [Nat.mod_eq_of_lt (by simpa using hstep)] at heqVal
  simp [P, Params.m] at heqVal
  omega

private theorem not_deep_two_of_ne_rho_of_ne_dIndex_rho
    (P : Params) (index : Fin P.cycle)
    (hrho : index ≠ rhoIndex P)
    (hdIndex : index ≠ dIndex P (rhoIndex P)) :
    ¬IsDeepIndex P 2 index := by
  rintro ⟨offset, hoffset, heq⟩
  have hoffsetCases : offset = 0 ∨ offset = 1 := by
    omega
  rcases hoffsetCases with rfl | rfl
  · simp only [Function.iterate_zero_apply] at heq
    exact hrho heq
  · simpa only [Function.iterate_one] using hdIndex heq

/-- The shortened two-depth prefix used on `X=0`: `Ap²D`. -/
theorem xzeroBalancedPrefix_avoidsDeep (R L : ℕ) :
    PrefixAvoidsDeep ⟨0, R, L⟩
      (xzeroBalancedPrefix ⟨0, R, L⟩) 2 := by
  let P : Params := ⟨0, R, L⟩
  intro state
  rw [xzeroBalancedPrefix, (automaton P).evalFrom_of_append]
  rcases xzeroLeadWord_range R L state with
    hzero | hsink | ⟨index, hindexRho, hindex⟩
  · let zeroIndex : Fin P.cycle := ⟨0, P.cycle_pos⟩
    let imageIndex := dIndex P zeroIndex
    have himage :
        (automaton P).evalFrom (P.stateOfNat 0)
            (wordPow aWord (2 * P.m)) =
          cycleState P imageIndex := by
      rw [← cycleState_zero P,
        evalFrom_aPower_cycleState]
      rfl
    have himageRho : imageIndex ≠ rhoIndex P :=
      dIndex_zero_ne_rho_xzero R L
    right
    refine ⟨imageIndex, ?_, ?_⟩
    · apply not_deep_two_of_ne_rho_of_ne_dIndex_rho
        P imageIndex himageRho
      intro heq
      have hzeroEq :
          zeroIndex = rhoIndex P :=
        ((cycleNext_injective P).iterate (2 * P.m)) heq
      have hzeroVal := congrArg Fin.val hzeroEq
      simp [zeroIndex, rhoIndex] at hzeroVal
    · rw [hzero, evalFrom_dWord_of_aPower_cycleState
        P (P.stateOfNat 0) imageIndex himage,
        if_neg himageRho]
  · left
    rw [hsink, evalFrom_dWord_one]
  · rw [hindex, evalFrom_dWord_intervalState]
    by_cases hcut : dIndex P index = rhoIndex P
    · left
      rw [if_pos hcut]
    · right
      refine ⟨dIndex P index, ?_, by rw [if_neg hcut]⟩
      apply not_deep_two_of_ne_rho_of_ne_dIndex_rho
        P (dIndex P index) hcut
      intro heq
      exact hindexRho
        (((cycleNext_injective P).iterate (2 * P.m)) heq)

@[simp]
private theorem length_xzeroBalancedPrefix (P : Params) :
    (xzeroBalancedPrefix P).length = 4 * P.m + 6 := by
  simp [xzeroBalancedPrefix, xzeroLeadWord]
  omega

/-- Every balanced automaton `(X,R,L)=(0,L,L)` satisfies the Černý
bound.  The displayed two-depth word meets the bound exactly. -/
theorem xzero_balanced_satisfiesCerny (L : ℕ)
    (hsynchronizing :
      (automaton ⟨0, L, L⟩).Synchronizing) :
    (automaton ⟨0, L, L⟩).SatisfiesCerny := by
  let P : Params := ⟨0, L, L⟩
  apply satisfiesCerny_of_prefix_avoidsDeep P
    (coprime_of_synchronizing P hsynchronizing)
    (xzeroBalancedPrefix P) 2
  · omega
  · simp [P, Params.cycle]
  · exact xzeroBalancedPrefix_avoidsDeep L L
  · dsimp only [P]
    simp only [length_xzeroBalancedPrefix, Params.m,
      Params.cycle, Params.order, Params.ell]
    have horder :
        2 * 0 + 2 + (2 * L + 2 * L + 3) - 1 =
          4 * L + 4 := by
      omega
    have hcycle :
        2 * L + 2 * L + 3 - 2 = 4 * L + 1 := by
      omega
    rw [horder, hcycle]
    nlinarith

/-!
## The upper neighboring diagonal

On `X=0`, the direct block `B=A^(2L+3)C²` is already a valid
one-point-deleting prefix: its initial `A`-power has put every state on
the hidden cycle.  This saves six letters relative to the general direct
prefix and covers the line `R=L+2`.
-/

/-- Pointwise prefix obligation for using one direct block itself as the
prefix of the direct cut. -/
def DirectBlockPrefixAvoidsDeepest (P : Params) : Prop :=
  ∀ state : State P, ∃ index : Fin P.cycle,
    index ≠ directRotation P P.directAlpha ∧
    (automaton P).evalFrom state (directBlockWord P) =
      intervalState P index

/-- On the whole face `X=0`, one direct block maps into the invariant
interval and omits the deepest point of the direct-block cut path. -/
theorem xzero_directBlockPrefix_avoidsDeepest (R L : ℕ) :
    DirectBlockPrefixAvoidsDeepest ⟨0, R, L⟩ := by
  let P : Params := ⟨0, R, L⟩
  intro state
  have hexponent : P.ell ≤ P.directExponent := by
    simp [P, Params.ell, Params.directExponent]
  obtain ⟨index, hindex⟩ :=
    exists_cycleState_aPower_of_ell_le P state
      P.directExponent hexponent
  rw [directBlockWord, (automaton P).evalFrom_of_append,
    hindex]
  by_cases hzero : index.val = 0
  · have hindexZero :
        index = ⟨0, P.cycle_pos⟩ := Fin.ext hzero
    refine ⟨P.directAlpha,
      directAlpha_ne_directRotation_alpha_of_domain P
        (xzero_directDomain R L), ?_⟩
    rw [hindexZero, cycleState_zero,
      evalFrom_cPower_ell_zero]
  · let finalIndex := (cyclePrev P)^[P.ell] index
    refine ⟨finalIndex, ?_, ?_⟩
    · rw [directRotation_alpha_eq_iterate_cyclePrev_zero]
      intro heq
      have hindexZero :
          index = cycleZeroIndex P :=
        ((cyclePrev_injective P).iterate P.ell) heq
      apply hzero
      have hval := congrArg Fin.val hindexZero
      simpa [cycleZeroIndex] using hval
    · rw [cycleState_of_ne_zero P index hzero,
        ← intervalState,
        evalFrom_cPower_intervalState]

/-- The shortened direct-block cut `B · B^(cycle-2)`. -/
def xzeroDirectBlockCutWord (P : Params) : List Letter :=
  directBlockWord P ++
    wordPow (directBlockWord P) (P.cycle - 2)

@[simp]
theorem length_xzeroDirectBlockCutWord (P : Params) :
    (xzeroDirectBlockCutWord P).length =
      2 * (P.directExponent + P.ell) +
        (P.cycle - 2) * (2 * (P.directExponent + P.ell)) := by
  simp [xzeroDirectBlockCutWord]

/-- Coprimality collapses the shortened direct-block cut on `X=0`. -/
theorem xzeroDirectBlockCut_isResetWord (R L : ℕ)
    (hcoprime :
      Nat.Coprime (Params.mk 0 R L).m
        (Params.mk 0 R L).cycle) :
    (automaton ⟨0, R, L⟩).IsResetWord
      (xzeroDirectBlockCutWord ⟨0, R, L⟩) := by
  let P : Params := ⟨0, R, L⟩
  refine ⟨intervalState P P.directAlpha, ?_⟩
  intro state
  obtain ⟨index, hdeleted, hprefixImage⟩ :=
    xzero_directBlockPrefix_avoidsDeepest R L state
  rw [xzeroDirectBlockCutWord,
    (automaton P).evalFrom_of_append,
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
    (directRotation_period P P.directAlpha)
    (directRotationIsCycle_of_coprime P hcoprime)
    hdeleted

/-- Every automaton on the neighboring diagonal
`(X,R,L)=(0,L+2,L)` satisfies the Černý bound. -/
theorem xzero_upperDiagonal_satisfiesCerny (L : ℕ)
    (hsynchronizing :
      (automaton ⟨0, L + 2, L⟩).Synchronizing) :
    (automaton ⟨0, L + 2, L⟩).SatisfiesCerny := by
  let P : Params := ⟨0, L + 2, L⟩
  apply DFA.satisfiesCerny_of_resetWord (automaton P)
    (xzeroDirectBlockCut_isResetWord (L + 2) L
      (coprime_of_synchronizing P hsynchronizing))
  simp only [length_xzeroDirectBlockCutWord, DFA.cernyBound,
    Fintype.card_fin]
  dsimp only [P]
  simp only [Params.directExponent, Params.ell, Params.cycle,
    Params.order]
  have hcycle :
      2 * (L + 2) + 2 * L + 3 - 2 = 4 * L + 5 := by
    omega
  have horder :
      2 * 0 + 2 + (2 * (L + 2) + 2 * L + 3) - 1 =
        4 * L + 8 := by
    omega
  rw [hcycle, horder]
  nlinarith

/-- The already-formalized large prefix covers the residual diagonal
`R=L+1` from `L=3` onward. -/
theorem xzero_residual_satisfiesCerny_of_three_le_L {L : ℕ}
    (hsynchronizing :
      (automaton (residualParams 0 L)).Synchronizing)
    (hL : 3 ≤ L) :
    (automaton (residualParams 0 L)).SatisfiesCerny := by
  have hcoprime :
      Nat.Coprime
        (residualParams 0 L).m
        (residualParams 0 L).cycle :=
    coprime_of_synchronizing (residualParams 0 L)
      hsynchronizing
  exact large_satisfiesCerny hcoprime (by
    simp only [Large]
    omega)

private def xzeroResidualWordZero : List Letter :=
  decodeWord "spppspspsppspspspsppspsspspppsps"

private def xzeroResidualWordTwo : List Letter :=
  decodeWord
    "spppspsppspspppspspppspspsppspspspspspspspsppspsspspppspspspspsppsppspspspspppspsppspspspspspspsppspsspspspppspspspsppsppspspspspspppsps"

private theorem xzeroResidualWordZero_isResetWord :
    (automaton (residualParams 0 0)).IsResetWord
      xzeroResidualWordZero := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

private theorem xzeroResidualWordTwo_isResetWord :
    (automaton (residualParams 0 2)).IsResetWord
      xzeroResidualWordTwo := by
  rw [isResetWord_iff_eq_start]
  decide +kernel

/-- Kernel-checked certificate for the first synchronizing residual point
`(X,R,L)=(0,1,0)`. -/
theorem safe_xzero_residual_l0 :
    (automaton (residualParams 0 0)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _
    xzeroResidualWordZero_isResetWord (by decide +kernel)

/-- Kernel-checked certificate for the second synchronizing residual point
`(X,R,L)=(0,3,2)`. -/
theorem safe_xzero_residual_l2 :
    (automaton (residualParams 0 2)).SatisfiesCerny :=
  satisfiesCerny_of_resetWord _
    xzeroResidualWordTwo_isResetWord (by decide +kernel)

/-- The residual diagonal `R=L+1` is completely covered on `X=0`.
The only small parameter not covered by a certificate is `L=1`, where
the synchronization coprimality criterion is impossible. -/
theorem xzero_residual_satisfiesCerny {L : ℕ}
    (hsynchronizing :
      (automaton (residualParams 0 L)).Synchronizing) :
    (automaton (residualParams 0 L)).SatisfiesCerny := by
  by_cases hlarge : 3 ≤ L
  · exact xzero_residual_satisfiesCerny_of_three_le_L
      hsynchronizing hlarge
  have hcases : L = 0 ∨ L = 1 ∨ L = 2 := by
    omega
  rcases hcases with rfl | rfl | rfl
  · exact safe_xzero_residual_l0
  · have hcoprime :
        Nat.Coprime
          (residualParams 0 1).m
          (residualParams 0 1).cycle :=
      coprime_of_synchronizing (residualParams 0 1)
        hsynchronizing
    have hnot :
        ¬ Nat.Coprime
          (residualParams 0 1).m
          (residualParams 0 1).cycle := by
      decide
    exact (hnot hcoprime).elim
  · exact safe_xzero_residual_l2

/-- Combining the two generic cut regions with the complete residual
diagonal leaves exactly the two neighboring diagonals `R=L` and
`R=L+2`. -/
theorem xzero_satisfiesCerny_or_two_diagonals (R L : ℕ)
    (hsynchronizing : (automaton ⟨0, R, L⟩).Synchronizing) :
    (automaton ⟨0, R, L⟩).SatisfiesCerny ∨
      R = L ∨ R = L + 2 := by
  rcases xzero_satisfiesCerny_or_three_diagonals
      R L hsynchronizing with
    hsafe | hbalanced | hresidual | hupper
  · exact Or.inl hsafe
  · exact Or.inr (Or.inl hbalanced)
  · left
    subst R
    simpa [residualParams] using
      xzero_residual_satisfiesCerny hsynchronizing
  · exact Or.inr (Or.inr hupper)

/-- Complete Černý theorem on the two-parameter face `X=0`. -/
theorem xzero_satisfiesCerny (R L : ℕ)
    (hsynchronizing : (automaton ⟨0, R, L⟩).Synchronizing) :
    (automaton ⟨0, R, L⟩).SatisfiesCerny := by
  rcases xzero_satisfiesCerny_or_two_diagonals
      R L hsynchronizing with
    hsafe | hbalanced | hupper
  · exact hsafe
  · subst R
    exact xzero_balanced_satisfiesCerny L hsynchronizing
  · subst R
    exact xzero_upperDiagonal_satisfiesCerny L
      hsynchronizing

end DFA.CycleTree
