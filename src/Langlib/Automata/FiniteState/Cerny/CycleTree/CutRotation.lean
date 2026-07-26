module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.Coordinates
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose]
public section

/-!
# The cut-rotation macro

This file begins the symbolic, parameter-uniform part of the cycle-tree
proof.  It turns the coordinate calculation for `D` into modular orbit
lemmas.  In particular, coprimality makes every local cycle coordinate hit
the cut within one period.
-/

namespace DFA.CycleTree

theorem exists_modular_hit {step modulus start target : ℕ}
    (hmodulus : 0 < modulus)
    (hcoprime : Nat.Coprime step modulus) :
    ∃ count < modulus,
      (start + count * step) % modulus = target % modulus := by
  letI : NeZero modulus := ⟨Nat.ne_of_gt hmodulus⟩
  let difference : ZMod modulus :=
    (target : ZMod modulus) - (start : ZMod modulus)
  let witness : ZMod modulus :=
    (step : ZMod modulus)⁻¹ * difference
  let count := witness.val
  refine ⟨count, ZMod.val_lt witness, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff'
    (start + count * step) target modulus).mp
  have hcount : (count : ZMod modulus) = witness :=
    ZMod.natCast_zmod_val witness
  rw [Nat.cast_add, Nat.cast_mul, hcount]
  dsimp [witness, difference]
  have hinverse :
      (step : ZMod modulus) * (step : ZMod modulus)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one step hcoprime
  calc
    (start : ZMod modulus) +
        ((step : ZMod modulus)⁻¹ *
          ((target : ZMod modulus) - (start : ZMod modulus))) *
          (step : ZMod modulus) =
      (start : ZMod modulus) +
        ((target : ZMod modulus) - (start : ZMod modulus)) *
          ((step : ZMod modulus) *
            (step : ZMod modulus)⁻¹) := by ring
    _ = (target : ZMod modulus) := by rw [hinverse]; ring

theorem cycle_coprime_two (P : Params) :
    Nat.Coprime 2 P.cycle := by
  rw [Nat.coprime_two_left]
  refine ⟨P.R + P.L + 1, ?_⟩
  simp [Params.cycle]
  omega

theorem twice_m_coprime_cycle (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle) :
    Nat.Coprime (2 * P.m) P.cycle :=
  (cycle_coprime_two P).mul_left hcoprime

/-- Under the exact coprimality condition, every local `J` coordinate
reaches `rhoIndex` after fewer than `M` applications of the underlying
rotation. -/
theorem exists_dIndex_iterate_eq_rho (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (index : Fin P.cycle) :
    ∃ count < P.cycle,
      cycleAdvance P index (count * (2 * P.m)) = rhoIndex P := by
  obtain ⟨count, hcount, hhit⟩ :=
    exists_modular_hit P.cycle_pos
      (twice_m_coprime_cycle P hcoprime)
      (start := index.val) (target := (rhoIndex P).val)
  refine ⟨count, hcount, ?_⟩
  rw [Nat.mod_eq_of_lt (rhoIndex P).isLt] at hhit
  apply Fin.ext
  exact hhit

theorem iterate_dIndex (P : Params) (index : Fin P.cycle)
    (count : ℕ) :
    (dIndex P)^[count] index =
      cycleAdvance P index (count * (2 * P.m)) := by
  change
    (((cycleNext P)^[2 * P.m])^[count]) index =
      cycleAdvance P index (count * (2 * P.m))
  rw [← congrFun (Function.iterate_mul (cycleNext P)
    (2 * P.m) count) index]
  rw [Nat.mul_comm, iterate_cycleNext]

/-- A positive hitting time is needed for the cut: if the initial coordinate
is already `rhoIndex`, one complete period is used. -/
theorem exists_positive_dIndex_iterate_eq_rho (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (index : Fin P.cycle) :
    ∃ count, 1 ≤ count ∧ count ≤ P.cycle ∧
      (dIndex P)^[count] index = rhoIndex P := by
  obtain ⟨previous, hprevious, hhit⟩ :=
    exists_dIndex_iterate_eq_rho P hcoprime (dIndex P index)
  refine ⟨previous + 1, by omega, by omega, ?_⟩
  rw [Function.iterate_succ_apply]
  rw [iterate_dIndex]
  exact hhit

theorem evalFrom_dWordPower_one (P : Params) (count : ℕ) :
    (automaton P).evalFrom (P.stateOfNat 1)
        (wordPow (dWord P) count) =
      P.stateOfNat 1 := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [wordPow_succ, (automaton P).evalFrom_of_append,
        evalFrom_dWord_one, ih]

theorem evalFrom_dWordPower_interval_of_hit (P : Params)
    (index : Fin P.cycle) (count : ℕ)
    (hcount : 0 < count)
    (hhit : (dIndex P)^[count] index = rhoIndex P) :
    (automaton P).evalFrom (intervalState P index)
        (wordPow (dWord P) count) =
      P.stateOfNat 1 := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      rw [wordPow_succ, (automaton P).evalFrom_of_append,
        evalFrom_dWord_intervalState]
      by_cases hfirst : dIndex P index = rhoIndex P
      · rw [if_pos hfirst, evalFrom_dWordPower_one]
      · rw [if_neg hfirst]
        by_cases hzero : count = 0
        · subst count
          simp only [Function.iterate_succ_apply,
            Function.iterate_zero_apply] at hhit
          exact (hfirst hhit).elim
        · apply ih (index := dIndex P index) (Nat.pos_of_ne_zero hzero)
          simpa only [Function.iterate_succ_apply] using hhit

/-- Every interval state reaches the sink in at most one `D`-period when
`m` and `M` are coprime. -/
theorem exists_short_dPower_reset_from_interval (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (index : Fin P.cycle) :
    ∃ count ≤ P.cycle,
      (automaton P).evalFrom (intervalState P index)
          (wordPow (dWord P) count) =
        P.stateOfNat 1 := by
  obtain ⟨count, hcountPos, hcountBound, hhit⟩ :=
    exists_positive_dIndex_iterate_eq_rho P hcoprime index
  exact ⟨count, hcountBound,
    evalFrom_dWordPower_interval_of_hit P index count
      hcountPos hhit⟩

theorem evalFrom_full_dPower_interval (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (index : Fin P.cycle) :
    (automaton P).evalFrom (intervalState P index)
        (dPowerWord P P.cycle) =
      P.stateOfNat 1 := by
  obtain ⟨count, hcount, hreset⟩ :=
    exists_short_dPower_reset_from_interval P hcoprime index
  unfold dPowerWord
  calc
    (automaton P).evalFrom (intervalState P index)
        (wordPow (dWord P) P.cycle) =
      (automaton P).evalFrom (intervalState P index)
        (wordPow (dWord P) count ++
          wordPow (dWord P) (P.cycle - count)) := by
            rw [← wordPow_add, Nat.add_sub_of_le hcount]
    _ = P.stateOfNat 1 := by
      rw [(automaton P).evalFrom_of_append, hreset,
        evalFrom_dWordPower_one]

/-- If an interval coordinate is not the unique depth-`M` point, then
`M - 1` copies of `D` already suffice. -/
theorem evalFrom_shortened_dPower_interval (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (index : Fin P.cycle) (hindex : index ≠ rhoIndex P) :
    (automaton P).evalFrom (intervalState P index)
        (dPowerWord P (P.cycle - 1)) =
      P.stateOfNat 1 := by
  obtain ⟨count, hcountLt, hhit⟩ :=
    exists_dIndex_iterate_eq_rho P hcoprime index
  have hhit' : (dIndex P)^[count] index = rhoIndex P := by
    rw [iterate_dIndex]
    exact hhit
  have hcountPos : 0 < count := by
    by_contra hnotPos
    have hcountZero : count = 0 := by omega
    subst count
    simp only [Function.iterate_zero_apply] at hhit'
    exact hindex hhit'
  have hcountBound : count ≤ P.cycle - 1 := by omega
  have hreset :=
    evalFrom_dWordPower_interval_of_hit P index count hcountPos hhit'
  unfold dPowerWord
  calc
    (automaton P).evalFrom (intervalState P index)
        (wordPow (dWord P) (P.cycle - 1)) =
      (automaton P).evalFrom (intervalState P index)
        (wordPow (dWord P) count ++
          wordPow (dWord P) (P.cycle - 1 - count)) := by
            rw [← wordPow_add, Nat.add_sub_of_le hcountBound]
    _ = P.stateOfNat 1 := by
      rw [(automaton P).evalFrom_of_append, hreset,
        evalFrom_dWordPower_one]

/-- The exact cut-rotation word `D^M` resets every state in the coprime
parameter regime. -/
theorem dPower_isResetWord (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle) :
    (automaton P).IsResetWord (dPowerWord P P.cycle) := by
  refine ⟨P.stateOfNat 1, ?_⟩
  intro state
  unfold dPowerWord
  have hcyclePos := P.cycle_pos
  conv_lhs =>
    rw [show P.cycle = (P.cycle - 1) + 1 by omega]
  rw [wordPow_succ, (automaton P).evalFrom_of_append]
  rcases dWord_image_sink_or_interval P state with
    hsink | ⟨index, hindex, himage⟩
  · rw [hsink, evalFrom_dWordPower_one]
  · rw [himage]
    exact evalFrom_shortened_dPower_interval P hcoprime index hindex

/-- With one leading `D` to enter the invariant interval, one complete
rotation period resets every state.  This is a uniform, constructive
synchronization theorem for the coprime parameter regime. -/
theorem dPower_succ_isResetWord (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle) :
    (automaton P).IsResetWord (dPowerWord P (P.cycle + 1)) := by
  refine ⟨P.stateOfNat 1, ?_⟩
  intro state
  unfold dPowerWord
  rw [wordPow_succ, (automaton P).evalFrom_of_append]
  rcases dWord_image_sink_or_interval P state with
    hsink | ⟨index, _, hindex⟩
  · rw [hsink, evalFrom_dWordPower_one]
  · rw [hindex]
    exact evalFrom_full_dPower_interval P hcoprime index

theorem synchronizing_of_coprime (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle) :
    (automaton P).Synchronizing :=
  (dPower_isResetWord P hcoprime).synchronizing

/-- The exact numerical condition under which the uniform word `D^M` fits
inside the Černý bound, written without truncated subtraction. -/
theorem dPower_length_le_cernyBound_of_arithmetic (P : Params)
    (hsafe :
      P.R ^ 2 + 2 * P.R + 1 ≤
        P.X ^ 2 + P.X + P.L ^ 2 + P.L) :
    (dPowerWord P P.cycle).length ≤ (automaton P).cernyBound := by
  simp only [length_dPowerWord, DFA.cernyBound, Fintype.card_fin]
  simp only [Params.cycle, Params.m, Params.order, Params.ell]
  have horder :
      2 * P.X + 2 + (2 * P.R + 2 * P.L + 3) - 1 =
        2 * (P.X + P.R + P.L) + 4 := by
    omega
  rw [horder]
  nlinarith

/-- The exact arithmetic region in which the unshortened cut-rotation word
fits the Černý bound. -/
def CutSafe (P : Params) : Prop :=
  P.R ^ 2 + 2 * P.R + 1 ≤
    P.X ^ 2 + P.X + P.L ^ 2 + P.L

/-- The cut-rotation construction proves the Černý conclusion throughout
its exact cost-safe region. -/
theorem satisfiesCerny_of_coprime_of_cutSafe (P : Params)
    (hcoprime : Nat.Coprime P.m P.cycle)
    (hsafe : CutSafe P) :
    (automaton P).SatisfiesCerny :=
  DFA.satisfiesCerny_of_resetWord (automaton P)
    (dPower_isResetWord P hcoprime)
    (dPower_length_le_cernyBound_of_arithmetic P hsafe)

end DFA.CycleTree
