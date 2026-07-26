module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.LargePrefix
public import Langlib.Automata.FiniteState.Cerny.CycleTree.ResidualUnitary
public import Langlib.Automata.FiniteState.Cerny.CycleTree.ShortenedCut
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose]
public section

/-!
# Global arithmetic coverage for positive `X`

This module combines the three inexpensive global constructions:

* the shortened cut `E D^(M-1)`;
* the complementary direct cut `Pcut B^(M-2)`;
* the residual unitary word on `R = L + 1`.

Their cost regions leave only `ResidualTail` on the residual diagonal.
The finite and large parts of that tail are already unconditional.  The
final theorem exposes only the exact middle-prefix image predicate.
-/

namespace DFA.CycleTree

/-- Cost-safe domain of the residual unitary word, in the subtraction-free
form used by its length theorem. -/
def ResidualUnitarySafe (X L : ℕ) : Prop :=
  X ≤ L ∧ L + 2 ≤ X ^ 2

/-- The single remaining symbolic predicate in the positive-`X`
arithmetic assembly. -/
def MiddlePrefixVerified : Prop :=
  ∀ {X L : ℕ}, Middle X L →
    PrefixAvoidsDeep (residualParams X L) (middlePrefix X L) 5

private theorem shortenedCutSafe_of_not_directDomain (P : Params)
    (hnotDomain : ¬P.DirectDomain) :
    ShortenedCutSafe P := by
  have hRX : P.R ≤ P.X := by
    simp only [Params.DirectDomain] at hnotDomain
    omega
  have hRXone : P.R + 1 ≤ P.X := by
    simp only [Params.DirectDomain] at hnotDomain
    omega
  have hsquare : P.R ^ 2 ≤ P.X ^ 2 :=
    Nat.pow_le_pow_left hRX 2
  simp only [ShortenedCutSafe]
  omega

private theorem shortenedCutSafe_of_R_le_L (P : Params)
    (hX : 1 ≤ P.X) (hRL : P.R ≤ P.L) :
    ShortenedCutSafe P := by
  have hsquare : P.R ^ 2 ≤ P.L ^ 2 :=
    Nat.pow_le_pow_left hRL 2
  have hpositive : 1 ≤ P.X ^ 2 + P.X := by
    nlinarith
  simp only [ShortenedCutSafe]
  omega

private theorem directSafe_of_L_add_two_le_R (P : Params)
    (hX : 1 ≤ P.X) (hLR : P.L + 2 ≤ P.R) :
    DirectSafe P := by
  have hleft : P.L + 2 ≤ P.R := hLR
  have hright : P.L + 1 ≤ P.R - 1 := by omega
  have hproduct :
      (P.L + 2) * (P.L + 1) ≤ P.R * (P.R - 1) :=
    Nat.mul_le_mul hleft hright
  have hleftExpand :
      (P.L + 2) * (P.L + 1) =
        P.L ^ 2 + 3 * P.L + 2 := by ring
  have hrightExpand :
      P.R * (P.R - 1) + P.R = P.R ^ 2 := by
    calc
      P.R * (P.R - 1) + P.R =
          (P.R * P.R - P.R) + P.R := by
            rw [Nat.mul_sub_left_distrib]
            simp
      _ = P.R * P.R :=
        Nat.sub_add_cancel
          (Nat.le_mul_of_pos_left P.R (by omega))
      _ = P.R ^ 2 := by rw [pow_two]
  have hquadratic :
      P.L ^ 2 + 3 * P.L + P.R + 2 ≤ P.R ^ 2 := by
    omega
  have hXcost : 3 ≤ P.X ^ 2 + 2 * P.X := by
    nlinarith
  simp only [DirectSafe]
  omega

/-- Pure arithmetic partition behind the global proof.  Outside the two
global cost regions, the parameters are on `R = L + 1`; there the unitary
region and `ResidualTail` are complementary. -/
theorem positiveX_global_arithmetic_partition (P : Params)
    (hX : 1 ≤ P.X) :
    ShortenedCutSafe P ∨
    (P.DirectDomain ∧ DirectSafe P) ∨
    (P.R = P.L + 1 ∧
      (ResidualUnitarySafe P.X P.L ∨
        ResidualTail P.X P.L)) := by
  by_cases hshort : ShortenedCutSafe P
  · exact Or.inl hshort
  right
  have hdomain : P.DirectDomain := by
    by_contra hnotDomain
    exact hshort
      (shortenedCutSafe_of_not_directDomain P hnotDomain)
  by_cases hdirect : DirectSafe P
  · exact Or.inl ⟨hdomain, hdirect⟩
  right
  have hRnotLeL : ¬P.R ≤ P.L := by
    intro hRL
    exact hshort (shortenedCutSafe_of_R_le_L P hX hRL)
  have hRnotLarge : ¬P.L + 2 ≤ P.R := by
    intro hlarge
    exact hdirect (directSafe_of_L_add_two_le_R P hX hlarge)
  have hdiagonal : P.R = P.L + 1 := by omega
  refine ⟨hdiagonal, ?_⟩
  have hXL : P.X ≤ P.L := by
    by_contra hnotXL
    have hLX : P.L + 1 ≤ P.X := by omega
    apply hdirect
    simp only [DirectSafe]
    rw [hdiagonal]
    have hsquare : 1 ≤ P.X ^ 2 := by nlinarith
    nlinarith
  by_cases hunitary : P.L + 2 ≤ P.X ^ 2
  · exact Or.inl ⟨hXL, hunitary⟩
  · right
    unfold ResidualTail
    by_cases hXone : P.X = 1
    · exact Or.inl ⟨hXone, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩

/-- All positive-`X` parameters outside the residual tail are already
covered by one of the three explicit global constructions. -/
theorem positiveX_satisfiesCerny_or_residualTail
    {X R L : ℕ} (hX : 1 ≤ X)
    (hsynchronizing :
      (automaton ⟨X, R, L⟩).Synchronizing) :
    (automaton ⟨X, R, L⟩).SatisfiesCerny ∨
      (R = L + 1 ∧ ResidualTail X L) := by
  let P : Params := ⟨X, R, L⟩
  have hcoprime : Nat.Coprime P.m P.cycle :=
    coprime_of_synchronizing P hsynchronizing
  rcases positiveX_global_arithmetic_partition P hX with
    hshort | ⟨hdomain, hdirect⟩ |
      ⟨hdiagonal, hunitary | htail⟩
  · left
    exact satisfiesCerny_of_synchronizing_of_shortenedCutSafe
      P hsynchronizing hshort
  · left
    exact satisfiesCerny_of_generalDirectCut
      P hcoprime hdomain hdirect
  · left
    rcases hunitary with ⟨hXL, hupper⟩
    have hR : R = L + 1 := hdiagonal
    subst R
    have hcoprimeResidual :
        Nat.Coprime
          (residualParams X L).m
          (residualParams X L).cycle := by
      simpa only [P, residualParams] using hcoprime
    exact residualUnitary_satisfiesCerny_of_add_two_le_square
      hcoprimeResidual hXL hupper
  · right
    exact ⟨hdiagonal, htail⟩

private theorem coprime_complement
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
  have hdifferenceEq : multiplier * a - c = b := by omega
  simpa only [hdifferenceEq] using hdifference

/-- Convert the exact cycle coprimality to the complementary arithmetic
form used by `residualTail_partition`. -/
theorem residual_arithmeticCoprime_of_cycleCoprime
    {X L : ℕ}
    (hcoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle) :
    Nat.Coprime (X + L + 2) (4 * X + 3) := by
  have hm : (residualParams X L).m = X + L + 2 := by
    simp [residualParams, Params.m]
    omega
  have hcycle :
      (residualParams X L).cycle = 4 * L + 5 := by
    simp [residualParams, Params.cycle]
    omega
  rw [hm, hcycle] at hcoprime
  exact coprime_complement
    (a := X + L + 2) (b := 4 * L + 5)
    (c := 4 * X + 3) (multiplier := 4)
    (by omega) hcoprime

/-- Complete residual-tail assembly conditional only on the exact
middle-prefix image predicate. -/
theorem residualTail_satisfiesCerny_of_middlePrefixVerified
    (hmiddleVerified : MiddlePrefixVerified)
    {X L : ℕ} (htail : ResidualTail X L)
    (hsynchronizing :
      (automaton (residualParams X L)).Synchronizing) :
    (automaton (residualParams X L)).SatisfiesCerny := by
  have hcycleCoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle :=
    coprime_of_synchronizing
      (residualParams X L) hsynchronizing
  have harithmeticCoprime :
      Nat.Coprime (X + L + 2) (4 * X + 3) :=
    residual_arithmeticCoprime_of_cycleCoprime hcycleCoprime
  rcases residualTail_partition harithmeticCoprime htail with
    hsmall | hmiddle | hlarge
  · exact residualSmall_satisfiesCerny hsmall
  · exact middle_satisfiesCerny_of_prefix_image
      hcycleCoprime hmiddle (hmiddleVerified hmiddle)
  · exact large_satisfiesCerny hcycleCoprime hlarge

/-- Strongest positive-`X` global theorem currently needed by the final
assembly.  Its only premise beyond synchronization is the precise,
parameter-uniform middle-prefix image calculation. -/
theorem positiveX_satisfiesCerny_of_middlePrefixVerified
    (hmiddleVerified : MiddlePrefixVerified)
    {X R L : ℕ} (hX : 1 ≤ X)
    (hsynchronizing :
      (automaton ⟨X, R, L⟩).Synchronizing) :
    (automaton ⟨X, R, L⟩).SatisfiesCerny := by
  rcases positiveX_satisfiesCerny_or_residualTail
      hX hsynchronizing with hsafe | ⟨hdiagonal, htail⟩
  · exact hsafe
  · subst R
    exact residualTail_satisfiesCerny_of_middlePrefixVerified
      hmiddleVerified htail hsynchronizing

end DFA.CycleTree
