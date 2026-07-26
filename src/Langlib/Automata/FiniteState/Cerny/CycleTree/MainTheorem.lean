module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.ResidualWords
public import Langlib.Automata.FiniteState.Cerny.CycleTree.LargePrefix
public import Langlib.Automata.FiniteState.Cerny.CycleTree.MiddlePrefix
public import Langlib.Automata.FiniteState.Cerny.CycleTree.ResidualUnitary
public import Langlib.Automata.FiniteState.Cerny.CycleTree.ShortenedCut
public import Langlib.Automata.FiniteState.Cerny.CycleTree.GlobalArithmetic
public import Langlib.Automata.FiniteState.Cerny.CycleTree.ArmEquivalence
public import Langlib.Automata.FiniteState.Cerny.CycleTree.XZeroFace
import Mathlib.Data.Nat.GCD.Basic

@[expose]
public section

/-!
# The cycle-tree Černý theorem: statement and proof assembly

`CompleteFamilySatisfiesCerny` is the exact statement for the coordinate
family in `Definition`.  This module assembles its unconditional proof
from the exact synchronization criterion, the global cut constructions,
the residual unitary, the two symbolic five-depth prefixes, the
kernel-checked finite certificates, and the separate `X = 0` theorem.
-/

namespace DFA.CycleTree

/-- The exact theorem asserted for the complete three-arm coordinate
family: every synchronizing member has a reset word of length at most the
Černý bound. -/
def CompleteFamilySatisfiesCerny : Prop :=
  ∀ P : Params,
    (automaton P).Synchronizing →
      (automaton P).SatisfiesCerny

/-- The exact theorem has the same content in the original three-arm
presentation and in hidden-cycle coordinates. -/
theorem completeArmFamily_iff_completeFamily :
    CompleteArmFamilySatisfiesCerny ↔
      CompleteFamilySatisfiesCerny := by
  simpa only [CompleteFamilySatisfiesCerny] using
    completeArmFamily_iff_coordinateFamily

/-- Exact synchronization classification for the literal three-arm DFA. -/
theorem arm_synchronizing_iff_coprime (P : Params) :
    (armAutomaton P).Synchronizing ↔ Nat.Coprime P.m P.cycle :=
  (arm_synchronizing_iff P).trans (synchronizing_iff_coprime P)

/-- The sharply delimited residual tail on the diagonal `R = L + 1`. -/
def OnResidualTail (P : Params) : Prop :=
  P.R = P.L + 1 ∧ ResidualTail P.X P.L

/-- The cost-safe part of the residual diagonal covered by the explicit
unitary construction. -/
def OnResidualUnitarySafe (P : Params) : Prop :=
  P.R = P.L + 1 ∧ 1 ≤ P.X ∧ P.X ≤ P.L ∧
    P.L ≤ P.X ^ 2 - 2

/-- If two complementary natural numbers add to a multiple of `a`, then
coprimality of `a` with either complement implies coprimality with the
other. -/
private theorem coprime_complement {a b c multiplier : ℕ}
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

/-- On the residual diagonal, the cycle coprimality used by
`synchronizing_of_coprime` is exactly the complementary arithmetic
coprimality used by `residualTail_partition`. -/
theorem residual_cycleCoprime_iff_arithmeticCoprime (X L : ℕ) :
    Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle ↔
      Nat.Coprime (X + L + 2) (4 * X + 3) := by
  have hm : (residualParams X L).m = X + L + 2 := by
    simp [residualParams, Params.m]
    omega
  have hcycle : (residualParams X L).cycle = 4 * L + 5 := by
    simp [residualParams, Params.cycle]
    omega
  rw [hm, hcycle]
  constructor
  · exact coprime_complement
      (a := X + L + 2) (b := 4 * L + 5) (c := 4 * X + 3)
      (multiplier := 4) (by omega)
  · exact coprime_complement
      (a := X + L + 2) (b := 4 * X + 3) (c := 4 * L + 5)
      (multiplier := 4) (by omega)

/-- The exact synchronization criterion specialized to the arithmetic form
used by the residual partition. -/
theorem residual_synchronizing_iff_arithmeticCoprime (X L : ℕ) :
    (automaton (residualParams X L)).Synchronizing ↔
      Nat.Coprime (X + L + 2) (4 * X + 3) := by
  exact (synchronizing_iff_coprime (residualParams X L)).trans
    (residual_cycleCoprime_iff_arithmeticCoprime X L)

/-- Unconditional completion of the residual tail from the nine
kernel-checked certificates and the two symbolic five-depth prefixes. -/
theorem residualTail_satisfiesCerny
    (X L : ℕ)
    (htail : ResidualTail X L)
    (hsynchronizing :
      (automaton (residualParams X L)).Synchronizing) :
    (automaton (residualParams X L)).SatisfiesCerny := by
  have hcoprime :
      Nat.Coprime (X + L + 2) (4 * X + 3) :=
    (residual_synchronizing_iff_arithmeticCoprime X L).mp hsynchronizing
  have hcycleCoprime :
      Nat.Coprime
        (residualParams X L).m
        (residualParams X L).cycle :=
    (residual_cycleCoprime_iff_arithmeticCoprime X L).mpr hcoprime
  rcases residualTail_partition hcoprime htail with
    hsmall | hmiddle | hlarge
  · exact residualSmall_satisfiesCerny hsmall
  · exact middle_satisfiesCerny hcycleCoprime hmiddle
  · exact large_satisfiesCerny hcycleCoprime hlarge

/-- Unconditional theorem for every positive-`X` member of the coordinate
family. -/
theorem positiveX_satisfiesCerny {X R L : ℕ} (hX : 1 ≤ X)
    (hsynchronizing : (automaton ⟨X, R, L⟩).Synchronizing) :
    (automaton ⟨X, R, L⟩).SatisfiesCerny :=
  positiveX_satisfiesCerny_of_middlePrefixVerified
    (fun hmiddle => middlePrefix_avoidsDeep hmiddle)
    hX hsynchronizing

/-- The same unconditional positive-`X` theorem for the literal three-arm
presentation. -/
theorem arm_positiveX_satisfiesCerny {X R L : ℕ} (hX : 1 ≤ X)
    (hsynchronizing : (armAutomaton ⟨X, R, L⟩).Synchronizing) :
    (armAutomaton ⟨X, R, L⟩).SatisfiesCerny :=
  (arm_satisfiesCerny_iff ⟨X, R, L⟩).mpr
    (positiveX_satisfiesCerny hX
      ((arm_synchronizing_iff ⟨X, R, L⟩).mp hsynchronizing))

/-- Every synchronizing member of the complete coordinate family satisfies
the Černý bound. -/
theorem completeFamilySatisfiesCerny :
    CompleteFamilySatisfiesCerny := by
  rintro ⟨X, R, L⟩ hsynchronizing
  cases X with
  | zero =>
      exact xzero_satisfiesCerny R L hsynchronizing
  | succ X =>
      exact positiveX_satisfiesCerny (Nat.succ_pos X) hsynchronizing

/-- Every synchronizing member of the literal tagged three-arm family
satisfies the Černý bound. -/
theorem completeArmFamilySatisfiesCerny :
    CompleteArmFamilySatisfiesCerny :=
  completeArmFamily_iff_completeFamily.mpr
    completeFamilySatisfiesCerny

end DFA.CycleTree
