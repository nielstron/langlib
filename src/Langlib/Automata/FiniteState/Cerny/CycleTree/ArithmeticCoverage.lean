module

public import Langlib.Automata.FiniteState.Cerny.CycleTree.FiniteCertificates

@[expose]
public section

/-!
# Arithmetic coverage of the residual cycle-tree diagonal

After the uniform residual unitary word has been applied, the remaining
parameters lie in `ResidualTail`.  Coprimality excludes the three gaps just
below the middle band, so every such parameter is either one of the nine
finite certificates, in the middle band, or in the large band.
-/

namespace DFA.CycleTree

/-- Parameters left on the residual diagonal after the unitary construction. -/
def ResidualTail (X L : ℕ) : Prop :=
  (X = 1 ∧ 1 ≤ L) ∨ (2 ≤ X ∧ X ^ 2 ≤ L + 1)

/-- The nine residual parameter pairs handled by explicit certificates. -/
def ResidualSmall (X L : ℕ) : Prop :=
  (X = 1 ∧ (L = 1 ∨ L = 2 ∨ L = 3)) ∨
  (X = 2 ∧ (L = 3 ∨ L = 4 ∨ L = 5 ∨ L = 6)) ∨
  (X = 3 ∧ (L = 8 ∨ L = 9))

/-- Domain of the uniform middle-band prefix. -/
def Middle (X L : ℕ) : Prop :=
  3 * X + 2 ≤ L ∧ L ≤ 5 * X + 2

/-- Domain of the uniform large-band prefix. -/
def Large (X L : ℕ) : Prop :=
  5 * X + 3 ≤ L

/-- Coprime residual-tail parameters partition into the finite set and the
two uniform five-depth bands. -/
theorem residualTail_partition {X L : ℕ}
    (hcoprime : Nat.Coprime (X + L + 2) (4 * X + 3))
    (htail : ResidualTail X L) :
    ResidualSmall X L ∨ Middle X L ∨ Large X L := by
  by_cases hmiddleLow : 3 * X + 2 ≤ L
  · by_cases hmiddleHigh : L ≤ 5 * X + 2
    · exact Or.inr (Or.inl ⟨hmiddleLow, hmiddleHigh⟩)
    · exact Or.inr (Or.inr (show 5 * X + 3 ≤ L by omega))
  · left
    rcases htail with ⟨rfl, hL⟩ | ⟨hX, htail⟩
    · have hcases : L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 := by
        omega
      rcases hcases with rfl | rfl | rfl | rfl
      · simp [ResidualSmall]
      · simp [ResidualSmall]
      · simp [ResidualSmall]
      · norm_num at hcoprime
    · by_cases hsmallX : X ≤ 3
      · have hXcases : X = 2 ∨ X = 3 := by
          omega
        rcases hXcases with rfl | rfl
        · have hcases :
              L = 3 ∨ L = 4 ∨ L = 5 ∨ L = 6 ∨ L = 7 := by
            omega
          rcases hcases with rfl | rfl | rfl | rfl | rfl
          · simp [ResidualSmall]
          · simp [ResidualSmall]
          · simp [ResidualSmall]
          · simp [ResidualSmall]
          · norm_num at hcoprime
        · have hcases : L = 8 ∨ L = 9 ∨ L = 10 := by
            omega
          rcases hcases with rfl | rfl | rfl
          · simp [ResidualSmall]
          · simp [ResidualSmall]
          · norm_num at hcoprime
      · have hXfour : 4 ≤ X := by
          omega
        have hquad : 4 * X ≤ X ^ 2 := by
          calc
            4 * X = X * 4 := by omega
            _ ≤ X * X := Nat.mul_le_mul_left X hXfour
            _ = X ^ 2 := by simp [pow_two]
        omega

/-- Every small residual pair is covered by one of the public kernel-checked
finite certificates. -/
theorem residualSmall_satisfiesCerny {X L : ℕ}
    (hsmall : ResidualSmall X L) :
    (automaton (residualParams X L)).SatisfiesCerny := by
  rcases hsmall with
    ⟨rfl, rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl⟩
  · exact safe_x1_l1
  · exact safe_x1_l2
  · exact safe_x1_l3
  · exact safe_x2_l3
  · exact safe_x2_l4
  · exact safe_x2_l5
  · exact safe_x2_l6
  · exact safe_x3_l8
  · exact safe_x3_l9

end DFA.CycleTree
