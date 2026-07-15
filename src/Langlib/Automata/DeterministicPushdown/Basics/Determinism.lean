module

public import Langlib.Automata.DeterministicPushdown.Definition

/-!
# Determinism of DPDA computations

The `Option`-valued transition functions and `DPDA.no_mixed` make the embedded
PDA transition relation functional.  This file records the corresponding
one-step, fixed-length-run, and prefix-comparison theorems for arbitrary DPDAs.
-/

@[expose]
public section

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- The PDA step relation underlying a DPDA is functional. -/
public theorem toPDA_step_deterministic (M : DPDA Q T S)
    {c d₁ d₂ : PDA.conf M.toPDA}
    (h₁ : @PDA.Reaches₁ Q T S _ _ _ M.toPDA c d₁)
    (h₂ : @PDA.Reaches₁ Q T S _ _ _ M.toPDA c d₂) :
    d₁ = d₂ := by
  rcases c with ⟨q, input, stack⟩
  cases stack with
  | nil => simp [PDA.Reaches₁, PDA.step] at h₁
  | cons Z rest =>
      cases input with
      | nil =>
          cases hε : M.epsilon_transition q Z with
          | none => simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε] at h₁
          | some out =>
              rcases out with ⟨p, beta⟩
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε] at h₁ h₂
              exact h₁.trans h₂.symm
      | cons a input =>
          cases hε : M.epsilon_transition q Z with
          | some out =>
              rcases out with ⟨p, beta⟩
              have hδ : M.transition q a Z = none :=
                M.no_mixed q Z (by simp [hε]) a
              simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε, hδ] at h₁ h₂
              exact h₁.trans h₂.symm
          | none =>
              cases hδ : M.transition q a Z with
              | none =>
                  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε, hδ] at h₁
              | some out =>
                  rcases out with ⟨p, beta⟩
                  simp [PDA.Reaches₁, PDA.step, DPDA.toPDA, hε, hδ] at h₁ h₂
                  exact h₁.trans h₂.symm

/-- Two computations of the same length from the same configuration have the
same endpoint. -/
public theorem toPDA_reachesIn_deterministic (M : DPDA Q T S)
    {n : ℕ} {c c₁ c₂ : PDA.conf M.toPDA}
    (h₁ : @PDA.ReachesIn Q T S _ _ _ M.toPDA n c c₁)
    (h₂ : @PDA.ReachesIn Q T S _ _ _ M.toPDA n c c₂) :
    c₁ = c₂ := by
  induction n generalizing c c₁ c₂ with
  | zero =>
      exact (PDA.reachesIn_zero h₁).symm.trans (PDA.reachesIn_zero h₂)
  | succ n ih =>
      obtain ⟨d₁, hd₁, hs₁⟩ := PDA.reachesIn_iff_split_last.mpr h₁
      obtain ⟨d₂, hd₂, hs₂⟩ := PDA.reachesIn_iff_split_last.mpr h₂
      have hd : d₁ = d₂ := ih hd₁ hd₂
      subst d₂
      exact M.toPDA_step_deterministic
        (PDA.reaches₁_iff_reachesIn_one.mpr hs₁)
        (PDA.reaches₁_iff_reachesIn_one.mpr hs₂)

private theorem reachesIn_split_add (M : DPDA Q T S)
    {n k : ℕ} {c d : PDA.conf M.toPDA}
    (h : @PDA.ReachesIn Q T S _ _ _ M.toPDA (n + k) c d) :
    ∃ middle : PDA.conf M.toPDA,
      @PDA.ReachesIn Q T S _ _ _ M.toPDA n c middle ∧
        @PDA.ReachesIn Q T S _ _ _ M.toPDA k middle d := by
  induction k generalizing d with
  | zero =>
      refine ⟨d, ?_, PDA.ReachesIn.refl d⟩
      simpa using h
  | succ k ih =>
      rw [Nat.add_succ] at h
      obtain ⟨before, hbefore, hlast⟩ := PDA.reachesIn_iff_split_last.mpr h
      obtain ⟨middle, hprefix, hsuffix⟩ := ih hbefore
      refine ⟨middle, hprefix, ?_⟩
      exact PDA.ReachesIn.step hsuffix
        (PDA.reaches₁_iff_reachesIn_one.mpr hlast)

/-- A shorter deterministic computation is the unique prefix of a longer one. -/
public theorem toPDA_reachesIn_prefix_of_le (M : DPDA Q T S)
    {n m : ℕ} {c c₁ c₂ : PDA.conf M.toPDA} (hnm : n ≤ m)
    (h₁ : @PDA.ReachesIn Q T S _ _ _ M.toPDA n c c₁)
    (h₂ : @PDA.ReachesIn Q T S _ _ _ M.toPDA m c c₂) :
    @PDA.Reaches Q T S _ _ _ M.toPDA c₁ c₂ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  obtain ⟨middle, hprefix, hsuffix⟩ :=
    reachesIn_split_add M h₂
  have hmiddle : middle = c₁ := M.toPDA_reachesIn_deterministic hprefix h₁
  subst middle
  exact PDA.reaches_of_reachesIn hsuffix

/-- Any two finite computations from one configuration are prefix-comparable. -/
public theorem toPDA_reaches_comparable (M : DPDA Q T S)
    {c c₁ c₂ : PDA.conf M.toPDA}
    (h₁ : @PDA.Reaches Q T S _ _ _ M.toPDA c c₁)
    (h₂ : @PDA.Reaches Q T S _ _ _ M.toPDA c c₂) :
    @PDA.Reaches Q T S _ _ _ M.toPDA c₁ c₂ ∨
      @PDA.Reaches Q T S _ _ _ M.toPDA c₂ c₁ := by
  rw [PDA.reaches_iff_reachesIn] at h₁ h₂
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  rcases le_total n m with hnm | hmn
  · exact Or.inl (M.toPDA_reachesIn_prefix_of_le hnm hn hm)
  · exact Or.inr (M.toPDA_reachesIn_prefix_of_le hmn hm hn)

end DPDA
