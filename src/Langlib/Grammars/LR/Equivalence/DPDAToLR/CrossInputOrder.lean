module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CrossInputDeterminism

/-!
# Ordering useful cuts across changed input suffixes

Equal-length cross-input synchronization also compares cuts reached after
different numbers of steps.  If both cuts have consumed the same visible
prefix and the first count is smaller, the second run contains a genuinely
nonempty, input-preserving segment between the corresponding physical cuts.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem reachesIn_split_exact
    {P : PDA Q T S} {n k : ℕ} {a c : PDA.conf P}
    (h : P.ReachesIn (n + k) a c) :
    ∃ b : PDA.conf P, P.ReachesIn n a b ∧ P.ReachesIn k b c := by
  induction k generalizing c with
  | zero =>
      refine ⟨c, ?_, PDA.ReachesIn.refl c⟩
      simpa using h
  | succ k ih =>
      rw [Nat.add_succ] at h
      obtain ⟨before, hbefore, hlast⟩ :=
        PDA.reachesIn_iff_split_last.mpr h
      obtain ⟨middle, hprefix, hsuffix⟩ := ih hbefore
      exact ⟨middle, hprefix,
        PDA.ReachesIn.step hsuffix
          (PDA.reaches₁_iff_reachesIn_one.mpr hlast)⟩

/-- A later useful cut at the same consumed prefix is reached from the
earlier corresponding cut by a positive epsilon-only segment.  The segment
is transported to the first run's untouched suffix. -/
public theorem emptyStack_cross_input_strict_extension
    (M : DPDA Q T S)
    {pre tail₁ tail₂ : List T} {n m : ℕ}
    {q₁ q₂ final₁ final₂ : EState M}
    {gamma₁ gamma₂ : List (EStack M)}
    (h₁ : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, pre ++ tail₁,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, tail₁, gamma₁⟩)
    (h₂ : (emptyStackPDA M).ReachesIn m
      ⟨(emptyStackPDA M).initial_state, pre ++ tail₂,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, tail₂, gamma₂⟩)
    (huseful₁ : (emptyStackPDA M).Reaches
      ⟨q₁, tail₁, gamma₁⟩ ⟨final₁, [], []⟩)
    (huseful₂ : (emptyStackPDA M).Reaches
      ⟨q₂, tail₂, gamma₂⟩ ⟨final₂, [], []⟩)
    (hlook : tail₁.take 1 = tail₂.take 1)
    (hlt : n < m) :
    ∃ k, 0 < k ∧
      (emptyStackPDA M).ReachesIn k
        ⟨q₁, tail₁, gamma₁⟩ ⟨q₂, tail₁, gamma₂⟩ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hlt)
  have hk : 0 < k := by omega
  obtain ⟨middle, hprefix₂, hrest₂⟩ :=
    reachesIn_split_exact h₂
  have hmiddleUseful : (emptyStackPDA M).Reaches
      middle ⟨final₂, [], []⟩ :=
    (PDA.reaches_of_reachesIn hrest₂).trans huseful₂
  have hmiddle : middle =
      (⟨q₁, tail₂, gamma₁⟩ : PDA.conf (emptyStackPDA M)) :=
    emptyStack_globally_useful_reachesIn_cross_input M
      h₁ hprefix₂ huseful₁ hmiddleUseful hlook
  subst middle
  have hstripped : (emptyStackPDA M).ReachesIn k
      ⟨q₁, [], gamma₁⟩ ⟨q₂, [], gamma₂⟩ := by
    exact (PDA.unconsumed_input_N
      (pda := emptyStackPDA M) tail₂).mpr hrest₂
  have hlifted := (PDA.unconsumed_input_N
    (pda := emptyStackPDA M) tail₁).mp hstripped
  exact ⟨k, hk, by simpa [PDA.conf.appendInput] using hlifted⟩

/-- Symmetric orientation of `emptyStack_cross_input_strict_extension`. -/
public theorem emptyStack_cross_input_strict_extension_symm
    (M : DPDA Q T S)
    {pre tail₁ tail₂ : List T} {n m : ℕ}
    {q₁ q₂ final₁ final₂ : EState M}
    {gamma₁ gamma₂ : List (EStack M)}
    (h₁ : (emptyStackPDA M).ReachesIn n
      ⟨(emptyStackPDA M).initial_state, pre ++ tail₁,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₁, tail₁, gamma₁⟩)
    (h₂ : (emptyStackPDA M).ReachesIn m
      ⟨(emptyStackPDA M).initial_state, pre ++ tail₂,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q₂, tail₂, gamma₂⟩)
    (huseful₁ : (emptyStackPDA M).Reaches
      ⟨q₁, tail₁, gamma₁⟩ ⟨final₁, [], []⟩)
    (huseful₂ : (emptyStackPDA M).Reaches
      ⟨q₂, tail₂, gamma₂⟩ ⟨final₂, [], []⟩)
    (hlook : tail₁.take 1 = tail₂.take 1)
    (hlt : m < n) :
    ∃ k, 0 < k ∧
      (emptyStackPDA M).ReachesIn k
        ⟨q₂, tail₂, gamma₂⟩ ⟨q₁, tail₂, gamma₁⟩ := by
  exact emptyStack_cross_input_strict_extension M
    h₂ h₁ huseful₂ huseful₁ hlook.symm hlt

end

end DPDA_to_LR
