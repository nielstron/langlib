import Mathlib
import Grammars.Classes.ContextFree.Basics.Inclusion
import Grammars.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
import Grammars.Classes.ContextFree.Pumping.ParseTree

/-! # Decidability of Emptiness

This file proves that emptiness is decidable for
regular languages (represented by DFAs)

## Main results

- `regular_emptiness_decidable` – emptiness of a regular language (DFA) is decidable
-/

open List Relation

/-! ## Part 1: Regular Languages -/

section Regular

variable {α σ : Type*}

/-- Any state reachable by a DFA can be reached by a word of length at most
`Fintype.card σ`. By the pigeonhole principle. -/
lemma DFA.short_word_of_reachable [Fintype σ] [DecidableEq σ]
    (M : DFA α σ) (w : List α) :
    ∃ w' : List α, w'.length ≤ Fintype.card σ ∧
      M.evalFrom M.start w' = M.evalFrom M.start w := by
  induction' h : w.length using Nat.strong_induction_on with n ih generalizing w M
  by_cases hn : n ≤ Fintype.card σ
  · exact ⟨w, h.symm ▸ hn, rfl⟩
  · obtain ⟨i, j, hij, h_eq⟩ :
        ∃ i j : Fin (w.length + 1), i < j ∧
          M.evalFrom M.start (w.take i) = M.evalFrom M.start (w.take j) := by
      by_contra! hc
      exact absurd (Finset.card_le_univ
        (Finset.image (fun i : Fin (w.length + 1) =>
          M.evalFrom M.start (take (i : ℕ) w)) Finset.univ))
        (by rw [Finset.card_image_of_injective _ fun i j hij =>
              le_antisymm (not_lt.1 fun hi => hc _ _ hi hij.symm)
                (not_lt.1 fun hj => hc _ _ hj hij)]
            simpa using by linarith)
    obtain ⟨w', hw'⟩ :
        ∃ w' : List α,
          w' = w.take i ++ w.drop j ∧
            M.evalFrom M.start w' = M.evalFrom M.start w := by
      simp_all +decide [DFA.evalFrom]
      conv_rhs => rw [← List.take_append_drop j w, List.foldl_append]
    have h_ind : w'.length < n := by grind
    exact Exists.elim (ih _ h_ind _ _ rfl)
      fun w'' hw'' => ⟨w'', hw''.1, hw''.2.trans hw'.2⟩

/-- The set of states reachable from `M.start` by following transitions. -/
def DFA.reachableSet [Fintype α] [Fintype σ] [DecidableEq σ]
    (M : DFA α σ) : Finset σ :=
  let step := fun (S : Finset σ) =>
    S ∪ Finset.univ.biUnion (fun a => S.image (M.step · a))
  step^[Fintype.card σ] {M.start}

/-- A state is in `reachableSet` iff it is reachable from `M.start` by some word. -/
lemma DFA.mem_reachableSet_iff [Fintype α] [Fintype σ] [DecidableEq σ]
    (M : DFA α σ) (s : σ) :
    s ∈ M.reachableSet ↔ ∃ w : List α, M.evalFrom M.start w = s := by
  constructor <;> intro h
  · contrapose! h
    have h_ind : ∀ n : ℕ, ∀ s : σ, (∀ w : List α, M.evalFrom M.start w ≠ s) →
        s ∉ (fun (S : Finset σ) =>
          S ∪ Finset.univ.biUnion (fun a => S.image (M.step · a)))^[n] {M.start} := by
      intro n s hs
      induction' n with n ih generalizing s <;>
        simp_all +decide [Function.iterate_succ_apply']
      · exact fun h => hs [] (by simp +decide [h])
      · intro a t ht hts
        specialize ih t
        simp_all +decide [Function.iterate_succ_apply']
        obtain ⟨w, rfl⟩ := ih
        specialize hs (w ++ [a])
        simp_all +decide [DFA.evalFrom]
    exact h_ind _ _ h
  · obtain ⟨w, rfl⟩ := h
    have h_ind : ∀ k ≤ Fintype.card σ, ∀ w : List α, w.length ≤ k →
        M.evalFrom M.start w ∈ (fun S =>
          S ∪ (Finset.univ : Finset α).biUnion
            (fun a => S.image (M.step · a)))^[k] {M.start} := by
      intro k hk w hw
      induction' w using List.reverseRecOn with w ih generalizing k
      · induction' k with k ih <;> simp_all +decide [Function.iterate_succ_apply']
        exact Or.inl (ih hk.le)
      · rcases k with (_ | k) <;> simp_all +decide [Function.iterate_succ_apply']
        exact Or.inr ⟨ih, _, by rename_i h; exact h k hk.le hw, rfl⟩
    obtain ⟨w', hw', hw'_eq⟩ := M.short_word_of_reachable w
    exact hw'_eq ▸ h_ind _ le_rfl _ hw'

/-- Emptiness of a DFA's accepted language is decidable. -/
noncomputable def regular_emptiness_decidable
    [Fintype α] [Fintype σ] [DecidableEq α] [DecidableEq σ]
    (M : DFA α σ) [DecidablePred (· ∈ M.accept)] :
    Decidable (M.accepts = (∅ : Set (List α))) := by
  have key : M.accepts = (∅ : Set (List α)) ↔
      ∀ s ∈ M.reachableSet, s ∉ M.accept := by
    constructor
    · intro h s hs hsa
      rw [M.mem_reachableSet_iff] at hs
      obtain ⟨w, rfl⟩ := hs
      have : w ∈ M.accepts := hsa
      rw [h] at this
      exact this
    · intro h
      apply Set.subset_eq_empty (fun w (hw : w ∈ M.accepts) => ?_) rfl
      exact h _ ((M.mem_reachableSet_iff _).mpr ⟨w, rfl⟩) hw
  rw [key]
  infer_instance

end Regular
