module

public import Mathlib.Computability.DFA
public import Langlib.Classes.Regular.Decidability.Helper
public import Langlib.Classes.Regular.Decidability.Characterization
public import Langlib.Classes.Regular.Decidability.Membership
public import Langlib.Classes.ContextFree.Decidability.Emptiness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
@[expose]
public section



/-! # Decidability of Emptiness

This file proves that emptiness is decidable for
regular languages.

## Main results

- `regular_emptiness_decidable` – emptiness of a regular language is decidable
- `regular_computableEmptiness` – emptiness is *uniformly* computable for encoded
  right-regular grammars (`ComputableEmptiness`)
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
        simp_all +decide
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
noncomputable def dfa_emptiness_decidable
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

/-- Emptiness of a regular language is decidable. -/
@[expose]
public noncomputable def regular_emptiness_decidable
    [Fintype α] [DecidableEq α] (L : Language α) (hL : L.IsRegular) :
    Decidable (L = (∅ : Set (List α))) := by
  classical
  let σ := Classical.choose hL
  let hσ := Classical.choose_spec hL
  let _ : Fintype σ := Classical.choose hσ
  let hσ' := Classical.choose_spec hσ
  let M : DFA α σ := Classical.choose hσ'
  let hM : M.accepts = L := Classical.choose_spec hσ'
  rw [← hM]
  exact dfa_emptiness_decidable M

end Regular

/-! ## Part 2: Uniform computability over encoded right-regular grammars -/

namespace Regular.EncodedRG

/-- The raw uniform emptiness decider for encoded right-regular grammars, obtained by
composing the context-free emptiness decider with the primitive-recursive translation
`toCFG : EncodedRG T → EncodedCFG T`. -/
public theorem regular_emptiness_computablePred [Fintype T] [DecidableEq T] [Primcodable T] :
    ComputablePred (fun c : EncodedRG T => regularLanguageOf c = (∅ : Set (List T))) := by
  obtain ⟨f, hf_comp, hf_eq⟩ :=
    ComputablePred.computable_iff.mp (contextFree_emptiness_computablePred (T := T))
  rw [ComputablePred.computable_iff]
  refine ⟨fun c => f (toCFG c), hf_comp.comp (Primrec.to_comp toCFG_primrec), ?_⟩
  funext c
  have h := congrFun hf_eq (toCFG c)
  simpa [regularLanguageOf] using h

/-- **Emptiness is uniformly computable** for the regular languages: encoded
right-regular grammars are an adequate, effective presentation
(`regularLanguageOf_characterizes`) with uniformly decidable emptiness. -/
public theorem regular_computableEmptiness [Fintype T] [DecidableEq T] [Primcodable T] :
    ComputableEmptiness RG (regularLanguageOf : EncodedRG T → Language T) :=
  ⟨regularLanguageOf_characterizes.onTrue, regular_membership_computablePred.to_re,
    ComputablePredOnPromise.ofComputablePred regular_emptiness_computablePred⟩

end Regular.EncodedRG
