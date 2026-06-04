module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Classes.ContextFree.Examples.AnBnCn
public import Langlib.Classes.ContextFree.Examples.AnBnCm
public import Langlib.Classes.ContextFree.Examples.AnBmCm
public import Langlib.Examples.AnBmCm
public import Langlib.Examples.AnBnCm
public import Langlib.Examples.AnBnCn
public import Langlib.Utilities.ClosurePredicates
public import Langlib.Utilities.ListUtils
import Langlib.Classes.ContextFree.Basics.Elementary
import Langlib.Classes.ContextFree.Closure.Bijection
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Langlib.Utilities.Tactics
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
@[expose]
public section




/-! # Context-Free Non-Closure Under Intersection

This file proves that context-free languages are not closed under intersection.

The witnesses are `lang_eq_any = {aⁿbⁿcᵐ | n,m ∈ ℕ}` and `lang_any_eq = {aⁿbᵐcᵐ | n,m ∈ ℕ}`,
each context-free (`CF_lang_eq_any` / `CF_lang_any_eq`, in
`Langlib.Classes.ContextFree.Examples.{AnBnCm,AnBmCm}`). Their intersection is
`lang_eq_eq = {aⁿbⁿcⁿ | n ∈ ℕ}`, which is not context-free (`notCF_lang_eq_eq`, in
`Langlib.Classes.ContextFree.Examples.AnBnCn`).

This file supplies the intersection bookkeeping `lang_eq_any ⊓ lang_any_eq = lang_eq_eq`
and assembles the non-closure statements.

## Main declarations

- `nnyCF_of_CF_i_CF` - if L₁ and L₂ are CF, then L₁ ∩ L₂ is not always CF
- `CF_notClosedUnderIntersection` — CF is not closed under intersection over `Fin 3`
-/

section defs_over_fin3

private lemma neq_ab : a_ ≠ b_ := by decide
private lemma neq_ba : b_ ≠ a_ := neq_ab.symm
private lemma neq_ac : a_ ≠ c_ := by decide
private lemma neq_ca : c_ ≠ a_ := neq_ac.symm
private lemma neq_bc : b_ ≠ c_ := by decide
private lemma neq_cb : c_ ≠ b_ := neq_bc.symm

end defs_over_fin3


section intersection_inclusions

public lemma intersection_of_lang_eq_eq {w : List (Fin 3)} :
  w ∈ lang_eq_eq  →  w ∈ lang_eq_any ⊓ lang_any_eq  :=
by
  intro h
  cases h with
  | intro n hyp =>
      constructor <;> exact ⟨n, n, hyp⟩

/-- Given `rep n₁ a ++ rep n₁ b ++ rep m₁ c = rep n₂ a ++ rep m₂ b ++ rep m₂ c`,
    if `k > 0` and `k ≤ n₁` (or `k ≤ n₂`), the element at position `k-1` in one side
    is `a` but in the other it falls past the `a`-block into `b`/`c`, contradiction. -/
private lemma replicate_abc_nthLe_contradiction
    {k₁ k₂ : ℕ} {a_ : Fin 3}
    (k₁pos : k₁ > 0) (hlt : k₁ > k₂)
    (l₁ l₂ : List (Fin 3))
    (equ : List.replicate k₁ a_ ++ l₁ = List.replicate k₂ a_ ++ l₂)
    (h_l₂ : ∀ x ∈ l₂, x ≠ a_) :
    False := by
  have idx_in_k₁ : k₁ - 1 < (List.replicate k₁ a_).length := by
    rw [List.length_replicate]; exact Nat.sub_lt k₁pos (Nat.succ_pos 0)
  have idx_past_k₂ : (List.replicate k₂ a_).length ≤ k₁ - 1 := by
    rw [List.length_replicate]; exact Nat.le_pred_of_lt hlt
  have idx_in_rhs : k₁ - 1 < (List.replicate k₂ a_ ++ l₂).length := by
    rw [← equ, List.length_append]; linarith [idx_in_k₁]
  have lhs_val : (List.replicate k₁ a_ ++ l₁).nthLe (k₁ - 1)
      (by rw [List.length_append]; linarith [idx_in_k₁]) = a_ := by
    rw [List.nthLe_append idx_in_k₁]
    exact List.nthLe_replicate a_ idx_in_k₁
  have rhs_val := List.nthLe_of_eq equ
    (n := k₁ - 1) (hn := by rw [List.length_append]; linarith [idx_in_k₁])
  rw [lhs_val] at rhs_val
  rw [List.nthLe_append_right idx_past_k₂ idx_in_rhs] at rhs_val
  exact h_l₂ _ (List.nthLe_mem _) rhs_val.symm

/-- In `rep n₁ a ++ rep n₁ b ++ rep m₁ c = rep n₂ a ++ rep m₂ b ++ rep m₂ c`, the
    nthLe-based argument gives `a` on one side and a non-`a` element on the other. -/
private lemma not_mem_bc_of_ne (a_ b_ c_ : Fin 3) (a_neq_b : a_ ≠ b_) (a_neq_c : a_ ≠ c_)
    {m₁ m₂ : ℕ} : ∀ x ∈ List.replicate m₁ b_ ++ List.replicate m₂ c_, x ≠ a_ := by
  intro x hx hxa
  rw [List.mem_append] at hx
  cases hx with
  | inl h => exact a_neq_b (hxa ▸ (List.mem_replicate.mp h).right)
  | inr h => exact a_neq_c (hxa ▸ (List.mem_replicate.mp h).right)

private lemma doubled_le_singled
    (n₁ m₁ n₂ m₂ : ℕ) (n₁pos : n₁ > 0)
    (a_ b_ c_ : Fin 3) (a_neq_b : a_ ≠ b_) (a_neq_c : a_ ≠ c_)
    (equ :
      List.replicate n₁ a_ ++ List.replicate n₁ b_ ++ List.replicate m₁ c_ =
      List.replicate n₂ a_ ++ List.replicate m₂ b_ ++ List.replicate m₂ c_
    ) :
  n₁ ≤ n₂ := by
  by_contra contr
  push_neg at contr
  rw [List.append_assoc, List.append_assoc] at equ
  exact replicate_abc_nthLe_contradiction n₁pos contr _ _ equ
    (not_mem_bc_of_ne a_ b_ c_ a_neq_b a_neq_c)

private lemma doubled_ge_singled
    (n₁ m₁ n₂ m₂ : ℕ) (n₂pos : n₂ > 0)
    (a_ b_ c_ : Fin 3) (a_neq_b : a_ ≠ b_) (a_neq_c : a_ ≠ c_)
    (equ :
      List.replicate n₁ a_ ++ List.replicate n₁ b_ ++ List.replicate m₁ c_ =
      List.replicate n₂ a_ ++ List.replicate m₂ b_ ++ List.replicate m₂ c_
    ) :
  n₁ ≥ n₂ := by
  by_contra contr
  push_neg at contr
  rw [List.append_assoc, List.append_assoc] at equ
  exact replicate_abc_nthLe_contradiction n₂pos contr _ _ equ.symm
    (not_mem_bc_of_ne a_ b_ c_ a_neq_b a_neq_c)



public lemma lang_eq_eq_of_intersection {w : List (Fin 3)} :
  w ∈ lang_eq_any ⊓ lang_any_eq  →  w ∈ lang_eq_eq  :=
by
  rintro ⟨⟨n₁, m₁, w_eq₁⟩, ⟨n₂, m₂, w_eq₂⟩⟩
  have equ := Eq.trans w_eq₁.symm w_eq₂
  by_cases hn₁ : n₁ = 0
  · have hn₂ : n₂ = 0 := by
      by_contra h
      have a_yes : a_ ∈ List.replicate n₂ a_ := List.mem_replicate.mpr ⟨h, rfl⟩
      have a_in_equ := congr_arg (fun lis => a_ ∈ lis) equ
      rw [hn₁] at a_in_equ
      simp [a_yes, List.mem_replicate, List.mem_append, neq_ab, neq_ac] at a_in_equ
    have hm₂ : m₂ = 0 := by
      by_contra h
      have b_yes : b_ ∈ List.replicate m₂ b_ := List.mem_replicate.mpr ⟨h, rfl⟩
      have b_in_equ := congr_arg (fun lis => b_ ∈ lis) equ
      rw [hn₁, hn₂] at b_in_equ
      simp [b_yes, List.mem_replicate, List.mem_append, neq_bc] at b_in_equ
    exact ⟨0, by rw [hn₂, hm₂] at w_eq₂; exact w_eq₂⟩
  have n₁pos : n₁ > 0 := Nat.pos_of_ne_zero hn₁
  have n₂pos : n₂ > 0 := by
    by_contra h; push_neg at h
    rw [Nat.eq_zero_of_le_zero h, List.replicate_zero, List.nil_append] at equ
    have a_in_equ := congr_arg (fun lis => a_ ∈ lis) equ
    simp [List.mem_append, List.mem_replicate, hn₁, neq_ab, neq_ac] at a_in_equ
  have m₂pos : m₂ > 0 := by
    by_contra h; push_neg at h
    rw [Nat.eq_zero_of_le_zero h, List.replicate_zero, List.append_nil] at equ
    have b_in_equ := congr_arg (fun lis => b_ ∈ lis) equ
    simp [List.mem_append, List.mem_replicate, hn₁, neq_ba] at b_in_equ
  have m₁pos : m₁ > 0 := by
    by_contra h; push_neg at h
    rw [Nat.eq_zero_of_le_zero h, List.replicate_zero, List.append_nil] at equ
    have c_in_equ := congr_arg (fun lis => c_ ∈ lis) equ
    simp [List.mem_append, List.mem_replicate, neq_ca, neq_cb, (show m₂ ≠ 0 by omega)] at c_in_equ

  have n_ge := doubled_ge_singled n₁ m₁ n₂ m₂ n₂pos a_ b_ c_ neq_ab neq_ac equ
  have n_le := doubled_le_singled n₁ m₁ n₂ m₂ n₁pos a_ b_ c_ neq_ab neq_ac equ
  have eqn : n₁ = n₂ := le_antisymm n_le n_ge
  -- For the m₁/m₂ comparison, reverse both sides
  have rev : List.replicate m₂ c_ ++ List.replicate m₂ b_ ++ List.replicate n₂ a_ =
             List.replicate m₁ c_ ++ List.replicate n₁ b_ ++ List.replicate n₁ a_ := by
    have := congr_arg List.reverse equ
    repeat rw [List.reverse_append] at this
    simp only [List.reverse_replicate, ← List.append_assoc] at this
    exact this.symm
  have m_ge : m₁ ≥ m₂ :=
    doubled_le_singled m₂ n₂ m₁ n₁ m₂pos c_ b_ a_ neq_cb neq_ca rev
  have m_le : m₁ ≤ m₂ :=
    doubled_ge_singled m₂ n₂ m₁ n₁ m₁pos c_ b_ a_ neq_cb neq_ca rev
  have eqm : m₁ = m₂ := le_antisymm m_le m_ge
  have eq₂ : n₂ = m₂ := by
    have lengs := congr_arg List.length equ
    simp only [List.length_append, List.length_replicate] at lengs
    omega
  rw [eq₂] at w_eq₂
  exact ⟨m₂, w_eq₂⟩

end intersection_inclusions


/-- The class of context-free languages isn't closed under intersection. -/
public theorem nnyCF_of_CF_i_CF : ¬ (∀ L₁ L₂ : Language (Fin 3),
    is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ ⊓ L₂)
) :=
by
  by_contra contra
  specialize contra lang_eq_any lang_any_eq ⟨CF_lang_eq_any, CF_lang_any_eq⟩
  apply notCF_lang_eq_eq
  convert contra
  ext w
  constructor
  · apply intersection_of_lang_eq_eq
  · apply lang_eq_eq_of_intersection

/-- Context-free languages over `Fin 3` are not closed under intersection. -/
theorem CF_notClosedUnderIntersection :
    ¬ ClosedUnderIntersection (α := Fin 3) is_CF := by
  rw [ClosedUnderIntersection]
  have contra := nnyCF_of_CF_i_CF
  grind

private lemma Language.map_inf_injective {α β : Type} {f : α → β} (hf : Function.Injective f)
    (L₁ L₂ : Language α) :
    Language.map f (L₁ ⊓ L₂) = Language.map f L₁ ⊓ Language.map f L₂ := by
  ext w
  constructor
  · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
    exact ⟨⟨v, hv1, rfl⟩, ⟨v, hv2, rfl⟩⟩
  · rintro ⟨⟨v1, hv1, hmap1⟩, ⟨v2, hv2, hmap2⟩⟩
    have heq : v1 = v2 := by
      apply List.map_injective_iff.mpr hf
      rw [hmap1, hmap2]
    subst heq
    exact ⟨v1, ⟨hv1, hv2⟩, hmap1⟩

/-- Context-free languages are not closed under intersection for any type with at least
    3 elements. That is, as long as `α` has at least 3 distinct elements, not all
    intersections of context-free languages over `α` are context-free. -/
public theorem CF_notClosedUnderIntersection_of_three {α : Type}
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ClosedUnderIntersection (α := α) is_CF := by
  intro hclosed
  -- Build an injection Fin 3 → α
  have hf : Function.Injective (fun i : Fin 3 => (![a, b, c] : Fin 3 → α) i) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  set f : Fin 3 → α := fun i => ![a, b, c] i
  -- Transfer the Fin 3 non-closure result
  apply nnyCF_of_CF_i_CF
  intro L₁ L₂ ⟨hL₁, hL₂⟩
  have hfL₁ : is_CF (Language.map f L₁) := CF_of_map_CF f L₁ hL₁
  have hfL₂ : is_CF (Language.map f L₂) := CF_of_map_CF f L₂ hL₂
  have hinter : is_CF (Language.map f L₁ ⊓ Language.map f L₂) :=
    hclosed _ _ hfL₁ hfL₂
  rw [← Language.map_inf_injective hf] at hinter
  exact CF_of_map_injective_CF_rev hf _ hinter

/-- Context-free languages are not closed under intersection for any finite alphabet with
    at least three symbols. -/
theorem CF_notClosedUnderIntersection_of_card {α : Type} [Fintype α]
    (hα : 3 ≤ Fintype.card α) :
    ¬ ClosedUnderIntersection (α := α) is_CF := by
  let π : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let e : Fin 3 ↪ α := (Fin.castLEEmb hα).trans π.symm.toEmbedding
  exact CF_notClosedUnderIntersection_of_three
    (e 0) (e 1) (e 2)
    (fun h => by simpa using e.injective h)
    (fun h => by simpa using e.injective h)
    (fun h => by simpa using e.injective h)

end
