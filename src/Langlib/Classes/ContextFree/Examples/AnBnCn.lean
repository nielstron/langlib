module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Examples.AnBnCn
public import Langlib.Examples.AlphabetABC
public import Langlib.Utilities.ListUtils
import Langlib.Classes.ContextFree.Basics.Elementary
import Langlib.Classes.ContextFree.Basics.Pumping
import Langlib.Utilities.Tactics
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
@[expose]
public section

/-! # `{aⁿbⁿcⁿ}` is not context-free

The language `lang_eq_eq = {aⁿbⁿcⁿ | n ∈ ℕ}` is not context-free. The pumping lemma
(`CF_pumping`) applied to `aⁿ⁺¹bⁿ⁺¹cⁿ⁺¹` yields a decomposition `u v x y z` where `v y`
omits some letter, so pumping unbalances the counts of the other two.
-/

private lemma neq_ab : a_ ≠ b_ := by decide
private lemma neq_ba : b_ ≠ a_ := neq_ab.symm
private lemma neq_ac : a_ ≠ c_ := by decide
private lemma neq_ca : c_ ≠ a_ := neq_ac.symm
private lemma neq_bc : b_ ≠ c_ := by decide
private lemma neq_cb : c_ ≠ b_ := neq_bc.symm

private lemma false_of_uvvxyyz
    {_a _b _c : Fin 3} {n : ℕ} {u v x y z : List (Fin 3)}
    (elimin : ∀ s : Fin 3,  s ≠ _a  →  s ≠ _b  →  s ≠ _c  → False)
    (no_a : _a ∉ v ++ y) (nonempty : (v ++ y).length > 0)
    (counts_ab : ∀ (w : List (Fin 3)), w ∈ lang_eq_eq → List.count_in w _a = List.count_in w _b)
    (counts_ac : ∀ (w : List (Fin 3)), w ∈ lang_eq_eq → List.count_in w _a = List.count_in w _c)
    (counted_a : List.count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _a = n + 1 + List.count_in (v ++ y) _a)
    (counted_b : List.count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _b = n + 1 + List.count_in (v ++ y) _b)
    (counted_c : List.count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _c = n + 1 + List.count_in (v ++ y) _c)
    (pumping : u ++ List.n_times v 2 ++ x ++ List.n_times y 2 ++ z ∈ lang_eq_eq) :
  False :=
by
  have extra_not_a : _b ∈ (v ++ y) ∨ _c ∈ (v ++ y) := by
    let first_letter := (v ++ y).nthLe 0 nonempty
    have first_letter_b_or_c : first_letter = _b ∨ first_letter = _c := by
      have first_letter_not_a : first_letter ≠ _a := by
        by_contra contra
        have yes_a : _a ∈ v ++ y := by
          rw [← contra]
          apply List.nthLe_mem
        exact no_a yes_a
      by_contra contr
      push_neg at contr
      cases contr with
      | intro first_letter_not_b first_letter_not_c =>
          exact elimin ((v ++ y).nthLe 0 nonempty) first_letter_not_a first_letter_not_b
            first_letter_not_c
    cases first_letter_b_or_c with
    | inl first_letter_b =>
        left
        rw [← first_letter_b]
        apply List.nthLe_mem
    | inr first_letter_c =>
        right
        rw [← first_letter_c]
        apply List.nthLe_mem
  have hab := counts_ab (u ++ List.n_times v 2 ++ x ++ List.n_times y 2 ++ z) pumping
  have hac := counts_ac (u ++ List.n_times v 2 ++ x ++ List.n_times y 2 ++ z) pumping
  cases pumping with
  | intro n' pump' =>
      have zero_in_v : List.count_in v _a = 0 := by
        rw [List.mem_append] at no_a; push_neg at no_a
        exact List.count_in_zero_of_notin no_a.left
      have zero_in_y : List.count_in y _a = 0 := by
        rw [List.mem_append] at no_a; push_neg at no_a
        exact List.count_in_zero_of_notin no_a.right
      have count_a : List.count_in (u ++ List.n_times v 2 ++ x ++ List.n_times y 2 ++ z) _a = n + 1 := by
        count_contra
      cases extra_not_a with
      | inl extra_b =>
          have at_least_one_b : List.count_in (v ++ y) _b > 0 :=
            List.count_in_pos_of_in extra_b
          have count_b : List.count_in (u ++ List.n_times v 2 ++ x ++ List.n_times y 2 ++ z) _b > n + 1 := by
            count_contra
          rw [count_a] at hab; rw [hab] at count_b
          exact (lt_irrefl _ count_b)
      | inr extra_c =>
          have at_least_one_c : List.count_in (v ++ y) _c > 0 :=
            List.count_in_pos_of_in extra_c
          have count_c : List.count_in (u ++ List.n_times v 2 ++ x ++ List.n_times y 2 ++ z) _c > n + 1 := by
            count_contra
          rw [count_a] at hac; rw [hac] at count_c
          exact (lt_irrefl _ count_c)

public lemma notCF_lang_eq_eq : ¬ is_CF lang_eq_eq := by
  intro h

  have pum := CF_pumping h
  obtain ⟨n, pump⟩ := pum
  specialize pump (List.replicate (n+1) a_ ++ List.replicate (n+1) b_ ++ List.replicate (n+1) c_)
  specialize pump (by
    use n + 1) (by
    rw [List.length_append, List.length_replicate]
    calc (List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_).length + (n + 1)
        ≥ n + 1 := le_add_self
    _ ≥ n := Nat.le_succ n)
  rcases pump with ⟨u, v, x, y, z, concatenating, nonempty, vxy_short, pumping⟩
  specialize pumping 2

  have not_all_letters : a_ ∉ (v ++ y) ∨ b_ ∉ (v ++ y) ∨ c_ ∉ (v ++ y) := by
    by_contra contr
    push_neg at contr
    rcases contr with ⟨hva, -, hvc⟩
    have vxy_long : (v ++ x ++ y).length > n := by
      by_contra contr
      push_neg at contr
      have total_length_exactly : u.length + (v ++ x ++ y).length + z.length = 3 * n + 3 := by
        have total_length := congr_arg List.length concatenating
        simp only [List.length_append, List.length_replicate] at total_length
        have vxy_len : (v ++ x ++ y).length = v.length + x.length + y.length := by
          simp only [List.length_append]
        rw [vxy_len]
        omega
      have u_short : u.length ≤ n := by
        -- in contradiction with `hva: a_ ∈ v ++ y`
        by_contra u_too_much
        push_neg at u_too_much
        have relaxed_a : a_ ∈ v ++ x ++ y ++ z := by
          cases (List.mem_append.1 hva) with
          | inl a_in_v =>
              rw [List.append_assoc, List.append_assoc, List.mem_append]
              left
              exact a_in_v
          | inr a_in_y =>
              have a_in_yz : a_ ∈ y ++ z := by
                rw [List.mem_append]
                left
                exact a_in_y
              rw [List.append_assoc, List.mem_append]
              right
              exact a_in_yz
        repeat
          rw [List.append_assoc] at concatenating
        rcases List.nthLe_of_mem relaxed_a with ⟨nₐ, hnₐ, h_nthₐ⟩
        obtain ⟨h_nth_a_pr, h_nth_a⟩ :
            ∃ proofoo, (v ++ x ++ y ++ z).nthLe ((nₐ + u.length) - u.length) proofoo = a_ := by
          rw [Nat.add_sub_cancel nₐ u.length]
          exact ⟨hnₐ, h_nthₐ⟩
        have lt_len : (nₐ + u.length) < (u ++ (v ++ x ++ y ++ z)).length := by
          rw [List.length_append]
          linarith
        rw [← List.nthLe_append_right le_add_self lt_len] at h_nth_a
        have orig_nth_le_eq_a :
            ∃ proofoo,
              (List.replicate (n + 1) a_ ++ (List.replicate (n + 1) b_ ++ List.replicate (n + 1) c_)).nthLe
                  (nₐ + u.length) proofoo =
                a_ := by
          have rebracket : u ++ (v ++ (x ++ (y ++ z))) = u ++ (v ++ x ++ y ++ z) := by
            simp only [List.append_assoc]
          rw [concatenating, rebracket]
          exact ⟨lt_len, h_nth_a⟩
        cases orig_nth_le_eq_a with
        | intro rrr_nth_le_eq_a_pr rrr_nth_le_eq_a =>
            rw [@List.nthLe_append_right (Fin 3)
                (List.replicate (n + 1) a_)
                (List.replicate (n + 1) b_ ++ List.replicate (n + 1) c_)
                (nₐ + u.length)
                (by
                  rw [List.length_replicate]
                  calc n + 1 ≤ u.length := u_too_much
                  _ ≤ nₐ + u.length := le_add_self)
                (by
                  rw [concatenating]
                  rw [← List.append_assoc x, ← List.append_assoc v, ← List.append_assoc v]
                  exact lt_len)] at rrr_nth_le_eq_a
            have a_in_rb_rc : a_ ∈ (List.replicate (n + 1) b_ ++ List.replicate (n + 1) c_) := by
              rw [← rrr_nth_le_eq_a]
              apply List.nthLe_mem
            rw [List.mem_append] at a_in_rb_rc
            cases a_in_rb_rc with
            | inl a_in_rb =>
                rw [List.mem_replicate] at a_in_rb
                exact neq_ab a_in_rb.right
            | inr a_in_rc =>
                rw [List.mem_replicate] at a_in_rc
                exact neq_ac a_in_rc.right
      have z_short : z.length ≤ n := by
        have our_bound : 2 * n + 2 < (u ++ v ++ x ++ y).length := by
          have relaxed_c : c_ ∈ u ++ v ++ x ++ y := by
            cases (List.mem_append.1 hvc) with
            | inl c_in_v =>
                have c_in_uv : c_ ∈ u ++ v := by
                  rw [List.mem_append]
                  right
                  exact c_in_v
                rw [List.append_assoc, List.mem_append]
                left
                exact c_in_uv
            | inr c_in_y =>
                rw [List.mem_append]
                right
                exact c_in_y
          have concat_reassoc : List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_ ++ List.replicate (n + 1) c_ = u ++ v ++ x ++ y ++ z := by
            repeat rw [List.append_assoc] at concatenating
            simp only [List.append_assoc]
            exact concatenating
          rcases List.nthLe_of_mem relaxed_c with ⟨m, hm, mth_is_c⟩
          have m_big : m ≥ 2 * n + 2 := by
            have orig_mth_is_c :
                ∃ proofoo,
                  ((List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_) ++ List.replicate (n + 1) c_).nthLe
                      m proofoo =
                    c_ := by
              rw [concat_reassoc]
              have m_small : m < (u ++ v ++ x ++ y ++ z).length := by
                rw [List.length_append]
                linarith
              use m_small
              -- mth_is_c : (u ++ v ++ x ++ y).nthLe m hm = c_
              -- We need to show: ((List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_) ++ List.replicate (n + 1) c_).nthLe m m_small = c_
              -- After substitution concat_reassoc, we get (u ++ v ++ x ++ y ++ z).nthLe m m_small = c_
              -- We need to relate this to (u ++ v ++ x ++ y).nthLe m hm
              have split_uvxyz : (u ++ v ++ x ++ y ++ z) = (u ++ v ++ x ++ y) ++ z := by
                simp only [List.append_assoc]
              have m_small' : m < ((u ++ v ++ x ++ y) ++ z).length := by
                rw [← split_uvxyz]; exact m_small
              rw [List.nthLe_append]
              exact mth_is_c
            cases orig_mth_is_c with
            | intro proof_m mth_is_c =>
                by_contra mle
                push_neg at mle
                have m_lt_len :
                    m < (List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_).length := by
                  simp only [List.length_append, List.length_replicate]
                  omega
                have regroup_for_mth : ((List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_) ++ List.replicate (n + 1) c_).nthLe m proof_m = (List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_).nthLe m m_lt_len := by
                  rw [List.nthLe_append m_lt_len]
                rw [regroup_for_mth] at mth_is_c
                have c_in_ra_rb :
                    c_ ∈ (List.replicate (n + 1) a_ ++ List.replicate (n + 1) b_) := by
                  rw [← mth_is_c]
                  apply List.nthLe_mem
                rw [List.mem_append] at c_in_ra_rb
                cases c_in_ra_rb with
                | inl c_in_ra =>
                    rw [List.mem_replicate] at c_in_ra
                    exact neq_ca c_in_ra.right
                | inr c_in_rb =>
                    rw [List.mem_replicate] at c_in_rb
                    exact neq_cb c_in_rb.right
          linarith
        rw [← List.length_append] at total_length_exactly
        rw [← List.append_assoc] at total_length_exactly
        rw [← List.append_assoc] at total_length_exactly
        linarith
      linarith
    exact not_le_of_gt vxy_long vxy_short

  have counts_ab : ∀ w ∈ lang_eq_eq, List.count_in w a_ = List.count_in w b_ := by
    intro w w_in
    cases w_in with
    | intro w_n w_prop => rw [w_prop]; count_contra
  have counts_ac : ∀ w ∈ lang_eq_eq, List.count_in w a_ = List.count_in w c_ := by
    intro w w_in
    cases w_in with
    | intro w_n w_prop => rw [w_prop]; count_contra
  have counts_bc : ∀ w ∈ lang_eq_eq, List.count_in w b_ = List.count_in w c_ := by
    intro w w_in
    rw [← counts_ab w w_in]
    exact counts_ac w w_in
  have counts_ba : ∀ w ∈ lang_eq_eq, List.count_in w b_ = List.count_in w a_ := by
    intro w w_in
    symm
    exact counts_ab w w_in
  have counts_ca : ∀ w ∈ lang_eq_eq, List.count_in w c_ = List.count_in w a_ := by
    intro w w_in
    symm
    exact counts_ac w w_in
  have counts_cb : ∀ w ∈ lang_eq_eq, List.count_in w c_ = List.count_in w b_ := by
    intro w w_in
    symm
    exact counts_bc w w_in

  have counted_letter : ∀ s,
      List.count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) s =
        List.count_in (List.replicate (n + 1) a_) s + List.count_in (List.replicate (n + 1) b_) s +
          List.count_in (List.replicate (n + 1) c_) s + List.count_in (v ++ y) s := by
    intro s
    rw [← concatenating]
    repeat
      rw [List.count_in_append]
  have counted_a :
      List.count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) a_ =
        n + 1 + List.count_in (v ++ y) a_ := by
    rw [counted_letter]; count_contra
  have counted_b :
      List.count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) b_ =
        n + 1 + List.count_in (v ++ y) b_ := by
    rw [counted_letter]; count_contra
  have counted_c :
      List.count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) c_ =
        n + 1 + List.count_in (v ++ y) c_ := by
    rw [counted_letter]; count_contra

  have elimin_abc : ∀ s : Fin 3, s ≠ a_ → s ≠ b_ → s ≠ c_ → False := by
    intro s hsa hsb hsc
    fin_cases s
    · rw [a_] at hsa
      exact hsa rfl
    · rw [b_] at hsb
      exact hsb rfl
    · rw [c_] at hsc
      exact hsc rfl

  cases not_all_letters with
  | inl no_a =>
      exact false_of_uvvxyyz elimin_abc no_a nonempty counts_ab counts_ac
        counted_a counted_b counted_c pumping
  | inr foo =>
      cases foo with
      | inl no_b =>
          have elimin_bca : ∀ s : Fin 3, s ≠ b_ → s ≠ c_ → s ≠ a_ → False := by
            intro s hsb hsc hsa
            exact elimin_abc s hsa hsb hsc
          exact false_of_uvvxyyz elimin_bca no_b nonempty counts_bc counts_ba
            counted_b counted_c counted_a pumping
      | inr no_c =>
          have elimin_cab : ∀ s : Fin 3, s ≠ c_ → s ≠ a_ → s ≠ b_ → False := by
            intro s hsc hsa hsb
            exact elimin_abc s hsa hsb hsc
          exact false_of_uvvxyyz elimin_cab no_c nonempty counts_ca counts_cb
            counted_c counted_a counted_b pumping

end
