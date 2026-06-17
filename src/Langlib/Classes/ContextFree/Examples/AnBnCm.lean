module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Examples.AnBnCm
public import Langlib.Examples.AlphabetABC
import Langlib.Classes.ContextFree.Basics.Elementary
import Langlib.Classes.ContextFree.Closure.Concatenation
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
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

/-! # `{aⁿbⁿcᵐ}` is context-free

The language `lang_eq_any = {aⁿbⁿcᵐ | n,m ∈ ℕ}` is context-free, presented as the
concatenation of the context-free factors `{aⁿbⁿ}` and `{cᵐ}`.

`lang_aux_ab` (the `{aⁿbⁿ}` factor over `Fin 3`) and its context-freeness are exposed
because the witness `{aⁿbᵐcᵐ}` reuses them via a letter permutation; see
`Langlib.Classes.ContextFree.Examples.AnBmCm`.
-/

private def a : symbol (Fin 3) (Fin 1) := symbol.terminal a_
private def b : symbol (Fin 3) (Fin 1) := symbol.terminal b_

/-- The `{aⁿbⁿ}` factor over the `Fin 3` alphabet. -/
public def lang_aux_ab : Language (Fin 3) :=
fun w => ∃ n : ℕ, w = List.replicate n a_ ++ List.replicate n b_

public lemma CF_lang_aux_ab : is_CF lang_aux_ab := by
  let S_ : Fin 1 := 0
  let S : symbol (Fin 3) (Fin 1) := symbol.nonterminal S_
  let g := CF_grammar.mk
    (Fin 1)
    S_
    [
      (S_, [a, S, b]),
      (S_, ([] : List (symbol (Fin 3) (Fin 1))))
    ]
  apply is_CF_via_cfg_implies_is_CF
  refine ⟨g, ?_⟩
  apply Set.eq_of_subset_of_subset
  · intro w ass
    change CF_derives g [S] (List.map symbol.terminal w) at ass
    have indu :
        ∀ v : List (symbol (Fin 3) (Fin 1)),
          CF_derives g [S] v →
            ∃ n : ℕ,
              v = List.replicate n a ++ List.replicate n b ∨
                v = List.replicate n a ++ [S] ++ List.replicate n b := by
      intro v hyp
      induction hyp with
      | refl =>
          use 0
          right
          rfl
      | tail u' orig hyp_ih =>
          rcases orig with ⟨r, p, q, rin, bef, aft⟩
          cases hyp_ih with
          | intro k ih =>
              cases ih with
              | inl ih =>
                  exfalso
                  rw [ih] at bef
                  have yes_in : symbol.nonterminal r.fst ∈ p ++ [symbol.nonterminal r.fst] ++ q := by
                    apply List.mem_append_left
                    apply List.mem_append_right
                    apply List.mem_cons_self
                  have not_in : symbol.nonterminal r.fst ∉ List.replicate k a ++ List.replicate k b := by
                    rw [List.mem_append]
                    push_neg
                    constructor <;>
                      · rw [List.mem_replicate]
                        push_neg
                        intro trash
                        tauto
                  rw [bef] at not_in
                  exact not_in yes_in
              | inr ih =>
                  have both_rule_rewrite_S : symbol.nonterminal r.fst = S := by
                    cases rin with
                    | head =>
                        rfl
                    | tail _ rin =>
                        cases rin with
                        | head =>
                            rfl
                        | tail _ rin =>
                            cases rin
                  rw [bef] at ih
                  rw [both_rule_rewrite_S] at ih
                  have p_len : p.length = k := by
                    by_contra contra
                    have kth_eq := congr_fun (congr_arg List.nth ih) p.length
                    have plengthth_is_S : (p ++ [S] ++ q).nth p.length = some S := by
                      rw [List.append_assoc]
                      rw [List.nth_append_right (le_of_eq rfl)]
                      · rw [Nat.sub_self]
                        rfl
                    rw [plengthth_is_S] at kth_eq
                    cases lt_or_gt_of_ne contra with
                    | inl h =>
                        have plengthth_is_a :
                            (List.replicate k a ++ [S] ++ List.replicate k b).nth p.length =
                              some a := by
                          rw [List.append_assoc]
                          have plength_small : p.length < (List.replicate k a).length := by
                            rw [List.length_replicate]
                            exact h
                          rw [List.nth_append plength_small]
                          rw [List.nthLe_nth plength_small]
                          apply congr_arg
                          exact List.nthLe_replicate a plength_small
                        rw [plengthth_is_a] at kth_eq
                        have S_neq_a : S ≠ a := by
                          tauto
                        rw [Option.some_inj] at kth_eq
                        exact S_neq_a kth_eq
                    | inr h =>
                        have plengthth_is_b :
                            (List.replicate k a ++ [S] ++ List.replicate k b).nth p.length =
                              some b := by
                          have plength_big : (List.replicate k a ++ [S]).length ≤ p.length := by
                            rw [List.length_append, List.length_replicate]
                            exact Nat.succ_le_iff.mpr h
                          rw [List.nth_append_right plength_big]
                          have len_within_list :
                              p.length - (List.replicate k a ++ [S]).length < (List.replicate k b).length := by
                            have ihlen := congr_arg List.length ih
                            simp only [List.length_replicate, List.length_append, List.length_singleton] at *
                            have ihlen' : p.length + 1 ≤ k + 1 + k := by
                              exact Nat.le.intro ihlen
                            have ihlen'' : p.length < k + 1 + k := by
                              exact Nat.succ_le_iff.mp ihlen'
                            rw [← tsub_lt_iff_left plength_big] at ihlen''
                            exact ihlen''
                          rw [List.nthLe_nth len_within_list]
                          apply congr_arg
                          exact List.nthLe_replicate b len_within_list
                        rw [plengthth_is_b] at kth_eq
                        have S_neq_b : S ≠ b := by
                          tauto
                        rw [Option.some_inj] at kth_eq
                        exact S_neq_b kth_eq
                  have ihl_len : (p ++ [symbol.nonterminal S_]).length = k + 1 := by
                    rw [List.length_append, p_len]
                    rfl
                  have ihr_len : (List.replicate k a ++ [S]).length = k + 1 := by
                    rw [List.length_append, List.length_replicate]
                    rfl
                  have qb : q = List.replicate k b := by
                    apply List.append_inj_right ih
                    rw [ihl_len, ihr_len]
                  have ih_reduced : p ++ [symbol.nonterminal S_] = List.replicate k a ++ [S] := by
                    rw [qb] at ih
                    rw [List.append_left_inj] at ih
                    exact ih
                  have pa : p = List.replicate k a := by
                    rw [List.append_left_inj] at ih_reduced
                    exact ih_reduced
                  cases rin with
                  | head =>
                      use k + 1
                      right
                      rw [aft]
                      -- In head case, r = (S_, [a, S, b])
                      rw [pa, qb]
                      rw [List.replicate_succ_eq_append_singleton]
                      rw [List.replicate_succ_eq_singleton_append]
                      simp
                  | tail _ rin =>
                      cases rin with
                      | head =>
                          use k
                          left
                          rw [aft, List.append_nil, pa, qb]
                      | tail _ rin =>
                          nomatch rin
    cases indu (List.map symbol.terminal w) ass with
    | intro n instantiated =>
        clear indu
        cases instantiated with
        | inl instantiated =>
            use n

            have foo := congr_arg (List.filterMap (
              λ z : symbol (Fin 3) (Fin 1) =>
                match z with
                | symbol.terminal t => some t
                | symbol.nonterminal _ => none
            )) instantiated
            simp only [List.filterMap_append, a, b] at foo

            have filterMap_replicate_terminal : ∀ (n : ℕ) (t : Fin 3),
                List.filterMap (fun z : symbol (Fin 3) (Fin 1) => match z with | symbol.terminal t => some t | symbol.nonterminal _ => none)
                  (List.replicate n (symbol.terminal t)) = List.replicate n t := by
              intro n t
              induction n with
              | zero => rfl
              | succ n ih => simp [List.replicate, ih]

            have filterMap_map_terminal : ∀ (l : List (Fin 3)),
                List.filterMap (fun z : symbol (Fin 3) (Fin 1) => match z with | symbol.terminal t => some t | symbol.nonterminal _ => none)
                  (List.map symbol.terminal l) = l := by
              intro l
              induction l with
              | nil => rfl
              | cons h t ih => simp [List.map, ih]

            rw [filterMap_map_terminal w, filterMap_replicate_terminal n a_, filterMap_replicate_terminal n b_] at foo
            exact foo
        | inr instantiated =>
            exfalso
            have S_in : S ∈ List.map symbol.terminal w := by
              rw [instantiated]
              apply List.mem_append_left
              apply List.mem_append_right
              exact List.mem_cons_self
            simp [S] at S_in
  · intro w ass
    obtain ⟨n, hw⟩ := ass
    change CF_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w)
    rw [hw, List.map_append, List.map_replicate, List.map_replicate, ←a, ←b]
    clear hw
    induction n with
    | zero =>
      convert_to CF_derives g [symbol.nonterminal g.initial] []
      apply CF_deri_of_tran
      use (S_, ([] : List (symbol (Fin 3) (Fin 1))))
      refine ⟨[], [], ?_, rfl, rfl⟩
      simp [g]
    | succ n ih =>
      convert_to
        CF_derives g
          [symbol.nonterminal g.initial]
          (List.map
            symbol.terminal
            ([a_] ++ (List.replicate n a_ ++ List.replicate n b_) ++ [b_])
          )
      · convert_to
          List.replicate (1 + n) a ++ List.replicate (n + 1) b =
          List.map symbol.terminal ([a_] ++ (List.replicate n a_ ++ List.replicate n b_) ++ [b_])
        · rw [add_comm]
        rw [
          List.map_append_append,
          List.map_singleton,
          List.map_singleton,
          List.replicate_add,
          List.replicate_add,
          a, b
        ]
        simp only [List.replicate, List.append_assoc, List.map_append, List.map_replicate]
      apply CF_deri_of_tran_deri
      · use (S_, [a, S, b])
        refine ⟨[], [], ?_, rfl, rfl⟩
        simp [g]
      rw [List.map_append_append]
      change
        CF_derives g
          ([a] ++ [S] ++ [b])
          ([a] ++ List.map symbol.terminal (List.replicate n a_ ++ List.replicate n b_) ++ [b])
      deri_context
      convert ih
      rw [List.map_append, List.map_replicate, List.map_replicate, a, b]

private def lang_aux_c : Language (Fin 3) :=
fun w => ∃ n : ℕ, w = List.replicate n c_

private lemma CF_lang_aux_c : is_CF lang_aux_c := by
  apply is_CF_via_cfg_implies_is_CF
  refine ⟨cfg_symbol_star c_, ?_⟩
  unfold lang_aux_c
  apply language_of_cfg_symbol_star

public lemma CF_lang_eq_any : is_CF lang_eq_any := by
  have concatenated : lang_eq_any = lang_aux_ab * lang_aux_c := by
    ext1 w
    constructor
    · rintro ⟨n, m, hnm⟩
      rw [Language.mem_mul]
      exact ⟨_, ⟨n, rfl⟩, _, ⟨m, rfl⟩, hnm.symm⟩
    · intro hmem
      rw [Language.mem_mul] at hmem
      obtain ⟨u, ⟨n, u_eq⟩, v, ⟨m, v_eq⟩, eq_w⟩ := hmem
      use n, m
      rw [← eq_w, ← u_eq, ← v_eq]
  rw [concatenated]
  apply CF_of_CF_c_CF
  exact And.intro CF_lang_aux_ab CF_lang_aux_c

end
