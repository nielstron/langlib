import Mathlib
import Langlib.Classes.ContextFree.Definition
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Utilities.Tactics

/-! # `a^n b^n` as a CFL

This file constructs a context-free grammar for `{a^n b^n}` and proves that the
language is context-free.
-/

open Language List

/-- Context-free grammar for the language `{aⁿbⁿ | n ∈ ℕ}` over `Bool`. -/
def cfg_anbn : CF_grammar Bool where
  nt := Unit
  initial := ()
  rules := [
    ((), [symbol.terminal false, symbol.nonterminal (), symbol.terminal true]),
    ((), [])
  ]

private def sentential_form (w : List (symbol Bool Unit)) : Prop :=
  (∃ n : ℕ, w = List.map symbol.terminal (List.replicate n false) ++
    [symbol.nonterminal ()] ++
    List.map symbol.terminal (List.replicate n true)) ∨
  (∃ n : ℕ, w = List.map symbol.terminal (List.replicate n false ++ List.replicate n true))

private lemma sentential_form_step (w w' : List (symbol Bool Unit))
    (hw : sentential_form w) (ht : CF_transforms cfg_anbn w w') :
    sentential_form w' := by
  rcases hw with ⟨n, rfl⟩ | ⟨n, rfl⟩ <;> simp_all +decide [CF_transforms, cfg_anbn]
  · rcases ht with (⟨x, y, hxy, rfl⟩ | ⟨x, y, hxy, rfl⟩) <;> simp_all +decide [sentential_form]
    · rw [List.append_eq_append_iff] at hxy
      rcases hxy with (⟨as, rfl, h⟩ | ⟨bs, h, h'⟩) <;> simp_all +decide [List.append_eq_append_iff]
      · rcases as with _ | ⟨a, as⟩ <;> simp_all +decide [List.replicate]
        · refine Or.inl ⟨n + 1, Or.inl ⟨[symbol.terminal false], ?_, ?_⟩⟩
          · rw [List.replicate_succ']
          · simpa [h, List.replicate_succ]
        · replace h := congr_arg List.toFinset h.2
          rw [Finset.ext_iff] at h
          specialize h (symbol.nonterminal ())
          aesop
      · rcases bs with _ | ⟨b, bs⟩ <;> simp_all +decide [List.append_eq_append_iff]
        · refine Or.inl ⟨n + 1, ?_⟩
          simp_all +decide [List.replicate]
          exact Or.inl ⟨[symbol.terminal false], by rw [← h]; exact Nat.recOn n (by simp +decide) fun n ihn => by simp +decide [List.replicate] at ihn ⊢; aesop⟩
        · replace h := congr_arg List.toFinset h
          rw [Finset.ext_iff] at h
          specialize h (symbol.nonterminal ())
          aesop
    · rw [List.append_eq_append_iff] at hxy
      rcases hxy with (⟨as, rfl, h⟩ | ⟨bs, h, h'⟩) <;> simp_all +decide [List.append_eq_append_iff]
      · rcases as with _ | ⟨a, as⟩ <;> simp_all +decide [List.replicate]
        · exact Or.inr ⟨n, Or.inl ⟨[], by aesop⟩⟩
        · replace h := congr_arg List.toFinset h.2
          rw [Finset.ext_iff] at h
          specialize h (symbol.nonterminal ())
          aesop
      · rcases bs with _ | ⟨a, bs⟩ <;> simp_all +decide [List.append_assoc]
        · exact Or.inr ⟨n, Or.inl ⟨[], by aesop⟩⟩
        · replace h := congr_arg List.toFinset h
          rw [Finset.ext_iff] at h
          specialize h a
          aesop
  · rcases ht with (⟨x, y, hxy, rfl⟩ | ⟨x, y, hxy, rfl⟩)
    · no_nonterminal (symbol.nonterminal ())
    · no_nonterminal (symbol.nonterminal ())

private lemma sentential_form_of_derives (w : List (symbol Bool Unit))
    (hd : CF_derives cfg_anbn [symbol.nonterminal ()] w) :
    sentential_form w := by
  induction hd with
  | refl => exact Or.inl ⟨0, by simp⟩
  | tail _ ht ih => exact sentential_form_step _ _ ih ht

private lemma CF_language_cfg_anbn_sub_anbn :
    ∀ w, w ∈ CF_language cfg_anbn → w ∈ anbn := by
  intro w hw
  have hsf : sentential_form (List.map symbol.terminal w) :=
    sentential_form_of_derives _ hw
  rcases hsf with ⟨n, hn⟩ | ⟨n, hn⟩
  · exfalso
    have hmem : symbol.nonterminal () ∈ List.map symbol.terminal w := by
      rw [hn]
      simp
    simp at hmem
  ·
    have hinj : Function.Injective (symbol.terminal (T := Bool) (N := Unit)) := by
      intro a b h
      cases h
      rfl
    exact ⟨n, hinj.list_map hn⟩

private lemma anbn_sub_CF_language_cfg_anbn :
    ∀ w, w ∈ anbn → w ∈ CF_language cfg_anbn := by
  intro w hw
  obtain ⟨n, rfl⟩ := hw
  have h_deriv : ∀ n : ℕ, CF_derives cfg_anbn [symbol.nonterminal ()]
      (List.replicate n (symbol.terminal false) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal true)) := by
    intro n
    induction' n with n ih
    · constructor
    ·
      have h_step : CF_derives cfg_anbn
          (List.replicate n (symbol.terminal false) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal true))
          (List.replicate n (symbol.terminal false) ++ [symbol.terminal false, symbol.nonterminal (), symbol.terminal true] ++ List.replicate n (symbol.terminal true)) := by
        apply_rules [CF_deri_of_tran, CF_deri_with_prefix_and_postfix]
        use ((), [symbol.terminal false, symbol.nonterminal (), symbol.terminal true])
        exact ⟨replicate n (symbol.terminal false), replicate n (symbol.terminal true), by simp +decide [cfg_anbn], by simp +decide, by simp +decide⟩
      convert ih.trans h_step using 1
      simp +decide [List.replicate_add]
      exact Nat.recOn n rfl fun n ih => by rw [replicate_succ']; aesop
  have h_final : CF_derives cfg_anbn
      (List.replicate n (symbol.terminal false) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal true))
      (List.replicate n (symbol.terminal false) ++ List.replicate n (symbol.terminal true)) := by
    apply_rules [CF_deri_of_tran, CF_deri_with_prefix_and_postfix]
    use ((), [])
    exact ⟨replicate n (symbol.terminal false), replicate n (symbol.terminal true), by simp +decide [cfg_anbn], by simp +decide, by simp +decide⟩
  apply_rules [CF_deri_of_deri_deri, h_deriv]
  any_goals tauto
  convert CF_deri_self using 1
  aesop

/-- The grammar `cfg_anbn` generates exactly `{aⁿbⁿ}`. -/
theorem CF_language_cfg_anbn : CF_language cfg_anbn = anbn := by
  ext w
  exact ⟨CF_language_cfg_anbn_sub_anbn w, anbn_sub_CF_language_cfg_anbn w⟩

/-- The language `{aⁿbⁿ}` is context-free. -/
theorem anbn_is_CF : is_CF anbn :=
  is_CF_via_cfg_implies_is_CF ⟨cfg_anbn, CF_language_cfg_anbn⟩
