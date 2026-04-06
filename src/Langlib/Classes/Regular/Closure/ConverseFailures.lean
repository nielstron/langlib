import Mathlib
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Closure.Complement
import Langlib.Utilities.LanguageOperations

/-! # Regular Closure Converses Fail

This file proves that the closure properties of regular languages under union,
intersection, prefix, and suffix are strict implications, not biconditionals.

That is, while:
- `L₁.IsRegular ∧ L₂.IsRegular → (L₁ + L₂).IsRegular` (closure under union),
- `L₁.IsRegular ∧ L₂.IsRegular → (L₁ ⊓ L₂).IsRegular` (closure under intersection),
- `L.IsRegular → (prefixLang L).IsRegular`,
- `L.IsRegular → (suffixLang L).IsRegular`,

the converses of all four fail.

## Proof sketch

All counterexamples derive from the non-regularity of `anbn` (see `NonRegular.lean`).

- **Union**: `anbn + anbnᶜ = ⊤` is regular, but `anbn` is not.
- **Intersection**: `anbn ⊓ ⊥ = ⊥` is regular, but `anbn` is not.
- **Prefix**: `prefixLang(anbnᶜ) = ⊤` is regular (since for any `w`, `w ++ [false] ∉ anbn`),
  but `anbnᶜ` is not regular.
- **Suffix**: `suffixLang(anbnᶜ) = ⊤` is regular (since for any `w`, `[true] ++ w ∉ anbn`),
  but `anbnᶜ` is not regular.

## Main declarations

- `Language.not_iff_regular_union`
- `Language.not_iff_regular_intersection`
- `Language.not_iff_regular_prefix`
- `Language.not_iff_regular_suffix`
-/

open Language List

namespace Language

/-- The empty language is regular (witnessed by a DFA that rejects everything). -/
private lemma isRegular_bot : (⊥ : Language Bool).IsRegular := by
  rw [isRegular_iff]
  exact ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, by
    ext w; simp [DFA.mem_accepts, DFA.eval]; exact fun a => a.elim⟩

/-- The universal language is regular (witnessed by a DFA that accepts everything). -/
private lemma isRegular_top : (⊤ : Language Bool).IsRegular := by
  rw [isRegular_iff]
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), (), Set.univ⟩, ?_⟩
  ext w; constructor
  · intro _; trivial
  · intro _; simp [DFA.mem_accepts, DFA.eval, Set.mem_univ]

/-- The complement of `anbn` is not regular. -/
private lemma anbn_compl_not_isRegular : ¬ anbnᶜ.IsRegular := by
  intro h
  exact anbn_not_isRegular (Language.isRegular_compl_iff.mp h)

/-- No word of the form `w ++ [false]` belongs to `anbn`. -/
private lemma append_false_not_mem_anbn (w : List Bool) :
    w ++ [false] ∉ anbn := by
  by_contra h_contra;
  obtain ⟨ n, hn ⟩ := h_contra;
  replace hn := congr_arg List.reverse hn ; simp_all +decide [ List.reverse_append ];
  cases n <;> simp_all +decide [ List.replicate ]

/-- No word of the form `[true] ++ w` belongs to `anbn`. -/
private lemma true_prepend_not_mem_anbn (w : List Bool) :
    [true] ++ w ∉ anbn := by
  rintro ⟨ n, hn ⟩ ; induction n <;> simp_all +decide [ List.replicate ]

/-- `prefixLang(anbnᶜ) = ⊤`. -/
private lemma prefixLang_anbn_compl_eq_top :
    prefixLang anbnᶜ = ⊤ := by
  ext w; constructor
  · intro _; trivial
  · intro _
    exact ⟨[false], append_false_not_mem_anbn w⟩

/-- `suffixLang(anbnᶜ) = ⊤`. -/
private lemma suffixLang_anbn_compl_eq_top :
    suffixLang anbnᶜ = ⊤ := by
  ext w; constructor
  · intro _; trivial
  · intro _
    exact ⟨[true], true_prepend_not_mem_anbn w⟩

/-- The converse of union closure fails: there exist languages where `L₁ + L₂` is regular
    but not both `L₁` and `L₂` are regular. -/
theorem not_iff_regular_union :
    ¬ (∀ (L₁ L₂ : Language Bool), (L₁ + L₂).IsRegular ↔ (L₁.IsRegular ∧ L₂.IsRegular)) := by
  intro h
  have hunion : (anbn + anbnᶜ).IsRegular := by
    have : anbn + anbnᶜ = ⊤ := sup_compl_eq_top
    rw [this]; exact isRegular_top
  exact anbn_not_isRegular ((h anbn anbnᶜ).mp hunion).1

/-- The converse of intersection closure fails: there exist languages where `L₁ ⊓ L₂` is regular
    but not both `L₁` and `L₂` are regular. -/
theorem not_iff_regular_intersection :
    ¬ (∀ (L₁ L₂ : Language Bool), (L₁ ⊓ L₂).IsRegular ↔ (L₁.IsRegular ∧ L₂.IsRegular)) := by
  intro h
  have hinf : (anbn ⊓ ⊥).IsRegular := by
    have : anbn ⊓ (⊥ : Language Bool) = ⊥ := by simp
    rw [this]; exact isRegular_bot
  exact anbn_not_isRegular ((h anbn ⊥).mp hinf).1

/-- The converse of prefix closure fails: there exists a language where `prefixLang L` is regular
    but `L` is not regular. -/
theorem not_iff_regular_prefix :
    ¬ (∀ (L : Language Bool), (prefixLang L).IsRegular ↔ L.IsRegular) := by
  intro h
  have hpref : (prefixLang anbnᶜ).IsRegular := by
    rw [prefixLang_anbn_compl_eq_top]; exact isRegular_top
  exact anbn_compl_not_isRegular ((h anbnᶜ).mp hpref)

/-- The converse of suffix closure fails: there exists a language where `suffixLang L` is regular
    but `L` is not regular. -/
theorem not_iff_regular_suffix :
    ¬ (∀ (L : Language Bool), (suffixLang L).IsRegular ↔ L.IsRegular) := by
  intro h
  have hsuff : (suffixLang anbnᶜ).IsRegular := by
    rw [suffixLang_anbn_compl_eq_top]; exact isRegular_top
  exact anbn_compl_not_isRegular ((h anbnᶜ).mp hsuff)

end Language