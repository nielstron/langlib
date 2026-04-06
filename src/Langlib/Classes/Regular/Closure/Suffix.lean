import Langlib.Classes.Regular.Closure.Prefix
import Langlib.Classes.Regular.Closure.Complement
import Langlib.Classes.Regular.Closure.Reverse
import Langlib.Classes.Regular.Examples.TopBot

/-! # Regular Closure Under Suffix

This file proves that regular languages are closed under the suffix operation,
via the decomposition `suffixLang L = reverse(prefixLang(reverse L))`, and
shows that the converse fails.

## Strategy

We use the identity `suffixLang L = (prefixLang L.reverse).reverse`
(proved in `LanguageOperations.lean` as `suffixLang_eq_reverse_prefixLang_reverse`),
together with the already-established closure of regular languages under:
- reversal (`Language.isRegular_reverse_iff'`), and
- prefix (`Language.IsRegular.prefixLang`).

## Main declarations

- `Language.IsRegular.suffixLang`
- `Language.not_iff_regular_suffix`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under the suffix operation. -/
theorem IsRegular.suffixLang {L : Language α} (h : L.IsRegular) :
    (suffixLang L).IsRegular := by
  rw [suffixLang_eq_reverse_prefixLang_reverse]
  exact (h.reverse.prefixLang).reverse

private lemma anbn_compl_not_isRegular : ¬ anbnᶜ.IsRegular := by
  intro h
  exact anbn_not_isRegular (Language.isRegular_compl_iff.mp h)

/-- No word of the form `[true] ++ w` belongs to `anbn`. -/
private lemma true_prepend_not_mem_anbn (w : List Bool) :
    [true] ++ w ∉ anbn := by
  rintro ⟨n, hn⟩
  induction n <;> simp_all +decide [List.replicate]

/-- `suffixLang(anbnᶜ) = ⊤`. -/
private lemma suffixLang_anbn_compl_eq_top :
    suffixLang anbnᶜ = ⊤ := by
  ext w
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨[true], true_prepend_not_mem_anbn w⟩

/-- The converse of suffix closure fails. -/
theorem not_iff_regular_suffix :
    ¬ (∀ (L : Language Bool), (suffixLang L).IsRegular ↔ L.IsRegular) := by
  intro h
  have hsuff : (suffixLang anbnᶜ).IsRegular := by
    rw [suffixLang_anbn_compl_eq_top]
    exact isRegular_top
  exact anbn_compl_not_isRegular ((h anbnᶜ).mp hsuff)

end Language
