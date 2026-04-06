import Langlib.Classes.Regular.Closure.Prefix
import Langlib.Classes.Regular.Closure.Reverse

/-! # Regular Closure Under Suffix

This file proves that regular languages are closed under the suffix operation,
via the decomposition `suffixLang L = reverse(prefixLang(reverse L))`.

## Strategy

We use the identity `suffixLang L = (prefixLang L.reverse).reverse`
(proved in `LanguageOperations.lean` as `suffixLang_eq_reverse_prefixLang_reverse`),
together with the already-established closure of regular languages under:
- reversal (`Language.isRegular_reverse_iff'`), and
- prefix (`Language.IsRegular.prefixLang`).

## Main declarations

- `Language.IsRegular.suffixLang`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under the suffix operation. -/
theorem IsRegular.suffixLang {L : Language α} (h : L.IsRegular) :
    (suffixLang L).IsRegular := by
  rw [suffixLang_eq_reverse_prefixLang_reverse]
  exact (h.reverse.prefixLang).reverse

end Language
