import Langlib.Classes.RecursivelyEnumerable.Decidability.Helper

/-! # Undecidability of Equivalence for RE Languages

This file proves that equivalence cannot be decided for recursively enumerable (RE)
languages. More precisely, there is no computable predicate that decides whether two
codes compute the same partial function.

The proof proceeds in two steps:

1. **Fixed-reference undecidability** (`RE_equivalence_undecidable_fixed`): By Rice's
   theorem, the predicate "does code `c` compute the same function as `Code.zero`?"
   is not computable. The property `{f | f = Code.zero.eval}` is non-trivial because
   `pure 0` satisfies it while `fun _ ↦ Part.none` does not.

2. **General equivalence undecidability** (`RE_equivalence_undecidable`): If the binary
   equivalence predicate on `Code × Code` were computable, we could fix one argument
   to `Code.zero` and obtain a computable unary predicate, contradicting step 1.

## Main results

- `RE_equivalence_undecidable_fixed` — comparing against a fixed code is undecidable.
- `RE_equivalence_undecidable` — equivalence of two codes is undecidable.
-/

open Nat.Partrec

/-- Comparing any code against a fixed code (`Code.zero`) is undecidable.

This is an instance of Rice's theorem: the semantic property
`{f | f = Code.zero.eval}` is non-trivial. -/
theorem RE_equivalence_undecidable_fixed :
    ¬ComputablePred (fun c : Code => c.eval = Code.zero.eval) := by
  intro h
  have rice := ComputablePred.rice {f : ℕ →. ℕ | f = Code.zero.eval}
  have h1 : ComputablePred (fun c : Code => c.eval ∈ {f : ℕ →. ℕ | f = Code.zero.eval}) := by
    convert h using 1
  -- The everywhere-undefined function is not equal to the constant zero function
  have none_ne : (fun (_ : ℕ) => (Part.none : Part ℕ)) ∉ {f : ℕ →. ℕ | f = Code.zero.eval} := by
    intro heq
    exact absurd (congr_fun heq 0 ▸ trivial : (Part.none : Part ℕ).Dom) Part.not_none_dom
  -- Rice: Code.zero.eval ∈ C  ⟹  (fun _ => Part.none) ∈ C, contradiction.
  exact none_ne (rice h1 Nat.Partrec.zero Nat.Partrec.none (by rfl))

/-- **Equivalence is undecidable for RE languages.**

There is no algorithm that, given two codes `c₁` and `c₂` for partial-recursive
functions, decides whether `c₁` and `c₂` compute the same function.

*Proof.* If such an algorithm existed, fixing the second argument to `Code.zero`
would yield a computable predicate deciding `c.eval = Code.zero.eval`, contradicting
`RE_equivalence_undecidable_fixed`. -/
theorem RE_equivalence_undecidable :
    ¬ComputablePred (fun p : Code × Code => p.1.eval = p.2.eval) := by
  intro ⟨D, hD⟩
  apply RE_equivalence_undecidable_fixed
  -- Fix the second component to Code.zero
  exact ⟨fun c => D (c, Code.zero),
         hD.comp (Computable.pair Computable.id (Computable.const Code.zero))⟩

/-- Equivalence for RE codes is not uniformly computable. -/
theorem recursivelyEnumerable_computableEquivalence_undecidable :
    ¬ComputableEquivalence partrecCodeGraphLanguageOf := by
  intro h
  apply RE_equivalence_undecidable
  unfold ComputableEquivalence at h
  exact h.of_eq fun p => partrecCodeGraphLanguage_eq_iff p
