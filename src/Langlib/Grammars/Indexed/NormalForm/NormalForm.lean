import Mathlib
import Langlib.Grammars.Indexed.Definition

/-! # Normal Form for Indexed Grammars

This file defines the normal form for indexed grammars following Aho (1968), and states
the equivalence theorem that every indexed grammar can be converted to an equivalent
one in normal form.

An indexed grammar is in **normal form** if:
1. The start symbol does not appear on the right-hand side of any production.
2. There are no ε-productions (except possibly S → ε).
3. Each production has one of the four forms:
   - `A → BC` (binary split, no flag consumed)
   - `Af → B` (flag consumption)
   - `A → Bf` (flag push)
   - `A → a` (terminal production)

## References

* A. V. Aho, "Indexed grammars — an extension of context-free grammars", *JACM* 15(4), 1968.
-/

open List

variable {T : Type}

namespace IndexedGrammar

/-- A production rule is in normal form with respect to a start symbol `s` if it has one of
the four canonical forms:
- `A → BC` (binary split)
- `Af → B` (flag consumption)
- `A → Bf` (flag push)
- `A → a` (terminal production)
and no nonterminal on the right-hand side is the start symbol `s`. -/
def IRule.IsNF [DecidableEq N] (r : IRule T N F) (s : N) : Prop :=
  -- A → BC
  (r.consume = none ∧
    ∃ B C : N, r.rhs = [IRhsSymbol.nonterminal B none, IRhsSymbol.nonterminal C none] ∧
      B ≠ s ∧ C ≠ s) ∨
  -- Af → B
  (∃ f : F, r.consume = some f ∧
    ∃ B : N, r.rhs = [IRhsSymbol.nonterminal B none] ∧ B ≠ s) ∨
  -- A → Bf
  (r.consume = none ∧
    ∃ B : N, ∃ f : F, r.rhs = [IRhsSymbol.nonterminal B (some f)] ∧ B ≠ s) ∨
  -- A → a
  (r.consume = none ∧ ∃ a : T, r.rhs = [IRhsSymbol.terminal a])

/-- An indexed grammar is in **normal form** if every production rule is in normal form
with respect to the start symbol. -/
def IsNormalForm (g : IndexedGrammar T) [DecidableEq g.nt] : Prop :=
  ∀ r ∈ g.rules, IRule.IsNF r g.initial

/- **Aho's Normal Form Theorem** (1968): Every indexed grammar can be converted to an
equivalent grammar in normal form. The proof involves:
1. Eliminating ε-productions
2. Eliminating unit productions
3. Removing the start symbol from right-hand sides
4. Converting remaining productions to binary form

This is a standard result in formal language theory.
theorem exists_normalForm (g : IndexedGrammar T) :
    ∃ g' : IndexedGrammar T,
      (∃ _ : DecidableEq g'.nt, g'.IsNormalForm) ∧
      g'.Language = g.Language := by

 -/

end IndexedGrammar
