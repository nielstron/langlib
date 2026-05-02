import Mathlib
import Langlib.Grammars.Indexed.Definition

/-! # ε-Elimination for Indexed Grammars

This file states the ε-elimination theorem for indexed grammars: every indexed grammar
can be transformed into one with no ε-productions while preserving the generated
language on non-empty words.

This is Step 2 of Aho's Normal Form theorem for indexed grammars.

## Construction outline

The correct ε-elimination for indexed grammars (unlike the simpler CFG version)
requires careful handling because nullability depends on the stack contents:

1. Compute the set of *nullable* nonterminal-stack configurations: those `(A, σ)` such
   that `g` can derive `[]` from `[indexed A σ]`.
2. For each rule `A[f·σ] → X₁ X₂ ⋯ Xₖ` (or `A[σ] → X₁ ⋯ Xₖ`), create all
   variants where subsets of nullable nonterminals on the RHS are dropped.
3. Remove all resulting rules with empty RHS.

Simply filtering out ε-rules is **insufficient** — it leaves nonterminals that can
only derive ε as dead ends, potentially losing words from the language. The rule
variant generation in step 2 compensates for this.

## References

* A. V. Aho, "Indexed grammars — an extension of context-free grammars", *JACM* 15(4), 1968.
-/

open List Relation

variable {T : Type}

namespace IndexedGrammar

section EpsilonElim

/-- A nonterminal `A` with stack `σ` is *nullable* if `g` can derive `[]` from
    `[indexed A σ]`. -/
def IsNullable (g : IndexedGrammar T) (A : g.nt) (σ : List g.flag) : Prop :=
  g.Derives [ISym.indexed A σ] []

/-- **ε-Elimination Theorem**: For any indexed grammar, there exists an equivalent
grammar with no ε-productions, preserving the language on non-empty words.

The proof constructs the ε-free grammar by:
1. Computing nullable nonterminal-stack configurations via a fixed point.
2. For each rule, generating all variants with nullable RHS nonterminals optionally dropped.
3. Filtering out the resulting ε-productions.

The forward direction (new grammar ⊆ original language) follows because each new rule
corresponds to an original rule with some nullable nonterminals removed, and those
nonterminals could derive ε in the original grammar.

The backward direction (original language on non-empty words ⊆ new grammar) proceeds
by induction on the derivation length, showing that any ε-rule application can be
"absorbed" into an earlier rule by using an appropriate variant. -/
theorem exists_noEpsilon (g : IndexedGrammar T) :
    ∃ g' : IndexedGrammar T,
      g'.NoEpsilon' ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g.Generates w) := by
  sorry

end EpsilonElim

end IndexedGrammar
