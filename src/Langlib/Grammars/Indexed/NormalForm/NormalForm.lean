import Mathlib
import Langlib.Grammars.Indexed.Definition
import Langlib.Grammars.Indexed.NormalForm.FreshStart
import Langlib.Grammars.Indexed.NormalForm.EpsilonElim
import Langlib.Grammars.Indexed.NormalForm.TerminalIsolation
import Langlib.Grammars.Indexed.NormalForm.FlagSeparation
import Langlib.Grammars.Indexed.NormalForm.Binarization

/-! # Normal Form for Indexed Grammars

This file assembles the normal form theorem for indexed grammars following Aho (1968).

An indexed grammar is in **normal form** if every production has one of the four forms:

1. `A → BC` — binary split, no flag consumed, no flag pushed
2. `Af → B` — flag consumption (pop)
3. `A → Bf` — flag push
4. `A → a` — terminal production

and the start symbol does not appear on the right-hand side of any production.

## Main results

- `IndexedGrammar.exists_normalForm` — **Aho's Normal Form Theorem**: every indexed
  grammar has an equivalent grammar in normal form (for non-empty words)

## Proof outline

The proof proceeds by a sequence of language-preserving transformations:

1. **Fresh start** (`FreshStart.lean`, fully proved): introduce a new start symbol
   that does not appear on any right-hand side.
2. **ε-elimination** (`EpsilonElim.lean`): remove productions with empty right-hand sides,
   while preserving the language on non-empty words.
3. **Terminal isolation** (`TerminalIsolation.lean`, fully proved): replace terminals in
   multi-symbol right-hand sides with dedicated nonterminals.
4. **Flag separation** (`FlagSeparation.lean`): split rules with complex flag operations.
5. **Binarization** (`Binarization.lean`): replace right-hand sides of length ≥ 3 with
   chains of binary rules.

## References

* A. V. Aho, "Indexed grammars — an extension of context-free grammars", *JACM* 15(4), 1968.
-/

open List

variable {T : Type}

namespace IndexedGrammar

/-! ## Aho's Normal Form Theorem -/

/-- **Aho's Normal Form Theorem** (1968): For every indexed grammar `g`, there exists an
indexed grammar `g'` in normal form such that `g'` generates the same non-empty words
as `g`. That is, for all `w ≠ []`, `w ∈ L(g') ↔ w ∈ L(g)`.

The proof constructs `g'` by composing the five grammar transformations described above.
Steps 1 (fresh start) and 3 (terminal isolation) are fully proved. -/
theorem exists_normalForm [Inhabited T] (g : IndexedGrammar T) :
    ∃ g' : IndexedGrammar T,
      (∃ _ : DecidableEq g'.nt, g'.IsNormalForm) ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g.Generates w) := by
  -- Step 1: Fresh start — introduce a new start symbol not on any RHS.
  let g₁ := g.freshStart
  have hg₁_lang : ∀ w : List T, w ∈ g₁.Language ↔ w ∈ g.Language :=
    fun w => ⟨freshStart_language_backward g, freshStart_language_forward g⟩
  -- Step 2: ε-elimination
  obtain ⟨g₂, hg₂_ne, hg₂_lang⟩ := exists_noEpsilon g₁
  -- Step 3: Terminal isolation (fully proved)
  obtain ⟨g₃, hg₃_ne, hg₃_ti, hg₃_lang⟩ := exists_terminalsIsolated' g₂ hg₂_ne
  -- Step 4: Flag separation
  obtain ⟨g₄, hg₄_ne, hg₄_ti, hg₄_fs, hg₄_lang⟩ :=
    exists_flagsSeparated' g₃ hg₃_ne hg₃_ti
  -- Step 5: Binarization + final NF assembly
  have hg₄_fresh : g₄.StartNotOnRhs' := by sorry
  obtain ⟨g₅, hg₅_nf, hg₅_lang⟩ :=
    exists_normalForm_from_separated' g₄ hg₄_ne hg₄_ti hg₄_fs hg₄_fresh
  exact ⟨g₅, hg₅_nf, fun w hw => by
    rw [hg₅_lang w hw, hg₄_lang w hw, hg₃_lang w hw, hg₂_lang w hw]
    exact hg₁_lang w⟩

end IndexedGrammar
