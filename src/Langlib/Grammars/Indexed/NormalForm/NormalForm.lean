module

public import Langlib.Grammars.Indexed.Definition
import Langlib.Grammars.Indexed.NormalForm.FreshStart
import Langlib.Grammars.Indexed.NormalForm.EpsilonElim
import Langlib.Grammars.Indexed.NormalForm.TerminalIsolation
import Langlib.Grammars.Indexed.NormalForm.FlagSeparation
import Langlib.Grammars.Indexed.NormalForm.Binarization
@[expose]
public section


/-! # Normal Form for Indexed Grammars

This file assembles the normal form theorem for indexed grammars following Aho (1968).

An indexed grammar is in **normal form** if every production has one of the four forms:

1. `A → BC` — binary split, no flag consumed, no flag pushed
2. `Af → B` — flag consumption (pop)
3. `A → Bf` — flag push
4. `A → a` — terminal production

and the start symbol does not appear on the right-hand side of any production.

## Main results

- `IndexedGrammar.exists_normalForm` — every ε-free indexed grammar has an equivalent
  grammar in normal form (for non-empty words)

## Proof outline

The proof proceeds by a sequence of language-preserving transformations:

1. **Fresh start** (`FreshStart.lean`, fully proved): introduce a new start symbol
   that does not appear on any right-hand side.
2. **ε-free pass-through** (`EpsilonElim.lean`): use the explicit ε-free hypothesis.
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

/-- Normal-form theorem for ε-free indexed grammars. For every indexed grammar `g`
with no ε-productions, there exists an indexed grammar `g'` in normal form such that
`g'` generates the same non-empty words as `g`. -/
theorem exists_normalForm [Inhabited T] (g : IndexedGrammar T) (hne : g.NoEpsilon') :
    ∃ g' : IndexedGrammar T,
      (∃ _ : DecidableEq g'.nt, g'.IsNormalForm) ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g.Generates w) := by
  -- Step 1: Fresh start — introduce a new start symbol not on any RHS.
  let g₁ := g.freshStart
  have hg₁_lang : ∀ w : List T, w ∈ g₁.Language ↔ w ∈ g.Language :=
    fun w => ⟨freshStart_language_backward g, freshStart_language_forward g⟩
  have hg₁_fresh : g₁.StartNotOnRhs' := freshStart_startNotOnRhs g
  have hg₁_ne : g₁.NoEpsilon' := freshStart_noEpsilon g hne
  -- Step 2: ε-free pass-through
  obtain ⟨g₂, hg₂_ne, hg₂_fresh_of, hg₂_lang⟩ := exists_noEpsilon g₁ hg₁_ne
  have hg₂_fresh : g₂.StartNotOnRhs' := hg₂_fresh_of hg₁_fresh
  -- Step 3: Terminal isolation (fully proved)
  obtain ⟨g₃, hg₃_ne, hg₃_ti, hg₃_fresh_of, hg₃_lang⟩ :=
    exists_terminalsIsolated' g₂ hg₂_ne
  have hg₃_fresh : g₃.StartNotOnRhs' := hg₃_fresh_of hg₂_fresh
  -- Step 4: Flag separation
  obtain ⟨g₄, hg₄_ne, hg₄_ti, hg₄_fs, hg₄_fresh_of, hg₄_lang⟩ :=
    exists_flagsSeparated' g₃ hg₃_ne hg₃_ti
  -- Step 5: Binarization + final NF assembly
  have hg₄_fresh : g₄.StartNotOnRhs' := hg₄_fresh_of hg₃_fresh
  obtain ⟨g₅, hg₅_nf, hg₅_lang⟩ :=
    exists_normalForm_from_separated' g₄ hg₄_ne hg₄_ti hg₄_fs hg₄_fresh
  exact ⟨g₅, hg₅_nf, fun w hw => by
    rw [hg₅_lang w hw, hg₄_lang w hw, hg₃_lang w hw, hg₂_lang w hw]
    exact hg₁_lang w⟩

end IndexedGrammar
