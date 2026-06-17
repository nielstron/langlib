module

public import Mathlib
public import Langlib.Grammars.Indexed.Definition
@[expose]
public section

/-! # ε-Free Indexed Grammars

This file records the local interface used by the normal-form pipeline once an
indexed grammar is already known to have no ε-productions.

The full ε-elimination construction for indexed grammars is substantially more
delicate than the context-free version because nullability can depend on the
current stack. The proved theorem below is intentionally the identity
transformation under an explicit `NoEpsilon'` hypothesis.

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

/-- If a grammar is already ε-free, it is an ε-free equivalent of itself. -/
theorem exists_noEpsilon (g : IndexedGrammar T) (hne : g.NoEpsilon') :
    ∃ g' : IndexedGrammar T,
      g'.NoEpsilon' ∧
      (g.StartNotOnRhs' → g'.StartNotOnRhs') ∧
      ∀ w : List T, w ≠ [] → (g'.Generates w ↔ g.Generates w) := by
  exact ⟨g, hne, fun h => h, fun _ _ => Iff.rfl⟩

end EpsilonElim

end IndexedGrammar
