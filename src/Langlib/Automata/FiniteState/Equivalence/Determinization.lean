module

public import Langlib.Automata.FiniteState.Definition
public import Mathlib.Computability.NFA

@[expose]
public section

/-!
# Nondeterministic and Deterministic Finite Automata

This file packages Mathlib's subset construction as a language-class equivalence.
Mathlib proves that `NFA.toDFA` and `DFA.toNFA` preserve accepted languages; here
we add the corresponding Langlib recognizability predicate and class equality.

## Main declarations

- `is_NFA` -- recognition by a finite-state nondeterministic automaton.
- `is_NFA_iff_is_DFA` -- NFAs and DFAs recognize the same languages.
- `NFA_eq_DFA` -- equality of the two language classes.
-/

variable {T : Type}

/-- A language is `NFA`-recognizable if it is accepted by some nondeterministic
finite automaton with a finite state type. -/
@[expose]
public def is_NFA (L : Language T) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : NFA T σ, M.accepts = L

/-- The class of NFA-recognizable languages. -/
@[expose]
public def NFA.Class : Set (Language T) :=
  setOf is_NFA

/-- Nondeterministic and deterministic finite automata recognize exactly the
same languages. -/
public theorem is_NFA_iff_is_DFA {L : Language T} :
    is_NFA L ↔ is_DFA L := by
  classical
  constructor
  · rintro ⟨σ, _, M, rfl⟩
    exact ⟨Set σ, inferInstance, M.toDFA, NFA.toDFA_correct⟩
  · rintro ⟨σ, _, M, rfl⟩
    exact ⟨σ, inferInstance, M.toNFA, DFA.toNFA_correct M⟩

/-- Equality of the NFA- and DFA-recognizable language classes. -/
public theorem NFA_eq_DFA :
    (NFA.Class : Set (Language T)) = DFA.Class := by
  ext L
  exact is_NFA_iff_is_DFA

end
