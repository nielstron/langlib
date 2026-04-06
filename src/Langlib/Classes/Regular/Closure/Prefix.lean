import Mathlib
import Langlib.Utilities.LanguageOperations

/-! # Regular Closure Under Prefix

This file proves that regular languages are closed under the prefix operation.

## Main declarations

- `DFA.reachableAccept`
- `DFA.prefixDFA`
- `Language.IsRegular.prefixLang`
-/

open List Set Computability

namespace DFA

variable {α : Type*} {σ : Type*}

/-- The set of states from which some accepting state is reachable. -/
def reachableAccept (M : DFA α σ) : Set σ :=
  { s : σ | ∃ x : List α, M.evalFrom s x ∈ M.accept }

/-- A DFA accepting the prefix language of the original DFA's language. -/
def prefixDFA (M : DFA α σ) : DFA α σ where
  step := M.step
  start := M.start
  accept := M.reachableAccept

theorem evalFrom_prefixDFA (M : DFA α σ) (s : σ) (x : List α) :
    M.prefixDFA.evalFrom s x = M.evalFrom s x := by
  rfl

theorem mem_prefixDFA_accept (M : DFA α σ) (s : σ) :
    s ∈ M.prefixDFA.accept ↔ ∃ x : List α, M.evalFrom s x ∈ M.accept := by
  rfl

/-- The prefix DFA accepts exactly the prefix language of the original DFA. -/
theorem prefixDFA_accepts (M : DFA α σ) :
    M.prefixDFA.accepts = Language.prefixLang M.accepts := by
  ext w
  simp only [DFA.mem_accepts, Language.mem_prefixLang, evalFrom_prefixDFA,
    mem_prefixDFA_accept, DFA.eval]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rwa [DFA.evalFrom_of_append]⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rwa [← DFA.evalFrom_of_append]⟩

end DFA

namespace Language

variable {α : Type*}

/-- Regular languages are closed under the prefix operation. -/
theorem IsRegular.prefixLang {L : Language α} (h : L.IsRegular) :
    (prefixLang L).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨σ, inferInstance, M.prefixDFA, M.prefixDFA_accepts⟩

end Language
