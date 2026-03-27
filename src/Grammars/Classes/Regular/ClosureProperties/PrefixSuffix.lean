import Mathlib
import Grammars.Utilities.LanguageOperations

/-! # Regular Closure Under Prefix and Suffix

This file adds regular-language closure results for the prefix and suffix operations.

## Main declarations

- `DFA.reachableAccept`
- `DFA.prefixDFA`
- `Language.IsRegular.prefixLang`
- `Language.IsRegular.suffixLang`
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

/-- Regular languages are closed under the suffix operation. -/
theorem IsRegular.suffixLang {L : Language α} (h : L.IsRegular) :
    (suffixLang L).IsRegular := by
  rw [Language.suffixLang_eq_reverse_prefixLang_reverse]
  exact (h.reverse.prefixLang).reverse

end Language
