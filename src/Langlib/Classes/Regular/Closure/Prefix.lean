import Mathlib
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Closure.Complement
import Langlib.Classes.Regular.Examples.TopBot
import Langlib.Utilities.LanguageOperations

/-! # Regular Closure Under Prefix

This file proves that regular languages are closed under the prefix operation
and shows that the converse fails.

## Main declarations

- `DFA.reachableAccept`
- `DFA.prefixDFA`
- `Language.IsRegular.prefixLang`
- `Language.not_iff_regular_prefix`
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

private lemma anbn_compl_not_isRegular : ¬ anbnᶜ.IsRegular := by
  intro h
  exact anbn_not_isRegular (Language.isRegular_compl_iff.mp h)

/-- No word of the form `w ++ [false]` belongs to `anbn`. -/
private lemma append_false_not_mem_anbn (w : List Bool) :
    w ++ [false] ∉ anbn := by
  by_contra h_contra
  obtain ⟨n, hn⟩ := h_contra
  replace hn := congr_arg List.reverse hn
  simp_all +decide [List.reverse_append]
  cases n <;> simp_all +decide [List.replicate]

/-- `prefixLang(anbnᶜ) = ⊤`. -/
private lemma prefixLang_anbn_compl_eq_top :
    prefixLang anbnᶜ = ⊤ := by
  ext w
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨[false], append_false_not_mem_anbn w⟩

/-- The converse of prefix closure fails. -/
theorem not_iff_regular_prefix :
    ¬ (∀ (L : Language Bool), (prefixLang L).IsRegular ↔ L.IsRegular) := by
  intro h
  have hpref : (prefixLang anbnᶜ).IsRegular := by
    rw [prefixLang_anbn_compl_eq_top]
    exact isRegular_top
  exact anbn_compl_not_isRegular ((h anbnᶜ).mp hpref)

end Language
