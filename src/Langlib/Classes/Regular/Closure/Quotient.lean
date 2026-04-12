import Mathlib
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
import Langlib.Utilities.LanguageOperations
import Langlib.Utilities.ClosurePredicates

/-! # Regular Closure Under Right Quotient

This file proves that regular languages are closed under right quotient with **any** language.
This generalises closure under prefix (which is the special case `R = Set.univ`).

Given a DFA `M` accepting `L` and an arbitrary language `R`, the quotient DFA keeps the same
transition function and start state but changes the accepting states to those from which some
word in `R` can drive `M` to an original accepting state.

## Main declarations

- `DFA.quotientAccept`
- `DFA.quotientDFA`
- `Language.IsRegular.rightQuotient`
-/

open List Set Computability Language

namespace DFA

variable {α : Type*} {σ : Type*}

/-- The set of states from which some word in `R` leads to an accepting state of `M`. -/
def quotientAccept (M : DFA α σ) (R : Language α) : Set σ :=
  { s : σ | ∃ v ∈ R, M.evalFrom s v ∈ M.accept }

/-- A DFA accepting the right quotient of `M`'s language by `R`. -/
def quotientDFA (M : DFA α σ) (R : Language α) : DFA α σ where
  step := M.step
  start := M.start
  accept := M.quotientAccept R

theorem evalFrom_quotientDFA (M : DFA α σ) (R : Language α) (s : σ) (x : List α) :
    (M.quotientDFA R).evalFrom s x = M.evalFrom s x := by
  rfl

theorem mem_quotientDFA_accept (M : DFA α σ) (R : Language α) (s : σ) :
    s ∈ (M.quotientDFA R).accept ↔ ∃ v ∈ R, M.evalFrom s v ∈ M.accept := by
  rfl

/-- The quotient DFA accepts exactly the right quotient of the original language by `R`. -/
theorem quotientDFA_accepts (M : DFA α σ) (R : Language α) :
    (M.quotientDFA R).accepts = M.accepts / R := by
  ext w
  constructor
  · intro h
    rcases h with ⟨v, hv, heval⟩
    refine ⟨v, hv, ?_⟩
    change M.eval (w ++ v) ∈ M.accept
    change M.evalFrom M.start (w ++ v) ∈ M.accept
    have heval' : M.evalFrom (M.evalFrom M.start w) v ∈ M.accept := by
      simpa [DFA.eval, evalFrom_quotientDFA] using heval
    rwa [← DFA.evalFrom_of_append] at heval'
  · rintro ⟨v, hv, hmem⟩
    refine ⟨v, hv, ?_⟩
    change M.eval (w ++ v) ∈ M.accept at hmem
    change M.evalFrom M.start (w ++ v) ∈ M.accept at hmem
    have hmem' : M.evalFrom (M.evalFrom M.start w) v ∈ M.accept := by
      rwa [DFA.evalFrom_of_append] at hmem
    simpa [DFA.eval, evalFrom_quotientDFA] using hmem'

end DFA

namespace Language

variable {α : Type*}

/-- Regular languages are closed under right quotient with any language.
-/
theorem IsRegular.rightQuotient {L : Language α} (hL : L.IsRegular) (R : Language α) :
    (L / R).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨σ, inferInstance, M.quotientDFA R, M.quotientDFA_accepts R⟩

/-- `prefixLang` as a special case of `rightQuotient` for regular languages. -/
theorem IsRegular.prefixLang' {L : Language α} (hL : L.IsRegular) :
    (Language.prefixLang L).IsRegular := by
  rw [Language.prefixLang_eq_rightQuotient_univ]
  exact hL.rightQuotient Set.univ

end Language

/-- The class of regular languages is closed under right quotient with any language. -/
theorem RG_closedUnderRightQuotient [Fintype α] :
    ClosedUnderRightQuotient (α := α) is_RG := by
  intro L₁ L₂ hL₁ _
  exact is_RG_of_isRegular ((isRegular_of_is_RG hL₁).rightQuotient L₂)

/-- The class of regular languages is closed under right quotient with regular languages. -/
theorem RG_closedUnderRightQuotientWithRegular [Fintype α] :
    ClosedUnderRightQuotientWithRegular (α := α) is_RG := by
  intro L hL R _
  exact is_RG_of_isRegular ((isRegular_of_is_RG hL).rightQuotient R)
