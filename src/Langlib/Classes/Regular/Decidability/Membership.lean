import Mathlib
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
import Langlib.Classes.ContextFree.Pumping.ParseTree

/-! # Computability of Membership

This file proves that membership is computable for
regular languages, using `ComputablePred` rather than the weaker `Decidable`.

## Main results

- `dfa_membership_computablePred` – membership in a DFA's language is a computable predicate
- `regular_membership_computablePred` – membership in a regular language is a computable predicate
-/

open List Relation

/-! ## Part 1: Regular Languages -/

section Regular

variable {α σ : Type*}

/-- Membership in a DFA's accepted language is a computable predicate.

The proof constructs the computable decision function explicitly as the
composition of `M.eval` (which is `List.foldl M.step M.start`, primitive
recursive by `Primrec.list_foldl` since `M.step` is a function from a
finite domain) with the accept-state test (primitive recursive by
`Primrec.dom_finite`). -/
theorem dfa_membership_computablePred [Primcodable α] [Primcodable σ]
    [Finite σ] [Finite α]
    (M : DFA α σ) [DecidablePred (· ∈ M.accept)] :
    ComputablePred (· ∈ M.accepts) := by
  show ComputablePred (fun w => M.eval w ∈ M.accept)
  have h_eval_comp : Computable M.eval := by
    show Computable (fun w => List.foldl M.step M.start w)
    exact (Primrec.list_foldl Primrec.id (Primrec.const M.start)
      (((Primrec.dom_finite (fun (p : σ × α) => M.step p.1 p.2)).comp
        Primrec.snd).to₂)).to_comp
  have h_dec : Computable (fun s : σ => decide (s ∈ M.accept)) :=
    (Primrec.dom_finite _).to_comp
  exact ⟨inferInstance, h_dec.comp h_eval_comp⟩

/-- Membership in a regular language is a computable predicate. -/
noncomputable def regular_membership_computablePred
    [Primcodable α] [Finite α]
    (L : Language α) (hL : L.IsRegular) :
    ComputablePred (· ∈ L) := by
  classical
  obtain ⟨σ, hσ⟩ := hL
  obtain ⟨hfin, hσ'⟩ := hσ
  obtain ⟨M, hM⟩ := hσ'
  rw [← hM]
  letI : Primcodable σ :=
    Primcodable.ofEquiv (Fin (Fintype.card σ)) (Fintype.equivFin σ)
  exact dfa_membership_computablePred M

end Regular
