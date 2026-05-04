import Langlib.Classes.RecursivelyEnumerable.Decidability.Helper

/-! # Undecidability of Membership for RE Languages

This file proves that membership cannot be decided for recursively enumerable (RE)
languages in general. More precisely, there exists an RE predicate whose membership
is not computable.

The proof uses the classical halting-problem undecidability result from Mathlib:

- `ComputablePred.halting_problem_re` — the halting predicate is RE.
- `ComputablePred.halting_problem` — the halting predicate is not computable.

Together these immediately yield: **there exists an RE predicate that is not computable**,
which is the formal content of the statement "membership is undecidable for RE languages."

## Main results

- `RE_membership_undecidable` — there exists a recursively enumerable predicate that is
  not computably decidable.
- `RE_membership_undecidable'` — the halting predicate (for input `0`) is RE but not
  computably decidable.
-/

open Nat.Partrec

/-- The halting predicate (for input `0`) is RE but not computably decidable. -/
theorem RE_membership_undecidable' :
    REPred (fun c : Code => (c.eval 0).Dom) ∧
    ¬ComputablePred (fun c : Code => (c.eval 0).Dom) :=
  ⟨ComputablePred.halting_problem_re 0, ComputablePred.halting_problem 0⟩

/-- There exists a recursively enumerable predicate that is not computably decidable.

This is the formal statement of the classical result that "membership is undecidable
for RE languages": while RE languages/predicates are those for which membership can be
*confirmed* (semi-decided) by a Turing machine, there is no algorithm that can *decide*
membership (i.e., always halt with a yes/no answer) for every RE language. -/
theorem RE_membership_undecidable :
    ∃ (p : Code → Prop), REPred p ∧ ¬ComputablePred p :=
  ⟨_, RE_membership_undecidable'.1, RE_membership_undecidable'.2⟩

/-- Membership for RE codes is not uniformly computable. -/
theorem recursivelyEnumerable_computableMembership_undecidable :
    ¬ComputableMembership partrecCodeDomainLanguageOf := by
  intro h
  apply RE_membership_undecidable'.2
  have h_nil : ComputablePred
      (fun c : Code => ([] : List Unit) ∈ partrecCodeDomainLanguageOf c) := by
    unfold ComputableMembership at h
    rcases h with ⟨dec, hcomp⟩
    letI : DecidablePred
        (fun c : Code => ([] : List Unit) ∈ partrecCodeDomainLanguageOf c) :=
      fun c => dec (c, ([] : List Unit))
    exact ⟨inferInstance,
      hcomp.comp (Computable.pair Computable.id (Computable.const ([] : List Unit)))⟩
  exact h_nil.of_eq fun c => by
    change (c.eval 0).Dom ↔ (c.eval 0).Dom
    rfl
