module

public import Langlib.Classes.ContextSensitive.Decidability.Membership
public import Langlib.Classes.ContextSensitive.Basics.NonContracting
public import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
import Mathlib.Tactic
@[expose]
public section



/-! # Context-Sensitive Languages are Recursive

This file proves the bridge theorem that every context-sensitive language (in the
broad `S → ε`-optional `grammar_context_sensitive` sense) is recursive, and the
corresponding class-level inclusion `(CS : Set (Language T)) ⊆ Recursive`.

## Strategy

`is_Recursive_of_is_CS` is a direct corollary of the uniform computable membership decider
for context-sensitive grammars (`computablePred_mem_of_is_CS`, in
`Classes/ContextSensitive/Decidability/Membership.lean`): membership in any context-sensitive
language is a `ComputablePred`, and a computable membership predicate is recursive
(`is_Recursive_of_computable_decide`).

## Main declarations

* `is_Recursive_of_is_CS`
* `CS_subset_Recursive_class`
-/

variable {T : Type}

/-! ## Main bridge theorems -/

/-- **Every context-sensitive language is recursive.** Derived from the uniform computable
membership decider for context-sensitive grammars (`computablePred_mem_of_is_CS`). -/
public theorem is_Recursive_of_is_CS
    [Fintype T] [DecidableEq T] [Primcodable T]
    {L : Language T} (h : is_CS L) : is_Recursive L := by
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp (computablePred_mem_of_is_CS h)
  exact is_Recursive_of_computable_decide L f hf (fun w => iff_of_eq (congrFun hfe w))

/-- **The class of context-sensitive languages is a subset of the recursive languages.** -/
public theorem CS_subset_Recursive_class
    [Fintype T] [DecidableEq T] [Primcodable T] :
    (CS : Set (Language T)) ⊆ (Recursive : Set (Language T)) := by
  intro L hL
  exact is_Recursive_of_is_CS hL
