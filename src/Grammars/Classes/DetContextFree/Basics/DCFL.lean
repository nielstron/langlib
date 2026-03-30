/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.DetPushdown.Basics.Inclusion
import Grammars.Classes.ContextFree.Basics.PDAEquivalence
import Grammars.Classes.ContextFree.ClosureProperties.Union
import Grammars.Classes.ContextFree.ClosureProperties.Intersection

/-! # Deterministic Context-Free Languages (DCFLs)

This file defines deterministic context-free languages (DCFLs) as a grammar class
and proves their basic inclusion into context-free languages.

## Definition

A language `L` is a **deterministic context-free language (DCFL)** if there exists a
deterministic pushdown automaton (DPDA) that accepts `L` by final-state acceptance.

## Main results

- `is_CF_of_is_DCFL` — Every DCFL is context-free.
- `lang_aibjck_eq_union` — The language `{aⁱbʲcᵏ | i = j ∨ j = k}` equals the union of two CFLs.
- `lang_aibjck_CFL` — The language `{aⁱbʲcᵏ | i = j ∨ j = k}` is context-free.

## References

* Hopcroft, Motwani, Ullman. *Introduction to Automata Theory, Languages, and Computation*,
  3rd ed. Section 6.4.
-/

open PDA

variable {T : Type} [Fintype T]

-- ============================================================================
-- DCFL definition and basic properties
-- ============================================================================

/-- A language `L` over a finite alphabet `T` is a **deterministic context-free language
    (DCFL)** if there exists a DPDA that recognizes `L` via final-state acceptance. -/
def is_DCFL (L : Language T) : Prop :=
  ∃ (Q S : Type) (_ : Fintype Q) (_ : Fintype S) (M : DPDA Q T S),
    M.acceptsByFinalState = L
