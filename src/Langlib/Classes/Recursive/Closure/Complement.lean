import Mathlib
import Langlib.Classes.Recursive.Definition
import Langlib.Utilities.ClosurePredicates

/-! # Recursive Closure Under Complement

This file proves that the class of recursive (decidable) languages is closed under
complement.

Given a TM0 decider `(Λ, M, accept)` for `L` that always halts, the complement
is decided by `(Λ, M, fun q => !accept q)` — the same machine with the acceptance
predicate negated.

## Main results

- `is_Recursive_complement` — if `L` is recursive then `Lᶜ` is recursive.
- `Recursive_complement_iff` — `L` is recursive iff `Lᶜ` is recursive.
-/

open Turing

variable {T : Type}

/-
The class of recursive languages is closed under complement.

Given a decider `(Λ, M, accept)` that always halts, we construct a decider for
`Lᶜ` by negating the acceptance predicate: `(Λ, M, fun q => !accept q)`.
-/
theorem is_Recursive_complement {L : Language T} (hL : is_Recursive L) :
    is_Recursive Lᶜ := by
  obtain ⟨ Λ, hΛ, hΛf, M, accept, hHalt, hCorrect ⟩ := hL;
  -- Construct the complement decider using the same machine M but with acceptance predicate `fun q => !accept q`.
  use Λ, hΛ, hΛf, M, fun q => !accept q;
  grind

/-- A language is recursive iff its complement is recursive. -/
theorem Recursive_complement_iff {L : Language T} :
    is_Recursive Lᶜ ↔ is_Recursive L := by
  constructor
  · intro h
    have := is_Recursive_complement h
    rwa [compl_compl] at this
  · exact is_Recursive_complement
/-- The class of recursive languages is closed under complement. -/
theorem Recursive_closedUnderComplement : ClosedUnderComplement (α := T) is_Recursive :=
  fun L hL => is_Recursive_complement hL
