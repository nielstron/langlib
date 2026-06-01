module

/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Linear.Inclusion.StrictContextFree
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.Regular.Inclusion.StrictLinear
@[expose]
public section



/-! # Linear languages are not closed under concatenation

A corollary of the [linear pumping lemma](../Pumping/Pumping.lean): the language
`{0ⁿ1ⁿ2ᵐ3ᵐ}` is the concatenation of the two **linear** languages `{0ⁿ1ⁿ}` and
`{2ᵐ3ᵐ}`, yet it is itself not linear. Hence the class of linear languages is not
closed under concatenation (in contrast to the context-free languages).

## Main results

- `exists_Linear_concat_not_Linear` — two linear languages whose concatenation is not linear.
- `Linear_not_closedUnderConcatenation` — `Linear` is not closed under concatenation.
-/

open Language

/-- `{0ⁿ1ⁿ}` is linear. -/
theorem map_f4_anbn_is_Linear : is_Linear (Language.map f4 anbn) :=
  map_anbn_is_Linear f4 (by decide)

/-- `{2ᵐ3ᵐ}` is linear. -/
theorem map_g4_anbn_is_Linear : is_Linear (Language.map g4 anbn) :=
  map_anbn_is_Linear g4 (by decide)

/-- There exist linear languages whose concatenation is not linear. -/
public theorem exists_Linear_concat_not_Linear :
    ∃ L₁ L₂ : Language (Fin 4), is_Linear L₁ ∧ is_Linear L₂ ∧ ¬ is_Linear (L₁ * L₂) :=
  ⟨Language.map f4 anbn, Language.map g4 anbn,
    map_f4_anbn_is_Linear, map_g4_anbn_is_Linear, L4_not_is_Linear⟩

/-- The class of linear languages is **not** closed under concatenation. -/
public theorem Linear_not_closedUnderConcatenation :
    ¬ ClosedUnderConcatenation (@is_Linear (Fin 4)) := by
  intro h
  exact L4_not_is_Linear (h _ _ map_f4_anbn_is_Linear map_g4_anbn_is_Linear)
