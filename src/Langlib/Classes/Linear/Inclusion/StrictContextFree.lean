module

/-
Copyright (c) 2026 Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Linear.Inclusion.ContextFree
public import Langlib.Examples.L4
public import Langlib.Classes.ContextFree.Examples.L4
public import Langlib.Classes.Linear.Examples.L4
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
@[expose]
public section



/-! # Linear ⊊ Context-Free

The language `{0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4` (`L4`) is context-free (`L4_is_CF`, in
`Langlib.Classes.ContextFree.Examples.L4`) but not linear (`L4_not_is_Linear`, in
`Langlib.Classes.Linear.Examples.L4`). This file assembles those two facts into the
strict inclusion, transported to an arbitrary alphabet `T` with at least four symbols by
relabelling along an embedding `e : Fin 4 ↪ T`.

## Main results

- `Linear_strict_subclass_CF`         — `Linear ⊊ CF` over `Fin 4`.
- `Linear_strict_subclass_CF_of_card` — `Linear ⊊ CF` for any `4 ≤ Fintype.card T`.
-/

open Language List

variable {T : Type}

/-- Linear languages are a strict subclass of context-free languages over `Fin 4`. -/
public theorem Linear_strict_subclass_CF :
    (Linear : Set (Language (Fin 4))) ⊂ (CF : Set (Language (Fin 4))) := by
  refine ⟨Linear_subclass_CF, fun hsub => ?_⟩
  exact L4_not_is_Linear (hsub L4_is_CF)

/-! ## Transport to an arbitrary alphabet with at least four symbols -/

/-- Linear languages are a strict subclass of context-free languages over any alphabet that
admits an embedding of four distinct symbols. -/
public theorem Linear_strict_subclass_CF_of_embedding (e : Fin 4 ↪ T) :
    (Linear : Set (Language T)) ⊂ (CF : Set (Language T)) := by
  refine ⟨Linear_subclass_CF, fun hsub => ?_⟩
  exact Lwit_not_is_Linear e (hsub (Lwit_is_CF e))

/-- Linear languages are a strict subclass of context-free languages over any finite alphabet
with at least four symbols. -/
public theorem Linear_strict_subclass_CF_of_card [Fintype T] (hT : 4 ≤ Fintype.card T) :
    (Linear : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  Linear_strict_subclass_CF_of_embedding
    ((Fin.castLEEmb hT).trans (Fintype.equivFin T).symm.toEmbedding)

end
