module

/-
Copyright (c) 2026 Niels Mündler. All rights reserved.
Released under Apache 2.0 license; see licenses/Apache-2.0.txt.
-/
public import Langlib.Classes.Linear.Inclusion.ContextFree
public import Langlib.Examples.AnBnCmDm
public import Langlib.Classes.ContextFree.Examples.AnBnCmDm
public import Langlib.Classes.Linear.Examples.AnBnCmDm
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
@[expose]
public section



/-! # Linear ⊊ Context-Free

The language `{0ⁿ1ⁿ2ᵐ3ᵐ}` over `Fin 4` (`anbncmdm`) is context-free
(`anbncmdm_is_CF`, in `Langlib.Classes.ContextFree.Examples.AnBnCmDm`) but not linear
(`anbncmdm_not_is_Linear`, in `Langlib.Classes.Linear.Examples.AnBnCmDm`). This file
assembles those two facts into the
strict inclusion over every finite alphabet with at least 4 elements by
relabelling along an embedding `e : Fin 4 ↪ T`.

## Main results

- `Linear_strict_subclass_CF_of_card` — `Linear ⊊ CF` over every finite alphabet with
  at least 4 elements.
-/

open Language List

variable {T : Type}

/-! ## Arbitrary alphabets with at least 4 elements -/

/-- Linear languages are a strict subclass of context-free languages over any alphabet with
at least 4 elements, as exhibited by an embedding `Fin 4 ↪ T`. -/
public theorem Linear_strict_subclass_CF_of_embedding (e : Fin 4 ↪ T) :
    (Linear : Set (Language T)) ⊂ (CF : Set (Language T)) := by
  refine ⟨Linear_subclass_CF, fun hsub => ?_⟩
  exact map_anbncmdm_not_is_Linear e (hsub (map_anbncmdm_is_CF e))

/-- Linear languages are a strict subclass of context-free languages over any finite alphabet
with at least 4 elements. -/
public theorem Linear_strict_subclass_CF_of_card [Fintype T] (hT : 4 ≤ Fintype.card T) :
    (Linear : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  Linear_strict_subclass_CF_of_embedding
    ((Fin.castLEEmb hT).trans (Fintype.equivFin T).symm.toEmbedding)

end
