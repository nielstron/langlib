module

/-
Copyright (c) 2026 Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Linear.Inclusion.StrictContextFree
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.Regular.Inclusion.StrictLinear
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
@[expose]
public section



/-! # Linear languages are not closed under concatenation

A corollary of the [linear pumping lemma](../Pumping/Pumping.lean): the witness
`{0ⁿ1ⁿ2ᵐ3ᵐ}` is the concatenation of the two **linear** languages `{0ⁿ1ⁿ}` and
`{2ᵐ3ᵐ}`, yet it is itself not linear. Hence the class of linear languages is not
closed under concatenation (unlike the context-free languages). As with the strict
inclusion, this transports to any alphabet with at least four symbols.

## Main results

- `exists_Linear_concat_not_Linear` — two linear languages whose concatenation is not linear.
- `Linear_not_closedUnderConcatenation` — `Linear` is not closed under concatenation,
  with an `_of_card` variant for `4 ≤ Fintype.card T`.
-/

open Language

variable {T : Type}

private theorem f4_injective : Function.Injective f4 := by decide
private theorem g4_injective : Function.Injective g4 := by decide

/-- The two linear factors concatenate to the relabelled witness language. -/
theorem map_concat_eq_map_L4 (e : Fin 4 ↪ T) :
    Language.map (⇑e ∘ f4) anbn * Language.map (⇑e ∘ g4) anbn = Language.map e L4 := by
  rw [L4, map_mul, Language.map_map, Language.map_map]

/-- `{aⁿbⁿ}` (the first factor over `T`) is linear. -/
theorem map_comp_f4_is_Linear (e : Fin 4 ↪ T) : is_Linear (Language.map (⇑e ∘ f4) anbn) :=
  map_anbn_is_Linear _ (e.injective.comp f4_injective)

/-- `{cᵐdᵐ}` (the second factor over `T`) is linear. -/
theorem map_comp_g4_is_Linear (e : Fin 4 ↪ T) : is_Linear (Language.map (⇑e ∘ g4) anbn) :=
  map_anbn_is_Linear _ (e.injective.comp g4_injective)

/-- There exist linear languages whose concatenation is not linear, over any alphabet that
admits an embedding of four distinct symbols. -/
public theorem exists_Linear_concat_not_Linear (e : Fin 4 ↪ T) :
    ∃ L₁ L₂ : Language T, is_Linear L₁ ∧ is_Linear L₂ ∧ ¬ is_Linear (L₁ * L₂) :=
  ⟨Language.map (⇑e ∘ f4) anbn, Language.map (⇑e ∘ g4) anbn,
    map_comp_f4_is_Linear e, map_comp_g4_is_Linear e,
    fun hL => Lwit_not_is_Linear e (map_concat_eq_map_L4 e ▸ hL)⟩

/-- The class of linear languages is **not** closed under concatenation, over any alphabet that
admits an embedding of four distinct symbols. -/
public theorem Linear_not_closedUnderConcatenation (e : Fin 4 ↪ T) :
    ¬ ClosedUnderConcatenation (@is_Linear T) := fun h =>
  Lwit_not_is_Linear e
    (map_concat_eq_map_L4 e ▸ h _ _ (map_comp_f4_is_Linear e) (map_comp_g4_is_Linear e))

/-- The class of linear languages is not closed under concatenation, over any finite alphabet
with at least four symbols. -/
public theorem Linear_not_closedUnderConcatenation_of_card [Fintype T]
    (hT : 4 ≤ Fintype.card T) : ¬ ClosedUnderConcatenation (@is_Linear T) :=
  Linear_not_closedUnderConcatenation
    ((Fin.castLEEmb hT).trans (Fintype.equivFin T).symm.toEmbedding)
