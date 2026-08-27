module

/-
Copyright (c) 2026 Niels Mündler. All rights reserved.
Released under Apache 2.0 license; see licenses/Apache-2.0.txt.
-/
public import Langlib.Classes.DeterministicContextFree.Closure.Bijection
public import Langlib.Classes.DeterministicContextFree.Closure.Star
public import Langlib.Classes.DeterministicContextFree.Examples.AnBnCmDm
public import Langlib.Classes.Linear.Basics.Map
public import Langlib.Classes.Linear.Examples.AbcPositive
public import Langlib.Classes.Linear.Examples.AnBnCmDm
public import Mathlib.Order.Comparable
@[expose]
public section

/-! # Linear and deterministic context-free languages are incomparable

Two standard witnesses establish the two directions:

* The positive unequal-count union is linear but not deterministic context-free.
* The language `{0ⁿ1ⁿ2ᵐ3ᵐ}` is deterministic context-free but not linear.

Injective terminal maps transport these witnesses to every finite alphabet with
at least four elements.
-/

open Language

variable {T : Type}

/-- Linear languages and DPDA-recognizable languages are incomparable over every
finite alphabet with at least four elements. -/
public theorem Linear_incomp_DPDA_of_card [Fintype T]
    (hT : 4 ≤ Fintype.card T) :
    IncompRel (· ⊆ ·) (Linear : Set (Language T))
      (DPDA.Class : Set (Language T)) := by
  let e3 : Fin 3 ↪ T :=
    (Fin.castLEEmb (by omega : 3 ≤ Fintype.card T)).trans
      (Fintype.equivFin T).symm.toEmbedding
  let e4 : Fin 4 ↪ T :=
    (Fin.castLEEmb hT).trans (Fintype.equivFin T).symm.toEmbedding
  constructor
  · intro hsub
    have hLinear : is_Linear
        (Language.map e3 (lang_not_eq_any_pos + lang_not_any_eq_pos)) :=
      is_Linear_map notEqUnion_is_Linear e3
    have hDCF : is_DCF
        (Language.map e3 (lang_not_eq_any_pos + lang_not_any_eq_pos)) :=
      hsub hLinear
    exact DCFStar.notDCF_not_pos_union
      (DCF_of_map_injective_DCF_rev e3.injective
        (lang_not_eq_any_pos + lang_not_any_eq_pos) hDCF)
  · intro hsub
    have hDCF : is_DCF (Language.map e4 anbncmdm) :=
      DCF_of_map_injective_DCF e4.injective anbncmdm
        DCFAnBnCmDm.anbncmdm_is_DCF
    exact map_anbncmdm_not_is_Linear e4 (hsub hDCF)

end
