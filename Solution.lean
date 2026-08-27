import Langlib

/-!
# Strict-inclusion Palomar solution

The compared declarations restate Langlib's hierarchy theorems under one
submission namespace. This gives Challenge and Solution identical Mathlib-level
statement elaboration while every proof delegates to the existing result.
-/

namespace ChomskyHierarchy

theorem RG_strict_subclass_Linear_of_card {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (RG : Set (Language T)) ⊂ Linear :=
  _root_.RG_strict_subclass_Linear_of_card hT

theorem Linear_strict_subclass_CF_of_card {T : Type} [Fintype T]
    (hT : 4 ≤ Fintype.card T) :
    (Linear : Set (Language T)) ⊂ CF :=
  _root_.Linear_strict_subclass_CF_of_card hT

theorem RG_strict_subclass_LR_of_card {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (RG : Set (Language T)) ⊂ (LR : Set (Language T)) := by
  let : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide) hT)
  exact RG_strict_subclass_LR

theorem LR_strict_subclass_CF_of_card {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (LR : Set (Language T)) ⊂ CF :=
  _root_.LR_strict_subclass_CF_of_card hT

theorem CF_strict_subclass_Indexed {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (CF : Set (Language T)) ⊂ Indexed :=
  _root_.CF_strict_subclass_Indexed hT

theorem Indexed_strict_subclass_CS {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (Indexed : Set (Language T)) ⊂ CS :=
  _root_.Indexed_strict_subclass_CS hT

theorem CS_strict_subclass_Recursive_of_card {T : Type} [Fintype T]
    (hT : 1 ≤ Fintype.card T) :
    (CS : Set (Language T)) ⊂ Recursive :=
  _root_.CS_strict_subclass_Recursive_of_card hT

theorem Recursive_strict_subclass_RE_of_card {T : Type} [Fintype T]
    (hT : 1 ≤ Fintype.card T) :
    (Recursive : Set (Language T)) ⊂ RE :=
  _root_.Recursive_strict_subclass_RE_of_card hT

end ChomskyHierarchy
