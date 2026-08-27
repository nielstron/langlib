import Mathlib
import Langlib

/-!
# Langlib Palomar solution

The declarations compared with `Challenge.lean` are imported from the completed
Langlib development.  This module intentionally adds no alternate statement:
Comparator exports the named declarations from this environment and checks them
against the independent Mathlib-only challenge.
-/

namespace ChomskyHierarchy

theorem RG_strict_subclass_Linear_of_card {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (RG : Set (Language T)) ⊂ (Linear : Set (Language T)) :=
  _root_.RG_strict_subclass_Linear_of_card hT

theorem Linear_strict_subclass_CF_of_card {T : Type} [Fintype T]
    (hT : 4 ≤ Fintype.card T) :
    (Linear : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  _root_.Linear_strict_subclass_CF_of_card hT

theorem RG_strict_subclass_DCF_of_card {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (RG : Set (Language T)) ⊂ (DCF : Set (Language T)) :=
  _root_.RG_strict_subclass_DCF_of_card hT

theorem DCF_strict_subclass_CF_of_card {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (DCF : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  _root_.DCF_strict_subclass_CF_of_card hT

theorem Linear_incomp_DPDA_of_card {T : Type} [Fintype T]
    (hT : 4 ≤ Fintype.card T) :
    IncompRel (· ⊆ ·) (Linear : Set (Language T))
      (DPDA.Class : Set (Language T)) :=
  _root_.Linear_incomp_DPDA_of_card hT

theorem CF_strict_subclass_Indexed {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (CF : Set (Language T)) ⊂ (Indexed : Set (Language T)) :=
  _root_.CF_strict_subclass_Indexed hT

theorem Indexed_strict_subclass_CS {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (Indexed : Set (Language T)) ⊂ (CS : Set (Language T)) :=
  _root_.Indexed_strict_subclass_CS hT

theorem CS_strict_subclass_Recursive_of_card {T : Type} [Fintype T]
    (hT : 1 ≤ Fintype.card T) :
    (CS : Set (Language T)) ⊂ (Recursive : Set (Language T)) :=
  _root_.CS_strict_subclass_Recursive_of_card hT

theorem Recursive_strict_subclass_RE_of_card {T : Type} [Fintype T]
    (hT : 1 ≤ Fintype.card T) :
    (Recursive : Set (Language T)) ⊂ (RE : Set (Language T)) :=
  _root_.Recursive_strict_subclass_RE_of_card hT

end ChomskyHierarchy
