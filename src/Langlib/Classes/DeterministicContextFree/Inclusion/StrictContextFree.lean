/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
import Langlib.Classes.DeterministicContextFree.Closure.Complement
import Langlib.Classes.ContextFree.Closure.Complement
import Langlib.Utilities.ClosurePredicates.Transport

/-! # DCFs are a strict subset of CFLs

This file records the closure-mismatch route to strictness for the inclusion
`DCF ⊆ CF`.

--/

/-- If deterministic context-free languages are closed under complement over `Fin 3`, then
they form a strict subclass of context-free languages over `Fin 3`.

This isolates the useful closure-property proof pattern behind the unconditional
strictness theorem below. -/
theorem DCF_strict_subclass_CF_of_closedUnderComplement
    (hDCFcomp : ClosedUnderComplement (α := Fin 3) is_DCF) :
    (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3))) :=
  strict_subset_of_subset_different_property
    (P := is_DCF) (Q := is_CF)
    (fun _ hL => DCF_subclass_CF hL)
    (X := ClosedUnderComplement)
    (fun hiff => ClosedUnderComplement_of_iff hiff)
    hDCFcomp
    CF_notClosedUnderComplement

/-- If deterministic context-free languages are closed under complement over an alphabet
with three distinguished symbols, then they form a strict subclass of context-free
languages over that alphabet. -/
theorem DCF_strict_subclass_CF_of_closedUnderComplement_of_three {T : Type} [Fintype T]
    (a b c : T) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hDCFcomp : ClosedUnderComplement (α := T) is_DCF) :
    (DCF : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  strict_subset_of_subset_different_property
    (P := is_DCF) (Q := is_CF)
    (fun _ hL => DCF_subclass_CF hL)
    (X := ClosedUnderComplement)
    (fun hiff => ClosedUnderComplement_of_iff hiff)
    hDCFcomp
    (CF_notClosedUnderComplement_of_three a b c hab hac hbc)

/-- If deterministic context-free languages are closed under complement over a finite alphabet
with at least three symbols, then they form a strict subclass of context-free languages over
that alphabet. -/
theorem DCF_strict_subclass_CF_of_closedUnderComplement_of_card {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T)
    (hDCFcomp : ClosedUnderComplement (α := T) is_DCF) :
    (DCF : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  strict_subset_of_subset_different_property
    (P := is_DCF) (Q := is_CF)
    (fun _ hL => DCF_subclass_CF hL)
    (X := ClosedUnderComplement)
    (fun hiff => ClosedUnderComplement_of_iff hiff)
    hDCFcomp
    (CF_notClosedUnderComplement_of_card hT)

/-- The closure-mismatch strictness result specialized to the DPDA totalization
principle. -/
theorem DCF_strict_subclass_CF_of_decider_presentations
    (htotal : EveryDCFHasDeciderPresentation (Fin 3)) :
    (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3))) :=
  DCF_strict_subclass_CF_of_closedUnderComplement
    (DCF_closedUnderComplement_of_decider_presentations htotal)

/-- The closure-mismatch strictness result specialized to the DPDA totalization principle
over any finite alphabet with at least three symbols. -/
theorem DCF_strict_subclass_CF_of_decider_presentations_of_card {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) (htotal : EveryDCFHasDeciderPresentation T) :
    (DCF : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  DCF_strict_subclass_CF_of_closedUnderComplement_of_card hT
    (DCF_closedUnderComplement_of_decider_presentations htotal)

/-- Deterministic context-free languages are a strict subclass of context-free
languages over a three-symbol alphabet. -/
theorem DCF_strict_subclass_CF :
    (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3))) :=
  DCF_strict_subclass_CF_of_closedUnderComplement DCF_closedUnderComplement

/-- Deterministic context-free languages are a strict subclass of context-free languages
over any finite alphabet with at least three symbols. -/
theorem DCF_strict_subclass_CF_of_card {T : Type} [Fintype T]
    (hT : 3 ≤ Fintype.card T) :
    (DCF : Set (Language T)) ⊂ (CF : Set (Language T)) :=
  DCF_strict_subclass_CF_of_closedUnderComplement_of_card hT DCF_closedUnderComplement
