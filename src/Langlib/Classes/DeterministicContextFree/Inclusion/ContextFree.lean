/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.DeterministicContextFree.Definition
import Langlib.Classes.DeterministicContextFree.Closure.Complement
import Langlib.Classes.ContextFree.Closure.Complement

/-! # DCFs are a strict subset of CFLs

This file shows that DCFs are a subset of the CFLs
and records the closure-mismatch route to strictness.

--/

-- ============================================================================
-- DCF inclusion into CFL
-- ============================================================================

theorem is_CF_of_is_DCF {T : Type} [Fintype T] {L : Language T} (h : is_DCF L) : is_CF L := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  exact is_CF_of_is_PDA M.is_PDA_acceptsByFinalState

/-- The class of deterministic context-free languages is contained in the class of
    context-free languages. -/
theorem DCF_subclass_CF {T : Type} [Fintype T] : (DCF : Set (Language T)) ⊆ CF :=
  fun _ h => is_CF_of_is_DCF h

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

/-- The closure-mismatch strictness result specialized to the DPDA totalization
principle. -/
theorem DCF_strict_subclass_CF_of_decider_presentations
    (htotal : EveryDCFHasDeciderPresentation (Fin 3)) :
    (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3))) :=
  DCF_strict_subclass_CF_of_closedUnderComplement
    (DCF_closedUnderComplement_of_decider_presentations htotal)

/-- The closure-mismatch strictness result specialized to the regular epsilon-analysis
existence theorem needed by the totalizer. -/
theorem DCF_strict_subclass_CF_of_regularEpsilonAnalysis
    (hanalysis : EveryDPDAHasRegularEpsilonAnalysis (Fin 3)) :
    (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3))) :=
  DCF_strict_subclass_CF_of_closedUnderComplement
    (DCF_closedUnderComplement_of_regularEpsilonAnalysis hanalysis)

/-- Deterministic context-free languages are a strict subclass of context-free
languages over a three-symbol alphabet. -/
theorem DCF_strict_subclass_CF :
    (DCF : Set (Language (Fin 3))) ⊂ (CF : Set (Language (Fin 3))) :=
  DCF_strict_subclass_CF_of_closedUnderComplement DCF_closedUnderComplement
