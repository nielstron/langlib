/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.DetPushdown.Basics.Inclusion
import Grammars.Classes.ContextFree.Basics.PDAEquivalence
import Grammars.Classes.ContextFree.ClosureProperties.Union

/-! # Deterministic Context-Free Languages (DCFLs)

This file defines deterministic context-free languages (DCFLs) as a grammar class
and proves their basic inclusion into context-free languages.

## Definition

A language `L` is a **deterministic context-free language (DCFL)** if there exists a
deterministic pushdown automaton (DPDA) that accepts `L` by final-state acceptance.

## Main results

- `is_CF_of_is_DCFL` — Every DCFL is context-free.
- `lang_aibjck_eq_union` — The language `{aⁱbʲcᵏ | i = j ∨ j = k}` equals the union of two CFLs.
- `lang_aibjck_CFL` — The language `{aⁱbʲcᵏ | i = j ∨ j = k}` is context-free.

## References

* Hopcroft, Motwani, Ullman. *Introduction to Automata Theory, Languages, and Computation*,
  3rd ed. Section 6.4.
-/

open PDA

variable {T : Type} [Fintype T]

-- ============================================================================
-- DCFL definition and basic properties
-- ============================================================================

/-- A language `L` over a finite alphabet `T` is a **deterministic context-free language
    (DCFL)** if there exists a DPDA that recognizes `L` via final-state acceptance. -/
def is_DCFL (L : Language T) : Prop :=
  ∃ (Q S : Type) (_ : Fintype Q) (_ : Fintype S) (M : DPDA Q T S),
    M.acceptsByFinalState = L

-- ============================================================================
-- DCFL inclusion into CFL
-- ============================================================================

theorem is_CF_of_is_DCFL {L : Language T} (h : is_DCFL L) : is_CF L := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  exact is_CF_of_is_PDA M.is_PDA_acceptsByFinalState

-- ============================================================================
-- The explicit witness: {aⁱ bʲ cᵏ | i = j ∨ j = k}
-- ============================================================================

section explicit_witness

/-- The language `{aⁿ bⁿ cᵐ | n, m ∈ ℕ}` over `{0, 1, 2}` = `{a, b, c}`. -/
def lang_anbnck : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n 0 ++ List.replicate n 1 ++ List.replicate m 2

/-- The language `{aⁿ bᵐ cᵐ | n, m ∈ ℕ}` over `{0, 1, 2}` = `{a, b, c}`. -/
def lang_anbmcm : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n 0 ++ List.replicate m 1 ++ List.replicate m 2

/-- The language `{aⁱ bʲ cᵏ | i = j ∨ j = k}` over `{0, 1, 2}`.
    The standard explicit witness of a CFL that is not a DCFL. -/
def lang_aibjck : Language (Fin 3) :=
  fun w => ∃ i j k : ℕ,
    w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2 ∧ (i = j ∨ j = k)

/-- `lang_aibjck` equals the union of `lang_anbnck` and `lang_anbmcm`. -/
theorem lang_aibjck_eq_union : lang_aibjck = lang_anbnck + lang_anbmcm := by
  ext w
  simp only [Language.mem_add]
  constructor
  · rintro ⟨i, j, k, hw, hij | hjk⟩
    · left; exact ⟨i, k, hij ▸ hw⟩
    · right; exact ⟨i, j, hjk ▸ hw⟩
  · rintro (⟨n, m, hw⟩ | ⟨n, m, hw⟩)
    · exact ⟨n, n, m, hw, Or.inl rfl⟩
    · exact ⟨n, m, m, hw, Or.inr rfl⟩

/-- `{aⁿ bⁿ cᵐ}` is context-free. -/
theorem is_CF_lang_anbnck : is_CF lang_anbnck :=
  sorry

/-- `{aⁿ bᵐ cᵐ}` is context-free. -/
theorem is_CF_lang_anbmcm : is_CF lang_anbmcm :=
  sorry

/-- `{aⁱ bʲ cᵏ | i = j ∨ j = k}` is context-free. -/
theorem lang_aibjck_CFL : is_CF lang_aibjck := by
  rw [lang_aibjck_eq_union]
  exact CF_of_CF_u_CF _ _ ⟨is_CF_lang_anbnck, is_CF_lang_anbmcm⟩

end explicit_witness
