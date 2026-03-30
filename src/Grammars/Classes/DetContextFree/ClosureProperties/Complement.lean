/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammars.Automata.DetPushdown.ClosureProperties.Complement
import Grammars.Classes.ContextFree.ClosureProperties.Complement
import Grammars.Classes.ContextFree.ClosureProperties.Intersection
import Grammars.Classes.DetContextFree.Basics.DCFL

/-! # Complement Properties of DCFLs

This file collects complement-closure results and consequences for deterministic
context-free languages.
-/

open PDA

variable {T : Type} [Fintype T]

/-- **DCFL Complement Closure**: The class of deterministic context-free languages is
    closed under complementation.

    Follows from the closure of DPDAs under complement. -/
theorem is_DCFL_compl {L : Language T} (h : is_DCFL L) : is_DCFL Lᶜ := by
  sorry

/-- If every CFL (over a fixed finite alphabet `T`) were a DCFL, then every CFL's
    complement would also be a CFL. -/
theorem complement_CF_of_all_CF_DCFL {T : Type} [Fintype T]
    (h : ∀ L : Language T, is_CF L → is_DCFL L) :
    ∀ L : Language T, is_CF L → is_CF Lᶜ :=
  fun L hCF => is_CF_of_is_DCFL (is_DCFL_compl (h L hCF))

/-- `{aⁱ bʲ cᵏ | i = j ∨ j = k}` is NOT a deterministic context-free language.

    **Proof sketch.** If this language were DCFL, its complement would be DCFL (by
    `is_DCFL_compl`), hence CFL (by `is_CF_of_is_DCFL`). The complement intersected
    with the regular language `a*b*c*` yields `{aⁱ bʲ cᵏ | i ≠ j ∧ j ≠ k}`. Since
    CFL ∩ regular = CFL (`CF_of_CF_inter_regular`), this language would be CFL. But
    `{aⁱ bʲ cᵏ | i ≠ j ∧ j ≠ k}` is NOT context-free (provable by Ogden's lemma),
    giving a contradiction. -/
theorem not_DCFL_lang_aibjck : ¬ is_DCFL lang_aibjck := by
  sorry

/-- There exist context-free languages over `Fin 3` that are not deterministic
    context-free. -/
theorem exists_CF_not_DCFL : ∃ L : Language (Fin 3), is_CF L ∧ ¬ is_DCFL L := by
  refine ⟨lang_aibjck, lang_aibjck_CFL, not_DCFL_lang_aibjck⟩
