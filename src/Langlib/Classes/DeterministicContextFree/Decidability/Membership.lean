/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.DeterministicContextFree.Basics.Inclusion
import Langlib.Classes.ContextFree.Decidability.Membership
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Classes.ContextFree.Basics.FiniteNT
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization

/-! # Decidability of Membership for DPDA Languages

This file proves that membership is decidable for deterministic context-free
languages (equivalently, DPDA-recognizable languages).

Since every DPDA language is context-free, and membership in context-free languages
is decidable (via the CYK algorithm on Chomsky normal form grammars), membership
in DPDA languages is decidable as well.

## Main results

- `dpda_membership_decidable` — membership in any DPDA language is decidable.
- `dcf_membership_decidable` — membership in any DCF language is decidable.
-/

open PDA

variable {T : Type} [Fintype T] [DecidableEq T]

/-- Membership in any DPDA-recognizable language is decidable.

The proof proceeds by reduction to context-free membership:
1. Every DPDA language is context-free (`is_CF_of_is_DCF`).
2. Every context-free language has a grammar with finitely many nonterminals
   (`ContextFreeGrammar.exists_fintype_nt`).
3. Membership in a context-free grammar with finite nonterminals is decidable
   via the CYK algorithm (`cf_membership_decidable`). -/
noncomputable def dpda_membership_decidable
    (L : Language T) (hL : is_DPDA L) (w : List T) :
    Decidable (w ∈ L) := by
  classical
  -- Every DPDA language is context-free
  have hCF : is_CF L := is_CF_of_is_DCF hL
  -- Extract a CF grammar witnessing L
  let hCF' : is_CF_via_cfg L := is_CF_implies_is_CF_via_cfg hCF
  let g : CF_grammar T := Classical.choose hCF'
  have hg : CF_language g = L := Classical.choose_spec hCF'
  -- Get a Mathlib CFG equivalent to g
  let mg := mathlib_cfg_of_cfg g
  have hmg : mg.language = L := by
    rw [← hg]; exact (CF_language_eq_mathlib_language g).symm
  -- Restrict to finite nonterminals
  let mg' := mg.toFiniteNT
  have hmg' : mg'.language = L := by
    rw [← hmg]; exact ContextFreeGrammar.toFiniteNT_language mg
  -- Convert back to a CF_grammar with finite nonterminals
  let g' := cfg_of_mathlib_cfg mg'
  have hg' : CF_language g' = L := by
    rw [← hmg']; exact (mathlib_language_eq_CF_language mg').symm
  -- The nonterminal type of g' is finite
  haveI : Fintype g'.nt := ContextFreeGrammar.toFiniteNT_fintype mg
  -- Decide membership
  rw [← hg']
  exact cf_membership_decidable g' w

/-- Membership in any deterministic context-free language is decidable. -/
noncomputable def dcf_membership_decidable
    (L : Language T) (hL : is_DCF L) (w : List T) :
    Decidable (w ∈ L) :=
  dpda_membership_decidable L hL w
