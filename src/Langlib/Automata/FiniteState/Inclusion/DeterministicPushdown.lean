module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Automata.DeterministicPushdown.Definition
public import Langlib.Automata.FiniteState.Equivalence.Determinization
import Mathlib.Tactic.Cases

@[expose]
public section

/-! # Finite Automata Included in Deterministic Pushdown Automata

This file proves the inclusion directly on automata.  A DFA is simulated by a
DPDA whose stack alphabet is `Unit`: every input transition updates the finite
control exactly as the DFA does and replaces the sole stack symbol by itself.
An NFA is first determinized by the subset construction and then passed through
the same simulation.

## Main results

- `DPDA_of_DFA` — the stack-ignoring DPDA associated with a DFA.
- `DPDA_of_DFA_accepts` — the construction preserves the accepted language.
- `DFA_subclass_DPDA` — every DFA language is a DPDA language.
- `NFA_subclass_DPDA` — every NFA language is a DPDA language.
-/

open Relation Classical

noncomputable section

variable {T : Type} [Fintype T]

/-- A DPDA that simulates a DFA while leaving its one-symbol stack unchanged. -/
@[expose]
public def DPDA_of_DFA {Q : Type} [Fintype Q] (M : DFA T Q) :
    DPDA Q T Unit where
  initial_state := M.start
  start_symbol := ()
  final_states := M.accept
  transition q a _ := some (M.step q a, [()])
  epsilon_transition _ _ := none
  no_mixed := by intro _ _ h; exact absurd rfl h

/-- The simulating DPDA can follow every DFA run without changing its stack. -/
public lemma DPDA_of_DFA_reaches {Q : Type} [Fintype Q] (M : DFA T Q) (q : Q)
    (w : List T) :
    @PDA.Reaches Q T Unit _ _ _ (DPDA_of_DFA M).toPDA
      ⟨q, w, [()]⟩ ⟨M.evalFrom q w, [], [()]⟩ := by
  induction' w with a w ih generalizing q <;> simp_all +decide [DFA.evalFrom]
  · exact Relation.ReflTransGen.refl
  · refine Relation.ReflTransGen.trans ?_ (ih _)
    apply_rules [Relation.ReflTransGen.single]
    constructor
    unfold DPDA.toPDA
    simp +decide [DPDA_of_DFA]

/-- Any accepting run of the simulating DPDA is the corresponding DFA run. -/
public lemma DPDA_of_DFA_reaches_unique {Q : Type} [Fintype Q] (M : DFA T Q)
    (q : Q) (w : List T) (q' : Q) (γ : List Unit)
    (h : @PDA.Reaches Q T Unit _ _ _ (DPDA_of_DFA M).toPDA
      ⟨q, w, [()]⟩ ⟨q', [], γ⟩) :
    q' = M.evalFrom q w ∧ γ = [()] := by
  induction' w with a w ih generalizing q q'
  · contrapose! h
    intro H
    have := H.cases_head
    simp_all +decide [PDA.Reaches₁]
    simp_all +decide [PDA.step]
    unfold DPDA_of_DFA at this
    aesop
  · obtain ⟨q'', hq'', h'⟩ := Relation.ReflTransGen.cases_head h
    rename_i h
    obtain ⟨c, hc₁, hc₂⟩ := h
    cases hc₁
    · unfold DPDA_of_DFA at *
      simp_all +decide
      unfold DPDA.toPDA at *
      simp_all +decide
      exact ih _ _ hc₂
    · simp_all +decide [DPDA_of_DFA]
      tauto

/-- The stack-ignoring DPDA accepts exactly the language of its source DFA. -/
public theorem DPDA_of_DFA_accepts {Q : Type} [Fintype Q] (M : DFA T Q) :
    (DPDA_of_DFA M).acceptsByFinalState = M.accepts := by
  ext w
  constructor <;> intro h
  · obtain ⟨q, hq, γ, hγ⟩ := h
    have := DPDA_of_DFA_reaches_unique M _ _ _ _ hγ
    aesop
  · rw [DFA.mem_accepts] at h
    exact ⟨M.eval w, h, [()], DPDA_of_DFA_reaches M M.start w⟩

/-- Every language accepted by a DFA is accepted by a DPDA, via `DPDA_of_DFA`. -/
public theorem is_DPDA_of_is_DFA {L : Language T} (hL : is_DFA L) : is_DPDA L := by
  obtain ⟨Q, hQ, M, hM⟩ := hL
  exact ⟨Q, Unit, hQ, inferInstance, DPDA_of_DFA M,
    (DPDA_of_DFA_accepts M).trans hM⟩

/-- DFA-recognizable languages form a subclass of DPDA-recognizable languages. -/
public theorem DFA_subclass_DPDA :
    (DFA.Class : Set (Language T)) ⊆ DPDA.Class := by
  intro L hL
  exact is_DPDA_of_is_DFA hL

/-- Every language accepted by an NFA is accepted by a DPDA.  The construction
first uses the finite subset construction and then `DPDA_of_DFA`. -/
public theorem is_DPDA_of_is_NFA {L : Language T} (hL : is_NFA L) : is_DPDA L := by
  obtain ⟨Q, hQ, M, hM⟩ := hL
  exact ⟨Set Q, Unit, inferInstance, inferInstance, DPDA_of_DFA M.toDFA,
    (DPDA_of_DFA_accepts M.toDFA).trans (NFA.toDFA_correct.trans hM)⟩

/-- NFA-recognizable languages form a subclass of DPDA-recognizable languages. -/
public theorem NFA_subclass_DPDA :
    (NFA.Class : Set (Language T)) ⊆ DPDA.Class := by
  intro L hL
  exact is_DPDA_of_is_NFA hL

end
