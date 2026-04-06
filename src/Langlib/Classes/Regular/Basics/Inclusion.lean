/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.Regular.Definition
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Classes.DeterministicContextFree.Basics.Inclusion
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv

/-! # Regular Language Inclusions

This file relates right-regular grammars (Type-3) to:
2. **Context-free languages** — every right-regular grammar is context-free.
3. **Deterministic context-free languages** — every regular language is a DCFL.

## Main results

- `RG_subclass_CF` — The class of right-regular languages is a subclass of the context free languages
- `RG_subclass_DCFL` - The class of right-regular languages is a subclass of DCFL

## References

* Hopcroft, Motwani, Ullman. *Introduction to Automata Theory, Languages, and Computation*,
  3rd ed. Section 3.3.
-/

open Relation Classical

noncomputable section

variable {T : Type}

-- ============================================================================
-- Conversion to unrestricted grammar
-- ============================================================================

/-- Convert a right-regular grammar to an unrestricted grammar.

Each RG rule is mapped to the corresponding unrestricted rule:
- `A → a B`  becomes `[] A [] → [a, B]`
- `A → a`    becomes `[] A [] → [a]`
- `A → ε`    becomes `[] A [] → []` -/
def grammar_of_RG (g : RG_grammar T) : grammar T where
  nt := g.nt
  initial := g.initial
  rules := g.rules.map fun r => ⟨[], r.lhs, [], r.output⟩

/-- An RG transformation step corresponds to a grammar transformation step. -/
lemma grammar_transforms_of_RG_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : RG_transforms g w₁ w₂) :
    grammar_transforms (grammar_of_RG g) w₁ w₂ := by
  obtain ⟨r, hr, u, v, hw1, hw2⟩ := h
  exact ⟨⟨[], r.lhs, [], r.output⟩,
    ⟨List.mem_map.mpr ⟨r, hr, rfl⟩, u, v, by simpa using hw1, by simpa using hw2⟩⟩

/-- A grammar transformation step from a converted RG corresponds to an RG step. -/
lemma RG_transforms_of_grammar_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : grammar_transforms (grammar_of_RG g) w₁ w₂) :
    RG_transforms g w₁ w₂ := by
  obtain ⟨r, hr, u, v, hw1, hw2⟩ := h
  simp only [grammar_of_RG, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨r', hr', u, v, by simpa using hw1, by simpa using hw2⟩

/-- RG derives iff grammar derives (for the converted grammar). -/
lemma RG_derives_iff_grammar_derives (g : RG_grammar T)
    (w₁ w₂ : List (symbol T g.nt)) :
    RG_derives g w₁ w₂ ↔ grammar_derives (grammar_of_RG g) w₁ w₂ := by
  constructor
  · intro h
    induction h with
    | refl => exact grammar_deri_self
    | tail _ hs ih =>
      exact grammar_deri_of_deri_tran ih (grammar_transforms_of_RG_transforms hs)
  · intro h
    induction h with
    | refl => exact RG_deri_self _
    | tail _ hs ih =>
      exact RG_deri_of_deri_tran ih (RG_transforms_of_grammar_transforms hs)

/-- Every right-regular language is recursively enumerable. -/
theorem RG_subclass_RE {L : Language T} (h : is_RG L) : is_RE L := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨grammar_of_RG g, ?_⟩
  ext w
  simp only [grammar_language, RG_language]
  exact (RG_derives_iff_grammar_derives g _ _).symm

-- ============================================================================
-- Part 1: RG ⊆ CFL
-- ============================================================================

/-- Convert a right-regular grammar to a context-free grammar. -/
def CF_grammar_of_RG (g : RG_grammar T) : CF_grammar T where
  nt := g.nt
  initial := g.initial
  rules := g.rules.map fun r => (r.lhs, r.output)

lemma CF_transforms_of_RG_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : RG_transforms g w₁ w₂) :
    CF_transforms (CF_grammar_of_RG g) w₁ w₂ := by
  obtain ⟨r, hr, u, v, hw1, hw2⟩ := h
  exact ⟨(r.lhs, r.output), u, v, List.mem_map.mpr ⟨r, hr, rfl⟩, hw1, hw2⟩

lemma RG_transforms_of_CF_transforms {g : RG_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CF_transforms (CF_grammar_of_RG g) w₁ w₂) :
    RG_transforms g w₁ w₂ := by
  obtain ⟨r, u, v, hr, hw1, hw2⟩ := h
  simp only [CF_grammar_of_RG, List.mem_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨r', hr', u, v, hw1, hw2⟩

lemma RG_derives_iff_CF_derives (g : RG_grammar T)
    (w₁ w₂ : List (symbol T g.nt)) :
    RG_derives g w₁ w₂ ↔ CF_derives (CF_grammar_of_RG g) w₁ w₂ := by
  constructor
  · intro h
    induction h with
    | refl => exact CF_deri_self
    | tail _ hs ih =>
      exact CF_deri_of_deri_tran ih (CF_transforms_of_RG_transforms hs)
  · intro h
    induction h with
    | refl => exact RG_deri_self _
    | tail _ hs ih =>
      exact RG_deri_of_deri_tran ih (RG_transforms_of_CF_transforms hs)

/-- Every right-regular language is context-free. -/
theorem is_CF_of_is_RG {L : Language T} (h : is_RG L) : is_CF L := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨CF_grammar_of_RG g, ?_⟩
  ext w
  simp only [CF_language, RG_language]
  exact (RG_derives_iff_CF_derives g _ _).symm

theorem RG_subclass_CF :
  (RG : Set (Language T)) ⊆ (CF : Set (Language T)) := by
  intro L hL
  exact is_CF_of_is_RG hL

-- ============================================================================
-- Part 2: RG ⊆ DCFL (via DFA → DPDA)
-- ============================================================================

variable [Fintype T]

/-- DPDA that simulates a DFA by ignoring its stack. -/
def DPDA_of_DFA {σ : Type} [Fintype σ] (M : DFA T σ) :
    DPDA σ T Unit where
  initial_state := M.start
  start_symbol := ()
  final_states := M.accept
  transition q a _ := some (M.step q a, [()])
  epsilon_transition _ _ := none
  no_mixed := by intro _ _ h; exact absurd rfl h

/-
PROBLEM
After processing `w` from state `q` in the DPDA, we reach `evalFrom q w` with stack `[()]`.

PROVIDED SOLUTION
By induction on `w`.

Base case (w = []): We need PDA.Reaches from ⟨q, [], [()]⟩ to ⟨q, [], [()]⟩. This is PDA.Reaches.refl (or Relation.ReflTransGen.refl).

Inductive step (w = a :: w'):
We need to show PDA.Reaches from ⟨q, a :: w', [()]⟩ to ⟨M.evalFrom q (a :: w'), [], [()]⟩.

Note M.evalFrom q (a :: w') = M.evalFrom (M.step q a) w'.

Step 1: One PDA step reading `a`:
The PDA configuration ⟨q, a :: w', [()]⟩ transitions to ⟨M.step q a, w', [()]⟩ via the transition function.

In the toPDA of our DPDA, `transition_fun q a () = {(M.step q a, [()])}` (since M.transition q a () = some (M.step q a, [()])).
So the PDA.step from ⟨q, a :: w', [()]⟩ includes ⟨M.step q a, w', [()]⟩.
This gives PDA.Reaches₁ and hence one step of PDA.Reaches.

Step 2: By induction hypothesis, PDA.Reaches from ⟨M.step q a, w', [()]⟩ to ⟨M.evalFrom (M.step q a) w', [], [()]⟩.

Combining steps 1 and 2 via transitivity gives the result.
-/
lemma DPDA_of_DFA_reaches {σ : Type} [Fintype σ] (M : DFA T σ) (q : σ) (w : List T) :
    @PDA.Reaches σ T Unit _ _ _ (DPDA_of_DFA M).toPDA
      ⟨q, w, [()]⟩ ⟨M.evalFrom q w, [], [()]⟩ := by
        induction' w with a w ih generalizing q <;> simp_all +decide [ DFA.evalFrom ];
        · exact Relation.ReflTransGen.refl
        · refine' Relation.ReflTransGen.trans _ ( ih _ );
          apply_rules [ Relation.ReflTransGen.single ];
          constructor;
          unfold DPDA.toPDA; simp +decide [ DPDA_of_DFA ] ;

/-
PROBLEM
The only reachable configuration with empty input from the DPDA initial config
    is the one predicted by the DFA.

PROVIDED SOLUTION
By induction on w.

Base case (w = []): We have PDA.Reaches ⟨q, [], [()]⟩ ⟨q', [], γ⟩.
Since the DPDA has no ε-transitions (epsilon_transition = none), the only possible step from ⟨q, [], [()]⟩ is an ε-transition, which doesn't exist. So the configuration is stuck, meaning q' = q and γ = [()] by PDA.reaches_on_empty_stack or similar. Since evalFrom q [] = q, we get q' = q = evalFrom q [].

Wait, actually, PDA.step from ⟨q, [], Z :: α⟩ only allows ε-transitions (transition_fun'). Since our toPDA has transition_fun' q Z = ∅ (because epsilon_transition q Z = none), PDA.step ⟨q, [], [()]⟩ = ∅. So no step is possible, and by ReflTransGen, q' = q and γ = [()].

Inductive step (w = a :: w'): We have PDA.Reaches ⟨q, a :: w', [()]⟩ ⟨q', [], γ⟩.
The first step from ⟨q, a :: w', [()]⟩ can be:
- A read transition: goes to ⟨M.step q a, w', [()]⟩ (the only option since transition q a () = some (M.step q a, [()]))
- An ε-transition: impossible since epsilon_transition is none

So PDA.Reaches must first go to ⟨M.step q a, w', [()]⟩, then to ⟨q', [], γ⟩.
By IH, q' = evalFrom (M.step q a) w' = evalFrom q (a :: w') and γ = [()].

The key is to use the determinism: from ⟨q, a :: w', [()]⟩, the PDA step set is exactly {⟨M.step q a, w', [()]⟩}. So any Reaches path must start by going there. Use PDA.step, show the step set is a singleton, then extract the intermediate config and apply IH.
-/
lemma DPDA_of_DFA_reaches_unique {σ : Type} [Fintype σ] (M : DFA T σ)
    (q : σ) (w : List T) (q' : σ) (γ : List Unit)
    (h : @PDA.Reaches σ T Unit _ _ _ (DPDA_of_DFA M).toPDA
      ⟨q, w, [()]⟩ ⟨q', [], γ⟩) :
    q' = M.evalFrom q w ∧ γ = [()] := by
      induction' w with a w ih generalizing q q';
      · contrapose! h;
        intro H;
        have := H.cases_head; simp_all +decide [ PDA.Reaches₁ ] ;
        simp_all +decide [ PDA.step ];
        unfold DPDA_of_DFA at this; aesop;
      · obtain ⟨ q'', hq'', h' ⟩ := Relation.ReflTransGen.cases_head h;
        rename_i h;
        obtain ⟨ c, hc₁, hc₂ ⟩ := h;
        cases hc₁;
        · unfold DPDA_of_DFA at *; simp_all +decide [ PDA.Reaches₁ ] ;
          unfold DPDA.toPDA at *; simp_all +decide [ PDA.Reaches₁ ] ;
          exact ih _ _ hc₂;
        · simp_all +decide [ DPDA_of_DFA ];
          tauto

/-
PROBLEM
The DPDA of a DFA accepts the same language as the DFA.

PROVIDED SOLUTION
Show set equality by ext w.

Forward: Assume w ∈ acceptsByFinalState, i.e., ∃ q ∈ M.accept, ∃ γ, PDA.Reaches ⟨M.start, w, [()]⟩ ⟨q, [], γ⟩. By DPDA_of_DFA_reaches_unique, q = M.evalFrom M.start w = M.eval w and γ = [()]. Since q ∈ M.accept, M.eval w ∈ M.accept, so w ∈ M.accepts.

Backward: Assume w ∈ M.accepts, i.e., M.eval w ∈ M.accept. By DPDA_of_DFA_reaches, PDA.Reaches ⟨M.start, w, [()]⟩ ⟨M.eval w, [], [()]⟩. Taking q = M.eval w and γ = [()], we get w ∈ acceptsByFinalState.
-/
theorem DPDA_of_DFA_accepts {σ : Type} [Fintype σ] (M : DFA T σ) :
    (DPDA_of_DFA M).acceptsByFinalState = M.accepts := by
      ext w;
      constructor <;> intro h;
      · obtain ⟨ q, hq, γ, hγ ⟩ := h;
        have := DPDA_of_DFA_reaches_unique M _ _ _ _ hγ;
        aesop;
      · rw [DFA.mem_accepts] at h
        exact ⟨M.eval w, h, [()], DPDA_of_DFA_reaches M M.start w⟩

/-- Every right-regular language over a finite alphabet is a DCFL. -/
theorem is_DCFL_of_is_RG {L : Language T} (h : is_RG L) : is_DCFL L := by
  obtain ⟨σ, hfin, M, rfl⟩ := isRegular_of_is_RG h
  exact ⟨σ, Unit, hfin, inferInstance, DPDA_of_DFA M, DPDA_of_DFA_accepts M⟩

theorem RG_subclass_DCFL {T : Type} [Fintype T] :
  RG ⊆ (DCFL : Set (Language T)) := by
  intro L
  exact is_DCFL_of_is_RG

end
