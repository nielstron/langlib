/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.DeterministicContextFree.Definition

/-! # DCF Closure Under Intersection with a Regular Language

This file proves that the intersection of a deterministic context-free language with a
regular language is again deterministic context-free.

## Strategy

Given a DPDA `M` over `(Q, T, S)` and a DFA `D` over `(T, σ)`, we build a **product DPDA**
over `(Q × σ, T, S)` that simulates both machines in parallel:

- On reading input symbol `a` with stack top `Z`:
  the DPDA component transitions via `M.transition q a Z` and
  the DFA component transitions via `D.step s a`.
- On an ε-transition with stack top `Z`:
  only the DPDA component moves (via `M.epsilon_transition q Z`);
  the DFA state stays the same.
- Acceptance: the product state `(q, s)` is accepting iff
  `q ∈ M.final_states` and `s ∈ D.accept`.

## Main declarations

- `DPDA.productDFA` : the product DPDA×DFA construction
- `DPDA.productDFA_correct` : the product accepts `M.acceptsByFinalState ⊓ D.accepts`
- `DCF_inter_regular` : DCFLs are closed under intersection with regular languages
-/

open PDA

noncomputable section

variable {Q T S σ : Type} [Fintype Q] [Fintype T] [Fintype S] [Fintype σ]

namespace DPDA

/-- The **product DPDA×DFA**: runs a DPDA and a DFA in parallel. -/
def productDFA (M : DPDA Q T S) (D : DFA T σ) : DPDA (Q × σ) T S where
  initial_state := (M.initial_state, D.start)
  start_symbol := M.start_symbol
  final_states := {p | p.1 ∈ M.final_states ∧ p.2 ∈ D.accept}
  transition := fun ⟨q, s⟩ a Z =>
    match M.transition q a Z with
    | some (q', γ) => some ((q', D.step s a), γ)
    | none => none
  epsilon_transition := fun ⟨q, s⟩ Z =>
    match M.epsilon_transition q Z with
    | some (q', γ) => some ((q', s), γ)
    | none => none
  no_mixed := by
    intro ⟨q, s⟩ Z hε a
    simp only at hε ⊢
    have : M.epsilon_transition q Z ≠ none := by
      intro h; simp [h] at hε
    have := M.no_mixed q Z this a
    simp [this]

/-
-----------------------------------------------------------------------
One-step projection lemmas
-----------------------------------------------------------------------

One step in the product projects to one step in the DPDA.
-/
theorem productDFA_step_projects (M : DPDA Q T S) (D : DFA T σ)
    {c₁ c₂ : @PDA.conf (Q × σ) T S _ _ _ (M.productDFA D).toPDA}
    (h : @PDA.Reaches₁ (Q × σ) T S _ _ _ (M.productDFA D).toPDA c₁ c₂) :
    @PDA.Reaches₁ Q T S _ _ _ M.toPDA
      ⟨c₁.state.1, c₁.input, c₁.stack⟩
      ⟨c₂.state.1, c₂.input, c₂.stack⟩ := by
  rcases c₁ with ⟨ ⟨ q₁, s₁ ⟩, w₁, γ₁ ⟩ ; rcases c₂ with ⟨ ⟨ q₂, s₂ ⟩, w₂, γ₂ ⟩ ; simp_all +decide [ Reaches₁ ];
  cases w₁ <;> cases γ₁ <;> simp_all +decide [ step ];
  · obtain ⟨ β, hβ, rfl, rfl ⟩ := h;
    cases hβ' : M.epsilon_transition q₁ ‹_› <;> simp_all +decide [ DPDA.toPDA, PDA.transition_fun' ];
    · unfold DPDA.productDFA at hβ; aesop;
    · unfold DPDA.productDFA at hβ; aesop;
  · unfold DPDA.toPDA at *; simp_all +decide [ PDA.transition_fun, PDA.transition_fun' ] ;
    unfold DPDA.productDFA at *;
    cases h' : M.transition q₁ ‹_› ‹_› <;> cases h'' : M.epsilon_transition q₁ ‹_› <;> simp_all +decide [ Set.mem_singleton_iff ];
    have := M.no_mixed q₁ ‹_›; aesop;

/-
One step in the product: the DFA state is updated by the consumed input.
-/
theorem productDFA_step_dfa (M : DPDA Q T S) (D : DFA T σ)
    {c₁ c₂ : @PDA.conf (Q × σ) T S _ _ _ (M.productDFA D).toPDA}
    (h : @PDA.Reaches₁ (Q × σ) T S _ _ _ (M.productDFA D).toPDA c₁ c₂) :
    ∃ consumed : List T, c₁.input = consumed ++ c₂.input ∧
      c₂.state.2 = consumed.foldl D.step c₁.state.2 := by
  rcases c₁ with ⟨ ⟨ q₁, s₁ ⟩, x₁, σ₁ ⟩ ; rcases c₂ with ⟨ ⟨ q₂, s₂ ⟩, x₂, σ₂ ⟩ ;
  rcases x₁ with ( _ | ⟨ a, x₁ ⟩ ) <;> rcases σ₁ with ( _ | ⟨ Z, σ₁ ⟩ ) <;> simp_all +decide [ Reaches₁ ];
  · cases h;
  · cases h;
    rename_i h;
    obtain ⟨ β, hβ₁, hβ₂ ⟩ := h;
    unfold DPDA.toPDA at hβ₁;
    unfold DPDA.productDFA at hβ₁;
    cases h : M.epsilon_transition q₁ Z <;> simp_all +decide;
  · cases h;
  · cases h;
    · unfold DPDA.toPDA at *;
      unfold DPDA.productDFA at *;
      cases h : M.transition q₁ a Z <;> simp_all +decide [ Set.mem_setOf_eq ];
      exact ⟨ [ a ], rfl, rfl ⟩;
    · unfold DPDA.productDFA at *;
      unfold DPDA.toPDA at *;
      cases h : M.epsilon_transition q₁ Z <;> simp_all +decide [ Set.mem_setOf_eq ]

/-
One step in the DPDA lifts to one step in the product.
-/
theorem productDFA_step_lift (M : DPDA Q T S) (D : DFA T σ)
    (q : Q) (s : σ) (w : List T) (γ : List S)
    (q' : Q) (w' : List T) (γ' : List S)
    (hstep : @PDA.Reaches₁ Q T S _ _ _ M.toPDA ⟨q, w, γ⟩ ⟨q', w', γ'⟩) :
    ∃ s', @PDA.Reaches₁ (Q × σ) T S _ _ _ (M.productDFA D).toPDA
      ⟨(q, s), w, γ⟩ ⟨(q', s'), w', γ'⟩ := by
  unfold PDA.Reaches₁ at *;
  cases w <;> cases γ <;> simp_all +decide [ step ];
  · unfold DPDA.toPDA at *;
    unfold DPDA.productDFA at *;
    cases h : M.epsilon_transition q ‹_› <;> simp_all +decide [ Set.mem_setOf_eq ];
    grind;
  · simp_all +decide [ DPDA.toPDA, PDA.transition_fun, PDA.transition_fun' ];
    unfold DPDA.productDFA at *;
    cases h : M.transition q ‹_› ‹_› <;> cases h' : M.epsilon_transition q ‹_› <;> simp_all +decide;
    · grind;
    · grind;
    · have := M.no_mixed q ‹_›; aesop;

/-
-----------------------------------------------------------------------
Multi-step projection lemmas
-----------------------------------------------------------------------

Multi-step reachability in the product projects to multi-step reachability in the DPDA.
-/
theorem productDFA_reaches_projects (M : DPDA Q T S) (D : DFA T σ)
    (q : Q) (s : σ) (w : List T) (γ : List S)
    (q' : Q) (s' : σ) (w' : List T) (γ' : List S)
    (h : @PDA.Reaches (Q × σ) T S _ _ _ (M.productDFA D).toPDA
      ⟨(q, s), w, γ⟩ ⟨(q', s'), w', γ'⟩) :
    @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q, w, γ⟩ ⟨q', w', γ'⟩ := by
  have h_proj : ∀ {c₁ c₂ : @PDA.conf (Q × σ) T S _ _ _ (M.productDFA D).toPDA}, @PDA.Reaches₁ (Q × σ) T S _ _ _ (M.productDFA D).toPDA c₁ c₂ → @PDA.Reaches₁ Q T S _ _ _ M.toPDA ⟨c₁.state.1, c₁.input, c₁.stack⟩ ⟨c₂.state.1, c₂.input, c₂.stack⟩ := by
    exact?;
  have h_proj : ∀ {c₁ c₂ : @PDA.conf (Q × σ) T S _ _ _ (M.productDFA D).toPDA}, @PDA.Reaches (Q × σ) T S _ _ _ (M.productDFA D).toPDA c₁ c₂ → @PDA.Reaches Q T S _ _ _ M.toPDA ⟨c₁.state.1, c₁.input, c₁.stack⟩ ⟨c₂.state.1, c₂.input, c₂.stack⟩ := by
    intros c₁ c₂ h; induction h; aesop;
    exact Relation.ReflTransGen.tail ‹_› ( h_proj ‹_› );
  exact h_proj h

/-
Multi-step reachability in the product tracks the DFA state correctly.
-/
theorem productDFA_reaches_dfa_state (M : DPDA Q T S) (D : DFA T σ)
    (q : Q) (s : σ) (w : List T) (γ : List S)
    (q' : Q) (s' : σ) (w' : List T) (γ' : List S)
    (h : @PDA.Reaches (Q × σ) T S _ _ _ (M.productDFA D).toPDA
      ⟨(q, s), w, γ⟩ ⟨(q', s'), w', γ'⟩) :
    ∃ consumed : List T, w = consumed ++ w' ∧
      s' = consumed.foldl D.step s := by
  obtain ⟨ n, hn ⟩ := PDA.reaches_iff_reachesIn.mp h;
  induction' n with n ih generalizing q s w γ q' s' w' γ';
  · cases hn ; aesop;
  · rcases hn with ⟨ c, hc ⟩;
    rename_i c hc₁ hc₂;
    obtain ⟨ consumed₁, hconsumed₁, hconsumed₂ ⟩ := ih q s w γ c.state.1 c.state.2 c.input c.stack ( by
      exact? ) hc₁;
    obtain ⟨ consumed₂, hconsumed₃, hconsumed₄ ⟩ := productDFA_step_dfa M D hc₂;
    grind +splitIndPred

/-
Multi-step: DPDA reachability lifts to product reachability.
-/
theorem productDFA_reaches_lift (M : DPDA Q T S) (D : DFA T σ)
    (q : Q) (s : σ) (w : List T) (γ : List S)
    (q' : Q) (w' : List T) (γ' : List S)
    (hreach : @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q, w, γ⟩ ⟨q', w', γ'⟩) :
    ∃ s', @PDA.Reaches (Q × σ) T S _ _ _ (M.productDFA D).toPDA
      ⟨(q, s), w, γ⟩ ⟨(q', s'), w', γ'⟩ := by
  have h_ind : ∀ (c₁ c₂ : PDA.conf M.toPDA), @PDA.Reaches Q T S _ _ _ M.toPDA c₁ c₂ → ∀ s : σ, ∃ s' : σ, @PDA.Reaches (Q × σ) T S _ _ _ (M.productDFA D).toPDA ⟨(c₁.state, s), c₁.input, c₁.stack⟩ ⟨(c₂.state, s'), c₂.input, c₂.stack⟩ := by
    intro c₁ c₂ hreach s
    induction' hreach with c₁ c₂ hstep ih generalizing s;
    · exact ⟨ s, by rfl ⟩;
    · rename_i h;
      obtain ⟨ s', hs' ⟩ := h s;
      obtain ⟨ s'', hs'' ⟩ := productDFA_step_lift M D c₁.state s' c₁.input c₁.stack c₂.state c₂.input c₂.stack ih;
      exact ⟨ s'', hs'.trans ( Relation.ReflTransGen.single hs'' ) ⟩;
  exact h_ind _ _ hreach s

/-
The product DPDA accepts exactly the intersection of the DPDA language
    and the DFA language.
-/
theorem productDFA_correct (M : DPDA Q T S) (D : DFA T σ) :
    (M.productDFA D).acceptsByFinalState = M.acceptsByFinalState ⊓ D.accepts := by
  ext w;
  constructor;
  · rintro ⟨ q', s', γ', h ⟩;
    constructor;
    · use q'.1;
      exact ⟨ s'.1, γ', productDFA_reaches_projects M D _ _ _ _ _ _ _ _ h ⟩;
    · obtain ⟨ consumed, hconsumed ⟩ := productDFA_reaches_dfa_state M D _ _ _ _ _ _ _ _ h;
      cases s' ; aesop;
  · intro hw;
    obtain ⟨q', γ', hq', hw'⟩ := hw.left;
    obtain ⟨s', hs'⟩ := productDFA_reaches_lift M D M.toPDA.initial_state D.start w [M.toPDA.start_symbol] q' [] hq' hw';
    obtain ⟨consumed, hconsumed⟩ := productDFA_reaches_dfa_state M D M.toPDA.initial_state D.start w [M.toPDA.start_symbol] q' s' [] hq' hs';
    use (q', s');
    exact ⟨ ⟨ γ', by simpa [ hconsumed ] using hw.2 ⟩, _, hs' ⟩

end DPDA

/-- The class of deterministic context-free languages is closed under intersection
    with regular languages. -/
theorem DCF_inter_regular {T : Type} [Fintype T]
    (L₁ : Language T) (L₂ : Language T)
    (h₁ : is_DCF L₁) (h₂ : L₂.IsRegular) :
    is_DCF (L₁ ⊓ L₂) := by
  obtain ⟨Q, S, hQ, hS, M, rfl⟩ := h₁
  obtain ⟨σ, hσ, D, rfl⟩ := h₂
  exact ⟨Q × σ, S, inferInstance, hS, M.productDFA D, M.productDFA_correct D⟩

end