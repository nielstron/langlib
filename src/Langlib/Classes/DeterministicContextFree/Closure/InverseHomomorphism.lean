/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.DeterministicContextFree.Definition
import Langlib.Classes.DeterministicContextFree.Closure.IntersectionRegular
import Langlib.Classes.DeterministicContextFree.Closure.Bijection
import Langlib.Classes.ContextFree.Closure.InverseHomomorphism

/-! # DCF Closure Under Inverse String Homomorphism -/

open PDA

noncomputable section

variable {α β : Type}

section DirectConstruction

variable [Fintype α] [Fintype β]

abbrev BufState (α β : Type) (h : α → List β) :=
  Option (Σ a : α, Fin (h a).length)

variable {Q S : Type} [Fintype Q] [Fintype S]

def DPDA.invHomDPDA (M : DPDA Q β S) (h : α → List β) : DPDA (Q × BufState α β h) α S where
  initial_state := (M.initial_state, none)
  start_symbol := M.start_symbol
  final_states := {p | p.1 ∈ M.final_states ∧ p.2 = none}
  transition := fun ⟨q, buf⟩ a Z =>
    match buf with
    | none =>
      match M.epsilon_transition q Z with
      | some _ => none
      | none =>
        if hlen : 0 < (h a).length then
          some ((q, some ⟨a, ⟨0, hlen⟩⟩), [Z])
        else
          some ((q, none), [Z])
    | some _ => none
  epsilon_transition := fun ⟨q, buf⟩ Z =>
    match M.epsilon_transition q Z with
    | some (q', γ) => some ((q', buf), γ)
    | none =>
      match buf with
      | none => none
      | some ⟨a, k⟩ =>
        match M.transition q (h a |>.get k) Z with
        | some (q', γ) =>
          if hk : k.val + 1 < (h a).length then
            some ((q', some ⟨a, ⟨k.val + 1, hk⟩⟩), γ)
          else
            some ((q', none), γ)
        | none => none
  no_mixed := by
    intro ⟨q, buf⟩ Z hε a
    simp only at hε ⊢
    cases hm : M.epsilon_transition q Z with
    | some p =>
      cases buf with
      | none => simp [hm]
      | some _ => rfl
    | none =>
      cases buf with
      | none => simp [hm] at hε
      | some bval => rfl

-- Helpers

def extHomDCF (h : α → List β) (w : List α) : List β :=
  (w.map h).flatten

omit [Fintype α] [Fintype β] in
@[simp] theorem extHomDCF_nil (h : α → List β) : extHomDCF h [] = [] := rfl

omit [Fintype α] [Fintype β] in
@[simp] theorem extHomDCF_cons (h : α → List β) (a : α) (w : List α) :
    extHomDCF h (a :: w) = h a ++ extHomDCF h w := by simp [extHomDCF]

def bufRemaining (h : α → List β) : BufState α β h → List β
  | none => []
  | some ⟨a, k⟩ => (h a).drop k.val

@[simp] theorem bufRemaining_none (h : α → List β) : bufRemaining h none = [] := rfl

omit [Fintype α] [Fintype β] in
theorem inverseHomomorphicImage_eq_extHomDCF (L : Language β) (h : α → List β) :
    Language.inverseHomomorphicImage L h = {w | extHomDCF h w ∈ L} := by
  ext w; simp only [Language.inverseHomomorphicImage, Set.mem_setOf_eq]; rfl

-- Forward direction (unchanged from original)

private theorem invHom_proj_eps_of_M (M : DPDA Q β S) (h : α → List β)
    (q q' : Q) (buf : BufState α β h) (w : List α) (Z : S) (γ γ' : List S)
    (hε : M.epsilon_transition q Z = some (q', γ')) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨q, bufRemaining h buf ++ extHomDCF h w, Z :: γ⟩
      ⟨q', bufRemaining h buf ++ extHomDCF h w, γ' ++ γ⟩ := by
  apply Relation.ReflTransGen.single
  simp_all +decide [ PDA.Reaches₁, PDA.step ]
  unfold DPDA.toPDA; aesop

private theorem invHom_proj_drain_mid (M : DPDA Q β S) (h : α → List β)
    (q q' : Q) (a : α) (k : Fin (h a).length) (w : List α) (Z : S) (γ γ' : List S)
    (hnoε : M.epsilon_transition q Z = none)
    (htr : M.transition q ((h a).get k) Z = some (q', γ'))
    (hk : k.val + 1 < (h a).length) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨q, bufRemaining h (some ⟨a, k⟩) ++ extHomDCF h w, Z :: γ⟩
      ⟨q', bufRemaining h (some ⟨a, ⟨k.val + 1, hk⟩⟩) ++ extHomDCF h w, γ' ++ γ⟩ := by
  rw [show bufRemaining h (some ⟨a, k⟩) = (h a).get k :: (h a).drop (k + 1) from ?_]
  · exact Relation.ReflTransGen.single (by constructor; unfold DPDA.toPDA; aesop)
  · unfold bufRemaining; aesop

private theorem invHom_proj_drain_last (M : DPDA Q β S) (h : α → List β)
    (q q' : Q) (a : α) (k : Fin (h a).length) (w : List α) (Z : S) (γ γ' : List S)
    (hnoε : M.epsilon_transition q Z = none)
    (htr : M.transition q ((h a).get k) Z = some (q', γ'))
    (hk : ¬(k.val + 1 < (h a).length)) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨q, bufRemaining h (some ⟨a, k⟩) ++ extHomDCF h w, Z :: γ⟩
      ⟨q', bufRemaining h none ++ extHomDCF h w, γ' ++ γ⟩ := by
  unfold bufRemaining; simp +decide [*, List.drop_eq_nil_of_le]
  have h_step : List.drop (k : ℕ) (h a) = [(h a).get k] := by
    simp +zetaDelta at *
    rw [List.drop_eq_getElem_cons]
    rw [List.drop_eq_nil_of_le]; linarith [Fin.is_lt k]
  have h_step2 : @PDA.Reaches₁ Q β S _ _ _ M.toPDA ⟨q, [(h a).get k] ++ extHomDCF h w, Z :: γ⟩ ⟨q', extHomDCF h w, γ' ++ γ⟩ := by
    constructor; unfold DPDA.toPDA; aesop
  rw [h_step]; exact Relation.ReflTransGen.single h_step2

private theorem invHom_eps_step_extract (M : DPDA Q β S) (h : α → List β)
    (q : Q) (buf : BufState α β h) (w : List α) (Z : S) (γ : List S)
    (c : @PDA.conf _ α S _ _ _ (M.invHomDPDA h).toPDA)
    (hc : c ∈ {r | ∃ (p : Q × BufState α β h) (β_1 : List S),
      (p, β_1) ∈ (M.invHomDPDA h).toPDA.transition_fun' (q, buf) Z ∧
      r = ⟨p, w, β_1 ++ γ⟩}) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨q, bufRemaining h buf ++ extHomDCF h w, Z :: γ⟩
      ⟨c.state.1, bufRemaining h c.state.2 ++ extHomDCF h c.input, c.stack⟩ := by
  contrapose! hc
  simp [PDA.transition_fun'] at *
  intro p buf' γ' hp hc'
  cases hε : M.epsilon_transition q Z <;> simp_all +decide [PDA.transition_fun']
  · cases buf; simp_all +decide [PDA.transition_fun']
    · unfold DPDA.toPDA at hp; unfold DPDA.invHomDPDA at hp; simp_all +decide [PDA.transition_fun']
    · cases hp' : M.transition q ((h ‹(a : α) × Fin (h a).length›.1).get ‹(a : α) × Fin (h a).length›.2) Z <;> simp_all +decide [PDA.transition_fun']
      · unfold DPDA.toPDA at hp; unfold DPDA.invHomDPDA at hp; simp_all +decide [PDA.transition_fun']
      · unfold DPDA.toPDA at hp; unfold DPDA.invHomDPDA at hp; simp_all +decide [PDA.transition_fun']
        split_ifs at hp <;> simp_all +decide [PDA.transition_fun']
        · exact hc (invHom_proj_drain_mid M h _ _ _ _ _ _ _ _ hε hp' ‹_›)
        · rename_i k hk
          exact hc (by convert invHom_proj_drain_last M h q k.1 _ _ _ _ _ _ _ _ _ using 1 <;> [exact hε; convert hp' using 1; linarith])
  · unfold DPDA.toPDA at hp; simp_all +decide [PDA.transition_fun']
    unfold DPDA.invHomDPDA at hp; simp_all +decide [PDA.transition_fun']
    exact hc (by exact?)

private theorem invHom_input_step_extract (M : DPDA Q β S) (h : α → List β)
    (q : Q) (buf : BufState α β h) (a : α) (w : List α) (Z : S) (γ : List S)
    (c : @PDA.conf _ α S _ _ _ (M.invHomDPDA h).toPDA)
    (hc : c ∈ {r | ∃ (p : Q × BufState α β h) (β_1 : List S),
      (p, β_1) ∈ (M.invHomDPDA h).toPDA.transition_fun (q, buf) a Z ∧
      r = ⟨p, w, β_1 ++ γ⟩}) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨q, bufRemaining h buf ++ extHomDCF h (a :: w), Z :: γ⟩
      ⟨c.state.1, bufRemaining h c.state.2 ++ extHomDCF h c.input, c.stack⟩ := by
  rcases buf with (_ | ⟨a, k⟩) <;> simp_all +decide [PDA.transition_fun]
  · rcases hc with ⟨q', buf', β', h, rfl⟩
    unfold DPDA.toPDA DPDA.invHomDPDA at h
    rcases h : M.epsilon_transition q Z with (_ | ⟨q', γ'⟩) <;> simp_all +decide [PDA.transition_fun]
    split_ifs at * <;> simp_all +decide [PDA.Reaches]
    · unfold bufRemaining; aesop
    · rfl
  · unfold DPDA.toPDA at hc; rcases hc with ⟨q', b, β_1, hc, rfl⟩; unfold DPDA.invHomDPDA at hc; rcases hc with ⟨⟩

theorem invHom_step_projects (M : DPDA Q β S) (h : α → List β)
    {c₁ c₂ : @PDA.conf _ α S _ _ _ (M.invHomDPDA h).toPDA}
    (hstep : @PDA.Reaches₁ _ α S _ _ _ (M.invHomDPDA h).toPDA c₁ c₂) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨c₁.state.1, bufRemaining h c₁.state.2 ++ extHomDCF h c₁.input, c₁.stack⟩
      ⟨c₂.state.1, bufRemaining h c₂.state.2 ++ extHomDCF h c₂.input, c₂.stack⟩ := by
  rcases c₁ with ⟨⟨q, buf⟩, w, stk⟩; rcases stk with (_ | ⟨Z, γ⟩) <;> simp_all +decide [Reaches₁]
  · unfold step at hstep; aesop
  · rcases w with (_ | ⟨a, w⟩) <;> simp_all +decide [step]
    · obtain ⟨a, b, β_1, h₁, rfl⟩ := hstep
      have := invHom_eps_step_extract M h q buf [] Z γ ⟨⟨a, b⟩, [], β_1 ++ γ⟩ ⟨⟨a, b⟩, β_1, h₁, rfl⟩; aesop
    · rcases hstep with (⟨q', buf', γ', h₁, rfl⟩ | ⟨q', buf', γ', h₁, rfl⟩) <;> simp_all +decide [PDA.conf]
      · convert invHom_input_step_extract M h q buf a w Z γ ⟨(q', buf'), w, γ' ++ γ⟩ _ using 1
        exact ⟨_, _, h₁, rfl⟩
      · convert invHom_eps_step_extract M h q buf (a :: w) Z γ ⟨(q', buf'), a :: w, γ' ++ γ⟩ _ using 1
        exact ⟨_, _, h₁, rfl⟩

theorem invHom_reaches_projects (M : DPDA Q β S) (h : α → List β)
    {c₁ c₂ : @PDA.conf _ α S _ _ _ (M.invHomDPDA h).toPDA}
    (hreach : @PDA.Reaches _ α S _ _ _ (M.invHomDPDA h).toPDA c₁ c₂) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨c₁.state.1, bufRemaining h c₁.state.2 ++ extHomDCF h c₁.input, c₁.stack⟩
      ⟨c₂.state.1, bufRemaining h c₂.state.2 ++ extHomDCF h c₂.input, c₂.stack⟩ := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans ih (invHom_step_projects M h hstep)

-- Backward direction

private theorem invHom_lift_eps_one (M : DPDA Q β S) (h : α → List β)
    (q q' : Q) (γ γ' : List S)
    (hstep : @PDA.Reaches₁ _ β S _ _ _ M.toPDA ⟨q, [], γ⟩ ⟨q', [], γ'⟩) :
    @PDA.Reaches₁ _ α S _ _ _ (M.invHomDPDA h).toPDA
      ⟨(q, (none : BufState α β h)), [], γ⟩ ⟨(q', (none : BufState α β h)), [], γ'⟩ := by
  revert hstep
  induction' γ with x γ ih generalizing q q' γ'
  · intro h; cases h
  · intro h; rcases h with ⟨h₁, h₂⟩
    cases h' : M.epsilon_transition q x <;> simp_all +decide [DPDA.toPDA]
    constructor; unfold DPDA.invHomDPDA; aesop

private theorem invHom_lift_eps_none_in (M : DPDA Q β S) (h : α → List β)
    (n : ℕ) (q q' : Q) (γ γ' : List S)
    (hreach : @PDA.ReachesIn _ β S _ _ _ M.toPDA n ⟨q, [], γ⟩ ⟨q', [], γ'⟩) :
    @PDA.Reaches _ α S _ _ _ (M.invHomDPDA h).toPDA
      ⟨(q, (none : BufState α β h)), [], γ⟩ ⟨(q', (none : BufState α β h)), [], γ'⟩ := by
  induction' n with n ih generalizing q q' γ γ'
  · cases hreach; aesop
  · obtain ⟨c, hc⟩ := hreach
    rename_i c hc₁ hc₂
    obtain ⟨q'', γ'', hq''⟩ : ∃ q'' : Q, ∃ γ'' : List S, c = ⟨q'', [], γ''⟩ := by
      obtain ⟨w, hw⟩ := PDA.decreasing_input (PDA.reaches_of_reachesIn hc₁)
      cases w <;> aesop
    have := invHom_lift_eps_one M h q'' q' γ'' γ' (by aesop)
    exact Relation.ReflTransGen.tail (ih q q'' γ γ'' (by simpa [hq''] using hc₁)) this

private theorem invHom_lift_eps_none (M : DPDA Q β S) (h : α → List β)
    (q q' : Q) (γ γ' : List S)
    (hreach : @PDA.Reaches _ β S _ _ _ M.toPDA ⟨q, [], γ⟩ ⟨q', [], γ'⟩) :
    @PDA.Reaches _ α S _ _ _ (M.invHomDPDA h).toPDA
      ⟨(q, none), [], γ⟩ ⟨(q', none), [], γ'⟩ := by
  obtain ⟨n, hn⟩ := PDA.reaches_iff_reachesIn.mp hreach
  exact invHom_lift_eps_none_in M h n q q' γ γ' hn

private theorem invHom_lift_skip_empty (M : DPDA Q β S) (h : α → List β)
    (q : Q) (a : α) (w : List α) (Z : S) (γ : List S)
    (hlen : (h a).length = 0) (hnoε : M.epsilon_transition q Z = none) :
    @PDA.Reaches₁ _ α S _ _ _ (M.invHomDPDA h).toPDA
      ⟨(q, none), a :: w, Z :: γ⟩ ⟨(q, none), w, Z :: γ⟩ := by
  constructor; unfold DPDA.toPDA; simp +decide [hlen, hnoε]
  unfold DPDA.invHomDPDA; aesop

private theorem invHom_gen_lift_eps_first (M : DPDA Q β S) (h : α → List β)
    (n : ℕ) (q q_e : Q) (Z : S) (γ_e rest : List S) (input : List β)
    (q' : Q) (γ' : List S)
    (hε : M.epsilon_transition q Z = some (q_e, γ_e))
    (hreach : @PDA.ReachesIn _ β S _ _ _ M.toPDA (n + 1)
      ⟨q, input, Z :: rest⟩ ⟨q', [], γ'⟩) :
    @PDA.ReachesIn _ β S _ _ _ M.toPDA n
      ⟨q_e, input, γ_e ++ rest⟩ ⟨q', [], γ'⟩ := by
  obtain ⟨c, hc1, hc2⟩ := PDA.reachesIn_iff_split_first.mpr hreach
  have := PDA.reachesIn_one.mp hc1
  unfold step at this
  cases input <;> simp_all +decide [DPDA.toPDA]
  cases this <;> simp_all +decide [DPDA.no_mixed]

private theorem invHom_gen_lift_read_first (M : DPDA Q β S) (h : α → List β)
    (n : ℕ) (q q_t : Q) (b : β) (Z : S) (γ_t rest : List S) (input_tail : List β)
    (q' : Q) (γ' : List S)
    (hnoε : M.epsilon_transition q Z = none)
    (htr : M.transition q b Z = some (q_t, γ_t))
    (hreach : @PDA.ReachesIn _ β S _ _ _ M.toPDA (n + 1)
      ⟨q, b :: input_tail, Z :: rest⟩ ⟨q', [], γ'⟩) :
    @PDA.ReachesIn _ β S _ _ _ M.toPDA n
      ⟨q_t, input_tail, γ_t ++ rest⟩ ⟨q', [], γ'⟩ := by
  -- By definition of ReachesIn, we can split the proof into two parts: the first step and the remaining steps.
  obtain ⟨c, hc⟩ : ∃ c, @PDA.Reaches₁ Q β S _ _ _ M.toPDA ⟨q, b :: input_tail, Z :: rest⟩ c ∧
    @PDA.ReachesIn Q β S _ _ _ M.toPDA n c ⟨q', [], γ'⟩ := by
      contrapose! hreach;
      intro h;
      have h_split : ∀ {c₁ c₂ : M.toPDA.conf} {n : ℕ}, @PDA.ReachesIn Q β S _ _ _ M.toPDA (n + 1) c₁ c₂ → ∃ c, @PDA.Reaches₁ Q β S _ _ _ M.toPDA c₁ c ∧ @PDA.ReachesIn Q β S _ _ _ M.toPDA n c c₂ := by
        intros c₁ c₂ n h; induction' n with n ih generalizing c₁ c₂; simp_all +decide [ PDA.ReachesIn ] ;
        · obtain ⟨ c, hc ⟩ := h;
          rename_i c₂ hc₁ hc₂;
          cases hc₁ ; aesop;
        · obtain ⟨ c, hc₁, hc₂ ⟩ := h;
          obtain ⟨ c, hc₁, hc₂ ⟩ := ih ‹_›; exact ⟨ c, hc₁, PDA.ReachesIn.step hc₂ ‹_› ⟩ ;
      exact hreach _ ( h_split h |> Classical.choose_spec |> And.left ) ( h_split h |> Classical.choose_spec |> And.right );
  unfold Reaches₁ at hc;
  unfold step at hc;
  unfold PDA.transition_fun' at hc; simp_all +decide [ DPDA.toPDA ] ;
  aesop

private theorem invHom_M'_eps_step (M : DPDA Q β S) (h : α → List β)
    (q q_e : Q) (buf : BufState α β h) (w : List α) (Z : S) (γ_e rest : List S)
    (hε : M.epsilon_transition q Z = some (q_e, γ_e)) :
    @PDA.Reaches₁ _ α S _ _ _ (M.invHomDPDA h).toPDA
      ⟨(q, buf), w, Z :: rest⟩ ⟨(q_e, buf), w, γ_e ++ rest⟩ := by
  rcases w with (_ | ⟨a, w⟩) <;> simp_all +decide [PDA.step, Reaches₁]
  · have : (DPDA.invHomDPDA M h).epsilon_transition (q, buf) Z = some ((q_e, buf), γ_e) := by
      unfold DPDA.invHomDPDA; aesop
    simp_all +decide [DPDA.toPDA, PDA.transition_fun']
  · unfold DPDA.invHomDPDA; unfold DPDA.toPDA; aesop

private theorem invHom_M'_input_step (M : DPDA Q β S) (h : α → List β)
    (q : Q) (a : α) (w : List α) (Z : S) (γ : List S)
    (hnoε : M.epsilon_transition q Z = none) (hlen : 0 < (h a).length) :
    @PDA.Reaches₁ _ α S _ _ _ (M.invHomDPDA h).toPDA
      ⟨(q, (none : BufState α β h)), a :: w, Z :: γ⟩
      ⟨(q, some ⟨a, ⟨0, hlen⟩⟩), w, Z :: γ⟩ := by
  simp +decide [Reaches₁, PDA.Reaches₁, PDA.step]
  unfold DPDA.toPDA; unfold DPDA.invHomDPDA; simp +decide [hnoε, hlen]

private theorem invHom_M'_drain_step (M : DPDA Q β S) (h : α → List β)
    (q q_t : Q) (a : α) (k : Fin (h a).length) (w : List α) (Z : S) (γ_t rest : List S)
    (hnoε : M.epsilon_transition q Z = none)
    (htr : M.transition q ((h a).get k) Z = some (q_t, γ_t)) :
    @PDA.Reaches₁ _ α S _ _ _ (M.invHomDPDA h).toPDA
      ⟨(q, some ⟨a, k⟩), w, Z :: rest⟩
      ⟨(q_t, if hk : k.val + 1 < (h a).length then some ⟨a, ⟨k.val + 1, hk⟩⟩ else none),
       w, γ_t ++ rest⟩ := by
  unfold Reaches₁; simp +decide [step, hnoε, htr]
  cases w <;> simp +decide [transition_fun, transition_fun']
  · unfold DPDA.toPDA PDA.transition_fun'; unfold DPDA.invHomDPDA; aesop
  · unfold DPDA.toPDA; unfold DPDA.invHomDPDA; aesop

/-- The main backward lifting lemma.
    Precondition: all configs reachable from the current M config have non-empty stack. -/
private theorem invHom_gen_lift (M : DPDA Q β S) (h : α → List β)
    (n : ℕ)
    (q : Q) (buf : BufState α β h) (w : List α) (γ : List S)
    (q' : Q) (γ' : List S)
    (hreach : @PDA.ReachesIn _ β S _ _ _ M.toPDA n
      ⟨q, bufRemaining h buf ++ extHomDCF h w, γ⟩ ⟨q', [], γ'⟩)
    (hne : ∀ (c : @PDA.conf _ β S _ _ _ M.toPDA),
      @PDA.Reaches _ β S _ _ _ M.toPDA
        ⟨q, bufRemaining h buf ++ extHomDCF h w, γ⟩ c → c.stack ≠ []) :
    @PDA.Reaches _ α S _ _ _ (M.invHomDPDA h).toPDA
      ⟨(q, buf), w, γ⟩ ⟨(q', none), [], γ'⟩ := by
  sorry

theorem invHom_reaches_lifts (M : DPDA Q β S) (h : α → List β)
    (q : Q) (w : List α) (γ : List S)
    (q' : Q) (γ' : List S)
    (hreach : @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨q, extHomDCF h w, γ⟩ ⟨q', [], γ'⟩)
    (hne : ∀ (c : @PDA.conf _ β S _ _ _ M.toPDA),
      @PDA.Reaches _ β S _ _ _ M.toPDA ⟨q, extHomDCF h w, γ⟩ c → c.stack ≠ []) :
    @PDA.Reaches _ α S _ _ _ (M.invHomDPDA h).toPDA
      ⟨(q, none), w, γ⟩ ⟨(q', none), [], γ'⟩ := by
  rw [PDA.reaches_iff_reachesIn] at hreach
  obtain ⟨n, hn⟩ := hreach
  exact invHom_gen_lift M h n q none w γ q' γ' hn hne

-- Bottom-of-stack marker

def DPDA.addBottomMarker (M : DPDA Q β S) : DPDA (Q ⊕ Unit) β (Option S) where
  initial_state := Sum.inr ()
  start_symbol := none
  final_states := {p | ∃ q ∈ M.final_states, p = Sum.inl q}
  transition := fun state a Z =>
    match state with
    | Sum.inr () => none
    | Sum.inl q =>
      match Z with
      | none => none
      | some Z => (M.transition q a Z).map fun ⟨q', γ⟩ => (Sum.inl q', γ.map some)
  epsilon_transition := fun state Z =>
    match state with
    | Sum.inr () =>
      match Z with
      | none => some (Sum.inl M.initial_state, [some M.start_symbol, none])
      | some _ => none
    | Sum.inl q =>
      match Z with
      | none => none
      | some Z => (M.epsilon_transition q Z).map fun ⟨q', γ⟩ => (Sum.inl q', γ.map some)
  no_mixed := by
    intro state Z hε a
    match state, Z with
    | Sum.inr (), none => simp_all
    | Sum.inr (), some _ => simp_all [Option.map]
    | Sum.inl q, none => simp_all [Option.map]
    | Sum.inl q, some Z =>
      simp only [Option.map] at hε ⊢
      cases hm : M.epsilon_transition q Z with
      | none => simp_all
      | some p =>
        have := M.no_mixed q Z (by simp [hm]) a
        simp_all

/-
Single-step: M step lifts to addBottomMarker step.
-/
private theorem addBottomMarker_lift_step (M : DPDA Q β S)
    (c₁ c₂ : @PDA.conf _ β S _ _ _ M.toPDA)
    (h : @PDA.Reaches₁ _ β S _ _ _ M.toPDA c₁ c₂) :
    @PDA.Reaches₁ _ β (Option S) _ _ _ M.addBottomMarker.toPDA
      ⟨Sum.inl c₁.state, c₁.input, c₁.stack.map some⟩
      ⟨Sum.inl c₂.state, c₂.input, c₂.stack.map some⟩ := by
  revert h;
  unfold Reaches₁;
  unfold step;
  rcases c₁ with ⟨ q, w, γ ⟩;
  cases γ <;> cases w <;> simp +decide [ * ];
  · unfold DPDA.toPDA at *;
    unfold DPDA.addBottomMarker at *;
    grind;
  · unfold DPDA.toPDA DPDA.addBottomMarker at * ; aesop

/-- Multi-step: M reaches lifts to addBottomMarker reaches. -/
private theorem addBottomMarker_lift_reaches (M : DPDA Q β S)
    (c₁ c₂ : @PDA.conf _ β S _ _ _ M.toPDA)
    (h : @PDA.Reaches _ β S _ _ _ M.toPDA c₁ c₂) :
    @PDA.Reaches _ β (Option S) _ _ _ M.addBottomMarker.toPDA
      ⟨Sum.inl c₁.state, c₁.input, c₁.stack.map some⟩
      ⟨Sum.inl c₂.state, c₂.input, c₂.stack.map some⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (addBottomMarker_lift_step M _ _ hstep)

/-
Single-step projection: addBottomMarker step from Sum.inl on some Z projects to M step.
-/
private theorem addBottomMarker_proj_step (M : DPDA Q β S)
    (q : Q) (input : List β) (Z : S) (rest : List (Option S))
    (c₂ : @PDA.conf _ β (Option S) _ _ _ M.addBottomMarker.toPDA)
    (h : @PDA.Reaches₁ _ β (Option S) _ _ _ M.addBottomMarker.toPDA
      ⟨Sum.inl q, input, some Z :: rest⟩ c₂) :
    ∃ q₂ β_new, c₂.state = Sum.inl q₂ ∧
      c₂.stack = β_new.map some ++ rest ∧
      @PDA.Reaches₁ _ β S _ _ _ M.toPDA ⟨q, input, Z :: rest.filterMap id⟩
        ⟨q₂, c₂.input, β_new ++ rest.filterMap id⟩ := by
  rcases c₂ with ⟨ q₂, input₂, stack₂ ⟩ ; rcases input with ( _ | ⟨ a, input ⟩ ) <;> simp_all +decide [ Reaches₁ ] ;
  · unfold step at *;
    unfold DPDA.toPDA at *; simp_all +decide [ DPDA.addBottomMarker ] ;
    cases h : M.epsilon_transition q Z <;> aesop;
  · rcases h with ⟨ q₂, hq₂ ⟩ ; simp_all +decide [ step ] ;
    · rcases hq₂ with ⟨ β_1, hβ_1, rfl, rfl, rfl ⟩ ; simp_all +decide [ DPDA.toPDA, PDA.transition_fun ] ;
      rcases h : M.transition q a Z with ( _ | ⟨ q₂, γ ⟩ ) <;> simp_all +decide [ DPDA.addBottomMarker ];
    · unfold PDA.transition_fun' at *; simp_all +decide [ PDA.step ] ;
      rcases ‹_› with ( ⟨ q₂, β_1, h₁, rfl, rfl, rfl ⟩ | ⟨ b, β_1, h₁, rfl, rfl, rfl ⟩ ) <;> simp_all +decide [ DPDA.toPDA ];
      · cases h : M.epsilon_transition q Z <;> simp_all +decide [ DPDA.addBottomMarker ];
        aesop;
      · cases h : M.epsilon_transition q Z <;> simp_all +decide [ DPDA.addBottomMarker ]

/-- Multi-step: addBottomMarker reaches from Sum.inl projects to M reaches.
    The stack invariant: addBottomMarker stack = M stack mapped with some ++ tail. -/
private theorem addBottomMarker_proj_reaches (M : DPDA Q β S)
    (q₁ q₂ : Q) (w₁ w₂ : List β) (γ₁ γ₂ : List S) (tail : List (Option S))
    (h : @PDA.Reaches _ β (Option S) _ _ _ M.addBottomMarker.toPDA
      ⟨Sum.inl q₁, w₁, γ₁.map some ++ tail⟩
      ⟨Sum.inl q₂, w₂, γ₂.map some ++ tail⟩)
    (hne : none ∈ γ₁.map some ++ tail) :
    @PDA.Reaches _ β S _ _ _ M.toPDA
      ⟨q₁, w₁, γ₁ ++ tail.filterMap id⟩
      ⟨q₂, w₂, γ₂ ++ tail.filterMap id⟩ := by
  sorry

theorem DPDA.addBottomMarker_forward (M : DPDA Q β S)
    (w : List β) (hw : w ∈ M.addBottomMarker.acceptsByFinalState) :
    w ∈ M.acceptsByFinalState := by
  sorry

theorem DPDA.addBottomMarker_backward (M : DPDA Q β S)
    (w : List β) (hw : w ∈ M.acceptsByFinalState) :
    w ∈ M.addBottomMarker.acceptsByFinalState := by
  obtain ⟨q, hq, γ, hγ⟩ : ∃ q ∈ M.final_states, ∃ γ, M.toPDA.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩ := by
    cases hw ; aesop;
  have h_lift : @PDA.Reaches _ β (Option S) _ _ _ M.addBottomMarker.toPDA
    ⟨Sum.inl M.initial_state, w, [some M.start_symbol]⟩
    ⟨Sum.inl q, [], γ.map some⟩ := by
      convert addBottomMarker_lift_reaches M _ _ hγ using 1;
  -- Combine the paths from the initial state to q and from q to the final state.
  have h_combined : @PDA.Reaches _ β (Option S) _ _ _ M.addBottomMarker.toPDA
    ⟨Sum.inr (), w, [none]⟩
    ⟨Sum.inl q, [], γ.map some ++ [none]⟩ := by
      have h_combined : @PDA.Reaches _ β (Option S) _ _ _ M.addBottomMarker.toPDA
        ⟨Sum.inr (), w, [none]⟩
        ⟨Sum.inl M.initial_state, w, [some M.start_symbol] ++ [none]⟩ := by
          apply_rules [ Relation.ReflTransGen.single ];
          simp [Reaches₁];
          unfold step; aesop;
      convert PDA.Reaches.trans h_combined _ using 1;
      exact?;
  exact ⟨ Sum.inl q, ⟨ q, hq, rfl ⟩, _, h_combined ⟩

theorem DPDA.addBottomMarker_correct (M : DPDA Q β S) :
    M.addBottomMarker.acceptsByFinalState = M.acceptsByFinalState := by
  ext w; exact ⟨M.addBottomMarker_forward w, M.addBottomMarker_backward w⟩

theorem DPDA.addBottomMarker_reachable_stack_ne (M : DPDA Q β S) (w : List β)
    (c : @PDA.conf _ β (Option S) _ _ _ M.addBottomMarker.toPDA)
    (hreach : @PDA.Reaches _ β (Option S) _ _ _ M.addBottomMarker.toPDA
      ⟨Sum.inr (), w, [none]⟩ c) :
    c.stack ≠ [] := by
  contrapose! hreach; simp_all +decide [ PDA.Reaches ] ;
  intro h
  have h_ind : ∀ c' : PDA.conf M.addBottomMarker.toPDA, Relation.ReflTransGen Reaches₁ ⟨Sum.inr (), w, [none]⟩ c' → none ∈ c'.stack := by
    intro c' hc'; induction hc' <;> simp_all +decide [ Reaches₁ ] ;
    rename_i c' hc' ih;
    rename_i c'';
    rename_i c'''; simp_all +decide [ step ] ;
    rcases c''' with ⟨ _ | q, _ | w, _ | Z ⟩ <;> simp_all +decide [ PDA.transition_fun, PDA.transition_fun' ] ;
    · cases Z <;> simp_all +decide [ PDA.transition_fun' ];
      · unfold DPDA.toPDA at hc'; simp_all +decide [ PDA.transition_fun' ] ;
        unfold DPDA.addBottomMarker at hc'; simp_all +decide [ PDA.transition_fun' ] ;
      · unfold PDA.transition_fun' at hc'; aesop;
    · rcases hc' with ( ( ⟨ a, β, h, rfl ⟩ | ⟨ b, β, h, rfl ⟩ ) | ⟨ a, β, h, rfl ⟩ | ⟨ b, β, h, rfl ⟩ ) <;> simp_all +decide [ PDA.transition_fun, PDA.transition_fun' ];
      · cases Z <;> simp_all +decide [ PDA.transition_fun ];
        exact?;
      · cases Z <;> simp_all +decide [ PDA.transition_fun ];
        cases h;
      · cases Z <;> simp_all +decide [ PDA.transition_fun' ];
        cases h;
      · cases Z <;> simp_all +decide [ PDA.transition_fun' ];
        cases h;
    · rcases hc' with ( ⟨ a, β_1, h, rfl ⟩ | ⟨ b, β_1, h, rfl ⟩ ) <;> simp_all +decide [ PDA.transition_fun' ];
      · cases Z <;> simp_all +decide [ PDA.transition_fun' ];
        cases h ; aesop;
      · cases Z <;> simp_all +decide [ PDA.transition_fun' ];
        cases h;
    · unfold DPDA.toPDA at hc'; simp_all +decide [ PDA.transition_fun, PDA.transition_fun' ] ;
      cases Z <;> simp_all +decide [ DPDA.addBottomMarker ];
  exact absurd ( h_ind c h ) ( by simp +decide [ hreach ] )

-- Main correctness

theorem DPDA.invHomDPDA_correct (M : DPDA Q β S) (h : α → List β)
    (hne : ∀ (w : List β) (c : @PDA.conf _ β S _ _ _ M.toPDA),
      @PDA.Reaches _ β S _ _ _ M.toPDA ⟨M.initial_state, w, [M.start_symbol]⟩ c →
      c.stack ≠ []) :
    (M.invHomDPDA h).acceptsByFinalState =
      Language.inverseHomomorphicImage M.acceptsByFinalState h := by
  rw [inverseHomomorphicImage_eq_extHomDCF]
  ext w
  unfold DPDA.acceptsByFinalState PDA.acceptsByFinalState
  constructor
  · rintro ⟨⟨q', buf'⟩, ⟨hq'_final, hbuf_none⟩, γ', hreach⟩
    change q' ∈ M.final_states at hq'_final
    change buf' = none at hbuf_none; subst hbuf_none
    have hproj := invHom_reaches_projects M h hreach
    simp only [bufRemaining, extHomDCF_nil, List.append_nil] at hproj
    exact ⟨q', hq'_final, γ', hproj⟩
  · rintro ⟨q', hq'_final, γ', hreach⟩
    have hreach' := invHom_reaches_lifts M h M.initial_state w [M.start_symbol] q' γ'
      hreach (hne (extHomDCF h w))
    exact ⟨(q', none), ⟨hq'_final, rfl⟩, γ', hreach'⟩

end DirectConstruction

theorem DCF_closed_under_inverse_homomorphism [Fintype α] [Fintype β]
    (L : Language β) (h : α → List β) (hL : is_DCF L) :
    is_DCF (Language.inverseHomomorphicImage L h) := by
  obtain ⟨Q, S, hQ, hS, M, rfl⟩ := hL
  let M' := M.addBottomMarker
  have hcorrect : M'.acceptsByFinalState = M.acceptsByFinalState := M.addBottomMarker_correct
  rw [← hcorrect]
  have hne : ∀ (w : List β) (c : @PDA.conf _ β (Option S) _ _ _ M'.toPDA),
      @PDA.Reaches _ β (Option S) _ _ _ M'.toPDA ⟨M'.initial_state, w, [M'.start_symbol]⟩ c →
      c.stack ≠ [] := fun w c hr => M.addBottomMarker_reachable_stack_ne w c hr
  exact ⟨(Q ⊕ Unit) × BufState α β h, Option S, inferInstance, inferInstance,
    M'.invHomDPDA h, M'.invHomDPDA_correct h hne⟩

end