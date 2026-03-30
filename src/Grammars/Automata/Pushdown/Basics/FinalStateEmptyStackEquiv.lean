/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grammars.Automata.Pushdown.Basics.PDA
import Grammars.Classes.ContextFree.Basics.PDAEquivalence

open PDA

variable {T : Type} [Fintype T]

section PDA_FS_to_ES

open Classical in
/-- ε-transition function for the FS→ES PDA conversion.
    Defined as a top-level function to ensure good definitional reduction. -/
noncomputable def PDA_FS_to_ES_eps {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : (Q ⊕ Fin 2) → (Option S) → Set ((Q ⊕ Fin 2) × List (Option S))
  | Sum.inr 0, none => {(Sum.inl M.initial_state, [some M.start_symbol, none])}
  | Sum.inl q, some s =>
      (fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' (M.transition_fun' q s)
        ∪ (if q ∈ M.final_states then {(Sum.inr 1, [])} else ∅)
  | Sum.inl q, none =>
      if q ∈ M.final_states then {(Sum.inr 1, [])} else ∅
  | Sum.inr 1, _ => {(Sum.inr 1, [])}
  | Sum.inr 0, some _ => ∅

open Classical in
/-- Input-reading transition function for the FS→ES PDA conversion. -/
noncomputable def PDA_FS_to_ES_trans {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : (Q ⊕ Fin 2) → T → (Option S) → Set ((Q ⊕ Fin 2) × List (Option S))
  | Sum.inl q, a, some s =>
      (fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' (M.transition_fun q a s)
  | _, _, _ => ∅

open Classical in
/-- The PDA that converts final-state acceptance to empty-stack acceptance. -/
noncomputable def PDA_FS_to_ES_pda {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : PDA (Q ⊕ Fin 2) T (Option S) where
  initial_state := Sum.inr 0
  start_symbol := none
  final_states := ∅
  transition_fun := PDA_FS_to_ES_trans M
  transition_fun' := PDA_FS_to_ES_eps M
  finite q' a Z' := by
    simp only [PDA_FS_to_ES_trans]
    split <;> try exact Set.toFinite _
    exact (M.finite _ a _).image _
  finite' q' Z' := by
    simp only [PDA_FS_to_ES_eps]
    split <;> try exact Set.toFinite _
    · exact ((M.finite' _ _).image _).union (by split_ifs <;> exact Set.toFinite _)
    · exact (by split_ifs <;> exact Set.toFinite _)

/-- Lifting a configuration from the original PDA to the new PDA. -/
def liftConf {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) (c : PDA.conf M) : PDA.conf (PDA_FS_to_ES_pda M) :=
  ⟨Sum.inl c.state, c.input, c.stack.map some ++ [none]⟩

lemma simulation_step {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (r₁ r₂ : PDA.conf M)
    (h : PDA.Reaches₁ r₁ r₂) :
    PDA.Reaches₁ (liftConf M r₁) (liftConf M r₂) := by
  cases r₁ ; cases r₂ ; simp_all +decide [ Reaches₁ ]
  unfold step at *
  rename_i q w α q' w' α'
  rcases w with (_ | ⟨a, w⟩) <;> rcases α with (_ | ⟨Z, α⟩) <;> simp_all +decide [liftConf]
  · rcases h with ⟨β, hβ, rfl, rfl⟩
    use β.map some
    simp_all +decide [PDA_FS_to_ES_pda]
    unfold PDA_FS_to_ES_eps
    aesop
  · rcases h with (⟨β, hβ, rfl, rfl⟩ | ⟨β, hβ, rfl, rfl⟩) <;> simp_all +decide [PDA_FS_to_ES_pda]
    · exact Set.mem_image_of_mem _ hβ
    · exact Set.mem_union_left _ (Set.mem_image_of_mem _ hβ)

/-- Multi-step simulation: if M reaches r₂ from r₁, then M' reaches
    lift(r₂) from lift(r₁). -/
lemma simulation_reaches {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (r₁ r₂ : PDA.conf M)
    (h : PDA.Reaches r₁ r₂) :
    PDA.Reaches (liftConf M r₁) (liftConf M r₂) := by
  induction h with
  | refl => rfl
  | tail _ h₂ ih => exact Relation.ReflTransGen.tail ih (simulation_step M _ _ h₂)

lemma drain_reaches {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (γ : List (Option S)) :
    @PDA.Reaches (Q ⊕ Fin 2) T (Option S) _ _ _ (PDA_FS_to_ES_pda M)
      ⟨Sum.inr 1, [], γ⟩ ⟨Sum.inr 1, [], []⟩ := by
  induction' γ with Z γ ih generalizing M
  · constructor
  · have h_step : Reaches₁ (⟨Sum.inr 1, [], Z :: γ⟩ : PDA.conf (PDA_FS_to_ES_pda M))
        (⟨Sum.inr 1, [], γ⟩ : PDA.conf (PDA_FS_to_ES_pda M)) := by
      unfold PDA.Reaches₁
      unfold step
      aesop
    exact .single h_step |> Relation.ReflTransGen.trans <| ih M

lemma PDA_FS_to_ES_forward {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (h : w ∈ M.acceptsByFinalState) :
    w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack := by
  have h_path : ∀ (q : Q) (γ : List S), q ∈ M.final_states →
      M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩ →
      w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack := by
    intro q γ hq hγ
    have h_lift : (PDA_FS_to_ES_pda M).Reaches ⟨Sum.inr 0, w, [none]⟩
        ⟨Sum.inl q, [], γ.map some ++ [none]⟩ := by
      convert PDA.Reaches.trans _ (simulation_reaches M _ _ hγ) using 1
      constructor
      aesop
      apply Set.mem_setOf_eq.mpr
      cases w <;> simp +decide [liftConf]
      · exact Or.inl ⟨_, _, by tauto, rfl⟩
      · exact Or.inr <| Or.inl <| by unfold PDA_FS_to_ES_pda; aesop
    have h_path : (PDA_FS_to_ES_pda M).Reaches ⟨Sum.inl q, [], γ.map some ++ [none]⟩
        ⟨Sum.inr 1, [], []⟩ := by
      induction' γ with Z γ ih generalizing q <;> simp_all +decide [Reaches]
      · apply_rules [Relation.ReflTransGen.single]
        simp [Reaches₁, PDA_FS_to_ES_pda]
        simp +decide [step, hq]
        unfold PDA_FS_to_ES_eps
        aesop
      · have h_step : PDA.Reaches₁
          (⟨Sum.inl q, [], some Z :: (List.map some γ ++ [none])⟩ : PDA.conf (PDA_FS_to_ES_pda M))
          (⟨Sum.inr 1, [], List.map some γ ++ [none]⟩ : PDA.conf (PDA_FS_to_ES_pda M)) := by
          constructor
          swap
          exact Sum.inr 1
          simp +decide [PDA_FS_to_ES_pda, PDA_FS_to_ES_eps]
          assumption
        exact .single h_step |> Relation.ReflTransGen.trans <| drain_reaches M _
    use Sum.inr 1
    exact h_lift.trans h_path
  cases h
  aesop

lemma reverse_simulation_step {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (q₁ q₂ : Q) (w₁ w₂ : List T) (γ₁ γ₂ : List S)
    (h : @PDA.Reaches₁ (Q ⊕ Fin 2) T (Option S) _ _ _ (PDA_FS_to_ES_pda M)
      ⟨Sum.inl q₁, w₁, γ₁.map some⟩ ⟨Sum.inl q₂, w₂, γ₂.map some⟩) :
    @PDA.Reaches₁ Q T S _ _ _ M ⟨q₁, w₁, γ₁⟩ ⟨q₂, w₂, γ₂⟩ := by
  unfold Reaches₁ at *
  unfold PDA.step at *
  rcases w₁ with (_ | ⟨a, w₁⟩) <;> simp_all +decide [Set.ext_iff]
  · rcases γ₁ with (_ | ⟨Z, γ₁⟩) <;> simp_all +decide [PDA_FS_to_ES_pda]
    rcases h with ⟨β, hβ, rfl, hβ'⟩
    simp_all +decide [PDA_FS_to_ES_eps]
    have h_inj : Function.Injective (some : S → Option S) := by
      exact Option.some_injective _
    have h_eq : List.map some γ₂ = List.map some (hβ.choose ++ γ₁) := by
      convert hβ' using 1
      simp +decide [hβ.choose_spec.2]
    exact ⟨_, hβ.choose_spec.1, List.map_injective_iff.mpr h_inj h_eq⟩
  · rcases γ₁ with (_ | ⟨Z, α⟩) <;> simp_all +decide [PDA_FS_to_ES_pda, PDA_FS_to_ES_eps, PDA_FS_to_ES_trans]
    rcases h with (⟨β, h₁, rfl, h₂⟩ | ⟨β, h₁, rfl, h₂⟩) <;> [left; right] <;>
      use β <;> simp_all +decide [List.map_append]
    · exact List.map_injective_iff.mpr (Option.some_injective _) <| by simpa using h₂
    · exact List.map_injective_iff.mpr (Option.some_injective _) <| by simpa using h₂

/-- Invariant for configurations reachable from the initial config of the FS→ES PDA.
    Every such configuration is either:
    (1) the initial config `(inr 0, w, [none])`
    (2) a simulation of M: `(inl q, w', γ.map some ++ [none])` with
        `M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, w', γ⟩`
    (3) the drain state `(inr 1, ...)` with a witness that some final state of M
        was reached on empty input. -/
def FSES_Inv {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T) (c : PDA.conf (PDA_FS_to_ES_pda M)) : Prop :=
  (c = ⟨Sum.inr 0, w, [none]⟩) ∨
  (∃ q : Q, ∃ w' : List T, ∃ γ : List S,
    c = ⟨Sum.inl q, w', γ.map some ++ [none]⟩ ∧
    M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, w', γ⟩) ∨
  (c.state = Sum.inr 1 ∧
    (c.input = [] →
      ∃ q ∈ M.final_states, ∃ γ' : List S,
        M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ'⟩))

/-- The invariant holds for the initial configuration. -/
lemma FSES_Inv_init {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T) :
    FSES_Inv M w ⟨Sum.inr 0, w, [none]⟩ := by
  left; rfl

/-
PROBLEM
The invariant is preserved by a single step.

PROVIDED SOLUTION
Case split on h_inv (the invariant for c₁):

**Case 1: c₁ = (Sum.inr 0, w, [none])** — initial state.
The step function from (Sum.inr 0, w, [none]): the stack top is none.
- If w = []: step = {r₂ | ∃ p β, (p,β) ∈ PDA_FS_to_ES_eps M (Sum.inr 0) none ∧ r₂ = (p, [], β)}
  PDA_FS_to_ES_eps (Sum.inr 0) none = {(Sum.inl M.initial_state, [some M.start_symbol, none])}
  So c₂ = (Sum.inl M.initial_state, [], [some M.start_symbol, none])
  This is Case 2 of the invariant with q = M.initial_state, w' = [], γ = [M.start_symbol], and M.Reaches is refl.

- If w = a::w': step includes ε-transition:
  PDA_FS_to_ES_eps (Sum.inr 0) none = {(Sum.inl M.initial_state, [some M.start_symbol, none])}
  Also PDA_FS_to_ES_trans (Sum.inr 0) a none = ∅ (matches | _, _, _ => ∅ since Sum.inr 0 is not Sum.inl)
  So c₂ = (Sum.inl M.initial_state, a::w', [some M.start_symbol, none])
  This is Case 2 with γ = [M.start_symbol] and M.Reaches is refl.

**Case 2: c₁ = (Sum.inl q, w', γ.map some ++ [none])** with M.Reaches to (q, w', γ).
Sub-case γ = Z :: γ': stack top is some Z.
- Input transition (if w' = a::w''): PDA_FS_to_ES_trans (Sum.inl q) a (some Z) = image of M.transition_fun q a Z.
  c₂ = (Sum.inl p, w'', β.map some ++ γ'.map some ++ [none]) for some (p, β) ∈ M.transition_fun q a Z.
  This gives Case 2 with γ_new = β ++ γ' and M.Reaches extended by M's step.

- ε-transition: PDA_FS_to_ES_eps (Sum.inl q) (some Z) = image of M.transition_fun' q Z ∪ (if q ∈ final_states then {(Sum.inr 1, [])} else ∅).
  - If from the M simulation part: c₂ = (Sum.inl p, w', β.map some ++ γ'.map some ++ [none]). Case 2.
  - If q ∈ final_states and c₂ = (Sum.inr 1, w', γ'.map some ++ [none]). Case 3:
    state is Sum.inr 1, and if w' = [], then we have M reaching (q, [], Z::γ') with q ∈ final_states.

Sub-case γ = []: stack is [none]. Stack top is none.
- PDA_FS_to_ES_trans for (Sum.inl q, _, none) returns ∅ (| _, _, _ => ∅ since none ≠ some s).
- PDA_FS_to_ES_eps (Sum.inl q) none = if q ∈ final_states then {(Sum.inr 1, [])} else ∅.
  If q ∈ final_states: c₂ = (Sum.inr 1, w', []). Case 3 with q final, M reaches (q, w', []).
  If q ∉ final_states: step is ∅, contradiction with h_step.

**Case 3: c₁.state = Sum.inr 1**.
From (Sum.inr 1, w_in, Z :: rest):
- PDA_FS_to_ES_eps (Sum.inr 1) Z = {(Sum.inr 1, [])}
  So c₂ = (Sum.inr 1, w_in, rest). Still Case 3. Input unchanged.
  If c₂.input = [], same as c₁.input = [], so same witness.
- PDA_FS_to_ES_trans (Sum.inr 1, _, _) = ∅.
If c₁.stack = []: step is ∅, contradiction.
-/
set_option maxHeartbeats 800000 in
lemma FSES_Inv_step {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (c₁ c₂ : PDA.conf (PDA_FS_to_ES_pda M))
    (h_inv : FSES_Inv M w c₁)
    (h_step : PDA.Reaches₁ c₁ c₂) :
    FSES_Inv M w c₂ := by
  cases' h_inv with h_inv_cases h_inv_cases;
  · cases' w with w <;> simp_all +decide [ Reaches₁ ];
    · cases c₂ ; simp_all +decide [ step ];
      unfold PDA_FS_to_ES_pda at h_step; simp_all +decide [ PDA_FS_to_ES_eps ] ;
      exact Or.inr <| Or.inl ⟨ M.initial_state, [ ], [ M.start_symbol ], by aesop ⟩;
    · cases' h_step with p hp;
      · obtain ⟨ p, β, hp, rfl ⟩ := p; simp_all +decide [ PDA_FS_to_ES_pda ] ;
        cases hp;
      · obtain ⟨ p, β, hp, rfl ⟩ := hp; simp_all +decide [ PDA_FS_to_ES_pda ] ;
        cases p <;> cases β <;> simp_all +decide [ PDA_FS_to_ES_eps ];
        exact Or.inr <| Or.inl ⟨ M.initial_state, _, _, rfl, by tauto ⟩;
  · rcases h_inv_cases with ( ⟨ q, w', γ, rfl, h ⟩ | ⟨ h₁, h₂ ⟩ ) <;> simp_all +decide [ FSES_Inv ];
    · unfold Reaches₁ at h_step;
      rcases γ with ( _ | ⟨ Z, γ ⟩ ) <;> simp_all +decide [ step ];
      · rcases w' with ( _ | ⟨ a, w' ⟩ ) <;> simp_all +decide [ PDA_FS_to_ES_pda ];
        · unfold PDA_FS_to_ES_eps at h_step; aesop;
        · rcases h_step with ( ( ⟨ a', β, h, rfl ⟩ | ⟨ β, h, rfl ⟩ | ⟨ β, h, rfl ⟩ ) | ⟨ a', β, h, rfl ⟩ | ⟨ β, h, rfl ⟩ | ⟨ β, h, rfl ⟩ ) <;> simp_all +decide [ PDA_FS_to_ES_trans, PDA_FS_to_ES_eps ];
      · rcases w' with ( _ | ⟨ a, w' ⟩ ) <;> simp_all +decide [ PDA_FS_to_ES_pda ];
        · unfold PDA_FS_to_ES_eps at h_step; simp_all +decide [ Set.mem_union, Set.mem_image ] ;
          rcases h_step with ( ⟨ a, b, h₁, rfl ⟩ | ⟨ h₁, rfl ⟩ ) <;> simp_all +decide [ Reaches ];
          · use b ++ γ; simp_all +decide [ List.map_append ] ;
            exact h.tail ( by exact ⟨ _, _, h₁, rfl ⟩ );
          · exact ⟨ q, h₁, Z :: γ, h ⟩;
        · rcases h_step with ( ( ⟨ q', β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ ) | ⟨ q', β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ ) <;> simp_all +decide [ PDA_FS_to_ES_trans, PDA_FS_to_ES_eps ];
          · rcases h₁ with ⟨ b, hb₁, rfl ⟩ ; use b ++ γ; simp_all +decide [ Reaches ] ;
            exact h.tail ( by exact Set.mem_union_left _ ⟨ q', b, hb₁, rfl ⟩ );
          · rcases h₁ with ⟨ b, hb₁, rfl ⟩ ; use b ++ γ; simp_all +decide [ Reaches ] ;
            exact h.trans ( Relation.ReflTransGen.single <| by exact Or.inr ⟨ q', b, hb₁, rfl ⟩ );
    · rcases c₁ with ⟨ q₁, w₁, γ₁ ⟩ ; rcases c₂ with ⟨ q₂, w₂, γ₂ ⟩ ; simp_all +decide [ Reaches₁ ] ;
      rcases γ₁ with ( _ | ⟨ Z, γ₁ ⟩ ) <;> simp_all +decide [ step ];
      rcases w₁ with ( _ | ⟨ a, w₁ ⟩ ) <;> simp_all +decide [ PDA_FS_to_ES_pda ];
      · rcases h_step with ( ⟨ a, β, h, rfl, rfl, rfl ⟩ | ⟨ β, h, rfl, rfl, rfl ⟩ | ⟨ β, h, rfl, rfl, rfl ⟩ ) <;> simp_all +decide [ PDA_FS_to_ES_eps ];
      · rcases h_step with ( ( ⟨ q, β, h₁, rfl, rfl, rfl ⟩ | ⟨ β, h₁, rfl, rfl, rfl ⟩ | ⟨ β, h₁, rfl, rfl, rfl ⟩ ) | ( ⟨ q, β, h₁, rfl, rfl, rfl ⟩ | ⟨ β, h₁, rfl, rfl, rfl ⟩ | ⟨ β, h₁, rfl, rfl, rfl ⟩ ) ) <;> simp_all +decide [ PDA_FS_to_ES_trans, PDA_FS_to_ES_eps ]

/-- The invariant is preserved by multi-step reachability. -/
lemma FSES_Inv_reaches {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (c₁ c₂ : PDA.conf (PDA_FS_to_ES_pda M))
    (h_inv : FSES_Inv M w c₁)
    (h_reach : PDA.Reaches c₁ c₂) :
    FSES_Inv M w c₂ := by
  induction h_reach with
  | refl => exact h_inv
  | tail _ h_step ih => exact FSES_Inv_step M w _ _ ih h_step

/-
PROBLEM
If the invariant holds at `(q, [], [])`, then `w ∈ M.acceptsByFinalState`.

PROVIDED SOLUTION
Case split on h_inv (the invariant for config (q, [], [])):

Case 1: (q, [], []) = (Sum.inr 0, w, [none]). This requires [] = [none], which is impossible. Contradiction.

Case 2: (q, [], []) = (Sum.inl q', w', γ.map some ++ [none]). This requires [] = γ.map some ++ [none]. But γ.map some ++ [none] always has at least one element (none), so [] ≠ γ.map some ++ [none]. Contradiction.

Case 3: q = Sum.inr 1 and (input = [] → ∃ q' ∈ final_states, ...). Since input = [], we get ∃ q' ∈ M.final_states, ∃ γ', M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q', [], γ'⟩. This is exactly acceptsByFinalState.
-/
lemma FSES_Inv_terminal {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (q : Q ⊕ Fin 2)
    (h_inv : FSES_Inv M w ⟨q, [], []⟩) :
    w ∈ M.acceptsByFinalState := by
  rcases h_inv with ( ⟨ ⟩ | ⟨ q, w', γ, h₁, h₂ ⟩ | ⟨ hq, h ⟩ ) <;> simp_all +decide [ FSES_Inv ];
  exact ⟨ _, h.choose_spec.1, _, h.choose_spec.2.choose_spec ⟩

/-- Backward direction of `PDA_FS_subset_ES`. -/
lemma PDA_FS_to_ES_backward {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (h : w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack) :
    w ∈ M.acceptsByFinalState := by
  obtain ⟨q, hreach⟩ := h
  exact FSES_Inv_terminal M w q
    (FSES_Inv_reaches M w _ _ (FSES_Inv_init M w) hreach)

/-- Any PDA final-state language is also a PDA empty-stack language. -/
theorem PDA_FS_subset_ES {Q S : Type} [Fintype Q] [Fintype S] (M : PDA Q T S) :
    is_PDA M.acceptsByFinalState := by
  refine ⟨Q ⊕ Fin 2, Option S, inferInstance, inferInstance, PDA_FS_to_ES_pda M, ?_⟩
  ext w
  exact ⟨PDA_FS_to_ES_backward M w, PDA_FS_to_ES_forward M w⟩

end PDA_FS_to_ES
