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

/-- Backward direction of `PDA_FS_subset_ES`. -/
lemma PDA_FS_to_ES_backward {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (h : w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack) :
    w ∈ M.acceptsByFinalState := by
  sorry

/-- Any PDA final-state language is also a PDA empty-stack language. -/
theorem PDA_FS_subset_ES {Q S : Type} [Fintype Q] [Fintype S] (M : PDA Q T S) :
    is_PDA M.acceptsByFinalState := by
  refine ⟨Q ⊕ Fin 2, Option S, inferInstance, inferInstance, PDA_FS_to_ES_pda M, ?_⟩
  ext w
  exact ⟨PDA_FS_to_ES_backward M w, PDA_FS_to_ES_forward M w⟩

end PDA_FS_to_ES
