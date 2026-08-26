module

/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license; see licenses/Apache-2.0.txt.
-/
public import Langlib.Automata.Pushdown.Definition
public import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



open PDA

variable {T : Type} [Fintype T]

section PDA_FS_to_ES

open Classical in
/-- ε-transition function for the FS→ES PDA conversion.
    Defined as a top-level function to ensure good definitional reduction. -/
@[expose]
public noncomputable def PDA_FS_to_ES_eps {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
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
@[expose]
public noncomputable def PDA_FS_to_ES_trans {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : (Q ⊕ Fin 2) → T → (Option S) → Set ((Q ⊕ Fin 2) × List (Option S))
  | Sum.inl q, a, some s =>
      (fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' (M.transition_fun q a s)
  | _, _, _ => ∅

open Classical in
/-- The PDA that converts final-state acceptance to empty-stack acceptance. -/
@[expose]
public noncomputable def PDA_FS_to_ES_pda {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
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
@[expose]
public def liftConf {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) (c : PDA.conf M) : PDA.conf (PDA_FS_to_ES_pda M) :=
  ⟨Sum.inl c.state, c.input, c.stack.map some ++ [none]⟩

public lemma simulation_step {Q S : Type} [Fintype Q] [Fintype S]
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
public lemma simulation_reaches {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (r₁ r₂ : PDA.conf M)
    (h : PDA.Reaches r₁ r₂) :
    PDA.Reaches (liftConf M r₁) (liftConf M r₂) := by
  induction h with
  | refl => rfl
  | tail _ h₂ ih => exact Relation.ReflTransGen.tail ih (simulation_step M _ _ h₂)

public lemma drain_reaches {Q S : Type} [Fintype Q] [Fintype S]
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

public lemma PDA_FS_to_ES_forward {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (h : w ∈ M.acceptsByFinalState) :
    w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack := by
  have h_path : ∀ (q : Q) (γ : List S), q ∈ M.final_states →
      M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩ →
      w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack := by
    intro q γ hq hγ
    have h_lift : (PDA_FS_to_ES_pda M).Reaches ⟨Sum.inr 0, w, [none]⟩
        ⟨Sum.inl q, [], γ.map some ++ [none]⟩ := by
      have h_init : (PDA_FS_to_ES_pda M).Reaches
          ⟨Sum.inr 0, w, [none]⟩
          (liftConf M ⟨M.initial_state, w, [M.start_symbol]⟩) := by
        apply Relation.ReflTransGen.single
        unfold Reaches₁ step
        cases w with
        | nil =>
            refine ⟨Sum.inl M.initial_state, [some M.start_symbol, none], ?_, rfl⟩
            exact Set.mem_singleton _
        | cons a w =>
            apply Set.mem_union_right
            refine ⟨Sum.inl M.initial_state, [some M.start_symbol, none], ?_, rfl⟩
            exact Set.mem_singleton _
      exact h_init.trans (simulation_reaches M _ _ hγ)
    have h_path : (PDA_FS_to_ES_pda M).Reaches ⟨Sum.inl q, [], γ.map some ++ [none]⟩
        ⟨Sum.inr 1, [], []⟩ := by
      induction' γ with Z γ ih generalizing q <;> simp_all +decide [Reaches]
      · apply_rules [Relation.ReflTransGen.single]
        simp [Reaches₁, PDA_FS_to_ES_pda]
        simp +decide [step]
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
  classical
  unfold Reaches₁ at *
  unfold PDA.step at *
  cases w₁ with
  | nil =>
      cases γ₁ with
      | nil => exact ((Set.mem_empty_iff_false _).mp h).elim
      | cons Z γ₁ =>
          rcases h with ⟨p, β, hβ, hc⟩
          have hp : Sum.inl q₂ = p := congrArg PDA.conf.state hc
          subst p
          change (Sum.inl q₂, β) ∈
            ((fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' M.transition_fun' q₁ Z) ∪
              (if q₁ ∈ M.final_states then {(Sum.inr 1, [])} else ∅) at hβ
          rw [Set.mem_union] at hβ
          rcases hβ with hβ | hβ
          · rcases hβ with ⟨⟨q', δ⟩, hδ, hmap⟩
            have hq' : q' = q₂ := Sum.inl.inj (congrArg Prod.fst hmap)
            subst q'
            have hmap' : δ.map some = β := congrArg Prod.snd hmap
            refine ⟨q₂, δ, hδ, ?_⟩
            apply PDA.conf.ext
            · rfl
            · exact congrArg (fun c : PDA.conf (PDA_FS_to_ES_pda M) => c.input) hc
            · apply List.map_injective_iff.mpr (Option.some_injective _)
              calc
                γ₂.map some = β ++ γ₁.map some := congrArg PDA.conf.stack hc
                _ = δ.map some ++ γ₁.map some := by rw [← hmap']
                _ = (δ ++ γ₁).map some := by rw [List.map_append]
          · by_cases hq : q₁ ∈ M.final_states <;> simp [hq] at hβ
  | cons a w₁ =>
      cases γ₁ with
      | nil => exact ((Set.mem_empty_iff_false _).mp h).elim
      | cons Z γ₁ =>
          simp only [List.map_cons] at h
          rw [Set.mem_union] at h ⊢
          rcases h with h | h
          · rcases h with ⟨p, β, hβ, hc⟩
            have hp : Sum.inl q₂ = p := congrArg PDA.conf.state hc
            subst p
            change (Sum.inl q₂, β) ∈
              (fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' M.transition_fun q₁ a Z at hβ
            rcases hβ with ⟨⟨q', δ⟩, hδ, hmap⟩
            have hq' : q' = q₂ := Sum.inl.inj (congrArg Prod.fst hmap)
            subst q'
            have hmap' : δ.map some = β := congrArg Prod.snd hmap
            left
            refine ⟨q₂, δ, hδ, ?_⟩
            apply PDA.conf.ext
            · rfl
            · exact congrArg (fun c : PDA.conf (PDA_FS_to_ES_pda M) => c.input) hc
            · apply List.map_injective_iff.mpr (Option.some_injective _)
              calc
                γ₂.map some = β ++ γ₁.map some := congrArg PDA.conf.stack hc
                _ = δ.map some ++ γ₁.map some := by rw [← hmap']
                _ = (δ ++ γ₁).map some := by rw [List.map_append]
          · rcases h with ⟨p, β, hβ, hc⟩
            have hp : Sum.inl q₂ = p := congrArg PDA.conf.state hc
            subst p
            change (Sum.inl q₂, β) ∈
              ((fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' M.transition_fun' q₁ Z) ∪
                (if q₁ ∈ M.final_states then {(Sum.inr 1, [])} else ∅) at hβ
            rw [Set.mem_union] at hβ
            rcases hβ with hβ | hβ
            · rcases hβ with ⟨⟨q', δ⟩, hδ, hmap⟩
              have hq' : q' = q₂ := Sum.inl.inj (congrArg Prod.fst hmap)
              subst q'
              have hmap' : δ.map some = β := congrArg Prod.snd hmap
              right
              refine ⟨q₂, δ, hδ, ?_⟩
              apply PDA.conf.ext
              · rfl
              · exact congrArg (fun c : PDA.conf (PDA_FS_to_ES_pda M) => c.input) hc
              · apply List.map_injective_iff.mpr (Option.some_injective _)
                calc
                  γ₂.map some = β ++ γ₁.map some := congrArg PDA.conf.stack hc
                  _ = δ.map some ++ γ₁.map some := by rw [← hmap']
                  _ = (δ ++ γ₁).map some := by rw [List.map_append]
            · by_cases hq : q₁ ∈ M.final_states <;> simp [hq] at hβ

/-- Invariant for configurations reachable from the initial config of the FS→ES PDA.
    Every such configuration is either:
    (1) the initial config `(inr 0, w, [none])`
    (2) a simulation of M: `(inl q, w', γ.map some ++ [none])` with
        `M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, w', γ⟩`
    (3) the drain state `(inr 1, ...)` with a witness that some final state of M
        was reached on empty input. -/
@[expose]
public def FSES_Inv {Q S : Type} [Fintype Q] [Fintype S]
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
public lemma FSES_Inv_init {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T) :
    FSES_Inv M w ⟨Sum.inr 0, w, [none]⟩ := by
  left; rfl

/-
The invariant is preserved by a single step.
-/
set_option maxHeartbeats 800000 in
public lemma FSES_Inv_step {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (c₁ c₂ : PDA.conf (PDA_FS_to_ES_pda M))
    (h_inv : FSES_Inv M w c₁)
    (h_step : PDA.Reaches₁ c₁ c₂) :
    FSES_Inv M w c₂ := by
  classical
  rcases h_inv with rfl | ⟨q, w', γ, rfl, hreach⟩ | ⟨hstate, hwitness⟩
  · unfold Reaches₁ step at h_step
    cases w with
    | nil =>
        rcases h_step with ⟨p, β, htrans, hc⟩
        change (p, β) ∈ ({(Sum.inl M.initial_state,
          [some M.start_symbol, none])} : Set ((Q ⊕ Fin 2) × List (Option S))) at htrans
        rw [Set.mem_singleton_iff] at htrans
        have hp := congrArg Prod.fst htrans
        have hβ := congrArg Prod.snd htrans
        simp only at hp hβ
        subst p
        subst β
        subst c₂
        exact Or.inr <| Or.inl ⟨M.initial_state, [], [M.start_symbol], rfl, Reaches.refl _⟩
    | cons a w =>
        rw [Set.mem_union] at h_step
        rcases h_step with hread | heps
        · rcases hread with ⟨p, β, htrans, _⟩
          change (p, β) ∈ (∅ : Set ((Q ⊕ Fin 2) × List (Option S))) at htrans
          exact ((Set.mem_empty_iff_false _).mp htrans).elim
        · rcases heps with ⟨p, β, htrans, hc⟩
          change (p, β) ∈ ({(Sum.inl M.initial_state,
            [some M.start_symbol, none])} : Set ((Q ⊕ Fin 2) × List (Option S))) at htrans
          rw [Set.mem_singleton_iff] at htrans
          have hp := congrArg Prod.fst htrans
          have hβ := congrArg Prod.snd htrans
          simp only at hp hβ
          subst p
          subst β
          subst c₂
          exact Or.inr <| Or.inl ⟨M.initial_state, a :: w, [M.start_symbol], rfl, Reaches.refl _⟩
  · unfold Reaches₁ step at h_step
    cases γ with
    | nil =>
        simp only [List.map_nil, List.nil_append] at h_step
        cases w' with
        | nil =>
            rcases h_step with ⟨p, β, htrans, hc⟩
            change (p, β) ∈ PDA_FS_to_ES_eps M (Sum.inl q) none at htrans
            by_cases hq : q ∈ M.final_states
            · simp only [PDA_FS_to_ES_eps, if_pos hq] at htrans
              rw [Set.mem_singleton_iff] at htrans
              have hp := congrArg Prod.fst htrans
              have hβ := congrArg Prod.snd htrans
              simp only at hp hβ
              subst p
              subst β
              subst c₂
              exact Or.inr <| Or.inr ⟨rfl, fun _ ↦ ⟨q, hq, [], hreach⟩⟩
            · simp only [PDA_FS_to_ES_eps, if_neg hq] at htrans
              exact ((Set.mem_empty_iff_false _).mp htrans).elim
        | cons a w' =>
            rw [Set.mem_union] at h_step
            rcases h_step with hread | heps
            · rcases hread with ⟨p, β, htrans, _⟩
              change (p, β) ∈ (∅ : Set ((Q ⊕ Fin 2) × List (Option S))) at htrans
              exact ((Set.mem_empty_iff_false _).mp htrans).elim
            · rcases heps with ⟨p, β, htrans, hc⟩
              change (p, β) ∈ PDA_FS_to_ES_eps M (Sum.inl q) none at htrans
              by_cases hq : q ∈ M.final_states
              · simp only [PDA_FS_to_ES_eps, if_pos hq] at htrans
                rw [Set.mem_singleton_iff] at htrans
                have hp := congrArg Prod.fst htrans
                have hβ := congrArg Prod.snd htrans
                simp only at hp hβ
                subst p
                subst β
                subst c₂
                exact Or.inr <| Or.inr ⟨rfl, by simp⟩
              · simp only [PDA_FS_to_ES_eps, if_neg hq] at htrans
                exact ((Set.mem_empty_iff_false _).mp htrans).elim
    | cons Z γ =>
        simp only [List.map_cons, List.cons_append] at h_step
        cases w' with
        | nil =>
            rcases h_step with ⟨p, β, htrans, hc⟩
            change (p, β) ∈
              ((fun x : Q × List S => (Sum.inl x.1, x.2.map some)) '' M.transition_fun' q Z) ∪
                (if q ∈ M.final_states then {(Sum.inr 1, [])} else ∅) at htrans
            rw [Set.mem_union] at htrans
            rcases htrans with hsim | hfinal
            · rcases hsim with ⟨⟨q', δ⟩, hδ, hmap⟩
              have hp := congrArg Prod.fst hmap
              have hβ := congrArg Prod.snd hmap
              simp only at hp hβ
              subst p
              subst β
              subst c₂
              refine Or.inr <| Or.inl ⟨q', [], δ ++ γ, ?_, ?_⟩
              · simp [List.map_append, List.append_assoc]
              · exact hreach.tail ⟨q', δ, hδ, rfl⟩
            · by_cases hq : q ∈ M.final_states
              · rw [if_pos hq, Set.mem_singleton_iff] at hfinal
                have hp := congrArg Prod.fst hfinal
                have hβ := congrArg Prod.snd hfinal
                simp only at hp hβ
                subst p
                subst β
                subst c₂
                exact Or.inr <| Or.inr ⟨rfl, fun _ ↦ ⟨q, hq, Z :: γ, hreach⟩⟩
              · rw [if_neg hq] at hfinal
                exact ((Set.mem_empty_iff_false _).mp hfinal).elim
        | cons a w' =>
            rw [Set.mem_union] at h_step
            rcases h_step with hread | heps
            · rcases hread with ⟨p, β, htrans, hc⟩
              change (p, β) ∈
                (fun x : Q × List S => (Sum.inl x.1, x.2.map some)) '' M.transition_fun q a Z at htrans
              rcases htrans with ⟨⟨q', δ⟩, hδ, hmap⟩
              have hp := congrArg Prod.fst hmap
              have hβ := congrArg Prod.snd hmap
              simp only at hp hβ
              subst p
              subst β
              subst c₂
              refine Or.inr <| Or.inl ⟨q', w', δ ++ γ, ?_, ?_⟩
              · simp [List.map_append, List.append_assoc]
              · exact hreach.tail (Set.mem_union_left _ ⟨q', δ, hδ, rfl⟩)
            · rcases heps with ⟨p, β, htrans, hc⟩
              change (p, β) ∈
                ((fun x : Q × List S => (Sum.inl x.1, x.2.map some)) '' M.transition_fun' q Z) ∪
                  (if q ∈ M.final_states then {(Sum.inr 1, [])} else ∅) at htrans
              rw [Set.mem_union] at htrans
              rcases htrans with hsim | hfinal
              · rcases hsim with ⟨⟨q', δ⟩, hδ, hmap⟩
                have hp := congrArg Prod.fst hmap
                have hβ := congrArg Prod.snd hmap
                simp only at hp hβ
                subst p
                subst β
                subst c₂
                refine Or.inr <| Or.inl ⟨q', a :: w', δ ++ γ, ?_, ?_⟩
                · simp [List.map_append, List.append_assoc]
                · exact hreach.tail (Set.mem_union_right _ ⟨q', δ, hδ, rfl⟩)
              · by_cases hq : q ∈ M.final_states
                · rw [if_pos hq, Set.mem_singleton_iff] at hfinal
                  have hp := congrArg Prod.fst hfinal
                  have hβ := congrArg Prod.snd hfinal
                  simp only at hp hβ
                  subst p
                  subst β
                  subst c₂
                  exact Or.inr <| Or.inr ⟨rfl, by simp⟩
                · rw [if_neg hq] at hfinal
                  exact ((Set.mem_empty_iff_false _).mp hfinal).elim
  · rcases c₁ with ⟨s, u, σ⟩
    simp only at hstate hwitness h_step ⊢
    subst s
    unfold Reaches₁ step at h_step
    cases σ with
    | nil =>
        cases u <;> exact ((Set.mem_empty_iff_false _).mp h_step).elim
    | cons Z σ =>
        cases u with
        | nil =>
            rcases h_step with ⟨p, β, htrans, hc⟩
            change (p, β) ∈ ({(Sum.inr 1, [])} : Set ((Q ⊕ Fin 2) × List (Option S))) at htrans
            rw [Set.mem_singleton_iff] at htrans
            have hp := congrArg Prod.fst htrans
            have hβ := congrArg Prod.snd htrans
            simp only at hp hβ
            subst p
            subst β
            subst c₂
            exact Or.inr <| Or.inr ⟨rfl, fun _ ↦ hwitness rfl⟩
        | cons a u =>
            rw [Set.mem_union] at h_step
            rcases h_step with hread | heps
            · rcases hread with ⟨p, β, htrans, _⟩
              change (p, β) ∈ (∅ : Set ((Q ⊕ Fin 2) × List (Option S))) at htrans
              exact ((Set.mem_empty_iff_false _).mp htrans).elim
            · rcases heps with ⟨p, β, htrans, hc⟩
              change (p, β) ∈ ({(Sum.inr 1, [])} : Set ((Q ⊕ Fin 2) × List (Option S))) at htrans
              rw [Set.mem_singleton_iff] at htrans
              have hp := congrArg Prod.fst htrans
              have hβ := congrArg Prod.snd htrans
              simp only at hp hβ
              subst p
              subst β
              subst c₂
              exact Or.inr <| Or.inr ⟨rfl, by simp⟩

/-- The invariant is preserved by multi-step reachability. -/
public lemma FSES_Inv_reaches {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (c₁ c₂ : PDA.conf (PDA_FS_to_ES_pda M))
    (h_inv : FSES_Inv M w c₁)
    (h_reach : PDA.Reaches c₁ c₂) :
    FSES_Inv M w c₂ := by
  induction h_reach with
  | refl => exact h_inv
  | tail _ h_step ih => exact FSES_Inv_step M w _ _ ih h_step

/-
If the invariant holds at `(q, [], [])`, then `w ∈ M.acceptsByFinalState`.
-/
public lemma FSES_Inv_terminal {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (q : Q ⊕ Fin 2)
    (h_inv : FSES_Inv M w ⟨q, [], []⟩) :
    w ∈ M.acceptsByFinalState := by
  rcases h_inv with ( ⟨ ⟩ | ⟨ q, w', γ, h₁, h₂ ⟩ | ⟨ hq, h ⟩ ) <;> simp_all +decide [  ];
  exact ⟨ _, h.choose_spec.1, _, h.choose_spec.2.choose_spec ⟩

/-- Backward direction of `PDA_FS_subset_ES`. -/
public lemma PDA_FS_to_ES_backward {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (h : w ∈ (PDA_FS_to_ES_pda M).acceptsByEmptyStack) :
    w ∈ M.acceptsByFinalState := by
  obtain ⟨q, hreach⟩ := h
  exact FSES_Inv_terminal M w q
    (FSES_Inv_reaches M w _ _ (FSES_Inv_init M w) hreach)

/-- Any PDA final-state language is also a PDA empty-stack language. -/
public theorem PDA_FS_subset_ES {Q S : Type} [Fintype Q] [Fintype S] (M : PDA Q T S) :
    is_PDA M.acceptsByFinalState := by
  refine ⟨Q ⊕ Fin 2, Option S, inferInstance, inferInstance, PDA_FS_to_ES_pda M, ?_⟩
  ext w
  exact ⟨PDA_FS_to_ES_backward M w, PDA_FS_to_ES_forward M w⟩

end PDA_FS_to_ES

/-! ## Empty-stack acceptance ⊆ Final-state acceptance

Given a PDA `M` that accepts by empty stack, we construct a new PDA `M'` that
accepts by final state, recognising the same language.

The construction adds:
- A new initial state `Sum.inr 0` that pushes `M`'s start symbol on top of a fresh
  bottom marker.
- A new accepting state `Sum.inr 1` that is entered whenever the simulated `M`
  empties its original stack (i.e. the bottom marker is exposed).
-/
section PDA_ES_to_FS

open PDA

variable {T : Type} [Fintype T]

open Classical in
/-- ε-transition function for the ES→FS PDA conversion. -/
noncomputable def PDA_ES_to_FS_eps {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : (Q ⊕ Fin 2) → (Option S) → Set ((Q ⊕ Fin 2) × List (Option S))
  | Sum.inr 0, none => {(Sum.inl M.initial_state, [some M.start_symbol, none])}
  | Sum.inl q, some s =>
      (fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' (M.transition_fun' q s)
  | Sum.inl _, none => {(Sum.inr 1, [])}
  | Sum.inr 1, _ => ∅
  | Sum.inr 0, some _ => ∅

open Classical in
/-- Input-reading transition function for the ES→FS PDA conversion. -/
noncomputable def PDA_ES_to_FS_trans {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : (Q ⊕ Fin 2) → T → (Option S) → Set ((Q ⊕ Fin 2) × List (Option S))
  | Sum.inl q, a, some s =>
      (fun p : Q × List S => (Sum.inl p.1, p.2.map some)) '' (M.transition_fun q a s)
  | _, _, _ => ∅

open Classical in
/-- The PDA that converts empty-stack acceptance to final-state acceptance. -/
noncomputable def PDA_ES_to_FS_pda {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) : PDA (Q ⊕ Fin 2) T (Option S) where
  initial_state := Sum.inr 0
  start_symbol := none
  final_states := {Sum.inr 1}
  transition_fun := PDA_ES_to_FS_trans M
  transition_fun' := PDA_ES_to_FS_eps M
  finite q' a Z' := by
    simp only [PDA_ES_to_FS_trans]
    split <;> try exact Set.toFinite _
    exact (M.finite _ a _).image _
  finite' q' Z' := by
    simp only [PDA_ES_to_FS_eps]
    split <;> try exact Set.toFinite _
    exact (M.finite' _ _).image _

/-- Lifting a configuration from the original PDA to the ES→FS PDA. -/
def liftConf_ES {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
    (M : PDA Q T S) (c : PDA.conf M) : PDA.conf (PDA_ES_to_FS_pda M) :=
  ⟨Sum.inl c.state, c.input, c.stack.map some ++ [none]⟩

lemma ES_simulation_step {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (r₁ r₂ : PDA.conf M)
    (h : PDA.Reaches₁ r₁ r₂) :
    PDA.Reaches₁ (liftConf_ES M r₁) (liftConf_ES M r₂) := by
      cases r₁; cases r₂; simp_all +decide [ Reaches₁ ] ;
      unfold step at h;
      rename_i q w α q' w' α';
      rcases w with ( _ | ⟨ a, w ⟩ ) <;> rcases α with ( _ | ⟨ Z, α ⟩ ) <;> simp_all +decide [ liftConf_ES ];
      · obtain ⟨ β, hβ, rfl, rfl ⟩ := h; simp_all +decide [ step ] ;
        exact Set.mem_image_of_mem _ hβ;
      · rcases h with ( ⟨ β, hβ, rfl, rfl ⟩ | ⟨ β, hβ, rfl, rfl ⟩ ) <;> simp_all +decide [ step ];
        · exact Set.mem_image_of_mem _ hβ;
        · exact Set.mem_image_of_mem _ hβ

/-- Multi-step simulation: if M reaches r₂ from r₁, then the ES→FS PDA reaches
    lift(r₂) from lift(r₁). -/
lemma ES_simulation_reaches {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (r₁ r₂ : PDA.conf M)
    (h : PDA.Reaches r₁ r₂) :
    PDA.Reaches (liftConf_ES M r₁) (liftConf_ES M r₂) := by
  induction h with
  | refl => rfl
  | tail _ h₂ ih => exact Relation.ReflTransGen.tail ih (ES_simulation_step M _ _ h₂)

lemma PDA_ES_to_FS_forward {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (h : w ∈ M.acceptsByEmptyStack) :
    w ∈ (PDA_ES_to_FS_pda M).acceptsByFinalState := by
  obtain ⟨q, hq⟩ := h
  refine ⟨Sum.inr 1, Set.mem_singleton _, [], ?_⟩
  have h_init : (PDA_ES_to_FS_pda M).Reaches
      ⟨Sum.inr 0, w, [none]⟩
      (liftConf_ES M ⟨M.initial_state, w, [M.start_symbol]⟩) := by
    apply Relation.ReflTransGen.single
    unfold Reaches₁ step
    cases w with
    | nil =>
        refine ⟨Sum.inl M.initial_state, [some M.start_symbol, none], ?_, rfl⟩
        exact Set.mem_singleton _
    | cons a w =>
        apply Set.mem_union_right
        refine ⟨Sum.inl M.initial_state, [some M.start_symbol, none], ?_, rfl⟩
        exact Set.mem_singleton _
  have h_sim := ES_simulation_reaches M _ _ hq
  have h_accept : (PDA_ES_to_FS_pda M).Reaches
      (liftConf_ES M ⟨q, [], []⟩) ⟨Sum.inr 1, [], []⟩ := by
    apply Relation.ReflTransGen.single
    unfold Reaches₁ step
    refine ⟨Sum.inr 1, [], ?_, rfl⟩
    exact Set.mem_singleton _
  exact h_init.trans (h_sim.trans h_accept)

/-- Invariant for configurations reachable from the initial config of the ES→FS PDA.
    Every such configuration is either:
    (1) the initial config `(inr 0, w, [none])`
    (2) a simulation of M: `(inl q, w', γ.map some ++ [none])` with
        `M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, w', γ⟩`
    (3) the accepting state `(inr 1, w', [])` with a witness that M
        reached empty stack on some suffix. -/
def ESFS_Inv {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T) (c : PDA.conf (PDA_ES_to_FS_pda M)) : Prop :=
  (c = ⟨Sum.inr 0, w, [none]⟩) ∨
  (∃ q : Q, ∃ w' : List T, ∃ γ : List S,
    c = ⟨Sum.inl q, w', γ.map some ++ [none]⟩ ∧
    M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, w', γ⟩) ∨
  (∃ w' : List T, c = ⟨Sum.inr 1, w', []⟩ ∧
    ∃ q : Q, M.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, w', []⟩)

lemma ESFS_Inv_init {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T) :
    ESFS_Inv M w ⟨Sum.inr 0, w, [none]⟩ := by
  left; rfl

set_option maxHeartbeats 800000 in
lemma ESFS_Inv_step {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (c₁ c₂ : PDA.conf (PDA_ES_to_FS_pda M))
    (h_inv : ESFS_Inv M w c₁)
    (h_step : PDA.Reaches₁ c₁ c₂) :
    ESFS_Inv M w c₂ := by
      rcases h_inv with ( rfl | ⟨ q, w', γ, rfl, h ⟩ | ⟨ w', rfl, q, h ⟩ );
      · cases w <;> simp_all +decide [ Reaches₁ ];
        · cases h_step;
          unfold PDA_ES_to_FS_pda at *; simp_all +decide [ PDA_ES_to_FS_eps ] ;
          exact Or.inr <| Or.inl ⟨ M.initial_state, [ ], [ M.start_symbol ], by aesop ⟩;
        · cases h_step;
          · rename_i h;
            rcases h with ⟨ p, β, hp, rfl ⟩ ; unfold PDA_ES_to_FS_pda at hp; simp_all +decide [ PDA_ES_to_FS_trans ] ;
          · unfold PDA_ES_to_FS_pda at *; simp_all +decide [ PDA_ES_to_FS_eps ] ;
            exact Or.inr <| Or.inl ⟨ M.initial_state, _, _, rfl, Relation.ReflTransGen.refl ⟩;
      · rcases γ with ( _ | ⟨ Z, γ ⟩ ) <;> simp_all +decide [ Reaches₁ ];
        · rcases w' with ( _ | ⟨ a, w' ⟩ ) <;> simp_all +decide [ step ];
          · rcases h_step with ( ⟨ a, β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ ) <;> simp_all +decide [ PDA_ES_to_FS_pda ];
            · unfold PDA_ES_to_FS_eps at h₁; aesop;
            · unfold PDA_ES_to_FS_eps at h₁; aesop;
            · cases h₁;
              exact Or.inr <| Or.inr ⟨ _, rfl, q, h ⟩;
          · unfold PDA_ES_to_FS_pda at * ; simp_all +decide [ PDA_ES_to_FS_trans, PDA_ES_to_FS_eps ];
            exact Or.inr <| Or.inr <| ⟨ _, rfl, q, h ⟩;
        · rcases w' with ( _ | ⟨ a, w' ⟩ ) <;> simp_all +decide [ step ];
          · rcases h_step with ( ⟨ a, β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ ) <;> simp_all +decide [ PDA_ES_to_FS_pda ];
            · rcases h₁ with ⟨ p, hp, rfl, rfl ⟩;
              exact Or.inr <| Or.inl ⟨ p.1, [], p.2 ++ γ, by aesop, by exact h.trans <| by exact Relation.ReflTransGen.single <| by exact ⟨ p.1, p.2, hp, rfl ⟩ ⟩;
            · unfold PDA_ES_to_FS_eps at h₁; aesop;
            · unfold PDA_ES_to_FS_eps at h₁; aesop;
          · rcases h_step with ( ( ⟨ p, β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ ) | ⟨ p, β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ | ⟨ β, h₁, rfl ⟩ ) <;> simp_all +decide [ ESFS_Inv ];
            all_goals unfold PDA_ES_to_FS_pda at h₁; simp_all +decide [ PDA_ES_to_FS_trans, PDA_ES_to_FS_eps ] ;
            · rcases h₁ with ⟨ b, hb₁, rfl ⟩ ; use b ++ γ; simp_all +decide [ Reaches ] ;
              exact h.tail ( by exact Set.mem_union_left _ <| Set.mem_setOf.mpr ⟨ p, b, hb₁, rfl ⟩ );
            · obtain ⟨ b, hb₁, hb₂ ⟩ := h₁; use b ++ γ; simp_all +decide [ List.map_append ] ;
              exact h.tail ( by exact Set.mem_union_right _ <| Set.mem_setOf.mpr ⟨ p, b, hb₁, rfl ⟩ );
      · contrapose! h_step;
        simp +decide [ Reaches₁ ];
        unfold step; aesop;

lemma ESFS_Inv_reaches {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (c₁ c₂ : PDA.conf (PDA_ES_to_FS_pda M))
    (h_inv : ESFS_Inv M w c₁)
    (h_reach : PDA.Reaches c₁ c₂) :
    ESFS_Inv M w c₂ := by
  induction h_reach with
  | refl => exact h_inv
  | tail _ h_step ih => exact ESFS_Inv_step M w _ _ ih h_step

lemma ESFS_Inv_terminal {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (q : Q ⊕ Fin 2) (γ : List (Option S))
    (hq : q ∈ ({Sum.inr 1} : Set (Q ⊕ Fin 2)))
    (h_inv : ESFS_Inv M w ⟨q, [], γ⟩) :
    w ∈ M.acceptsByEmptyStack := by
      rcases h_inv with ( ⟨ ⟩ | ⟨ q, w', γ', h₁, h₂ ⟩ | ⟨ w', h₁, q', h₂ ⟩ ) <;> simp_all +decide;
      exact ⟨ q', h₂ ⟩

lemma PDA_ES_to_FS_backward {Q S : Type} [Fintype Q] [Fintype S]
    (M : PDA Q T S) (w : List T)
    (h : w ∈ (PDA_ES_to_FS_pda M).acceptsByFinalState) :
    w ∈ M.acceptsByEmptyStack := by
  obtain ⟨q, hq, γ, hreach⟩ := h
  exact ESFS_Inv_terminal M w q γ hq
    (ESFS_Inv_reaches M w _ _ (ESFS_Inv_init M w) hreach)

/-- Any PDA empty-stack language is also a PDA final-state language. -/
theorem PDA_ES_subset_FS {Q S : Type} [Fintype Q] [Fintype S] (M : PDA Q T S) :
    ∃ (Q' S' : Type) (_ : Fintype Q') (_ : Fintype S'),
      ∃ M' : PDA Q' T S', M'.acceptsByFinalState = M.acceptsByEmptyStack := by
  refine ⟨Q ⊕ Fin 2, Option S, inferInstance, inferInstance, PDA_ES_to_FS_pda M, ?_⟩
  ext w
  exact ⟨PDA_ES_to_FS_backward M w, PDA_ES_to_FS_forward M w⟩

end PDA_ES_to_FS

/-- A language is accepted by some PDA via empty-stack acceptance iff it is accepted by
some PDA via final-state acceptance. -/
theorem is_PDA_finalState_iff_is_PDA_emptyStack {L : Language T} :
    is_PDA_finalState L  ↔ is_PDA_emptyStack L := by
  constructor
  · rintro ⟨Q, S, _, _, M, hM⟩
    rw [← hM]
    exact PDA_FS_subset_ES M
  · rintro ⟨Q, S, _, _, M, hM⟩
    obtain ⟨Q', S', hQ', hS', M', hM'⟩ := PDA_ES_subset_FS M
    exact ⟨Q', S', hQ', hS', M', hM'.trans hM⟩

@[simp]
theorem is_PDA_finalState_iff_is_PDA {L : Language T} :
    is_PDA_finalState L  ↔ is_PDA L := by
  rw [is_PDA, is_PDA_finalState_iff_is_PDA_emptyStack]

/-- The languages accepted by PDAs via final-state acceptance are exactly the languages
accepted by PDAs via empty-stack acceptance. -/
theorem PDA_FinalStateClass_eq_EmptyStackClass :
    (PDA.FinalStateClass : Set (Language T)) = PDA.EmptyStackClass := by
  ext L
  change is_PDA_finalState L ↔ is_PDA L
  exact is_PDA_finalState_iff_is_PDA

theorem PDA_FinalStateClass_eq_Class :
    (PDA.FinalStateClass : Set (Language T)) = PDA.Class := by
  rw [PDA.Class, PDA_FinalStateClass_eq_EmptyStackClass]
