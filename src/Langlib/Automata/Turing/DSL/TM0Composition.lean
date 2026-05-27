import Mathlib

/-! # TM0 Sequential Composition

This file defines sequential composition of TM0 machines and proves that
the composed machine halts iff M₁ halts and M₂ halts on M₁'s output tape.

## Main definitions

- `TM0Seq.compose` — compose two TM0 machines sequentially
- `TM0Seq.evalCfg` — evaluate a TM0 returning the full config
- `TM0Seq.compose_phase2_respects` — phase 2 bisimulation
- `TM0Seq.compose_dom_iff` — full correctness theorem

## Architecture

The composed machine `compose M₁ M₂` uses states `Λ₁ ⊕ Λ₂`:
- In `Sum.inl q₁` states: runs M₁. When M₁ halts, immediately tries M₂'s first step.
- In `Sum.inr q₂` states: runs M₂.

The key correctness theorem says: if M₁ always halts on input `l` and
produces output tape `Tape.mk₁ l'`, then the composed machine halts on `l`
iff `M₂` halts on `l'`.
-/

open Turing

namespace TM0Seq

variable {Γ : Type} [Inhabited Γ]

/-- Evaluate a TM0 machine and return the full output configuration
(state + tape), rather than just the tape as `TM0.eval` does. -/
def evalCfg {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (l : List Γ) : Part (TM0.Cfg Γ Λ) :=
  Turing.eval (TM0.step M) (TM0.init l)

/-- `evalCfg` has the same `Dom` as `TM0.eval`. -/
theorem evalCfg_dom_iff {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (l : List Γ) :
    (evalCfg M l).Dom ↔ (TM0.eval M l).Dom := by
  simp [evalCfg, TM0.eval, Part.map]

/-- Evaluate a TM0 from an arbitrary configuration. -/
def evalFromCfg {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (cfg : TM0.Cfg Γ Λ) : Part (TM0.Cfg Γ Λ) :=
  Turing.eval (TM0.step M) cfg

/-- `evalFromCfg` from the initial config equals `evalCfg`. -/
theorem evalFromCfg_init {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (l : List Γ) :
    evalFromCfg M (TM0.init l) = evalCfg M l := rfl

/-- Sequential composition of TM0 machines.
When M₁ halts (returns `none`), we immediately invoke M₂ from its default state
on the current tape symbol. -/
noncomputable def compose
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂) :
    @TM0.Machine Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ :=
  fun q a =>
    match q with
    | Sum.inl q₁ =>
      match M₁ q₁ a with
      | some (q₁', s) => some (Sum.inl q₁', s)
      | none =>
        match M₂ default a with
        | some (q₂', s) => some (Sum.inr q₂', s)
        | none => none
    | Sum.inr q₂ =>
      match M₂ q₂ a with
      | some (q₂', s) => some (Sum.inr q₂', s)
      | none => none

section Phase1Helpers

variable {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]

/-
One step of M₁ at state q₁ maps to one step of compose at Sum.inl q₁.
-/
theorem compose_step_inl (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (c₁ c₁' : TM0.Cfg Γ Λ₁)
    (h : TM0.step M₁ c₁ = some c₁') :
    @TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)
      ⟨Sum.inl c₁.q, c₁.Tape⟩ =
    some ⟨Sum.inl c₁'.q, c₁'.Tape⟩ := by
  unfold TM0.step at *;
  unfold compose; aesop;

/-
`Reaches` of M₁ lifts to `Reaches` of compose in `Sum.inl` states.
-/
theorem compose_phase1_reaches (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (c₁ : TM0.Cfg Γ Λ₁) (l : List Γ)
    (h : Reaches (TM0.step M₁) (TM0.init l) c₁) :
    Reaches (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂))
      (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l)
      ⟨Sum.inl c₁.q, c₁.Tape⟩ := by
  induction h;
  · constructor;
  · rename_i c₁ c₂ h₁ h₂ h₃;
    convert h₃.tail _;
    unfold TM0.step at *;
    unfold compose; aesop;

/-
When M₁ halts, compose's transition matches M₂'s first step.
-/
theorem compose_step_on_halt (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (q₁ : Λ₁) (T : Tape Γ)
    (h : TM0.step M₁ ⟨q₁, T⟩ = none) :
    @TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)
      ⟨Sum.inl q₁, T⟩ =
    (TM0.step M₂ ⟨default, T⟩).map
      (fun c₂ => ⟨Sum.inr c₂.q, c₂.Tape⟩) := by
  unfold TM0.step at *; simp_all +decide [ compose ] ;
  cases M₂ default T.head <;> rfl

end Phase1Helpers

section Phase2

variable {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]

/-
Phase 2 bisimulation: once in `Sum.inr` states, the composed machine
exactly simulates M₂.
-/
theorem compose_phase2_respects (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂) :
    Respects
      (TM0.step M₂)
      (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂))
      (fun c₂ c => c.q = Sum.inr c₂.q ∧ c.Tape = c₂.Tape) := by
  intro c₂ c hc₂c;
  rcases c₂ with ⟨ q₂, T₂ ⟩;
  cases h : TM0.step M₂ ⟨ q₂, T₂ ⟩ <;> simp +decide [ *, Reaches₁ ];
  · unfold TM0.step at *;
    unfold compose; aesop;
  · refine' ⟨ ⟨ Sum.inr _, _ ⟩, ⟨ rfl, rfl ⟩, _ ⟩;
    convert Relation.TransGen.single _;
    unfold TM0.step at *;
    unfold compose; aesop;

/-- Phase 2 preserves `Dom`: `evalFromCfg` of M₂ from ⟨default, T⟩ halts iff
the composed machine from `⟨Sum.inr default, T⟩` halts. -/
theorem compose_phase2_dom (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (T : Tape Γ) :
    (evalFromCfg M₂ ⟨default, T⟩).Dom ↔
    (Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
      (compose M₁ M₂)) ⟨Sum.inr default, T⟩).Dom := by
  exact (tr_eval_dom (compose_phase2_respects M₁ M₂) ⟨rfl, rfl⟩).symm

end Phase2

section FullComposition

variable {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]

/-
The composed machine's eval from init l equals its eval from M₁'s halting state.
-/
theorem compose_eval_split (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l : List Γ) (h₁ : (evalCfg M₁ l).Dom) :
    let c₁ := (evalCfg M₁ l).get h₁
    Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂))
      (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l) =
    Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂))
      ⟨Sum.inl c₁.q, c₁.Tape⟩ := by
  have := Turing.mem_eval.mp ( Part.get_mem h₁ );
  obtain ⟨c₁, hc₁⟩ := this;
  have := compose_phase1_reaches M₁ M₂ ( ( evalCfg M₁ l ).get h₁ ) l c₁;
  exact let c₁ := (evalCfg M₁ l).get h₁; reaches_eval this

/-
At M₁'s halting state, the composed machine's eval equals M₂'s eval
(via phase 2 transition).
-/
theorem compose_eval_at_halt (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (q₁ : Λ₁) (T : Tape Γ) (h : TM0.step M₁ ⟨q₁, T⟩ = none) :
    (Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂))
      ⟨Sum.inl q₁, T⟩).Dom ↔
    (evalFromCfg M₂ ⟨default, T⟩).Dom := by
  by_cases h₂ : TM0.step M₂ ⟨ default, T ⟩ = none <;> simp_all +decide [ evalFromCfg ];
  · constructor <;> intro h₃;
    · convert Turing.mem_eval.mpr ⟨ Relation.ReflTransGen.refl, _ ⟩ using 1;
      any_goals exact h₂;
      rw [ Turing.mem_eval ];
      constructor <;> intro <;> simp_all +decide [ Part.dom_iff_mem ];
      · constructor;
      · exact ⟨ _, Turing.mem_eval.mpr ⟨ Relation.ReflTransGen.refl, by tauto ⟩ ⟩;
    · rw [ Turing.eval ];
      convert Part.dom_iff_mem.mpr _;
      use ⟨ Sum.inl q₁, T ⟩;
      rw [ PFun.mem_fix_iff ];
      simp +decide [ h, h₂, compose_step_on_halt ];
  · obtain ⟨ c₂, hc₂ ⟩ := Option.ne_none_iff_exists'.mp h₂;
    rw [ Turing.reaches_eval, Turing.reaches_eval ];
    rotate_left;
    rotate_left;
    exact ⟨ Sum.inr c₂.q, c₂.Tape ⟩;
    exact ⟨ Sum.inr c₂.q, c₂.Tape ⟩;
    · exact Relation.ReflTransGen.single ( by rw [ compose_step_on_halt M₁ M₂ q₁ T h ] ; aesop );
    · rw [ show eval ( TM0.step M₂ ) { q := default, Tape := T } = eval ( TM0.step M₂ ) c₂ from ?_ ];
      · apply Turing.tr_eval_dom;
        apply compose_phase2_respects;
        exact ⟨ rfl, rfl ⟩;
      · apply Turing.reaches_eval;
        exact Relation.ReflTransGen.single hc₂;
    · constructor

/-
Forward direction: if M₁ halts producing tape T, and M₂ halts starting
from ⟨default, T⟩, then the composed machine halts.
-/
theorem compose_dom_of_parts (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l : List Γ)
    (h₁ : (evalCfg M₁ l).Dom)
    (h₂ : (evalFromCfg M₂ ⟨default, ((evalCfg M₁ l).get h₁).Tape⟩).Dom) :
    (@TM0.eval Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂) l).Dom := by
  convert compose_eval_at_halt M₁ M₂ _ _ _ using 1;
  rotate_left;
  exact ( evalCfg M₁ l |> Part.get ) h₁ |> fun c => c.q;
  exact ( evalCfg M₁ l |> Part.get ) h₁ |> fun c => c.Tape;
  · have := Part.get_mem h₁;
    convert Turing.mem_eval.mp this |>.2;
  · rw [ ← compose_eval_split M₁ M₂ l h₁ ];
    unfold TM0.eval; aesop;

/-
Backward: if the composed machine halts, then M₁ halts.
-/
theorem compose_dom_left (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l : List Γ)
    (h : (@TM0.eval Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂) l).Dom) :
    (evalCfg M₁ l).Dom := by
  contrapose! h;
  -- If M₁ does not halt, then for any configuration c of M₁, there exists a configuration c' such that c' is reachable from c and M₁ steps from c to c'.
  have h_not_halt : ∀ c : TM0.Cfg Γ Λ₁, Reaches (TM0.step M₁) (TM0.init l) c → ∃ c' : TM0.Cfg Γ Λ₁, TM0.step M₁ c = some c' := by
    intro c hc
    by_contra h_not_halt_c
    push_neg at h_not_halt_c
    have h_halt_c : TM0.step M₁ c = none := by
      cases h : TM0.step M₁ c <;> tauto
    have h_halt : (evalCfg M₁ l).Dom := by
      apply_rules [ Part.dom_iff_mem.mpr ];
      use c;
      apply_rules [ Turing.mem_eval.mpr ];
      exact ⟨ hc, h_halt_c ⟩
    exact h h_halt;
  -- By definition of `eval`, if M₁ does not halt, then the composed machine also does not halt.
  have h_compose_not_halt : ∀ c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂), Reaches (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)) (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l) c → c.q.isLeft ∧ ∃ c' : TM0.Cfg Γ Λ₁, c = ⟨Sum.inl c'.q, c'.Tape⟩ ∧ Reaches (TM0.step M₁) (TM0.init l) c' := by
    intro c hc;
    induction hc;
    · exact ⟨ rfl, TM0.init l, rfl, by tauto ⟩;
    · rename_i c hc ih;
      rcases ih with ⟨ ih₁, c', rfl, ih₂ ⟩;
      obtain ⟨ c'', hc'' ⟩ := h_not_halt c' ih₂;
      have h_compose_step : @TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂) ⟨Sum.inl c'.q, c'.Tape⟩ = some ⟨Sum.inl c''.q, c''.Tape⟩ := by
        convert compose_step_inl M₁ M₂ c' c'' hc'' using 1;
      cases hc.symm.trans h_compose_step ; tauto;
  intro h_dom;
  obtain ⟨c, hc⟩ : ∃ c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂), Reaches (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)) (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l) c ∧ @TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂) c = none := by
    obtain ⟨c, hc⟩ : ∃ c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂), c ∈ Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)) (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l) := by
      exact Part.dom_iff_mem.mp h_dom
    use c;
    exact mem_eval.mp hc;
  obtain ⟨ hc₁, hc₂ ⟩ := h_compose_not_halt c hc.1;
  obtain ⟨ c', rfl, hc' ⟩ := hc₂;
  obtain ⟨ c'', hc'' ⟩ := h_not_halt c' hc';
  have := compose_step_inl M₁ M₂ c' c'' hc''; simp_all +decide [ TM0.step ] ;

/-
Backward: if the composed machine halts and M₁ halts producing tape T,
then M₂ halts from ⟨default, T⟩.
-/
theorem compose_dom_right (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l : List Γ)
    (h₁ : (evalCfg M₁ l).Dom)
    (h : (@TM0.eval Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂) l).Dom) :
    (evalFromCfg M₂ ⟨default, ((evalCfg M₁ l).get h₁).Tape⟩).Dom := by
  convert compose_eval_at_halt M₁ M₂ _ _ _;
  rotate_left;
  exact ( evalCfg M₁ l |> Part.get <| h₁ ) |> fun x => x.q;
  exact ( evalCfg M₁ l |> Part.get <| h₁ ) |> fun x => x.Tape;
  · have h_step : ∀ c, c ∈ Turing.eval (TM0.step M₁) (TM0.init l) → TM0.step M₁ c = none := by
      intro c hc;
      have := Turing.mem_eval.mp hc;
      exact this.2;
    convert h_step _ _;
    convert Part.get_mem _;
    convert h₁ using 1;
  · have := compose_eval_split M₁ M₂ l h₁;
    unfold TM0.eval at *; aesop;

/-- **Correctness of sequential composition.**

If M₁ halts on input `l`, then the composed machine halts on `l` iff
M₂ halts on M₁'s output tape. -/
theorem compose_dom_iff (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l : List Γ)
    (h₁ : (evalCfg M₁ l).Dom) :
    (@TM0.eval Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂) l).Dom ↔
    (evalFromCfg M₂ ⟨default, ((evalCfg M₁ l).get h₁).Tape⟩).Dom :=
  ⟨compose_dom_right M₁ M₂ l h₁,
   compose_dom_of_parts M₁ M₂ l h₁⟩

/-
Variant: when M₁'s output tape is `Tape.mk₁ l'`, composition halts iff
M₂ halts on input `l'`.
-/
theorem compose_dom_iff' (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l l' : List Γ)
    (h₁ : (evalCfg M₁ l).Dom)
    (h_tape : ((evalCfg M₁ l).get h₁).Tape = Tape.mk₁ l') :
    (@TM0.eval Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂) l).Dom ↔
    (TM0.eval M₂ l').Dom := by
  rw [ compose_dom_iff ];
  convert evalCfg_dom_iff M₂ l' using 1;
  rw [ h_tape ];
  · unfold evalFromCfg evalCfg; aesop;
  · grind

end FullComposition

/-! ### Compose Output Tape Tracking -/

theorem evalCfg_step_none
    {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (l : List Γ)
    (h : (evalCfg M l).Dom) :
    TM0.step M ((evalCfg M l).get h) = none := by
  have := @Turing.mem_eval;
  exact this.mp ( Part.get_mem _ ) |>.2

theorem compose_eval_from_halt_tape
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (q₁ : Λ₁) (T : Tape Γ)
    (h_halt : TM0.step M₁ ⟨q₁, T⟩ = none)
    (h₂ : (evalFromCfg M₂ ⟨default, T⟩).Dom) :
    ∃ c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂),
      c ∈ @Turing.eval (TM0.Cfg Γ (Λ₁ ⊕ Λ₂))
        (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
          (compose M₁ M₂))
        ⟨Sum.inl q₁, T⟩ ∧
      c.Tape = ((evalFromCfg M₂ ⟨default, T⟩).get h₂).Tape := by
  by_cases h₂' : TM0.step M₂ ⟨ default, T ⟩ = none;
  · have h_c₂ : (evalFromCfg M₂ ⟨default, T⟩).get h₂ = ⟨default, T⟩ := by
      have h_c₂ : ∀ c ∈ eval (TM0.step M₂) ⟨default, T⟩, c = ⟨default, T⟩ := by
        intro c hc; exact (by
        exact (by
          have := hc;
          rw [ eval ] at this;
          rw [ PFun.mem_fix_iff ] at this;
          aesop
        ));
      exact h_c₂ _ ( Part.get_mem _ );
    use ⟨Sum.inl q₁, T⟩;
    rw [ Turing.eval ];
    rw [ PFun.mem_fix_iff ];
    rw [ compose_step_on_halt ] <;> aesop;
  · obtain ⟨ c₂', hc₂' ⟩ := Option.ne_none_iff_exists'.mp h₂';
    have h_reaches : evalFromCfg M₂ ⟨ default, T ⟩ = evalFromCfg M₂ c₂' := by
      apply Turing.reaches_eval;
      exact Relation.ReflTransGen.single hc₂';
    have h_tr_eval : ∀ {c₂ : TM0.Cfg Γ Λ₂} {c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂)},
      c₂.Tape = c.Tape →
      c.q = Sum.inr c₂.q →
      ∀ {c₂_final : TM0.Cfg Γ Λ₂},
        c₂_final ∈ Turing.eval (TM0.step M₂) c₂ →
        ∃ b₂ : TM0.Cfg Γ (Λ₁ ⊕ Λ₂),
          b₂.Tape = c₂_final.Tape ∧ b₂ ∈ Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)) c := by
            intros c₂ c hc₂ hc q₂ hq₂;
            have := compose_phase2_respects M₁ M₂;
            have := tr_eval this ⟨ hc, hc₂.symm ⟩ hq₂;
            exact ⟨ this.choose, this.choose_spec.1.2, this.choose_spec.2 ⟩;
    obtain ⟨c₂_final, hc₂_final⟩ : ∃ c₂_final : TM0.Cfg Γ Λ₂,
        c₂_final ∈ Turing.eval (TM0.step M₂) c₂' ∧
        c₂_final.Tape = ((evalFromCfg M₂ { q := default, Tape := T }).get h₂).Tape := by
                                            use (evalFromCfg M₂ { q := default, Tape := T }).get h₂;
                                            simp [h_reaches];
                                            exact Part.get_mem _;
    have h_reaches : Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)) ⟨Sum.inl q₁, T⟩ = Turing.eval (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (compose M₁ M₂)) ⟨Sum.inr c₂'.q, c₂'.Tape⟩ := by
      apply reaches_eval;
      apply Relation.ReflTransGen.single;
      rw [ compose_step_on_halt ] <;> aesop;
    exact h_reaches.symm ▸ h_tr_eval rfl rfl hc₂_final.1 |> fun ⟨ b₂, hb₂₁, hb₂₂ ⟩ => ⟨ b₂, hb₂₂, hb₂₁.trans hc₂_final.2 ⟩

theorem compose_eval_tape_mem
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l l' : List Γ)
    (h₁ : (evalCfg M₁ l).Dom)
    (h₁_tape : ((evalCfg M₁ l).get h₁).Tape = Tape.mk₁ l')
    (h₂ : (evalCfg M₂ l').Dom) :
    ∃ c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂),
      c ∈ @Turing.eval (TM0.Cfg Γ (Λ₁ ⊕ Λ₂))
        (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
          (compose M₁ M₂))
        (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l) ∧
      c.Tape = ((evalCfg M₂ l').get h₂).Tape := by
  set c₁ := (evalCfg M₁ l).get h₁
  have h_step_none := evalCfg_step_none M₁ l h₁
  have h_split := compose_eval_split M₁ M₂ l h₁
  have h₂' : (evalFromCfg M₂ ⟨default, c₁.Tape⟩).Dom := by
    rw [h₁_tape]; exact h₂
  obtain ⟨c, hc_mem, hc_tape⟩ := compose_eval_from_halt_tape M₁ M₂
    c₁.q c₁.Tape h_step_none h₂'
  refine ⟨c, ?_, ?_⟩
  · rw [h_split]; exact hc_mem
  · rw [hc_tape]
    congr 1
    apply Part.get_eq_get_of_eq
    show evalFromCfg M₂ ⟨default, c₁.Tape⟩ = evalCfg M₂ l'
    rw [h₁_tape]; rfl

theorem compose_evalCfg_tape
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l l' : List Γ)
    (h₁ : (evalCfg M₁ l).Dom)
    (h₁_tape : ((evalCfg M₁ l).get h₁).Tape = Tape.mk₁ l')
    (h₂ : (evalCfg M₂ l').Dom)
    (h_comp : (@evalCfg Γ _ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩
      (compose M₁ M₂) l).Dom) :
    ((@evalCfg Γ _ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩
      (compose M₁ M₂) l).get h_comp).Tape =
    ((evalCfg M₂ l').get h₂).Tape := by
  obtain ⟨c, hc_mem, hc_tape⟩ := compose_eval_tape_mem M₁ M₂ l l' h₁ h₁_tape h₂
  have h_get_mem := Part.get_mem h_comp
  have h_unique := Part.mem_unique h_get_mem hc_mem
  rw [h_unique]; exact hc_tape

end TM0Seq