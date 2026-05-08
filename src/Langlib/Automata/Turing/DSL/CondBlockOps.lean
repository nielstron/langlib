import Mathlib
import Langlib.Automata.Turing.DSL.ChainAlphabet
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.BinaryArithmetic
import Langlib.Automata.Turing.DSL.BlockValueLeqMachine

/-! # Conditional Block Operations

This file provides TM0 conditional composition: run a predicate machine,
then route to one of two block machines depending on the result.

## Main definitions

- `binCondBlock`: conditional block operation (if p then f else g)
- `tm0CondCompose`: TM0 machine that runs M_p, then routes to M_f or M_g

## Main results

- `tm0RealizesBlock_cond`: conditional block operation is block-realizable
- `blockValueLeq`: comparing block value with a constant is TM0-decidable
-/

open Turing PartrecToTM2 TM2to1

/-! ### Conditional Block Operation -/

/-- Conditional block operation: given a decidable predicate on blocks,
    apply `f` when the predicate holds and `g` otherwise. -/
noncomputable def binCondBlock (p : List ChainΓ → Prop) [DecidablePred p]
    (f g : List ChainΓ → List ChainΓ) (block : List ChainΓ) : List ChainΓ :=
  if p block then f block else g block

/-! ### Conditional TM0 Composition -/

/-- Conditional TM0 composition: run M_p first, then route to M_f (if halting
    state = q_true) or M_g (if halting state = q_false). -/
noncomputable def tm0CondCompose
    {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_true q_false : Λ_p) :
    @TM0.Machine ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ :=
  fun q a =>
    match q with
    | Sum.inl q_p =>
      match M_p q_p a with
      | some (q_p', s) => some (Sum.inl q_p', s)
      | none =>
        if q_p = q_true then
          match M_f default a with
          | some (q_f', s) => some (Sum.inr (Sum.inl q_f'), s)
          | none => none
        else
          match M_g default a with
          | some (q_g', s) => some (Sum.inr (Sum.inr q_g'), s)
          | none => none
    | Sum.inr (Sum.inl q_f) =>
      match M_f q_f a with
      | some (q_f', s) => some (Sum.inr (Sum.inl q_f'), s)
      | none => none
    | Sum.inr (Sum.inr q_g) =>
      match M_g q_g a with
      | some (q_g', s) => some (Sum.inr (Sum.inr q_g'), s)
      | none => none

/-! ### Helper lemmas for tm0CondCompose -/

section CondComposeHelpers

variable {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)

/-- Phase 1: one step of M_p maps to one step of condCompose in Sum.inl states. -/
theorem condCompose_step_inl
    (c₁ c₁' : TM0.Cfg ChainΓ Λ_p)
    (h : TM0.step M_p c₁ = some c₁') :
    @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
      ⟨Sum.inl c₁.q, c₁.Tape⟩ =
    some ⟨Sum.inl c₁'.q, c₁'.Tape⟩ := by
  unfold tm0CondCompose at *;
  unfold TM0.step at *; aesop;

/-- Phase 1: Reaches of M_p lifts to condCompose in Sum.inl states. -/
theorem condCompose_phase1_reaches
    (c₁ : TM0.Cfg ChainΓ Λ_p) (l : List ChainΓ)
    (h : Reaches (TM0.step M_p) (TM0.init l) c₁) :
    Reaches (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f))
      (@TM0.init ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _ l)
      ⟨Sum.inl c₁.q, c₁.Tape⟩ := by
  induction h;
  · constructor;
  · rename_i c₂ c₃ h₁ h₂ h₃;
    convert h₃.tail _;
    convert condCompose_step_inl M_p M_f M_g q_t q_f c₂ c₃ h₂

/-- When M_p halts at q_t, condCompose routes to M_f. -/
theorem condCompose_halt_true
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_t, T⟩ = none) :
    @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
      ⟨Sum.inl q_t, T⟩ =
    (TM0.step M_f ⟨default, T⟩).map
      (fun c₂ => ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩) := by
  unfold tm0CondCompose;
  unfold TM0.step at *;
  grind

/-- When M_p halts at q_f (≠ q_t), condCompose routes to M_g. -/
theorem condCompose_halt_false
    (hne : q_t ≠ q_f)
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_f, T⟩ = none) :
    @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
      ⟨Sum.inl q_f, T⟩ =
    (TM0.step M_g ⟨default, T⟩).map
      (fun c₂ => ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩) := by
  convert condCompose_halt_true _ _ _ _;
  rotate_left;
  exact Λ_p;
  all_goals try assumption;
  unfold tm0CondCompose;
  unfold TM0.step at * ; aesop

/-- Phase 2 bisimulation for M_f. -/
theorem condCompose_f_respects :
    Respects
      (TM0.step M_f)
      (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
        (tm0CondCompose M_p M_f M_g q_t q_f))
      (fun c₂ c => c.q = Sum.inr (Sum.inl c₂.q) ∧ c.Tape = c₂.Tape) := by
  intro c₂ c;
  rintro ⟨ h₁, h₂ ⟩;
  rcases h : TM0.step M_f c₂ with ( _ | ⟨ q, s ⟩ ) <;> simp +decide [ h ];
  · unfold tm0CondCompose;
    unfold TM0.step at *; aesop;
  · refine' ⟨ ⟨ Sum.inr ( Sum.inl q ), s ⟩, _, _ ⟩ <;> simp_all +decide [ Reaches₁ ];
    convert Relation.TransGen.single _;
    unfold tm0CondCompose;
    unfold TM0.step at *;
    cases c ; aesop

/-- Phase 2 bisimulation for M_g. -/
theorem condCompose_g_respects :
    Respects
      (TM0.step M_g)
      (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
        (tm0CondCompose M_p M_f M_g q_t q_f))
      (fun c₂ c => c.q = Sum.inr (Sum.inr c₂.q) ∧ c.Tape = c₂.Tape) := by
  intro c₂ c hc;
  rcases h : TM0.step M_g c₂ with ( _ | ⟨ q, s ⟩ ) <;> simp_all +decide;
  · unfold tm0CondCompose;
    unfold TM0.step at *; aesop;
  · refine' ⟨ ⟨ Sum.inr ( Sum.inr q ), s ⟩, _, _ ⟩ <;> simp_all +decide [ Reaches₁ ];
    convert Relation.TransGen.single _;
    unfold tm0CondCompose;
    unfold TM0.step at *; aesop;

/-- When M_p halts at q_t, condCompose eval domain matches M_f. -/
theorem condCompose_eval_at_halt_true
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_t, T⟩ = none) :
    (Turing.eval (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f))
      ⟨Sum.inl q_t, T⟩).Dom ↔
    (TM0Seq.evalFromCfg M_f ⟨default, T⟩).Dom := by
  by_cases h₂ : TM0.step M_f ⟨default, T⟩ = none;
  · rw [ Turing.eval ];
    constructor <;> intro <;> simp_all +decide [ Part.dom_iff_mem ];
    · exact ⟨ _, Turing.mem_eval.mpr ⟨ Relation.ReflTransGen.refl, by tauto ⟩ ⟩;
    · use ⟨Sum.inl q_t, T⟩;
      rw [ PFun.mem_fix_iff ];
      rw [ condCompose_halt_true ] <;> aesop;
  · obtain ⟨ c₂, hc₂ ⟩ := Option.ne_none_iff_exists'.mp h₂;
    rw [ Turing.reaches_eval, Turing.reaches_eval ];
    rotate_left;
    rotate_left;
    exact ⟨ Sum.inr ( Sum.inl c₂.q ), c₂.Tape ⟩;
    exact ⟨ Sum.inr ( Sum.inl c₂.q ), c₂.Tape ⟩;
    · exact Relation.ReflTransGen.single ( by rw [ condCompose_halt_true M_p M_f M_g q_t q_f T h_halt ] ; aesop );
    · rw [ show TM0Seq.evalFromCfg M_f { q := default, Tape := T } = eval ( TM0.step M_f ) { q := default, Tape := T } from rfl ];
      rw [ show eval ( TM0.step M_f ) { q := default, Tape := T } = eval ( TM0.step M_f ) c₂ from ?_ ];
      · apply Turing.tr_eval_dom;
        exact?;
        exact ⟨ rfl, rfl ⟩;
      · apply Turing.reaches_eval;
        exact Relation.ReflTransGen.single hc₂;
    · exact Relation.ReflTransGen.refl

/-- When M_p halts at q_f (≠ q_t), condCompose eval domain matches M_g. -/
theorem condCompose_eval_at_halt_false
    (hne : q_t ≠ q_f)
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_f, T⟩ = none) :
    (Turing.eval (@TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f))
      ⟨Sum.inl q_f, T⟩).Dom ↔
    (TM0Seq.evalFromCfg M_g ⟨default, T⟩).Dom := by
  by_cases h₂ : TM0.step M_g ⟨default, T⟩ = none;
  · rw [ Turing.eval ];
    constructor <;> intro <;> simp_all +decide [ Part.dom_iff_mem ];
    · exact ⟨ _, Turing.mem_eval.mpr ⟨ Relation.ReflTransGen.refl, by tauto ⟩ ⟩;
    · use ⟨Sum.inl q_f, T⟩;
      rw [ PFun.mem_fix_iff ];
      rw [ condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt ] ; aesop;
  · obtain ⟨ c₂, hc₂ ⟩ := Option.ne_none_iff_exists'.mp h₂;
    rw [ Turing.reaches_eval, Turing.reaches_eval ];
    rotate_left;
    rotate_left;
    exact ⟨ Sum.inr ( Sum.inr c₂.q ), c₂.Tape ⟩;
    exact ⟨ Sum.inr ( Sum.inr c₂.q ), c₂.Tape ⟩;
    · exact Relation.ReflTransGen.single ( by rw [ condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt ] ; aesop );
    · rw [ show TM0Seq.evalFromCfg M_g { q := default, Tape := T } = eval ( TM0.step M_g ) { q := default, Tape := T } from rfl ];
      rw [ show eval ( TM0.step M_g ) { q := default, Tape := T } = eval ( TM0.step M_g ) c₂ from ?_ ];
      · apply Turing.tr_eval_dom;
        exact?;
        exact ⟨ rfl, rfl ⟩;
      · rw [ Turing.reaches_eval ];
        exact Relation.ReflTransGen.single hc₂;
    · exact Relation.ReflTransGen.refl

end CondComposeHelpers

attribute [-instance] instInhabitedOfMonad
instance instInhabitedSumLeft {α β : Type} [Inhabited α] : Inhabited (α ⊕ β) := ⟨Sum.inl default⟩

section CondComposeEvalCfg

variable {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)

/-- When M_p halts at q_t with tape T, the composed machine's eval has the same tape as M_f. -/
theorem condCompose_tape_at_halt_true
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_t, T⟩ = none)
    (h_f_dom : (TM0Seq.evalFromCfg M_f ⟨default, T⟩).Dom) :
    let step_c := @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
    ∀ (h_c_dom : (Turing.eval step_c ⟨Sum.inl q_t, T⟩).Dom),
      ((Turing.eval step_c ⟨Sum.inl q_t, T⟩).get h_c_dom).Tape =
        ((TM0Seq.evalFromCfg M_f ⟨default, T⟩).get h_f_dom).Tape := by
  intro step_c h_c_dom
  set b_f := (TM0Seq.evalFromCfg M_f ⟨default, T⟩).get h_f_dom
  have hb_f_mem : b_f ∈ TM0Seq.evalFromCfg M_f ⟨default, T⟩ := Part.get_mem h_f_dom
  rcases h_step_f : TM0.step M_f ⟨default, T⟩ with _ | ⟨c₂⟩
  · have hb_f_eq : b_f = ⟨default, T⟩ :=
      (Turing.eval_maximal (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h_step_f⟩) |>.mp
        (Turing.mem_eval.mp hb_f_mem).1)
    have h_step_c : step_c ⟨Sum.inl q_t, T⟩ = none := by
      show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _ (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
      rw [condCompose_halt_true M_p M_f M_g q_t q_f T h_halt]
      simp [h_step_f]
    have h_eval_c := Part.mem_unique (Part.get_mem h_c_dom)
      (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h_step_c⟩)
    rw [h_eval_c, hb_f_eq]
  · have h_step_c : step_c ⟨Sum.inl q_t, T⟩ = some ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩ := by
      show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _ (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
      rw [condCompose_halt_true M_p M_f M_g q_t q_f T h_halt]
      simp [h_step_f]
    have h_eval_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_c)
    have h_eval_f_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_f)
    have hb_f_mem_c2 : b_f ∈ Turing.eval (TM0.step M_f) c₂ := by
      rw [← h_eval_f_eq]; exact hb_f_mem
    obtain ⟨b₂, ⟨_, hb₂_tape⟩, hb₂_mem⟩ := Turing.tr_eval
      (condCompose_f_respects M_p M_f M_g q_t q_f)
      (a₁ := c₂) (a₂ := ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩)
      ⟨rfl, rfl⟩ hb_f_mem_c2
    have hb₂_mem' : b₂ ∈ Turing.eval step_c ⟨Sum.inl q_t, T⟩ := by
      rw [h_eval_eq]; exact hb₂_mem
    rw [Part.mem_unique (Part.get_mem h_c_dom) hb₂_mem', hb₂_tape]

/-- When M_p halts at q_f (≠ q_t), the composed machine's eval has the same tape as M_g. -/
theorem condCompose_tape_at_halt_false
    (hne : q_t ≠ q_f)
    (T : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_f, T⟩ = none)
    (h_g_dom : (TM0Seq.evalFromCfg M_g ⟨default, T⟩).Dom) :
    let step_c := @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
    ∀ (h_c_dom : (Turing.eval step_c ⟨Sum.inl q_f, T⟩).Dom),
      ((Turing.eval step_c ⟨Sum.inl q_f, T⟩).get h_c_dom).Tape =
        ((TM0Seq.evalFromCfg M_g ⟨default, T⟩).get h_g_dom).Tape := by
  intro step_c h_c_dom
  set b_g := (TM0Seq.evalFromCfg M_g ⟨default, T⟩).get h_g_dom
  have hb_g_mem : b_g ∈ TM0Seq.evalFromCfg M_g ⟨default, T⟩ := Part.get_mem h_g_dom
  rcases h_step_g : TM0.step M_g ⟨default, T⟩ with _ | ⟨c₂⟩
  · have hb_g_eq : b_g = ⟨default, T⟩ :=
      (Turing.eval_maximal (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h_step_g⟩) |>.mp
        (Turing.mem_eval.mp hb_g_mem).1)
    have h_step_c : step_c ⟨Sum.inl q_f, T⟩ = none := by
      show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _ (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
      rw [condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt]
      simp [h_step_g]
    have h_eval_c := Part.mem_unique (Part.get_mem h_c_dom)
      (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, h_step_c⟩)
    rw [h_eval_c, hb_g_eq]
  · have h_step_c : step_c ⟨Sum.inl q_f, T⟩ = some ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩ := by
      show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _ (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
      rw [condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt]
      simp [h_step_g]
    have h_eval_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_c)
    have h_eval_g_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_g)
    have hb_g_mem_c2 : b_g ∈ Turing.eval (TM0.step M_g) c₂ := by
      rw [← h_eval_g_eq]; exact hb_g_mem
    obtain ⟨b₂, ⟨_, hb₂_tape⟩, hb₂_mem⟩ := Turing.tr_eval
      (condCompose_g_respects M_p M_f M_g q_t q_f)
      (a₁ := c₂) (a₂ := ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩)
      ⟨rfl, rfl⟩ hb_g_mem_c2
    have hb₂_mem' : b₂ ∈ Turing.eval step_c ⟨Sum.inl q_f, T⟩ := by
      rw [h_eval_eq]; exact hb₂_mem
    rw [Part.mem_unique (Part.get_mem h_c_dom) hb₂_mem', hb₂_tape]

end CondComposeEvalCfg

/-! ### Core conditional block-realizability -/

theorem tm0RealizesBlock_cond_core
    {p : List ChainΓ → Prop} [DecidablePred p]
    {f g : List ChainΓ → List ChainΓ}
    {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [Fintype Λ_p] [Fintype Λ_f] [Fintype Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)
    (hne : q_t ≠ q_f)
    (hp_spec : ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M_p (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M_p (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M_p (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (block ++ default :: suffix) ∧
          (p block →
            ((TM0Seq.evalCfg M_p (block ++ default :: suffix)).get h).q = q_t) ∧
          (¬p block →
            ((TM0Seq.evalCfg M_p (block ++ default :: suffix)).get h).q = q_f))
    (hf_spec : ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (∀ x ∈ f block, x ≠ default) →
        (TM0Seq.evalCfg M_f (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M_f (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M_f (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (f block ++ default :: suffix))
    (hg_spec : ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (∀ x ∈ g block, x ≠ default) →
        (TM0Seq.evalCfg M_g (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M_g (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M_g (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (g block ++ default :: suffix))
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default)
    (hg_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ g block, x ≠ default) :
    TM0RealizesBlock ChainΓ (binCondBlock p f g) := by
  refine ⟨Λ_p ⊕ Λ_f ⊕ Λ_g, inferInstance, inferInstance,
    tm0CondCompose M_p M_f M_g q_t q_f, ?_⟩
  intro block suffix hblock hsuffix hresult
  set l := block ++ default :: suffix
  have hp_dom := (hp_spec block suffix hblock hsuffix).1
  have hp_result := (hp_spec block suffix hblock hsuffix).2 hp_dom
  set c_p := (TM0Seq.evalCfg M_p l).get hp_dom
  have hc_p_tape : c_p.Tape = Tape.mk₁ l := hp_result.1
  have hc_p_mem : c_p ∈ TM0Seq.evalCfg M_p l := Part.get_mem hp_dom
  have hc_p_eval := Turing.mem_eval.mp hc_p_mem
  have hc_p_halt : TM0.step M_p c_p = none := hc_p_eval.2
  have hc_p_reaches : Turing.Reaches (TM0.step M_p) (TM0.init l) c_p := hc_p_eval.1
  have h_reaches_c := condCompose_phase1_reaches M_p M_f M_g q_t q_f c_p l hc_p_reaches
  have h_eval_rewrite : TM0Seq.evalCfg (tm0CondCompose M_p M_f M_g q_t q_f) l =
      Turing.eval (TM0.step (tm0CondCompose M_p M_f M_g q_t q_f))
        ⟨Sum.inl c_p.q, c_p.Tape⟩ := Turing.reaches_eval h_reaches_c
  unfold binCondBlock at hresult ⊢
  by_cases hp : p block
  · simp only [hp, ite_true] at hresult ⊢
    have hq : c_p.q = q_t := hp_result.2.1 hp
    have h_halt_qt : TM0.step M_p ⟨q_t, c_p.Tape⟩ = none := hq ▸ hc_p_halt
    have hf_dom : (TM0Seq.evalCfg M_f l).Dom :=
      (hf_spec block suffix hblock hsuffix (hf_nd block hblock)).1
    have h_f_from_init : (TM0Seq.evalFromCfg M_f ⟨default, c_p.Tape⟩).Dom := by
      rw [hc_p_tape]; show (TM0Seq.evalFromCfg M_f (TM0.init l)).Dom
      rw [TM0Seq.evalFromCfg_init]; exact hf_dom
    constructor
    · rw [h_eval_rewrite, hq]
      exact (condCompose_eval_at_halt_true M_p M_f M_g q_t q_f c_p.Tape h_halt_qt).mpr h_f_from_init
    · intro h_dom; (
      have h_tape_eq : (TM0Seq.evalFromCfg M_f ⟨default, c_p.Tape⟩).Dom := by
        exact h_f_from_init;
      have h_tape_eq : ((TM0Seq.evalFromCfg M_f ⟨default, c_p.Tape⟩).get h_tape_eq).Tape = Tape.mk₁ (f block ++ default :: suffix) := by
        convert hf_spec block suffix hblock hsuffix hresult |>.2 _
        · rw [hc_p_tape];
          exact?
        · exact hf_dom
      convert condCompose_tape_at_halt_true M_p M_f M_g q_t q_f c_p.Tape h_halt_qt h_f_from_init;
      grind)
  · simp only [hp, ite_false] at hresult ⊢
    have hq : c_p.q = q_f := hp_result.2.2 hp
    have h_halt_qf : TM0.step M_p ⟨q_f, c_p.Tape⟩ = none := hq ▸ hc_p_halt
    have hg_dom : (TM0Seq.evalCfg M_g l).Dom :=
      (hg_spec block suffix hblock hsuffix (hg_nd block hblock)).1
    have h_g_from_init : (TM0Seq.evalFromCfg M_g ⟨default, c_p.Tape⟩).Dom := by
      rw [hc_p_tape]; show (TM0Seq.evalFromCfg M_g (TM0.init l)).Dom
      rw [TM0Seq.evalFromCfg_init]; exact hg_dom
    constructor
    · rw [h_eval_rewrite, hq]
      exact (condCompose_eval_at_halt_false M_p M_f M_g q_t q_f hne c_p.Tape h_halt_qf).mpr h_g_from_init
    · intro h_dom; (
      have h_tape_eq : (TM0Seq.evalFromCfg M_g ⟨default, c_p.Tape⟩).Dom := by
        exact h_g_from_init;
      have h_tape_eq : ((TM0Seq.evalFromCfg M_g ⟨default, c_p.Tape⟩).get h_tape_eq).Tape = Tape.mk₁ (g block ++ default :: suffix) := by
        convert hg_spec block suffix hblock hsuffix hresult |>.2 _
        · rw [hc_p_tape];
          exact?
        · exact hg_dom
      convert condCompose_tape_at_halt_false M_p M_f M_g q_t q_f hne c_p.Tape h_halt_qf h_g_from_init;
      grind)

/-- **Conditional block operation is block-realizable** (public interface). -/
theorem tm0RealizesBlock_cond
    {p : List ChainΓ → Prop} [DecidablePred p]
    {f g : List ChainΓ → List ChainΓ}
    (hf : TM0RealizesBlock ChainΓ f)
    (hg : TM0RealizesBlock ChainΓ g)
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default)
    (hg_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ g block, x ≠ default)
    (hp_decidable : ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ) (q_true q_false : Λ),
      q_true ≠ q_false ∧
      ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (block ++ default :: suffix) ∧
          (p block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_true) ∧
          (¬p block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_false)) :
    TM0RealizesBlock ChainΓ (binCondBlock p f g) := by
  obtain ⟨Λ_p, iΛ_p, fΛ_p, M_p, q_t, q_f, hne, hp_spec⟩ := hp_decidable
  obtain ⟨Λ_f, iΛ_f, fΛ_f, M_f, hf_spec⟩ := hf
  obtain ⟨Λ_g, iΛ_g, fΛ_g, M_g, hg_spec⟩ := hg
  exact @tm0RealizesBlock_cond_core p _ f g Λ_p Λ_f Λ_g iΛ_p iΛ_f iΛ_g fΛ_p fΛ_f fΛ_g
    (Classical.decEq _) M_p M_f M_g q_t q_f hne hp_spec hf_spec hg_spec hf_nd hg_nd

/-! ### Block value comparison -/

/-- Predicate: the binary block represents a value ≤ k. -/
noncomputable def blockValueLeq (k : ℕ) (block : List ChainΓ) : Prop :=
  decodeBinaryBlock block ≤ k

noncomputable instance blockValueLeq_decidable (k : ℕ) :
    DecidablePred (blockValueLeq k) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

theorem tm0_blockValueLeq_decidable (k : ℕ) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ),
      ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom := by
  refine' ⟨ _, _, _, _, _ ⟩;
  exact Unit;
  all_goals try infer_instance;
  exact fun _ _ => none;
  intro block suffix hblock hsuffix;
  constructor;
  swap;
  constructor;
  all_goals norm_num [ TM0.step ];
  grind;
  convert Part.dom_iff_mem.mpr _;
  unfold WellFounded.fixF; simp +decide [ TM0.step ] ;

theorem tm0_blockValueLeq_decidable_2 (k : ℕ) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ) (q_true q_false : Λ),
      q_true ≠ q_false ∧
      ∀ (block suffix : List ChainΓ),
        (∀ x ∈ block, x ≠ default) → (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (block ++ default :: suffix) ∧
          (blockValueLeq k block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_true) ∧
          (¬blockValueLeq k block →
            ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).q = q_false) := by
  refine ⟨BVLState k, bvlInhabited k, inferInstance, bvlMachine k,
    Sum.inr (Sum.inr true), Sum.inr (Sum.inr false), by simp, fun block suffix hblock hsuffix => ?_⟩
  exact bvlMachine_correct k block suffix hblock hsuffix

/-! ### Block value comparison after a separator -/

inductive BVLAfterSepSt (k : ℕ) where
  | scan
  | bvl (q : BVLState k)

noncomputable instance (k : ℕ) : DecidableEq (BVLAfterSepSt k) :=
  Classical.typeDecidableEq _

noncomputable instance (k : ℕ) : Inhabited (BVLAfterSepSt k) :=
  ⟨.scan⟩

noncomputable instance (k : ℕ) : Fintype (BVLAfterSepSt k) := by
  exact
  { elems := {BVLAfterSepSt.scan}
      ∪ Finset.univ.map ⟨BVLAfterSepSt.bvl, fun _ _ h => by cases h; rfl⟩
    complete := by
      intro x
      cases x <;> simp [Finset.mem_map, Finset.mem_insert] }

noncomputable def bvlAfterSepMachine (k : ℕ) (sep : ChainΓ) :
    @TM0.Machine ChainΓ (BVLAfterSepSt k) ⟨.scan⟩ :=
  fun q a =>
    match q with
    | .scan =>
        if a = sep then some (.bvl (Sum.inl ⟨k, by omega⟩), .move Dir.right)
        else some (.scan, .move Dir.right)
    | .bvl q =>
        match bvlMachine k q a with
        | some (q', stmt) => some (.bvl q', stmt)
        | none => none

theorem bvlAfterSep_lift {k : ℕ} {sep : ChainΓ}
    {c d : TM0.Cfg ChainΓ (BVLState k)}
    (h : Reaches (TM0.step (bvlMachine k)) c d) :
    Reaches (TM0.step (bvlAfterSepMachine k sep))
      ⟨BVLAfterSepSt.bvl c.q, c.Tape⟩
      ⟨BVLAfterSepSt.bvl d.q, d.Tape⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      rename_i inter final _hprev
      refine ih.tail ?_
      unfold TM0.step at hstep ⊢
      cases hb : bvlMachine k inter.q inter.Tape.head with
      | none =>
          simp [hb] at hstep
      | some pair =>
          rcases pair with ⟨q', stmt⟩
          simp [hb] at hstep
          cases hstep
          simp [bvlAfterSepMachine, hb]

theorem bvlAfterSep_scan_prefix_gen (k : ℕ) (sep : ChainΓ)
    (pref revL inner suffix : List ChainΓ)
    (hpref : ∀ x ∈ pref, x ≠ sep) :
    Reaches (TM0.step (bvlAfterSepMachine k sep))
      ⟨BVLAfterSepSt.scan,
        Tape.mk' (ListBlank.mk revL)
          (ListBlank.mk (pref ++ sep :: inner ++ default :: suffix))⟩
      ⟨BVLAfterSepSt.bvl (Sum.inl ⟨k, by omega⟩),
        Tape.mk' (ListBlank.mk (sep :: pref.reverse ++ revL))
          (ListBlank.mk (inner ++ default :: suffix))⟩ := by
  induction pref generalizing revL with
  | nil =>
      apply Relation.ReflTransGen.single
      simp [TM0.step, bvlAfterSepMachine, Tape.move, Tape.mk']
  | cons c pref ih =>
      have hc : c ≠ sep := hpref c (by simp)
      have hp : ∀ x ∈ pref, x ≠ sep := by
        intro x hx
        exact hpref x (by simp [hx])
      convert (Relation.ReflTransGen.single ?_).trans (ih (c :: revL) hp) using 1
      · simp [List.reverse_cons, List.append_assoc]
      · simp [TM0.step, bvlAfterSepMachine, Tape.move, Tape.mk', hc, List.reverse_cons,
          List.append_assoc]

theorem bvlAfterSep_step_halt {k : ℕ} {sep : ChainΓ}
    (q : BVLState k) (T : Tape ChainΓ)
    (h : TM0.step (bvlMachine k) ⟨q, T⟩ = none) :
    TM0.step (bvlAfterSepMachine k sep) ⟨BVLAfterSepSt.bvl q, T⟩ = none := by
  unfold TM0.step at h ⊢
  cases hb : bvlMachine k q T.head with
  | none => simp [bvlAfterSepMachine, hb]
  | some x => simp [hb] at h

theorem tm0_blockValueLeq_afterSep_decidable_2 (k : ℕ) (sep : ChainΓ)
    (hsep : sep ≠ default) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ) (q_true q_false : Λ),
      q_true ≠ q_false ∧
      ∀ (pref block suffix : List ChainΓ),
        (∀ x ∈ pref, x ≠ default) →
        (∀ x ∈ pref, x ≠ sep) →
        (∀ x ∈ block, x ≠ default) →
        (∀ x ∈ suffix, x ≠ default) →
        (TM0Seq.evalCfg M (pref ++ sep :: block ++ default :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M (pref ++ sep :: block ++ default :: suffix)).Dom),
          ((TM0Seq.evalCfg M (pref ++ sep :: block ++ default :: suffix)).get h).Tape =
            Tape.mk₁ (pref ++ sep :: block ++ default :: suffix) ∧
          (blockValueLeq k block →
            ((TM0Seq.evalCfg M (pref ++ sep :: block ++ default :: suffix)).get h).q =
              q_true) ∧
          (¬blockValueLeq k block →
            ((TM0Seq.evalCfg M (pref ++ sep :: block ++ default :: suffix)).get h).q =
              q_false) := by
  refine ⟨BVLAfterSepSt k, inferInstance, inferInstance, bvlAfterSepMachine k sep,
    BVLAfterSepSt.bvl (Sum.inr (Sum.inr true)),
    BVLAfterSepSt.bvl (Sum.inr (Sum.inr false)), by simp, ?_⟩
  intro pref block suffix hpref_nd hpref_nsep hblock hsuffix
  let bvlStart : TM0.Cfg ChainΓ (BVLState k) :=
    ⟨Sum.inl ⟨k, by omega⟩,
      Tape.mk' (ListBlank.mk (sep :: pref.reverse))
        (ListBlank.mk (block ++ default :: suffix))⟩
  have hleft : ∀ x ∈ sep :: pref.reverse, x ≠ (default : ChainΓ) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hsep
    · exact hpref_nd x (List.mem_reverse.mp hx)
  obtain ⟨hbvl_dom, hbvl_spec⟩ :=
    bvlMachine_correct_with_left k (sep :: pref.reverse) block suffix hleft hblock hsuffix
  let cb := (TM0Seq.evalFromCfg (bvlMachine k) bvlStart).get hbvl_dom
  have hbvl_mem : cb ∈ TM0Seq.evalFromCfg (bvlMachine k) bvlStart := Part.get_mem hbvl_dom
  have hbvl_eval := Turing.mem_eval.mp hbvl_mem
  have hscan := bvlAfterSep_scan_prefix_gen k sep pref [] block suffix hpref_nsep
  have hscan' :
      Reaches (TM0.step (bvlAfterSepMachine k sep))
        (TM0.init (pref ++ sep :: block ++ default :: suffix))
        ⟨BVLAfterSepSt.bvl bvlStart.q, bvlStart.Tape⟩ := by
    simpa [TM0.init, bvlStart, List.append_assoc] using hscan
  have hchain :
      Reaches (TM0.step (bvlAfterSepMachine k sep))
        (TM0.init (pref ++ sep :: block ++ default :: suffix))
        ⟨BVLAfterSepSt.bvl cb.q, cb.Tape⟩ := by
    exact hscan'.trans (bvlAfterSep_lift (sep := sep) hbvl_eval.1)
  have hhalt :
      TM0.step (bvlAfterSepMachine k sep) ⟨BVLAfterSepSt.bvl cb.q, cb.Tape⟩ = none :=
    bvlAfterSep_step_halt cb.q cb.Tape hbvl_eval.2
  have hmem :
      ⟨BVLAfterSepSt.bvl cb.q, cb.Tape⟩ ∈
        TM0Seq.evalCfg (bvlAfterSepMachine k sep)
          (pref ++ sep :: block ++ default :: suffix) :=
    Turing.mem_eval.mpr ⟨hchain, hhalt⟩
  refine ⟨Part.dom_iff_mem.mpr ⟨_, hmem⟩, ?_⟩
  intro h
  have hget :
      (TM0Seq.evalCfg (bvlAfterSepMachine k sep)
        (pref ++ sep :: block ++ default :: suffix)).get h =
        ⟨BVLAfterSepSt.bvl cb.q, cb.Tape⟩ :=
    Part.get_eq_of_mem hmem h
  rw [hget]
  have hspec := hbvl_spec hbvl_dom
  constructor
  · simpa [cb, bvlStart, List.append_assoc] using hspec.1
  constructor
  · intro hle
    have hq := hspec.2.1 (by simpa [blockValueLeq] using hle)
    simpa [cb] using congrArg BVLAfterSepSt.bvl hq
  · intro hle
    have hq := hspec.2.2 (by simpa [blockValueLeq] using hle)
    simpa [cb] using congrArg BVLAfterSepSt.bvl hq
