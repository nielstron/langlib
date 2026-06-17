module

public import Langlib.Classes.Recursive.Definition
public import Langlib.Utilities.ClosurePredicates
public import Langlib.Automata.Turing.DSL.TM0BlockRealizability
public import Mathlib.Data.Fintype.Option

/-! # Recursive Closure Under Reversal

Proof idea: given a decider `M` for `L`, first run a finite-state TM0 block
routine that rewrites the input tape from `w` to `w.reverse`. Then continue
with `M` on that reversed tape. The composed machine halts because both the
reversal routine and `M` halt, and it accepts exactly when `M` accepts
`w.reverse`, which is the definition of membership in `L.reverse`.
-/

open Turing

namespace RecursiveReverse

variable {Γ : Type} [Inhabited Γ]

private noncomputable def delayedCompose
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂) :
    @TM0.Machine Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ :=
  fun q γ =>
    match q with
    | Sum.inl q₁ =>
        match M₁ q₁ γ with
        | some (q₁', stmt) => some (Sum.inl q₁', stmt)
        | none => some (Sum.inr default, TM0.Stmt.write γ)
    | Sum.inr q₂ =>
        match M₂ q₂ γ with
        | some (q₂', stmt) => some (Sum.inr q₂', stmt)
        | none => none

private def sumAccept {Λ₁ Λ₂ : Type} (accept : Λ₂ → Bool) : Λ₁ ⊕ Λ₂ → Bool
  | Sum.inl _ => false
  | Sum.inr q => accept q

private theorem delayed_step_inl_of_step
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    {c₁ c₂ : TM0.Cfg Γ Λ₁} (h : c₂ ∈ TM0.step M₁ c₁) :
    ⟨Sum.inl c₂.q, c₂.Tape⟩ ∈
      @TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
        (delayedCompose M₁ M₂) ⟨Sum.inl c₁.q, c₁.Tape⟩ := by
  rcases c₁ with ⟨q, T⟩
  unfold TM0.step at h ⊢
  cases hM : M₁ q T.head with
  | none => simp [hM] at h
  | some next =>
      rcases next with ⟨q', stmt⟩
      simp [delayedCompose, hM] at h ⊢
      cases h
      simp

private theorem delayed_phase1_reaches
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (c₁ : TM0.Cfg Γ Λ₁) (l : List Γ)
    (h : Reaches (TM0.step M₁) (TM0.init l) c₁) :
    Reaches (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (delayedCompose M₁ M₂))
      (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l)
      ⟨Sum.inl c₁.q, c₁.Tape⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (delayed_step_inl_of_step M₁ M₂ hstep)

private theorem delayed_step_on_halt
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (c₁ : TM0.Cfg Γ Λ₁) (h : TM0.step M₁ c₁ = none) :
    @TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
      (delayedCompose M₁ M₂) ⟨Sum.inl c₁.q, c₁.Tape⟩ =
      some ⟨Sum.inr (default : Λ₂), c₁.Tape⟩ := by
  unfold TM0.step at h ⊢
  cases hM : M₁ c₁.q c₁.Tape.head with
  | none =>
      simp [delayedCompose, hM, Tape.write_self]
  | some next =>
      simp [hM] at h

private theorem delayed_step_inr_of_step
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    {c₁ c₂ : TM0.Cfg Γ Λ₂} (h : c₂ ∈ TM0.step M₂ c₁) :
    ⟨Sum.inr c₂.q, c₂.Tape⟩ ∈
      @TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
        (delayedCompose M₁ M₂) ⟨Sum.inr c₁.q, c₁.Tape⟩ := by
  rcases c₁ with ⟨q, T⟩
  unfold TM0.step at h ⊢
  cases hM : M₂ q T.head with
  | none => simp [hM] at h
  | some next =>
      rcases next with ⟨q', stmt⟩
      simp [delayedCompose, hM] at h ⊢
      cases h
      simp

private theorem delayed_step_inr_halt
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (c : TM0.Cfg Γ Λ₂) (h : TM0.step M₂ c = none) :
    @TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
      (delayedCompose M₁ M₂) ⟨Sum.inr c.q, c.Tape⟩ = none := by
  rcases c with ⟨q, T⟩
  unfold TM0.step at h ⊢
  cases hM : M₂ q T.head with
  | none => simp [delayedCompose, hM]
  | some next => simp [hM] at h

private theorem delayed_phase2_respects
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂) :
    Respects
      (TM0.step M₂)
      (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (delayedCompose M₁ M₂))
      (fun c₂ c => c.q = Sum.inr c₂.q ∧ c.Tape = c₂.Tape) := by
  intro c₂ c hc
  rcases c₂ with ⟨q₂, T₂⟩
  rcases c with ⟨q, T⟩
  rcases hc with ⟨hq, hT⟩
  cases hq
  cases hT
  cases hstep : TM0.step M₂ (⟨q₂, T₂⟩ : TM0.Cfg Γ Λ₂) with
  | none =>
    exact delayed_step_inr_halt M₁ M₂ ⟨q₂, T₂⟩ hstep
  | some c₂' =>
    rcases c₂' with ⟨q₂', T₂'⟩
    refine ⟨⟨Sum.inr q₂', T₂'⟩, ⟨rfl, rfl⟩, ?_⟩
    exact Relation.TransGen.single
      (delayed_step_inr_of_step M₁ M₂ (by
        show (⟨q₂', T₂'⟩ : TM0.Cfg Γ Λ₂) ∈
          TM0.step M₂ (⟨q₂, T₂⟩ : TM0.Cfg Γ Λ₂)
        rw [hstep]
        simp))

private theorem delayed_eval_mem
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l l' : List Γ)
    (h₁ : (TM0Seq.evalCfg M₁ l).Dom)
    (h₁_tape : ((TM0Seq.evalCfg M₁ l).get h₁).Tape = Tape.mk₁ l')
    (h₂ : (TM0Seq.evalCfg M₂ l').Dom) :
    ∃ c : TM0.Cfg Γ (Λ₁ ⊕ Λ₂),
      c ∈ @Turing.eval (TM0.Cfg Γ (Λ₁ ⊕ Λ₂))
        (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
          (delayedCompose M₁ M₂))
        (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l) ∧
      c.q = Sum.inr ((TM0Seq.evalCfg M₂ l').get h₂).q := by
  let c₁ := (TM0Seq.evalCfg M₁ l).get h₁
  have hM₁_mem := Part.get_mem h₁
  have hM₁_eval := Turing.mem_eval.mp hM₁_mem
  have hphase1 := delayed_phase1_reaches M₁ M₂ c₁ l hM₁_eval.1
  have hstep : @TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _
      (delayedCompose M₁ M₂) ⟨Sum.inl c₁.q, c₁.Tape⟩ =
      some ⟨Sum.inr (default : Λ₂), c₁.Tape⟩ := by
    exact delayed_step_on_halt M₁ M₂ c₁ hM₁_eval.2
  have hstart :
      Reaches (@TM0.step Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ (delayedCompose M₁ M₂))
        (@TM0.init Γ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩ _ l)
        ⟨Sum.inr (default : Λ₂), c₁.Tape⟩ :=
    hphase1.tail hstep
  have heval₂ :
      Turing.eval (TM0.step M₂) ⟨default, c₁.Tape⟩ = TM0Seq.evalCfg M₂ l' := by
    rw [h₁_tape]
    rfl
  have h₂_mem : (TM0Seq.evalCfg M₂ l').get h₂ ∈
      Turing.eval (TM0.step M₂) ⟨default, c₁.Tape⟩ := by
    rw [heval₂]
    exact Part.get_mem h₂
  obtain ⟨c, hc_rel, hc_mem⟩ :=
    tr_eval (delayed_phase2_respects M₁ M₂)
      (show (fun c₂ c => c.q = Sum.inr c₂.q ∧ c.Tape = c₂.Tape)
          (⟨default, c₁.Tape⟩ : TM0.Cfg Γ Λ₂)
          (⟨Sum.inr (default : Λ₂), c₁.Tape⟩ :
            TM0.Cfg Γ (Λ₁ ⊕ Λ₂)) from by
        simp)
      h₂_mem
  refine ⟨c, ?_, hc_rel.1⟩
  rw [Turing.reaches_eval hstart]
  exact hc_mem

private theorem delayed_eval_accept
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (accept : Λ₂ → Bool)
    (l l' : List Γ)
    (h₁ : (TM0Seq.evalCfg M₁ l).Dom)
    (h₁_tape : ((TM0Seq.evalCfg M₁ l).get h₁).Tape = Tape.mk₁ l')
    (h₂ : (TM0Seq.evalCfg M₂ l').Dom)
    (hcomp : (@TM0Seq.evalCfg Γ _ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩
      (delayedCompose M₁ M₂) l).Dom) :
    sumAccept accept
      (((@TM0Seq.evalCfg Γ _ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩
        (delayedCompose M₁ M₂) l).get hcomp).q) =
    accept ((TM0Seq.evalCfg M₂ l').get h₂).q := by
  obtain ⟨c, hc_mem, hcq⟩ := delayed_eval_mem M₁ M₂ l l' h₁ h₁_tape h₂
  have hget := Part.get_mem hcomp
  have hsame := Part.mem_unique hget hc_mem
  rw [hsame, hcq]
  simp [sumAccept]

private theorem delayed_dom
    {Λ₁ : Type} [Inhabited Λ₁] {Λ₂ : Type} [Inhabited Λ₂]
    (M₁ : TM0.Machine Γ Λ₁) (M₂ : TM0.Machine Γ Λ₂)
    (l l' : List Γ)
    (h₁ : (TM0Seq.evalCfg M₁ l).Dom)
    (h₁_tape : ((TM0Seq.evalCfg M₁ l).get h₁).Tape = Tape.mk₁ l')
    (h₂ : (TM0Seq.evalCfg M₂ l').Dom) :
    (@TM0Seq.evalCfg Γ _ (Λ₁ ⊕ Λ₂) ⟨Sum.inl default⟩
      (delayedCompose M₁ M₂) l).Dom := by
  obtain ⟨c, hc, _⟩ := delayed_eval_mem M₁ M₂ l l' h₁ h₁_tape h₂
  exact Part.dom_iff_mem.mpr ⟨c, hc⟩

variable {T : Type} [DecidableEq T] [Fintype T]

omit [DecidableEq T] [Fintype T] in
private lemma map_input_ne_none {Γw : Type} (w : List T) :
    ∀ x ∈ (w.map fun t => some (Sum.inl (α := T) (β := Γw) t)),
      x ≠ (default : Option (T ⊕ Γw)) := by
  intro x hx
  obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hx
  simp

omit [DecidableEq T] [Fintype T] in
private lemma reverse_preprocessor
    {Γw : Type}
    {Λ : Type} [Inhabited Λ] [Fintype Λ]
    (M : TM0.Machine (Option (T ⊕ Γw)) Λ)
    (hM : ∀ (block suffix : List (Option (T ⊕ Γw))),
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ List.reverse block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
      ∀ h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom,
        ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).Tape =
          Tape.mk₁ (List.reverse block ++ default :: suffix))
    (w : List T) :
    ∃ h : (TM0Seq.evalCfg M (w.map fun t => some (Sum.inl (α := T) (β := Γw) t))).Dom,
      ((TM0Seq.evalCfg M (w.map fun t => some (Sum.inl (α := T) (β := Γw) t))).get h).Tape =
        Tape.mk₁ (w.reverse.map fun t => some (Sum.inl (α := T) (β := Γw) t)) := by
  let block := w.map fun t => some (Sum.inl (α := T) (β := Γw) t)
  have hblock : ∀ x ∈ block, x ≠ (default : Option (T ⊕ Γw)) := map_input_ne_none w
  have hrev : ∀ x ∈ block.reverse, x ≠ (default : Option (T ⊕ Γw)) :=
    reverse_ne_default block hblock
  obtain ⟨hdom₀, htape₀⟩ := hM block [] hblock hrev
  have heq : TM0Seq.evalCfg M (block ++ [default]) = TM0Seq.evalCfg M block :=
    evalCfg_append_default M block
  have hdom : (TM0Seq.evalCfg M block).Dom := by
    simpa [block] using (show (TM0Seq.evalCfg M block).Dom from heq ▸ hdom₀)
  refine ⟨hdom, ?_⟩
  have hcfg_eq :
      (TM0Seq.evalCfg M block).get hdom =
        (TM0Seq.evalCfg M (block ++ [default])).get hdom₀ := by
    apply Part.get_eq_get_of_eq
    exact heq.symm
  rw [hcfg_eq, htape₀ hdom₀]
  simp [block, List.map_reverse, tape_mk₁_append_default]

/-- Recursive languages over finite alphabets are closed under reversal. -/
public theorem is_Recursive_reverse {L : Language T} (hL : is_Recursive L) :
    is_Recursive L.reverse := by
  classical
  obtain ⟨Γw, hΓwfin, Λ, hΛ, hΛfin, M, accept, hHalt, hCorrect⟩ := hL
  letI : Fintype (Option (T ⊕ Γw)) := inferInstance
  obtain ⟨ΛR, hΛR, hΛRfin, MR, hMR⟩ :=
    (tm0_reverse_block_anySuffix (Γ := Option (T ⊕ Γw)))
  letI : Inhabited (ΛR ⊕ Λ) := ⟨Sum.inl default⟩
  refine ⟨Γw, hΓwfin, ΛR ⊕ Λ, inferInstance, inferInstance, delayedCompose MR M,
    sumAccept accept,
    ?_, ?_⟩
  · intro w
    obtain ⟨hrev, htape⟩ := reverse_preprocessor MR hMR w
    have hdec : (TM0Seq.evalCfg M
        (w.reverse.map fun t => some (Sum.inl (α := T) (β := Γw) t))).Dom := hHalt w.reverse
    change (TM0Seq.evalCfg (delayedCompose MR M)
      (w.map fun t => some (Sum.inl (α := T) (β := Γw) t))).Dom
    exact delayed_dom MR M
      (w.map fun t => some (Sum.inl (α := T) (β := Γw) t))
      (w.reverse.map fun t => some (Sum.inl (α := T) (β := Γw) t)) hrev htape hdec
  · intro w hcomp
    obtain ⟨hrev, htape⟩ := reverse_preprocessor MR hMR w
    have hdec : (TM0Seq.evalCfg M
        (w.reverse.map fun t => some (Sum.inl (α := T) (β := Γw) t))).Dom := hHalt w.reverse
    change (TM0Seq.evalCfg (delayedCompose MR M)
      (w.map fun t => some (Sum.inl (α := T) (β := Γw) t))).Dom at hcomp
    have hacc := delayed_eval_accept MR M accept
      (w.map fun t => some (Sum.inl (α := T) (β := Γw) t))
      (w.reverse.map fun t => some (Sum.inl (α := T) (β := Γw) t)) hrev htape hdec hcomp
    change w.reverse ∈ L ↔
      sumAccept accept
        (((TM0Seq.evalCfg (delayedCompose MR M)
          (w.map fun t => some (Sum.inl (α := T) (β := Γw) t))).get hcomp).q) = true
    constructor
    · intro hw
      convert hacc.trans ((hCorrect w.reverse hdec).mp hw)
    · intro hcomp_accept
      apply (hCorrect w.reverse hdec).mpr
      convert hacc.symm.trans hcomp_accept

/-- Recursive languages over finite alphabets are closed under reversal. -/
public theorem Recursive_closedUnderReverse :
    ClosedUnderReverse (α := T) is_Recursive :=
  fun _ hL => is_Recursive_reverse hL

end RecursiveReverse
