import Mathlib
import Langlib.Automata.Turing.DSL.PairedBlockArithmetic
import Langlib.Automata.Turing.DSL.SepPresenceInvariant
import Langlib.Automata.Turing.DSL.FixedStateFinalize

/-! # Paired separator invariant establishers

This file connects the generic separator-presence scanner to the paired-block
predicates used by `PairedBlockArithmetic`.
-/

open Turing PartrecToTM2 TM2to1

noncomputable instance hasConsBottom_decidablePred : DecidablePred hasConsBottom :=
  fun block => inferInstanceAs (Decidable (chainConsBottom ∈ block))

theorem sepPresent_iff_hasConsBottom (block : List ChainΓ) :
    sepPresent block ↔ hasConsBottom block := by
  rfl

/-- The separator-presence scanner, specialized to the paired-block predicate
    name used in `PairedBlockArithmetic`. -/
theorem tm0_hasConsBottom_paired_blockCondInv :
    TM0RealizesBlockCondInv (Γ := ChainΓ) (fun block => block)
      hasConsBottom (fun _block => True) := by
  simpa [sepPresent_iff_hasConsBottom] using tm0_hasConsBottom_blockCondInv

/-- A normalized paired step establishes the stronger paired separator
    invariant needed by the inner-block successor lift. -/
theorem pairedDecrLeftIncrRight_step_inv
    (block : List ChainΓ) (hInv : pairedSepInv block)
    (_hblock : ∀ g ∈ block, g ≠ default) (_hcond : pairedAddCond block) :
    pairedSepInv (pairedDecrLeftIncrRight block) :=
  pairedDecrLeftIncrRight_pairedSepInv block hInv

/-! ## Fixed-state wrappers for invariant-restricted machines -/

def TM0RealizesBlockInvFixed {Γ : Type} [Inhabited Γ]
    (f : List Γ → List Γ) (blockInv : List Γ → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ) (q_done : Λ),
    ∀ (block : List Γ),
      blockInv block →
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ f block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ [default])).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ [default])).Dom),
        let cfg := (TM0Seq.evalCfg M (block ++ [default])).get h
        cfg.q = q_done ∧ cfg.Tape = Tape.mk₁ (f block ++ [default])

def TM0RealizesBlockInvSuffixFixed {Γ : Type} [Inhabited Γ]
    (f : List Γ → List Γ) (blockInv : List Γ → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ) (q_done : Λ),
    ∀ (block suffix : List Γ),
      blockInv block →
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
        let cfg := (TM0Seq.evalCfg M (block ++ default :: suffix)).get h
        cfg.q = q_done ∧ cfg.Tape = Tape.mk₁ (f block ++ default :: suffix)

theorem tm0RealizesBlockInvFixed_of_inv {Γ : Type} [Inhabited Γ]
    {f : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlockInv f blockInv) :
    TM0RealizesBlockInvFixed f blockInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  let hsum : Inhabited (Λ ⊕ FinalizeSt) := ⟨Sum.inl (@default _ hΛi)⟩
  let Mcomp : TM0.Machine Γ (Λ ⊕ FinalizeSt) :=
    @TM0Seq.compose Γ Λ hΛi FinalizeSt inferInstance M finalizeMachine
  refine ⟨Λ ⊕ FinalizeSt, hsum, inferInstance, Mcomp,
    Sum.inr FinalizeSt.done, ?_⟩
  intro block hInv hblock hfblock
  obtain ⟨hM_dom, hM_tape⟩ := hM block hInv hblock hfblock
  have hfinal := compose_finalize_evalCfg M (block ++ [default]) (f block ++ [default])
    hM_dom (hM_tape hM_dom)
  change (TM0Seq.evalCfg Mcomp (block ++ [default])).Dom ∧
    ∀ h, let cfg := (TM0Seq.evalCfg Mcomp (block ++ [default])).get h
      cfg.q = Sum.inr FinalizeSt.done ∧ cfg.Tape = Tape.mk₁ (f block ++ [default])
  constructor
  · exact hfinal.1
  · intro h
    have hcfg := hfinal.2 h
    rw [hcfg]
    simp

theorem tm0RealizesBlockInvSuffixFixed_of_invSuffix {Γ : Type} [Inhabited Γ]
    {f : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlockInvSuffix f blockInv) :
    TM0RealizesBlockInvSuffixFixed f blockInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  let hsum : Inhabited (Λ ⊕ FinalizeSt) := ⟨Sum.inl (@default _ hΛi)⟩
  let Mcomp : TM0.Machine Γ (Λ ⊕ FinalizeSt) :=
    @TM0Seq.compose Γ Λ hΛi FinalizeSt inferInstance M finalizeMachine
  refine ⟨Λ ⊕ FinalizeSt, hsum, inferInstance, Mcomp,
    Sum.inr FinalizeSt.done, ?_⟩
  intro block suffix hInv hblock hsuffix hfblock
  obtain ⟨hM_dom, hM_tape⟩ := hM block suffix hInv hblock hsuffix hfblock
  have hfinal := compose_finalize_evalCfg M (block ++ default :: suffix)
    (f block ++ default :: suffix) hM_dom (hM_tape hM_dom)
  change (TM0Seq.evalCfg Mcomp (block ++ default :: suffix)).Dom ∧
    ∀ h, let cfg := (TM0Seq.evalCfg Mcomp (block ++ default :: suffix)).get h
      cfg.q = Sum.inr FinalizeSt.done ∧
      cfg.Tape = Tape.mk₁ (f block ++ default :: suffix)
  constructor
  · exact hfinal.1
  · intro h
    have hcfg := hfinal.2 h
    rw [hcfg]
    simp

theorem condCompose_fixed_at_halt_true_of_step
    {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)
    (q_done : Λ_f) (T T' : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_t, T⟩ = none)
    (h_step : ∃ c₂, TM0.step M_f ⟨default, T⟩ = some c₂)
    (h_f_dom : (TM0Seq.evalFromCfg M_f ⟨default, T⟩).Dom)
    (h_f_spec : ∀ h, (TM0Seq.evalFromCfg M_f ⟨default, T⟩).get h =
      ⟨q_done, T'⟩) :
    let step_c := @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
    ∀ (h_c_dom : (Turing.eval step_c ⟨Sum.inl q_t, T⟩).Dom),
      (Turing.eval step_c ⟨Sum.inl q_t, T⟩).get h_c_dom =
        ⟨Sum.inr (Sum.inl q_done), T'⟩ := by
  intro step_c h_c_dom
  obtain ⟨c₂, h_step_f⟩ := h_step
  have h_step_c : step_c ⟨Sum.inl q_t, T⟩ =
      some ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩ := by
    show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _
      (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
    rw [condCompose_halt_true M_p M_f M_g q_t q_f T h_halt]
    simp [h_step_f]
  have h_eval_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_c)
  have h_eval_f_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_f)
  have hb_f_mem_c2 :
      ⟨q_done, T'⟩ ∈ Turing.eval (TM0.step M_f) c₂ := by
    rw [← h_eval_f_eq]
    exact h_f_spec h_f_dom ▸ Part.get_mem h_f_dom
  obtain ⟨b₂, hb₂_rel, hb₂_mem⟩ := Turing.tr_eval
    (condCompose_f_respects M_p M_f M_g q_t q_f)
    (a₁ := c₂) (a₂ := ⟨Sum.inr (Sum.inl c₂.q), c₂.Tape⟩)
    ⟨rfl, rfl⟩ hb_f_mem_c2
  have hb₂_mem' : b₂ ∈ Turing.eval step_c ⟨Sum.inl q_t, T⟩ := by
    rw [h_eval_eq]
    exact hb₂_mem
  have hb₂_eq : b₂ = ⟨Sum.inr (Sum.inl q_done), T'⟩ := by
    rcases hb₂_rel with ⟨hq, hT⟩
    cases b₂
    simp at hq hT
    simp [hq, hT]
  exact (Part.get_eq_of_mem hb₂_mem' h_c_dom).trans hb₂_eq

theorem condCompose_fixed_at_halt_false_of_step
    {Λ_p Λ_f Λ_g : Type}
    [Inhabited Λ_p] [Inhabited Λ_f] [Inhabited Λ_g]
    [DecidableEq Λ_p]
    (M_p : TM0.Machine ChainΓ Λ_p)
    (M_f : TM0.Machine ChainΓ Λ_f)
    (M_g : TM0.Machine ChainΓ Λ_g)
    (q_t q_f : Λ_p)
    (hne : q_t ≠ q_f)
    (q_done : Λ_g) (T T' : Tape ChainΓ)
    (h_halt : TM0.step M_p ⟨q_f, T⟩ = none)
    (h_step : ∃ c₂, TM0.step M_g ⟨default, T⟩ = some c₂)
    (h_g_dom : (TM0Seq.evalFromCfg M_g ⟨default, T⟩).Dom)
    (h_g_spec : ∀ h, (TM0Seq.evalFromCfg M_g ⟨default, T⟩).get h =
      ⟨q_done, T'⟩) :
    let step_c := @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) ⟨Sum.inl default⟩ _
      (tm0CondCompose M_p M_f M_g q_t q_f)
    ∀ (h_c_dom : (Turing.eval step_c ⟨Sum.inl q_f, T⟩).Dom),
      (Turing.eval step_c ⟨Sum.inl q_f, T⟩).get h_c_dom =
        ⟨Sum.inr (Sum.inr q_done), T'⟩ := by
  intro step_c h_c_dom
  obtain ⟨c₂, h_step_g⟩ := h_step
  have h_step_c : step_c ⟨Sum.inl q_f, T⟩ =
      some ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩ := by
    show @TM0.step ChainΓ (Λ_p ⊕ Λ_f ⊕ Λ_g) _ _
      (tm0CondCompose M_p M_f M_g q_t q_f) _ = _
    rw [condCompose_halt_false M_p M_f M_g q_t q_f hne T h_halt]
    simp [h_step_g]
  have h_eval_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_c)
  have h_eval_g_eq := Turing.reaches_eval (Relation.ReflTransGen.single h_step_g)
  have hb_g_mem_c2 :
      ⟨q_done, T'⟩ ∈ Turing.eval (TM0.step M_g) c₂ := by
    rw [← h_eval_g_eq]
    exact h_g_spec h_g_dom ▸ Part.get_mem h_g_dom
  obtain ⟨b₂, hb₂_rel, hb₂_mem⟩ := Turing.tr_eval
    (condCompose_g_respects M_p M_f M_g q_t q_f)
    (a₁ := c₂) (a₂ := ⟨Sum.inr (Sum.inr c₂.q), c₂.Tape⟩)
    ⟨rfl, rfl⟩ hb_g_mem_c2
  have hb₂_mem' : b₂ ∈ Turing.eval step_c ⟨Sum.inl q_f, T⟩ := by
    rw [h_eval_eq]
    exact hb₂_mem
  have hb₂_eq : b₂ = ⟨Sum.inr (Sum.inr q_done), T'⟩ := by
    rcases hb₂_rel with ⟨hq, hT⟩
    cases b₂
    simp at hq hT
    simp [hq, hT]
  exact (Part.get_eq_of_mem hb₂_mem' h_c_dom).trans hb₂_eq

theorem tm0_pairedDecrLeftIncrRight_blockCondInv :
    TM0RealizesBlockCondInv pairedDecrLeftIncrRight pairedAddCond pairedSepInv := by
  obtain ⟨Λs, hΛsi, hΛsf, Ms, hMs⟩ := tm0_pairedDecrLeftIncrRight_blockInv
  obtain ⟨Λp, hΛpi, hΛpf, Mp, q_le, q_gt, hne, hp⟩ :=
    tm0_blockValueLeq_decidable_2 0
  haveI : DecidableEq Λp := Classical.decEq Λp
  let hΛsFi : Inhabited (Λs ⊕ FinalizeSt) := ⟨Sum.inl (@default _ hΛsi)⟩
  let MsF : TM0.Machine ChainΓ (Λs ⊕ FinalizeSt) :=
    @TM0Seq.compose ChainΓ Λs hΛsi FinalizeSt inferInstance Ms finalizeMachine
  let Mcond : TM0.Machine ChainΓ (Λp ⊕ FinalizeSt ⊕ (Λs ⊕ FinalizeSt)) :=
    @tm0CondCompose Λp FinalizeSt (Λs ⊕ FinalizeSt)
      hΛpi inferInstance hΛsFi inferInstance
      Mp finalizeMachine MsF q_le q_gt
  refine ⟨Λp ⊕ FinalizeSt ⊕ (Λs ⊕ FinalizeSt), inferInstance, inferInstance,
    Mcond, Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)), ?_⟩
  intro block hInv hblock hstep_nd
  have hp_spec := hp block [] hblock (by simp)
  have hp_dom := hp_spec.1
  have hp_out := hp_spec.2 hp_dom
  set cp := (TM0Seq.evalCfg Mp (block ++ [default])).get hp_dom
  have hcp_tape : cp.Tape = Tape.mk₁ (block ++ [default]) := hp_out.1
  have hcp_mem : cp ∈ TM0Seq.evalCfg Mp (block ++ [default]) := Part.get_mem hp_dom
  have hcp_eval := Turing.mem_eval.mp hcp_mem
  have hcp_halt : TM0.step Mp cp = none := hcp_eval.2
  have hcp_reaches : Reaches (TM0.step Mp) (TM0.init (block ++ [default])) cp := hcp_eval.1
  have hphase1 := condCompose_phase1_reaches Mp finalizeMachine MsF q_le q_gt
    cp (block ++ [default]) hcp_reaches
  change Reaches (TM0.step Mcond) (TM0.init (block ++ [default]))
    { q := Sum.inl cp.q, Tape := cp.Tape } at hphase1
  have heval_rewrite :
      TM0Seq.evalCfg Mcond (block ++ [default]) =
        Turing.eval (TM0.step Mcond) ⟨Sum.inl cp.q, cp.Tape⟩ := by
    exact Turing.reaches_eval hphase1
  by_cases hcond : pairedAddCond block
  · have hp_false : ¬ blockValueLeq 0 block := by
      simpa [pairedAddCond] using hcond
    have hq : cp.q = q_gt := hp_out.2.2 hp_false
    have hhalt_q : TM0.step Mp ⟨q_gt, cp.Tape⟩ = none := hq ▸ hcp_halt
    have hstep_block_nd : ∀ g ∈ pairedDecrLeftIncrRight block, g ≠ default :=
      hstep_nd hcond
    obtain ⟨hMs_dom, hMs_tape⟩ := hMs block hInv hblock hstep_block_nd
    have hfinal := compose_finalize_evalCfg Ms (block ++ [default])
      (pairedDecrLeftIncrRight block ++ [default]) hMs_dom (hMs_tape hMs_dom)
    have hbranch_dom :
        (TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩).Dom := by
      rw [hcp_tape]
      change (TM0Seq.evalFromCfg MsF (TM0.init (block ++ [default]))).Dom
      rw [TM0Seq.evalFromCfg_init]
      exact hfinal.1
    have hbranch_spec :
        ∀ h, (TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩).get h =
          ⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (pairedDecrLeftIncrRight block ++ [default])⟩ := by
      intro h
      have heq :
          TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩ =
            TM0Seq.evalCfg MsF (block ++ [default]) := by
        rw [hcp_tape]
        exact TM0Seq.evalFromCfg_init (M := MsF) (l := block ++ [default])
      have hget :
          (TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩).get h =
            (TM0Seq.evalCfg MsF (block ++ [default])).get hfinal.1 := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hfinal.2 hfinal.1
    have hbranch_step :
        ∃ c₂, TM0.step MsF ⟨default, cp.Tape⟩ = some c₂ := by
      rw [hcp_tape]
      change ∃ c₂, TM0.step MsF (TM0.init (block ++ [default])) = some c₂
      change ∃ c₂, TM0.step MsF ⟨default, Tape.mk₁ (block ++ [default])⟩ = some c₂
      rcases hfirst : TM0.step Ms ⟨default, Tape.mk₁ (block ++ [default])⟩ with _ | c₂
      · refine ⟨(⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (block ++ [default])⟩ :
            TM0.Cfg ChainΓ (Λs ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λs hΛsi FinalizeSt inferInstance
          Ms finalizeMachine) ⟨Sum.inl default, Tape.mk₁ (block ++ [default])⟩ =
          some ⟨Sum.inr FinalizeSt.done, Tape.mk₁ (block ++ [default])⟩
        rw [TM0Seq.compose_step_on_halt Ms finalizeMachine default
          (Tape.mk₁ (block ++ [default])) hfirst]
        change Option.map
          (fun c₂ : TM0.Cfg ChainΓ FinalizeSt =>
            ({ q := Sum.inr c₂.q, Tape := c₂.Tape } :
              TM0.Cfg ChainΓ (Λs ⊕ FinalizeSt)))
          (TM0.step finalizeMachine
            ⟨FinalizeSt.start, Tape.mk₁ (block ++ [default])⟩) =
          some ⟨Sum.inr FinalizeSt.done, Tape.mk₁ (block ++ [default])⟩
        rw [finalize_step_start]
        rfl
      · refine ⟨(⟨Sum.inl c₂.q, c₂.Tape⟩ :
            TM0.Cfg ChainΓ (Λs ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λs hΛsi FinalizeSt inferInstance
          Ms finalizeMachine) ⟨Sum.inl default, Tape.mk₁ (block ++ [default])⟩ =
          some ⟨Sum.inl c₂.q, c₂.Tape⟩
        simpa using TM0Seq.compose_step_inl Ms finalizeMachine
          (⟨default, Tape.mk₁ (block ++ [default])⟩ : TM0.Cfg ChainΓ Λs) c₂ hfirst
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MsF q_le q_gt))
        ⟨Sum.inl q_gt, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_false Mp finalizeMachine MsF q_le q_gt hne
        cp.Tape hhalt_q).mpr hbranch_dom
    have hdom : (TM0Seq.evalCfg Mcond (block ++ [default])).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_false_of_step
      Mp finalizeMachine MsF q_le q_gt hne (Sum.inr FinalizeSt.done) cp.Tape
      (Tape.mk₁ (pairedDecrLeftIncrRight block ++ [default]))
      hhalt_q hbranch_step hbranch_dom hbranch_spec
    have hcfg' : (TM0Seq.evalCfg Mcond (block ++ [default])).get h =
        ⟨Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)),
          Tape.mk₁ (pairedDecrLeftIncrRight block ++ [default])⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond (block ++ [default]) =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond (block ++ [default])).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    simp [hcond, hcfg']
  · have hp_true : blockValueLeq 0 block := by
      simpa [pairedAddCond] using hcond
    have hq : cp.q = q_le := hp_out.2.1 hp_true
    have hhalt_q : TM0.step Mp ⟨q_le, cp.Tape⟩ = none := hq ▸ hcp_halt
    obtain ⟨hid_dom, hid_spec⟩ := finalize_evalFromCfg cp.Tape
    have hid_step : ∃ c₂, TM0.step finalizeMachine ⟨default, cp.Tape⟩ = some c₂ := by
      exact ⟨⟨FinalizeSt.done, cp.Tape⟩, finalize_step_start cp.Tape⟩
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MsF q_le q_gt))
        ⟨Sum.inl q_le, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_true Mp finalizeMachine MsF q_le q_gt
        cp.Tape hhalt_q).mpr hid_dom
    have hdom : (TM0Seq.evalCfg Mcond (block ++ [default])).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_true_of_step
      Mp finalizeMachine MsF q_le q_gt FinalizeSt.done cp.Tape cp.Tape
      hhalt_q hid_step hid_dom (fun h => hid_spec h)
    have hcfg' : (TM0Seq.evalCfg Mcond (block ++ [default])).get h =
        ⟨Sum.inr (Sum.inl FinalizeSt.done), cp.Tape⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond (block ++ [default]) =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond (block ++ [default])).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    have hq_ne :
        Sum.inr (Sum.inl FinalizeSt.done) ≠
          (Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)) :
            Λp ⊕ FinalizeSt ⊕ (Λs ⊕ FinalizeSt)) := by
      simp
    simp [hcond, hcfg', hq_ne, hcp_tape]

theorem blockIterateWhile_pairedSepInv
    (n : ℕ) (block : List ChainΓ)
    (hInv : pairedSepInv block) :
    pairedSepInv
      (blockIterateWhile pairedDecrLeftIncrRight pairedAddCond n block) := by
  induction n generalizing block with
  | zero =>
      exact hInv
  | succ n ih =>
      by_cases hcond : pairedAddCond block
      · rw [blockIterateWhile_succ_true _ _ _ _ hcond]
        exact ih _ (pairedDecrLeftIncrRight_pairedSepInv block hInv)
      · rw [blockIterateWhile_succ_false _ _ _ _ hcond]
        exact hInv

theorem binAddPairedWhile_pairedSepInv
    (block : List ChainΓ)
    (hInv : pairedSepInv block)
    (hblock : ∀ g ∈ block, g ≠ default) :
    pairedSepInv (binAddPairedWhile block) := by
  obtain ⟨n, hn, _hstop⟩ := binAddPairedWhile_eq_iterate block hblock hInv
  rw [hn]
  exact blockIterateWhile_pairedSepInv n block hInv

theorem tm0RealizesBlockInv_of_block {Γ : Type} [Inhabited Γ]
    {f : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlock Γ f) :
    TM0RealizesBlockInv f blockInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block _hInv hblock hfblock
  obtain ⟨hdom, htape⟩ := hM block [] hblock (by simp) hfblock
  exact ⟨hdom, htape⟩

theorem tm0RealizesBlockInv_comp' {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ} {blockInv₁ blockInv₂ : List Γ → Prop}
    (hf : TM0RealizesBlockInv f blockInv₁)
    (hg : TM0RealizesBlockInv g blockInv₂)
    (hf_inv : ∀ block, blockInv₁ block → (∀ x ∈ block, x ≠ default) → blockInv₂ (f block))
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default) :
    TM0RealizesBlockInv (g ∘ f) blockInv₁ := by
  obtain ⟨Λ_f, hΛfi, hΛff, M_f, hM_f⟩ := hf
  obtain ⟨Λ_g, hΛgi, hΛgf, M_g, hM_g⟩ := hg
  let hsum : Inhabited (Λ_f ⊕ Λ_g) := ⟨Sum.inl (@default _ hΛfi)⟩
  refine ⟨Λ_f ⊕ Λ_g, hsum, inferInstance,
    @TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g, ?_⟩
  intro block hInv hblock hgf
  have hfblock_nd := hf_nd block hblock
  obtain ⟨hf_dom, hf_tape⟩ := hM_f block hInv hblock hfblock_nd
  obtain ⟨hg_dom, hg_tape⟩ := hM_g (f block)
    (hf_inv block hInv hblock) hfblock_nd hgf
  have hg_from_cfg :
      (TM0Seq.evalFromCfg M_g
        ⟨default, ((TM0Seq.evalCfg M_f (block ++ [default])).get hf_dom).Tape⟩).Dom := by
    rw [hf_tape hf_dom]
    show (TM0Seq.evalFromCfg M_g (TM0.init (f block ++ [default]))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hg_dom
  have hcomp_dom :
      (TM0Seq.evalCfg
        (@TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g)
        (block ++ [default])).Dom := by
    exact (TM0Seq.evalCfg_dom_iff
      (@TM0Seq.compose Γ Λ_f hΛfi Λ_g hΛgi M_f M_g)
      (block ++ [default])).mpr
        (@TM0Seq.compose_dom_of_parts Γ _ Λ_f hΛfi Λ_g hΛgi
          M_f M_g (block ++ [default]) hf_dom hg_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have hcomp_tape :=
    @TM0Seq.compose_evalCfg_tape Γ _ Λ_f hΛfi Λ_g hΛgi M_f M_g
      (block ++ [default]) (f block ++ [default])
      hf_dom (hf_tape hf_dom) hg_dom h
  rw [hcomp_tape]
  exact hg_tape hg_dom

theorem tm0_binAddPairedWhile_blockInv :
    TM0RealizesBlockInv binAddPairedWhile pairedSepInv :=
  tm0RealizesBlock_while_inv
    pairedDecrLeftIncrRight
    binAddPairedWhile
    pairedAddCond
    pairedSepInv
    tm0_pairedDecrLeftIncrRight_blockCondInv
    pairedDecrLeftIncrRight_step_inv
    pairedDecrLeftIncrRight_ne_default
    (fun block hblock hInv => binAddPairedWhile_eq_iterate block hblock hInv)
    (fun block hblock _hInv => binAddPairedWhile_ne_default block hblock)

theorem tm0_extractPairedRight_blockInv :
    TM0RealizesBlockInv extractPairedRight pairedSepInv :=
  tm0RealizesBlockInv_of_block tm0_extractPairedRight_block

theorem tm0_normalizeBlock_blockInvTrue :
    TM0RealizesBlockInv normalizeBlock (fun _block => True) :=
  tm0RealizesBlockInv_of_block tm0_normalizeBlock

theorem tm0_binAddPaired_blockInv :
    TM0RealizesBlockInv binAddPaired pairedSepInv := by
  let f : List ChainΓ → List ChainΓ :=
    normalizeBlock ∘ extractPairedRight ∘ binAddPairedWhile
  have hf : TM0RealizesBlockInv f pairedSepInv := by
    exact
      show TM0RealizesBlockInv
          (normalizeBlock ∘ (extractPairedRight ∘ binAddPairedWhile)) pairedSepInv from
        tm0RealizesBlockInv_comp'
        (tm0RealizesBlockInv_comp
          tm0_binAddPairedWhile_blockInv
          tm0_extractPairedRight_blockInv
          (fun block hInv hblock => binAddPairedWhile_pairedSepInv block hInv hblock)
          binAddPairedWhile_ne_default)
        tm0_normalizeBlock_blockInvTrue
        (fun _block _hInv _hblock => True.intro)
        extractPairedRight_binAddPairedWhile_ne_default
  exact tm0RealizesBlockInv_congr hf (fun block hInv =>
    (binAddPaired_eq_while_decomp block hInv).symm)

/-- Separator-parametric paired addition, reduced through the existing
`chainConsBottom` paired-add machine.

The strengthened invariant says the chosen auxiliary separator
`chainConsBottom` is fresh for the whole paired block. Under that condition,
we may rewrite the first `pairSep` boundary to `chainConsBottom`, run the
fixed paired-add machine, and read the result as `binAddPairedSep pairSep`. -/
theorem tm0_binAddPairedSep_blockInvFreshConsBottom
    (pairSep : ChainΓ) :
    TM0RealizesBlockInv (binAddPairedSep pairSep)
      (pairedSepInvFresh pairSep chainConsBottom) := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0_binAddPaired_blockInv
  let Mpre := boundaryReplaceMachine pairSep chainConsBottom
  let hsum : Inhabited (BoundaryReplaceSt ⊕ Λ) :=
    ⟨Sum.inl (@default _ inferInstance)⟩
  let Mcomp : TM0.Machine ChainΓ (BoundaryReplaceSt ⊕ Λ) :=
    @TM0Seq.compose ChainΓ BoundaryReplaceSt inferInstance Λ hΛi Mpre M
  refine ⟨BoundaryReplaceSt ⊕ Λ, hsum, inferInstance, Mcomp, ?_⟩
  intro block hInv hblock hfblock
  rcases hsplit : splitAtSep pairSep block with ⟨left, right⟩
  have hmem : pairSep ∈ block := hInv.1.1
  have hblock_reconstruct :
      block = left ++ pairSep :: right := by
    simpa [hsplit] using splitAtSep_reconstruct_of_mem pairSep block hmem
  have hleft_nd : ∀ g ∈ left, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_left _ hg)
  have hleft_npair : ∀ g ∈ left, g ≠ pairSep := by
    simpa [hsplit] using splitAtSep_fst_no_sep pairSep block
  have hleft_ncons : ∀ g ∈ left, g ≠ chainConsBottom := by
    intro g hg
    exact hInv.2 g (by
      rw [hblock_reconstruct]
      exact List.mem_append_left _ hg)
  have hright_nd : ∀ g ∈ right, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have hright_ncons : ∀ g ∈ right, g ≠ chainConsBottom := by
    intro g hg
    exact hInv.2 g (by
      rw [hblock_reconstruct]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have hfixed_inv : pairedSepInv (left ++ chainConsBottom :: right) := by
    constructor
    · unfold hasConsBottom
      simp
    · rw [show splitAtConsBottom (left ++ chainConsBottom :: right) = (left, right) by
        simpa using splitAtConsBottom_general left right hleft_ncons]
      exact hright_ncons
  have hfixed_nd : ∀ g ∈ left ++ chainConsBottom :: right, g ≠ default := by
    intro g hg
    simp only [List.mem_append, List.mem_cons] at hg
    rcases hg with hg | rfl | hg
    · exact hleft_nd g hg
    · exact chainConsBottom_ne_default
    · exact hright_nd g hg
  have hfixed_out_nd :
      ∀ g ∈ binAddPaired (left ++ chainConsBottom :: right), g ≠ default :=
    binAddPaired_ne_default _ hfixed_nd
  have hpre := tm0_boundaryReplace pairSep chainConsBottom
    left (right ++ [default]) hleft_nd hleft_npair
  have hpre_dom' : (TM0Seq.evalCfg Mpre (block ++ [default])).Dom := by
    rw [hblock_reconstruct]
    simpa [Mpre, List.append_assoc] using hpre.1
  have hpre_tape' :
      ((TM0Seq.evalCfg Mpre (block ++ [default])).get hpre_dom').Tape =
        Tape.mk₁ (left ++ chainConsBottom :: right ++ [default]) := by
    have hget :
        (TM0Seq.evalCfg Mpre (block ++ [default])).get hpre_dom' =
          (TM0Seq.evalCfg Mpre (left ++ pairSep :: (right ++ [default]))).get hpre.1 := by
      apply Part.get_eq_get_of_eq
      rw [hblock_reconstruct]
      simpa [Mpre, List.append_assoc]
    rw [hget, hpre.2 hpre.1]
    simp [List.append_assoc]
  obtain ⟨hm_dom, hm_tape⟩ :=
    hM (left ++ chainConsBottom :: right) hfixed_inv hfixed_nd hfixed_out_nd
  have hm_from_cfg :
      (TM0Seq.evalFromCfg M
        ⟨default, ((TM0Seq.evalCfg Mpre (block ++ [default])).get
          hpre_dom').Tape⟩).Dom := by
    rw [hpre_tape']
    show (TM0Seq.evalFromCfg M
      (TM0.init ((left ++ chainConsBottom :: right) ++ [default]))).Dom
    rw [TM0Seq.evalFromCfg_init]
    simpa [List.append_assoc] using hm_dom
  have hcomp_dom :
      (TM0Seq.evalCfg Mcomp (block ++ [default])).Dom := by
    exact (TM0Seq.evalCfg_dom_iff Mcomp (block ++ [default])).mpr
      (TM0Seq.compose_dom_of_parts Mpre M
        (block ++ [default]) hpre_dom' hm_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have hcomp_tape :=
    TM0Seq.compose_evalCfg_tape Mpre M
      (block ++ [default]) (left ++ chainConsBottom :: right ++ [default])
      hpre_dom' hpre_tape' hm_dom h
  rw [hcomp_tape]
  have hsem :
      binAddPairedSep pairSep block =
        binAddPaired (left ++ chainConsBottom :: right) := by
    rw [hblock_reconstruct]
    exact binAddPairedSep_eq_binAddPaired_replaceSep
      pairSep left right hleft_npair hleft_ncons
  rw [hm_tape hm_dom]
  rw [hsem]

theorem binPredRaw_no_mulSep₂ (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ binMulStateSep₂) :
    ∀ g ∈ binPredRaw block, g ≠ binMulStateSep₂ := by
  induction block with
  | nil =>
      simp [binPredRaw]
  | cons c rest ih =>
      intro g hg
      have hc : c ≠ binMulStateSep₂ := hblock c (by simp)
      have hrest : ∀ g ∈ rest, g ≠ binMulStateSep₂ := by
        intro g hg
        exact hblock g (List.mem_cons_of_mem c hg)
      have hbit01 : γ'ToChainΓ Γ'.bit0 ≠ γ'ToChainΓ Γ'.bit1 := by decide
      by_cases hbit0 : c = γ'ToChainΓ Γ'.bit0
      · simp [binPredRaw, hbit0, hbit01] at hg
        rcases hg with rfl | hg
        · simpa [binMulStateSep₂] using (Ne.symm chainMulSep₂_ne_bit1)
        · exact ih hrest g hg
      · by_cases hbit1 : c = γ'ToChainΓ Γ'.bit1
        · simp [binPredRaw, hbit1] at hg
          rcases hg with rfl | hg
          · simpa [binMulStateSep₂] using (Ne.symm chainMulSep₂_ne_bit0)
          · exact hrest g hg
        · simp [binPredRaw, hbit0, hbit1] at hg
          rcases hg with rfl | hg
          · exact hc
          · exact hrest g hg

theorem tm0_binPred_blockSep_mulSep₂ :
    TM0RealizesBlockSep ChainΓ binMulStateSep₂ binPred := by
  rw [binPred_eq_comp]
  exact tm0RealizesBlockSep_comp
    (tm0RealizesBlockSep_comp
      (tm0_normalizeBlockSep (sep := binMulStateSep₂)
        (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit0)
        (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit1))
      (tm0_binPredRaw_blockSep binMulStateSep₂
        (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit1)
        (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit0))
      (fun _block _hblock => normalizeBlock_ne_default _)
      (fun block _hblock => normalizeBlock_no_mulSep₂ block))
    (tm0_normalizeBlockSep (sep := binMulStateSep₂)
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit0)
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit1))
    (fun block hblock => binPredRaw_ne_default _ (normalizeBlock_ne_default _))
    (fun block hblock => binPredRaw_no_mulSep₂ _ (normalizeBlock_no_mulSep₂ _))

theorem binAddPairedKeepRightSep_no_mulSep₂
    (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ binMulStateSep₂) :
    ∀ g ∈ binAddPairedKeepRightSep binMulStateSep₁ block,
      g ≠ binMulStateSep₂ := by
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨left, right⟩
  intro g hg
  unfold binAddPairedKeepRightSep binAddPairedSep at hg
  simp [hsplit] at hg
  rcases hg with hg | rfl | hg
  · exact chainBinaryRepr_no_chainMulSep₂ _ g hg
  · exact chainMulSep₁_ne_chainMulSep₂
  · exact hblock g
      (splitAtSep_snd_subset binMulStateSep₁ block g (by simpa [hsplit] using hg))

/-- A paired-block operation bounded by an outer separator. The suffix after
the outer separator is unrestricted: in the multiplication step it is
`fuel ++ outerSep :: suffix`, so requiring it to be blank-free would be the
wrong interface. -/
def TM0RealizesPairedBlockBeforeSep
    (pairSep outerSep : ChainΓ) (f : List ChainΓ → List ChainΓ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine ChainΓ Λ),
    ∀ (left right suffix : List ChainΓ),
      (∀ g ∈ left, g ≠ default) →
      (∀ g ∈ left, g ≠ pairSep) →
      (∀ g ∈ left, g ≠ outerSep) →
      (∀ g ∈ right, g ≠ default) →
      (∀ g ∈ right, g ≠ pairSep) →
      (∀ g ∈ right, g ≠ outerSep) →
      (∀ g ∈ f (left ++ pairSep :: right), g ≠ default) →
      (TM0Seq.evalCfg M
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom),
        ((TM0Seq.evalCfg M
          (left ++ pairSep :: right ++ outerSep :: suffix)).get h).Tape =
          Tape.mk₁ (f (left ++ pairSep :: right) ++ outerSep :: suffix)

/-- Variant of `TM0RealizesPairedBlockBeforeSep` that exposes the extra
freshness needed by the copy/delete construction.

The intended route is:

1. copy the paired block with `copySep`, using the new suffix-opaque copy
   machine before `outerSep`;
2. run paired addition before the copied tail;
3. use the copied tail and `dropUntilFirstSep pairSep` to recover the right
   component.

The plain `TM0RealizesPairedBlockBeforeSep` interface has no assumptions that
`copySep` is fresh for `left` and `right`, so this is the theorem shape that
can actually be proved by the generic copy machine. -/
def TM0RealizesPairedBlockBeforeSepViaCopySep
    (pairSep copySep outerSep : ChainΓ)
    (f : List ChainΓ → List ChainΓ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine ChainΓ Λ),
    ∀ (left right suffix : List ChainΓ),
      (∀ g ∈ left, g ≠ default) →
      (∀ g ∈ left, g ≠ pairSep) →
      (∀ g ∈ left, g ≠ copySep) →
      (∀ g ∈ left, g ≠ outerSep) →
      (∀ g ∈ right, g ≠ default) →
      (∀ g ∈ right, g ≠ pairSep) →
      (∀ g ∈ right, g ≠ copySep) →
      (∀ g ∈ right, g ≠ outerSep) →
      (∀ g ∈ f (left ++ pairSep :: right), g ≠ default) →
      (TM0Seq.evalCfg M
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom),
        ((TM0Seq.evalCfg M
          (left ++ pairSep :: right ++ outerSep :: suffix)).get h).Tape =
          Tape.mk₁ (f (left ++ pairSep :: right) ++ outerSep :: suffix)

/-- Suffix-opaque paired-block operation before an explicit separator.

This is the same external contract as `TM0RealizesPairedBlockBeforeSep`; the
separate name marks the implementation requirement: proofs of this shape must
not consume the suffix after `outerSep`. -/
abbrev TM0RealizesPairedBlockBeforeSepAnySuffix
    (pairSep outerSep : ChainΓ) (f : List ChainΓ → List ChainΓ) : Prop :=
  TM0RealizesPairedBlockBeforeSep pairSep outerSep f

/-- Parameterized paired-add loop condition: the left side of the paired block
is positive. The value comparison is separator-bounded, so `pairSep` does not
need to be a non-binary decoder sentinel. -/
noncomputable abbrev pairedAddCondSep (pairSep : ChainΓ) : List ChainΓ → Prop :=
  fun block => ¬ blockValueLeqBeforeSep 0 pairSep block

/-- One separator-parametric paired-add transfer step. On a well-formed block
`left ++ pairSep :: right`, this decrements the left side and increments the
right side, preserving `pairSep`. -/
noncomputable def pairedDecrLeftIncrRightSep
    (pairSep : ChainΓ) (block : List ChainΓ) : List ChainΓ :=
  by
    classical
    exact
      if pairedSepInvSep pairSep block then
        let (left, right) := splitAtSep pairSep block
        binPred left ++ pairSep :: binSucc (normalizeBlock right)
      else
        block

/-- While-loop result for separator-parametric paired addition. -/
noncomputable def binAddPairedWhileSep
    (pairSep : ChainΓ) (block : List ChainΓ) : List ChainΓ :=
  let (left, _right) := splitAtSep pairSep block
  let n := decodeBinaryBlock left
  blockIterateWhile (pairedDecrLeftIncrRightSep pairSep)
    (pairedAddCondSep pairSep) n block

/-- Conditional paired-block body before an explicit outer separator. -/
def TM0RealizesPairedBlockBeforeSepCond
    (pairSep outerSep : ChainΓ)
    (step : List ChainΓ → List ChainΓ)
    (cond : List ChainΓ → Prop) [DecidablePred cond] : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine ChainΓ Λ) (q_cont : Λ),
    ∀ (left right suffix : List ChainΓ),
      (∀ g ∈ left, g ≠ default) →
      (∀ g ∈ left, g ≠ pairSep) →
      (∀ g ∈ left, g ≠ outerSep) →
      (∀ g ∈ right, g ≠ default) →
      (∀ g ∈ right, g ≠ pairSep) →
      (∀ g ∈ right, g ≠ outerSep) →
      (cond (left ++ pairSep :: right) →
        ∀ g ∈ step (left ++ pairSep :: right), g ≠ default) →
      (TM0Seq.evalCfg M
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom),
        let cfg := (TM0Seq.evalCfg M
          (left ++ pairSep :: right ++ outerSep :: suffix)).get h
        if cond (left ++ pairSep :: right) then
          cfg.q = q_cont ∧
            cfg.Tape =
              Tape.mk₁ (step (left ++ pairSep :: right) ++ outerSep :: suffix)
        else
          cfg.q ≠ q_cont ∧
            cfg.Tape = Tape.mk₁
              (left ++ pairSep :: right ++ outerSep :: suffix)

/-- The parametric transfer step preserves the paired separator invariant. -/
theorem pairedDecrLeftIncrRightSep_pairedSepInvSep
    (pairSep : ChainΓ) (block : List ChainΓ)
    (hpred_npair : ∀ left : List ChainΓ,
      ∀ g ∈ binPred left, g ≠ pairSep)
    (hsucc_npair : ∀ right : List ChainΓ,
      (∀ g ∈ right, g ≠ pairSep) →
      ∀ g ∈ binSucc (normalizeBlock right), g ≠ pairSep)
    (hInv : pairedSepInvSep pairSep block) :
    pairedSepInvSep pairSep (pairedDecrLeftIncrRightSep pairSep block) := by
  classical
  rcases hsplit : splitAtSep pairSep block with ⟨left, right⟩
  have hright_npair : ∀ g ∈ right, g ≠ pairSep := by
    simpa [pairedSepInvSep, hsplit] using hInv.2
  unfold pairedDecrLeftIncrRightSep
  simp [hInv, hsplit]
  constructor
  · simp
  · rw [show splitAtSep pairSep
        (binPred left ++ pairSep :: binSucc (normalizeBlock right)) =
        (binPred left, binSucc (normalizeBlock right)) by
      apply splitAtSep_general_cons
      exact hpred_npair left]
    exact hsucc_npair right hright_npair

theorem pairedDecrLeftIncrRightSep_ne_default
    (pairSep : ChainΓ) (hpair_nd : pairSep ≠ default)
    (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (_hcond : pairedAddCondSep pairSep block) :
    ∀ g ∈ pairedDecrLeftIncrRightSep pairSep block, g ≠ default := by
  classical
  unfold pairedDecrLeftIncrRightSep
  by_cases hInv : pairedSepInvSep pairSep block
  · rcases hsplit : splitAtSep pairSep block with ⟨left, right⟩
    have hleft_nd : ∀ g ∈ left, g ≠ default := by
      intro g hg
      exact hblock g (splitAtSep_fst_subset pairSep block g (by simpa [hsplit] using hg))
    have hright_nd : ∀ g ∈ right, g ≠ default := by
      intro g hg
      exact hblock g (splitAtSep_snd_subset pairSep block g (by simpa [hsplit] using hg))
    simp [hInv, hsplit]
    rintro g (hg | rfl | hg)
    · exact binPred_ne_default left hleft_nd g hg
    · exact hpair_nd
    · exact binSucc_ne_default _ (normalizeBlock_ne_default right) g hg
  · simpa [hInv] using hblock

theorem pairedDecrLeftIncrRightSep_ne_marker
    (pairSep marker : ChainΓ)
    (hpair_marker : pairSep ≠ marker)
    (hmarker_bit0 : marker ≠ γ'ToChainΓ Γ'.bit0)
    (hmarker_bit1 : marker ≠ γ'ToChainΓ Γ'.bit1)
    (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ marker)
    (_hcond : pairedAddCondSep pairSep block) :
    ∀ g ∈ pairedDecrLeftIncrRightSep pairSep block, g ≠ marker := by
  classical
  unfold pairedDecrLeftIncrRightSep
  by_cases hInv : pairedSepInvSep pairSep block
  · rcases hsplit : splitAtSep pairSep block with ⟨left, right⟩
    have hleft_nm : ∀ g ∈ left, g ≠ marker := by
      intro g hg
      exact hblock g (splitAtSep_fst_subset pairSep block g (by simpa [hsplit] using hg))
    have hright_nm : ∀ g ∈ right, g ≠ marker := by
      intro g hg
      exact hblock g (splitAtSep_snd_subset pairSep block g (by simpa [hsplit] using hg))
    simp [hInv, hsplit]
    rintro g (hg | rfl | hg)
    · unfold binPred at hg
      exact chainBinaryRepr_no_of_ne_bits marker hmarker_bit0 hmarker_bit1
        (decodeBinaryBlock left - 1) g hg
    · exact hpair_marker
    · exact binSucc_no_of_ne_bits hmarker_bit0 hmarker_bit1
        (normalizeBlock right)
        (normalizeBlock_no_of_ne_bits marker hmarker_bit0 hmarker_bit1 right) g hg
  · simpa [hInv] using hblock

/-- The unconditional paired-add transfer body before an explicit outer
separator. The left predecessor is suffix-opaque, and the right successor runs
as an inner block before `outerSep`. -/
theorem tm0_pairedDecrLeftIncrRightSep_beforeSep
    {pairSep outerSep : ChainΓ}
    (hpair_bit0 : pairSep ≠ γ'ToChainΓ Γ'.bit0)
    (hpair_bit1 : pairSep ≠ γ'ToChainΓ Γ'.bit1)
    (houter_bit0 : outerSep ≠ γ'ToChainΓ Γ'.bit0)
    (houter_bit1 : outerSep ≠ γ'ToChainΓ Γ'.bit1)
    (hsucc :
      TM0RealizesInnerBlockSepAnySuffix ChainΓ outerSep pairSep
        (binSucc ∘ normalizeBlock)) :
    TM0RealizesPairedBlockBeforeSep pairSep outerSep
      (pairedDecrLeftIncrRightSep pairSep) := by
  obtain ⟨Λp, hΛpi, hΛpf, Mp, hMp⟩ :=
    tm0_binPred_blockSepAnySuffix_of_ne_bits (sep := pairSep) hpair_bit0 hpair_bit1
  obtain ⟨Λs, hΛsi, hΛsf, Ms, hMs⟩ := hsucc
  let hsum : Inhabited (Λp ⊕ Λs) := ⟨Sum.inl (@default _ hΛpi)⟩
  refine ⟨Λp ⊕ Λs, hsum, inferInstance,
    @TM0Seq.compose ChainΓ Λp hΛpi Λs hΛsi Mp Ms, ?_⟩
  intro left right suffix hleft_nd hleft_npair hleft_nouter
    hright_nd hright_npair hright_nouter hf_nd
  have hpred_nd : ∀ g ∈ binPred left, g ≠ default :=
    binPred_ne_default left hleft_nd
  have hpred_npair : ∀ g ∈ binPred left, g ≠ pairSep := by
    unfold binPred
    exact chainBinaryRepr_no_of_ne_bits pairSep hpair_bit0 hpair_bit1
      (decodeBinaryBlock left - 1)
  have hpred_nouter : ∀ g ∈ binPred left, g ≠ outerSep := by
    unfold binPred
    exact chainBinaryRepr_no_of_ne_bits outerSep houter_bit0 houter_bit1
      (decodeBinaryBlock left - 1)
  have hsucc_nd : ∀ g ∈ (binSucc ∘ normalizeBlock) right, g ≠ default := by
    intro g hg
    exact binSucc_ne_default (normalizeBlock right)
      (normalizeBlock_ne_default right) g hg
  have hsucc_nouter : ∀ g ∈ (binSucc ∘ normalizeBlock) right, g ≠ outerSep := by
    intro g hg
    exact binSucc_no_of_ne_bits houter_bit0 houter_bit1
      (normalizeBlock right)
      (normalizeBlock_no_of_ne_bits outerSep houter_bit0 houter_bit1 right) g hg
  have hsucc_npair : ∀ g ∈ (binSucc ∘ normalizeBlock) right, g ≠ pairSep := by
    intro g hg
    exact binSucc_no_of_ne_bits hpair_bit0 hpair_bit1
      (normalizeBlock right)
      (normalizeBlock_no_of_ne_bits pairSep hpair_bit0 hpair_bit1 right) g hg
  obtain ⟨hp_dom, hp_tape⟩ :=
    hMp left (right ++ outerSep :: suffix)
      hleft_nd hleft_npair hpred_nd hpred_npair
  have hp_dom' :
      (TM0Seq.evalCfg Mp
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom := by
    simpa [List.append_assoc] using hp_dom
  have hp_tape' :
      ((TM0Seq.evalCfg Mp
        (left ++ pairSep :: right ++ outerSep :: suffix)).get hp_dom').Tape =
        Tape.mk₁ (binPred left ++ pairSep :: right ++ outerSep :: suffix) := by
    have hget :
        (TM0Seq.evalCfg Mp
          (left ++ pairSep :: right ++ outerSep :: suffix)).get hp_dom' =
          (TM0Seq.evalCfg Mp
            (left ++ pairSep :: (right ++ outerSep :: suffix))).get hp_dom := by
      apply Part.get_eq_get_of_eq
      simp [List.append_assoc]
    rw [hget, hp_tape hp_dom]
    simp [List.append_assoc]
  obtain ⟨hs_dom, hs_tape⟩ :=
    hMs (binPred left) right suffix
      hpred_nd hpred_nouter hpred_npair
      hright_nd hright_nouter hright_npair
      hsucc_nd hsucc_nouter hsucc_npair
  have hs_from_cfg :
      (TM0Seq.evalFromCfg Ms
        ⟨default, ((TM0Seq.evalCfg Mp
          (left ++ pairSep :: right ++ outerSep :: suffix)).get hp_dom').Tape⟩).Dom := by
    rw [hp_tape']
    show (TM0Seq.evalFromCfg Ms
      (TM0.init (binPred left ++ pairSep :: right ++ outerSep :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hs_dom
  have hcomp_dom :
      (TM0Seq.evalCfg
        (@TM0Seq.compose ChainΓ Λp hΛpi Λs hΛsi Mp Ms)
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff
      (@TM0Seq.compose ChainΓ Λp hΛpi Λs hΛsi Mp Ms)
      (left ++ pairSep :: right ++ outerSep :: suffix)).mpr
        (@TM0Seq.compose_dom_of_parts ChainΓ _ Λp hΛpi Λs hΛsi
          Mp Ms
          (left ++ pairSep :: right ++ outerSep :: suffix)
          hp_dom' hs_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have hcomp_tape :=
    @TM0Seq.compose_evalCfg_tape ChainΓ _ Λp hΛpi Λs hΛsi Mp Ms
      (left ++ pairSep :: right ++ outerSep :: suffix)
      (binPred left ++ pairSep :: right ++ outerSep :: suffix)
      hp_dom' hp_tape' hs_dom h
  rw [hcomp_tape, hs_tape hs_dom]
  unfold pairedDecrLeftIncrRightSep
  have hInv : pairedSepInvSep pairSep (left ++ pairSep :: right) := by
    constructor
    · simp
    · rw [splitAtSep_general_cons pairSep left right hleft_npair]
      exact hright_npair
  rw [if_pos hInv]
  rw [splitAtSep_general_cons pairSep left right hleft_npair]
  simp [Function.comp, List.append_assoc]

/-- The one-step paired-add body, composed from predecessor on the left and
successor on the right. -/
theorem tm0_pairedDecrLeftIncrRightSep_beforeSepCond
    {pairSep outerSep : ChainΓ}
    (hpair_nd : pairSep ≠ default)
    (hpair_outer : pairSep ≠ outerSep)
    (hpair_bit0 : pairSep ≠ γ'ToChainΓ Γ'.bit0)
    (hpair_bit1 : pairSep ≠ γ'ToChainΓ Γ'.bit1)
    (houter_bit0 : outerSep ≠ γ'ToChainΓ Γ'.bit0)
    (houter_bit1 : outerSep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesPairedBlockBeforeSepCond pairSep outerSep
      (pairedDecrLeftIncrRightSep pairSep) (pairedAddCondSep pairSep) := by
  have hRightNormSucc :
      TM0RealizesBlockSepAnySuffix ChainΓ pairSep (binSucc ∘ normalizeBlock) := by
    exact tm0RealizesBlockSepAnySuffix_comp
      (tm0_normalizeBlockSep_anySuffix hpair_bit0 hpair_bit1)
      (tm0_binSucc_blockSepAnySuffix hpair_bit0 hpair_bit1)
      (fun block _ => normalizeBlock_ne_default block)
      (fun block _ =>
        normalizeBlock_no_of_ne_bits pairSep hpair_bit0 hpair_bit1 block)
  have hsucc :
      TM0RealizesInnerBlockSepAnySuffix ChainΓ outerSep pairSep
        (binSucc ∘ normalizeBlock) :=
    tm0RealizesBlockSepAnySuffix_toInner
      hpair_nd (Ne.symm hpair_outer)
      hRightNormSucc
      (fun block _ =>
        binSucc_ne_default (normalizeBlock block)
          (normalizeBlock_ne_default block))
      (fun block _ =>
        binSucc_no_of_ne_bits hpair_bit0 hpair_bit1
          (normalizeBlock block)
          (normalizeBlock_no_of_ne_bits pairSep hpair_bit0 hpair_bit1 block))
  obtain ⟨Λr, hΛri, hΛrf, Mr, hMr⟩ :=
    tm0_pairedDecrLeftIncrRightSep_beforeSep
      hpair_bit0 hpair_bit1 houter_bit0 houter_bit1 hsucc
  obtain ⟨Λp, hΛpi, hΛpf, Mp, q_le, q_gt, hne, hp⟩ :=
    tm0_blockValueLeq_beforeSep_decidable_2 0 pairSep
  haveI : DecidableEq Λp := Classical.decEq Λp
  let hΛrFi : Inhabited (Λr ⊕ FinalizeSt) := ⟨Sum.inl (@default _ hΛri)⟩
  let MrF : TM0.Machine ChainΓ (Λr ⊕ FinalizeSt) :=
    @TM0Seq.compose ChainΓ Λr hΛri FinalizeSt inferInstance Mr finalizeMachine
  let Mcond : TM0.Machine ChainΓ (Λp ⊕ FinalizeSt ⊕ (Λr ⊕ FinalizeSt)) :=
    @tm0CondCompose Λp FinalizeSt (Λr ⊕ FinalizeSt)
      hΛpi inferInstance hΛrFi inferInstance
      Mp finalizeMachine MrF q_le q_gt
  refine ⟨Λp ⊕ FinalizeSt ⊕ (Λr ⊕ FinalizeSt), inferInstance, inferInstance,
    Mcond, Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)), ?_⟩
  intro left right suffix hleft_nd hleft_npair hleft_nouter
    hright_nd hright_npair hright_nouter hstep_nd
  set pairBlock := left ++ pairSep :: right with hpair_def
  set whole := left ++ pairSep :: right ++ outerSep :: suffix with hwhole_def
  have hcond_bridge :
      blockValueLeqBeforeSep 0 pairSep whole ↔
        blockValueLeqBeforeSep 0 pairSep pairBlock := by
    have hsplit_whole :
        splitAtSep pairSep whole = (left, right ++ outerSep :: suffix) := by
      simpa [whole, List.append_assoc] using
        splitAtSep_general_cons pairSep left (right ++ outerSep :: suffix)
          hleft_npair
    have hsplit_pair : splitAtSep pairSep pairBlock = (left, right) := by
      simpa [pairBlock] using splitAtSep_general_cons pairSep left right hleft_npair
    unfold blockValueLeqBeforeSep
    rw [hsplit_whole, hsplit_pair]
  obtain ⟨hp_dom, hp_out⟩ :=
    hp left (right ++ outerSep :: suffix) hleft_nd hleft_npair
  have hp_dom' : (TM0Seq.evalCfg Mp whole).Dom := by
    simpa [whole, List.append_assoc] using hp_dom
  set cp := (TM0Seq.evalCfg Mp whole).get hp_dom'
  have hcp_get :
      cp =
        (TM0Seq.evalCfg Mp (left ++ pairSep :: (right ++ outerSep :: suffix))).get
          hp_dom := by
    apply Part.get_eq_get_of_eq
    simp [whole, List.append_assoc]
  have hp_out' := hp_out hp_dom
  have hcp_tape : cp.Tape = Tape.mk₁ whole := by
    rw [hcp_get, hp_out'.1]
    simp [whole, List.append_assoc]
  have hcp_mem : cp ∈ TM0Seq.evalCfg Mp whole := Part.get_mem hp_dom'
  have hcp_eval := Turing.mem_eval.mp hcp_mem
  have hcp_halt : TM0.step Mp cp = none := hcp_eval.2
  have hcp_reaches : Reaches (TM0.step Mp) (TM0.init whole) cp := hcp_eval.1
  have hphase1 := condCompose_phase1_reaches Mp finalizeMachine MrF q_le q_gt
    cp whole hcp_reaches
  change Reaches (TM0.step Mcond) (TM0.init whole)
    { q := Sum.inl cp.q, Tape := cp.Tape } at hphase1
  have heval_rewrite :
      TM0Seq.evalCfg Mcond whole =
        Turing.eval (TM0.step Mcond) ⟨Sum.inl cp.q, cp.Tape⟩ := by
    exact Turing.reaches_eval hphase1
  by_cases hcond : pairedAddCondSep pairSep pairBlock
  · have hp_false : ¬ blockValueLeqBeforeSep 0 pairSep whole := by
      intro hle
      exact hcond (hcond_bridge.mp hle)
    have hq : cp.q = q_gt := by
      have hout := hp_out'.2.2 (by simpa [whole, List.append_assoc] using hp_false)
      rw [← hcp_get] at hout
      exact hout
    have hhalt_q : TM0.step Mp ⟨q_gt, cp.Tape⟩ = none := hq ▸ hcp_halt
    have hstep_nd' :
        ∀ g ∈ pairedDecrLeftIncrRightSep pairSep pairBlock, g ≠ default :=
      hstep_nd hcond
    obtain ⟨hMr_dom, hMr_tape⟩ :=
      hMr left right suffix hleft_nd hleft_npair hleft_nouter
        hright_nd hright_npair hright_nouter
        (by simpa [pairBlock] using hstep_nd')
    have hMr_dom' : (TM0Seq.evalCfg Mr whole).Dom := by
      simpa [whole] using hMr_dom
    have hMr_tape' :
        ∀ h, ((TM0Seq.evalCfg Mr whole).get h).Tape =
          Tape.mk₁ (pairedDecrLeftIncrRightSep pairSep pairBlock ++
            outerSep :: suffix) := by
      intro h
      have hget :
          (TM0Seq.evalCfg Mr whole).get h =
            (TM0Seq.evalCfg Mr
              (left ++ pairSep :: right ++ outerSep :: suffix)).get hMr_dom := by
        apply Part.get_eq_get_of_eq
        simp [whole]
      rw [hget, hMr_tape hMr_dom]
    have hfinal := compose_finalize_evalCfg Mr whole
      (pairedDecrLeftIncrRightSep pairSep pairBlock ++ outerSep :: suffix)
      hMr_dom' (hMr_tape' hMr_dom')
    have hbranch_dom :
        (TM0Seq.evalFromCfg MrF ⟨default, cp.Tape⟩).Dom := by
      rw [hcp_tape]
      change (TM0Seq.evalFromCfg MrF (TM0.init whole)).Dom
      rw [TM0Seq.evalFromCfg_init]
      exact hfinal.1
    have hbranch_spec :
        ∀ h, (TM0Seq.evalFromCfg MrF ⟨default, cp.Tape⟩).get h =
          ⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (pairedDecrLeftIncrRightSep pairSep pairBlock ++
              outerSep :: suffix)⟩ := by
      intro h
      have heq :
          TM0Seq.evalFromCfg MrF ⟨default, cp.Tape⟩ =
            TM0Seq.evalCfg MrF whole := by
        rw [hcp_tape]
        exact TM0Seq.evalFromCfg_init (M := MrF) (l := whole)
      have hget :
          (TM0Seq.evalFromCfg MrF ⟨default, cp.Tape⟩).get h =
            (TM0Seq.evalCfg MrF whole).get hfinal.1 := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hfinal.2 hfinal.1
    have hbranch_step :
        ∃ c₂, TM0.step MrF ⟨default, cp.Tape⟩ = some c₂ := by
      rw [hcp_tape]
      change ∃ c₂, TM0.step MrF (TM0.init whole) = some c₂
      change ∃ c₂, TM0.step MrF ⟨default, Tape.mk₁ whole⟩ = some c₂
      rcases hfirst : TM0.step Mr ⟨default, Tape.mk₁ whole⟩ with _ | c₂
      · refine ⟨(⟨Sum.inr FinalizeSt.done, Tape.mk₁ whole⟩ :
            TM0.Cfg ChainΓ (Λr ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λr hΛri FinalizeSt inferInstance
          Mr finalizeMachine) ⟨Sum.inl default, Tape.mk₁ whole⟩ =
          some ⟨Sum.inr FinalizeSt.done, Tape.mk₁ whole⟩
        rw [TM0Seq.compose_step_on_halt Mr finalizeMachine default
          (Tape.mk₁ whole) hfirst]
        change Option.map
          (fun c₂ : TM0.Cfg ChainΓ FinalizeSt =>
            ({ q := Sum.inr c₂.q, Tape := c₂.Tape } :
              TM0.Cfg ChainΓ (Λr ⊕ FinalizeSt)))
          (TM0.step finalizeMachine ⟨FinalizeSt.start, Tape.mk₁ whole⟩) =
          some ⟨Sum.inr FinalizeSt.done, Tape.mk₁ whole⟩
        rw [finalize_step_start]
        rfl
      · refine ⟨(⟨Sum.inl c₂.q, c₂.Tape⟩ :
            TM0.Cfg ChainΓ (Λr ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λr hΛri FinalizeSt inferInstance
          Mr finalizeMachine) ⟨Sum.inl default, Tape.mk₁ whole⟩ =
          some ⟨Sum.inl c₂.q, c₂.Tape⟩
        simpa using TM0Seq.compose_step_inl Mr finalizeMachine
          (⟨default, Tape.mk₁ whole⟩ : TM0.Cfg ChainΓ Λr) c₂ hfirst
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MrF q_le q_gt))
        ⟨Sum.inl q_gt, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_false Mp finalizeMachine MrF q_le q_gt hne
        cp.Tape hhalt_q).mpr hbranch_dom
    have hdom : (TM0Seq.evalCfg Mcond whole).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_false_of_step_local
      Mp finalizeMachine MrF q_le q_gt hne (Sum.inr FinalizeSt.done) cp.Tape
      (Tape.mk₁ (pairedDecrLeftIncrRightSep pairSep pairBlock ++
        outerSep :: suffix))
      hhalt_q hbranch_step hbranch_dom hbranch_spec
    have hcfg' : (TM0Seq.evalCfg Mcond whole).get h =
        ⟨Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)),
          Tape.mk₁ (pairedDecrLeftIncrRightSep pairSep pairBlock ++
            outerSep :: suffix)⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond whole =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond whole).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    simp [hcond]
    constructor
    · simpa [hwhole_def] using congrArg TM0.Cfg.q hcfg'
    · simpa [hwhole_def, hpair_def] using congrArg TM0.Cfg.Tape hcfg'
  · have hp_true : blockValueLeqBeforeSep 0 pairSep whole := by
      exact hcond_bridge.mpr (by simpa [pairedAddCondSep] using hcond)
    have hq : cp.q = q_le := by
      have hout := hp_out'.2.1 (by simpa [whole, List.append_assoc] using hp_true)
      rw [← hcp_get] at hout
      exact hout
    have hhalt_q : TM0.step Mp ⟨q_le, cp.Tape⟩ = none := hq ▸ hcp_halt
    obtain ⟨hid_dom, hid_spec⟩ := finalize_evalFromCfg cp.Tape
    have hid_step : ∃ c₂, TM0.step finalizeMachine ⟨default, cp.Tape⟩ = some c₂ := by
      exact ⟨⟨FinalizeSt.done, cp.Tape⟩, finalize_step_start cp.Tape⟩
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MrF q_le q_gt))
        ⟨Sum.inl q_le, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_true Mp finalizeMachine MrF q_le q_gt
        cp.Tape hhalt_q).mpr hid_dom
    have hdom : (TM0Seq.evalCfg Mcond whole).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_true_of_step_local
      Mp finalizeMachine MrF q_le q_gt FinalizeSt.done cp.Tape cp.Tape
      hhalt_q hid_step hid_dom (fun h => hid_spec h)
    have hcfg' : (TM0Seq.evalCfg Mcond whole).get h =
        ⟨Sum.inr (Sum.inl FinalizeSt.done), cp.Tape⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond whole =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond whole).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    have hq_ne :
        Sum.inr (Sum.inl FinalizeSt.done) ≠
          (Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)) :
            Λp ⊕ FinalizeSt ⊕ (Λr ⊕ FinalizeSt)) := by
      simp
    simp [hcond]
    constructor
    · have hq_out : ((TM0Seq.evalCfg Mcond whole).get h).q ≠
          (Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)) :
            Λp ⊕ FinalizeSt ⊕ (Λr ⊕ FinalizeSt)) := by
        rw [hcfg']
        exact hq_ne
      simpa [hwhole_def] using hq_out
    · have htape_out : ((TM0Seq.evalCfg Mcond whole).get h).Tape =
          Tape.mk₁ whole := by
        rw [hcfg', hcp_tape]
      simpa [hwhole_def] using htape_out

/-- Separator-parametric while combinator for paired blocks before an explicit
outer separator. -/
theorem tm0RealizesPairedBlockBeforeSep_while_pairedSepInvSep
    {pairSep outerSep : ChainΓ}
    (hpair_nd : pairSep ≠ default)
    (hpair_outer : pairSep ≠ outerSep)
    (step result : List ChainΓ → List ChainΓ)
    (cond : List ChainΓ → Prop) [DecidablePred cond]
    (hbody : TM0RealizesPairedBlockBeforeSepCond pairSep outerSep step cond)
    (hinv_step : ∀ block, pairedSepInvSep pairSep block →
      (∀ g ∈ block, g ≠ default) → cond block →
      pairedSepInvSep pairSep (step block))
    (hstep_nd : ∀ block, (∀ g ∈ block, g ≠ default) → cond block →
      ∀ g ∈ step block, g ≠ default)
    (hstep_nouter : ∀ block, (∀ g ∈ block, g ≠ outerSep) → cond block →
      ∀ g ∈ step block, g ≠ outerSep)
    (hresult_eq : ∀ block, (∀ g ∈ block, g ≠ default) →
      pairedSepInvSep pairSep block →
      ∃ n, result block = blockIterateWhile step cond n block ∧
        ¬cond (blockIterateWhile step cond n block)) :
    TM0RealizesPairedBlockBeforeSepAnySuffix pairSep outerSep result := by
  obtain ⟨Λ, hΛi, hΛf, M, q_cont, hM⟩ := hbody
  haveI : DecidableEq Λ := Classical.decEq Λ
  refine ⟨Λ, hΛi, hΛf, tm0WhileLoop M q_cont, ?_⟩
  intro left right suffix hleft_nd hleft_npair hleft_nouter
    hright_nd hright_npair hright_nouter hresult
  set block := left ++ [pairSep] ++ right with hblock_def
  have hblock_nd : ∀ g ∈ block, g ≠ default := by
    intro g hg
    simp [block, List.mem_append] at hg
    rcases hg with hg | rfl | hg
    · exact hleft_nd g hg
    · exact hpair_nd
    · exact hright_nd g hg
  have hblock_nouter : ∀ g ∈ block, g ≠ outerSep := by
    intro g hg
    simp [block, List.mem_append] at hg
    rcases hg with hg | rfl | hg
    · exact hleft_nouter g hg
    · exact hpair_outer
    · exact hright_nouter g hg
  have hblockInv : pairedSepInvSep pairSep block := by
    constructor
    · simp [block]
    · rw [show splitAtSep pairSep block = (left, right) by
        simpa [block] using splitAtSep_general pairSep left right hleft_npair]
      exact hright_npair
  obtain ⟨n, hn_eq, hn_not_cond⟩ := hresult_eq block hblock_nd hblockInv
  suffices key : ∀ (m : ℕ) (blk : List ChainΓ),
      pairedSepInvSep pairSep blk →
      (∀ g ∈ blk, g ≠ default) →
      (∀ g ∈ blk, g ≠ outerSep) →
      ¬cond (blockIterateWhile step cond m blk) →
      (TM0Seq.evalCfg (tm0WhileLoop M q_cont)
        (blk ++ outerSep :: suffix)).Dom ∧
      ∀ (hd : (TM0Seq.evalCfg (tm0WhileLoop M q_cont)
        (blk ++ outerSep :: suffix)).Dom),
        ((TM0Seq.evalCfg (tm0WhileLoop M q_cont)
          (blk ++ outerSep :: suffix)).get hd).Tape =
          Tape.mk₁ (blockIterateWhile step cond m blk ++
            outerSep :: suffix) by
    obtain ⟨h_dom, h_tape⟩ :=
      key n block hblockInv hblock_nd hblock_nouter hn_not_cond
    have hinput : block ++ outerSep :: suffix =
        left ++ pairSep :: right ++ outerSep :: suffix := by
      simp [block, List.append_assoc]
    refine ⟨by simpa [hinput] using h_dom, ?_⟩
    intro hd
    have hget :
        (TM0Seq.evalCfg (tm0WhileLoop M q_cont)
          (left ++ pairSep :: right ++ outerSep :: suffix)).get hd =
        (TM0Seq.evalCfg (tm0WhileLoop M q_cont)
          (block ++ outerSep :: suffix)).get h_dom := by
      apply Part.get_eq_get_of_eq
      simp [hinput]
    rw [hget, h_tape h_dom, ← hn_eq]
    simp [block]
  intro m
  induction m with
  | zero =>
      intro blk hInv hblk_nd hblk_nouter hn_not
      simp only [blockIterateWhile] at hn_not ⊢
      rcases hsplit : splitAtSep pairSep blk with ⟨l, r⟩
      have hblk_recon : blk = l ++ pairSep :: r := by
        simpa [hsplit] using splitAtSep_reconstruct_of_mem pairSep blk hInv.1
      have hl_nd : ∀ g ∈ l, g ≠ default := by
        intro g hg
        exact hblk_nd g
          (splitAtSep_fst_subset pairSep blk g (by simpa [hsplit] using hg))
      have hr_nd : ∀ g ∈ r, g ≠ default := by
        intro g hg
        exact hblk_nd g
          (splitAtSep_snd_subset pairSep blk g (by simpa [hsplit] using hg))
      have hl_npair : ∀ g ∈ l, g ≠ pairSep := by
        simpa [hsplit] using splitAtSep_fst_no_sep pairSep blk
      have hr_npair : ∀ g ∈ r, g ≠ pairSep := by
        simpa [pairedSepInvSep, hsplit] using hInv.2
      have hl_nouter : ∀ g ∈ l, g ≠ outerSep := by
        intro g hg
        exact hblk_nouter g
          (splitAtSep_fst_subset pairSep blk g (by simpa [hsplit] using hg))
      have hr_nouter : ∀ g ∈ r, g ≠ outerSep := by
        intro g hg
        exact hblk_nouter g
          (splitAtSep_snd_subset pairSep blk g (by simpa [hsplit] using hg))
      obtain ⟨h_body_dom, h_body_spec⟩ := hM l r suffix
        hl_nd hl_npair hl_nouter hr_nd hr_npair hr_nouter
        (fun hc => by
          simpa [hblk_recon] using hstep_nd blk hblk_nd
            (by simpa [hblk_recon] using hc))
      have h_body_dom' :
          (TM0Seq.evalCfg M (blk ++ outerSep :: suffix)).Dom := by
        simpa [hblk_recon, List.append_assoc] using h_body_dom
      have h_body_spec' := h_body_spec h_body_dom
      have hcond_lr : ¬ cond (l ++ pairSep :: r) := by
        simpa [hblk_recon] using hn_not
      by_cases hc_lr : cond (l ++ pairSep :: r)
      · exact False.elim (hcond_lr hc_lr)
      ·
        simp [hc_lr] at h_body_spec'
        obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
        have hget_body :
            (TM0Seq.evalCfg M (blk ++ outerSep :: suffix)).get h_body_dom' =
            (TM0Seq.evalCfg M
              (l ++ pairSep :: r ++ outerSep :: suffix)).get h_body_dom := by
          apply Part.get_eq_get_of_eq
          simp [hblk_recon, List.append_assoc]
        have h_q_ne' :
            ((TM0Seq.evalCfg M (blk ++ outerSep :: suffix)).get
              h_body_dom').q ≠ q_cont := by
          rw [hget_body]
          simpa [List.append_assoc] using h_q_ne
        obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _
          h_body_dom' h_q_ne'
        exact ⟨h_dom, fun hd => by
          rw [h_tape hd]
          simpa [hblk_recon, List.append_assoc] using h_tape_eq⟩
  | succ m ih =>
      intro blk hInv hblk_nd hblk_nouter hn_not
      by_cases hcond : cond blk
      · rw [blockIterateWhile_succ_true _ _ _ _ hcond] at hn_not ⊢
        have h_step_nd := hstep_nd blk hblk_nd hcond
        have h_step_nouter := hstep_nouter blk hblk_nouter hcond
        have h_step_inv := hinv_step blk hInv hblk_nd hcond
        rcases hsplit : splitAtSep pairSep blk with ⟨l, r⟩
        have hblk_recon : blk = l ++ pairSep :: r := by
          simpa [hsplit] using splitAtSep_reconstruct_of_mem pairSep blk hInv.1
        have hl_nd : ∀ g ∈ l, g ≠ default := by
          intro g hg
          exact hblk_nd g
            (splitAtSep_fst_subset pairSep blk g (by simpa [hsplit] using hg))
        have hr_nd : ∀ g ∈ r, g ≠ default := by
          intro g hg
          exact hblk_nd g
            (splitAtSep_snd_subset pairSep blk g (by simpa [hsplit] using hg))
        have hl_npair : ∀ g ∈ l, g ≠ pairSep := by
          simpa [hsplit] using splitAtSep_fst_no_sep pairSep blk
        have hr_npair : ∀ g ∈ r, g ≠ pairSep := by
          simpa [pairedSepInvSep, hsplit] using hInv.2
        have hl_nouter : ∀ g ∈ l, g ≠ outerSep := by
          intro g hg
          exact hblk_nouter g
            (splitAtSep_fst_subset pairSep blk g (by simpa [hsplit] using hg))
        have hr_nouter : ∀ g ∈ r, g ≠ outerSep := by
          intro g hg
          exact hblk_nouter g
            (splitAtSep_snd_subset pairSep blk g (by simpa [hsplit] using hg))
        obtain ⟨h_body_dom, h_body_spec⟩ := hM l r suffix
          hl_nd hl_npair hl_nouter hr_nd hr_npair hr_nouter
          (fun _ => by simpa [hblk_recon] using h_step_nd)
        have h_body_dom' :
            (TM0Seq.evalCfg M (blk ++ outerSep :: suffix)).Dom := by
          simpa [hblk_recon, List.append_assoc] using h_body_dom
        have h_body_spec' := h_body_spec h_body_dom
        have hcond_lr : cond (l ++ pairSep :: r) := by
          simpa [hblk_recon] using hcond
        by_cases hc_lr : cond (l ++ pairSep :: r)
        ·
          simp [hc_lr] at h_body_spec'
          obtain ⟨h_q_cont, h_tape_step⟩ := h_body_spec'
          have hget_body :
              (TM0Seq.evalCfg M (blk ++ outerSep :: suffix)).get h_body_dom' =
              (TM0Seq.evalCfg M
                (l ++ pairSep :: r ++ outerSep :: suffix)).get h_body_dom := by
            apply Part.get_eq_get_of_eq
            simp [hblk_recon, List.append_assoc]
          have h_q_cont' :
              ((TM0Seq.evalCfg M (blk ++ outerSep :: suffix)).get
                h_body_dom').q = q_cont := by
            rw [hget_body]
            simpa [List.append_assoc] using h_q_cont
          obtain ⟨h_W_step_dom, h_W_step_tape⟩ :=
            ih (step blk) h_step_inv h_step_nd h_step_nouter hn_not
          obtain ⟨h_W_dom, h_W_tape⟩ := whileLoop_eval_cont M q_cont _ _
            h_body_dom' h_q_cont'
            (by simpa [hblk_recon, List.append_assoc] using h_tape_step)
            h_W_step_dom
          exact ⟨h_W_dom, fun hd => by
            rw [h_W_tape hd, h_W_step_tape h_W_step_dom]⟩
        · exact False.elim (hc_lr hcond_lr)
      · rw [blockIterateWhile_succ_false _ _ _ _ hcond] at hn_not ⊢
        rcases hsplit : splitAtSep pairSep blk with ⟨l, r⟩
        have hblk_recon : blk = l ++ pairSep :: r := by
          simpa [hsplit] using splitAtSep_reconstruct_of_mem pairSep blk hInv.1
        have hl_nd : ∀ g ∈ l, g ≠ default := by
          intro g hg
          exact hblk_nd g
            (splitAtSep_fst_subset pairSep blk g (by simpa [hsplit] using hg))
        have hr_nd : ∀ g ∈ r, g ≠ default := by
          intro g hg
          exact hblk_nd g
            (splitAtSep_snd_subset pairSep blk g (by simpa [hsplit] using hg))
        have hl_npair : ∀ g ∈ l, g ≠ pairSep := by
          simpa [hsplit] using splitAtSep_fst_no_sep pairSep blk
        have hr_npair : ∀ g ∈ r, g ≠ pairSep := by
          simpa [pairedSepInvSep, hsplit] using hInv.2
        have hl_nouter : ∀ g ∈ l, g ≠ outerSep := by
          intro g hg
          exact hblk_nouter g
            (splitAtSep_fst_subset pairSep blk g (by simpa [hsplit] using hg))
        have hr_nouter : ∀ g ∈ r, g ≠ outerSep := by
          intro g hg
          exact hblk_nouter g
            (splitAtSep_snd_subset pairSep blk g (by simpa [hsplit] using hg))
        obtain ⟨h_body_dom, h_body_spec⟩ := hM l r suffix
          hl_nd hl_npair hl_nouter hr_nd hr_npair hr_nouter
          (fun hc => False.elim (hcond (by simpa [hblk_recon] using hc)))
        have h_body_dom' :
            (TM0Seq.evalCfg M (blk ++ outerSep :: suffix)).Dom := by
          simpa [hblk_recon, List.append_assoc] using h_body_dom
        have h_body_spec' := h_body_spec h_body_dom
        have hcond_lr : ¬ cond (l ++ pairSep :: r) := by
          simpa [hblk_recon] using hcond
        by_cases hc_lr : cond (l ++ pairSep :: r)
        · exact False.elim (hcond_lr hc_lr)
        ·
          simp [hc_lr] at h_body_spec'
          obtain ⟨h_q_ne, h_tape_eq⟩ := h_body_spec'
          have hget_body :
              (TM0Seq.evalCfg M (blk ++ outerSep :: suffix)).get h_body_dom' =
              (TM0Seq.evalCfg M
                (l ++ pairSep :: r ++ outerSep :: suffix)).get h_body_dom := by
            apply Part.get_eq_get_of_eq
            simp [hblk_recon, List.append_assoc]
          have h_q_ne' :
              ((TM0Seq.evalCfg M (blk ++ outerSep :: suffix)).get
                h_body_dom').q ≠ q_cont := by
            rw [hget_body]
            simpa [List.append_assoc] using h_q_ne
          obtain ⟨h_dom, h_tape⟩ := whileLoop_eval_not_cont M q_cont _
            h_body_dom' h_q_ne'
          exact ⟨h_dom, fun hd => by
            rw [h_tape hd]
            simpa [hblk_recon, List.append_assoc] using h_tape_eq⟩

/-- `decodeBinaryBlock` on a paired block equals decoding the prefix before
the first non-binary separator. -/
theorem decodeBinaryBlock_eq_splitLeftSep
    (sep : ChainΓ)
    (hsep_bit0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep_bit1 : sep ≠ γ'ToChainΓ Γ'.bit1)
    (block : List ChainΓ) :
    decodeBinaryBlock block = decodeBinaryBlock (splitAtSep sep block).1 := by
  induction block with
  | nil => rfl
  | cons c rest ih =>
      by_cases hc : c = sep
      · subst c
        simp [splitAtSep, decodeBinaryBlock, hsep_bit0, hsep_bit1]
      · by_cases hc0 : c = γ'ToChainΓ Γ'.bit0
        · have hbit0_ne_sep : γ'ToChainΓ Γ'.bit0 ≠ sep := by
            intro h
            exact hsep_bit0 h.symm
          simp [splitAtSep, decodeBinaryBlock, hc, hc0, hbit0_ne_sep, ih]
        · by_cases hc1 : c = γ'ToChainΓ Γ'.bit1
          · have hbit1_ne_sep : γ'ToChainΓ Γ'.bit1 ≠ sep := by
              intro h
              exact hsep_bit1 h.symm
            simp [splitAtSep, decodeBinaryBlock, hc, hc0, hc1, hbit1_ne_sep, ih]
          · simp [splitAtSep, decodeBinaryBlock, hc, hc0, hc1]

theorem decodeBinaryBlock_binSucc_normalizeBlock (block : List ChainΓ) :
    decodeBinaryBlock (binSucc (normalizeBlock block)) =
      decodeBinaryBlock block + 1 := by
  unfold normalizeBlock
  rw [binSucc_correct, decodeBinaryBlock_chainBinaryRepr]

/-- After `k` transfer steps, the decoded left value has been decremented by
`k` and the decoded right value incremented by `k`. -/
theorem pairedDecrLeftIncrRightSep_iterate_decode
    (pairSep : ChainΓ)
    (hpair_bit0 : pairSep ≠ γ'ToChainΓ Γ'.bit0)
    (hpair_bit1 : pairSep ≠ γ'ToChainΓ Γ'.bit1)
    (block : List ChainΓ) (k : ℕ)
    (hInv : pairedSepInvSep pairSep block)
    (hk : k ≤ decodeBinaryBlock (splitAtSep pairSep block).1) :
    let result := (pairedDecrLeftIncrRightSep pairSep)^[k] block
    decodeBinaryBlock (splitAtSep pairSep result).1 =
      decodeBinaryBlock (splitAtSep pairSep block).1 - k ∧
    decodeBinaryBlock (splitAtSep pairSep result).2 =
      decodeBinaryBlock (splitAtSep pairSep block).2 + k := by
  induction k generalizing block with
  | zero =>
      norm_num
  | succ k ih =>
      convert ih (pairedDecrLeftIncrRightSep pairSep block)
        (pairedDecrLeftIncrRightSep_pairedSepInvSep
          pairSep block
          (fun left => by
            unfold binPred
            exact chainBinaryRepr_no_of_ne_bits pairSep hpair_bit0 hpair_bit1
              (decodeBinaryBlock left - 1))
          (fun right _hright_npair =>
            binSucc_no_of_ne_bits hpair_bit0 hpair_bit1
              (normalizeBlock right)
              (normalizeBlock_no_of_ne_bits pairSep hpair_bit0 hpair_bit1 right))
          hInv)
        (by
          simp [pairedDecrLeftIncrRightSep, hInv]
          rcases hsplit : splitAtSep pairSep block with ⟨left, right⟩
          have hpred_npair : ∀ g ∈ binPred left, g ≠ pairSep := by
            unfold binPred
            exact chainBinaryRepr_no_of_ne_bits pairSep hpair_bit0 hpair_bit1
              (decodeBinaryBlock left - 1)
          rw [show splitAtSep pairSep
                (binPred left ++ pairSep :: binSucc (normalizeBlock right)) =
                (binPred left, binSucc (normalizeBlock right)) by
              exact splitAtSep_general_cons pairSep (binPred left)
                (binSucc (normalizeBlock right)) hpred_npair]
          simp [decodeBinaryBlock_binPred]
          simpa [hsplit] using Nat.le_sub_one_of_lt hk) using 1
      · simp [pairedDecrLeftIncrRightSep, hInv]
        rcases hsplit : splitAtSep pairSep block with ⟨left, right⟩
        have hpred_npair : ∀ g ∈ binPred left, g ≠ pairSep := by
          unfold binPred
          exact chainBinaryRepr_no_of_ne_bits pairSep hpair_bit0 hpair_bit1
            (decodeBinaryBlock left - 1)
        rw [show splitAtSep pairSep
              (binPred left ++ pairSep :: binSucc (normalizeBlock right)) =
              (binPred left, binSucc (normalizeBlock right)) by
            exact splitAtSep_general_cons pairSep (binPred left)
              (binSucc (normalizeBlock right)) hpred_npair]
        simp [decodeBinaryBlock_binPred, decodeBinaryBlock_binSucc_normalizeBlock]
        omega

theorem binAddPairedWhileSep_eq_iterate
    (pairSep : ChainΓ) (block : List ChainΓ)
    (hpair_bit0 : pairSep ≠ γ'ToChainΓ Γ'.bit0)
    (hpair_bit1 : pairSep ≠ γ'ToChainΓ Γ'.bit1)
    (_hblock : ∀ g ∈ block, g ≠ default)
    (hInv : pairedSepInvSep pairSep block) :
    ∃ n, binAddPairedWhileSep pairSep block =
        blockIterateWhile (pairedDecrLeftIncrRightSep pairSep)
          (pairedAddCondSep pairSep) n block ∧
      ¬ pairedAddCondSep pairSep
        (blockIterateWhile (pairedDecrLeftIncrRightSep pairSep)
          (pairedAddCondSep pairSep) n block) := by
  unfold binAddPairedWhileSep pairedAddCondSep blockValueLeqBeforeSep
  refine ⟨decodeBinaryBlock (splitAtSep pairSep block).1, rfl, ?_⟩
  rw [blockIterateWhile_eq_iterate_of_cond]
  · have hdec := (pairedDecrLeftIncrRightSep_iterate_decode
      pairSep hpair_bit0 hpair_bit1 block
      (decodeBinaryBlock (splitAtSep pairSep block).1) hInv le_rfl).1
    simp [hdec]
  · intro k hk
    have hdec := (pairedDecrLeftIncrRightSep_iterate_decode
      pairSep hpair_bit0 hpair_bit1 block k hInv (by omega)).1
    simp [hdec]
    omega

theorem pairedDecrLeftIncrRightSep_iterate_pairedSepInvSep
    (pairSep : ChainΓ)
    (hpair_bit0 : pairSep ≠ γ'ToChainΓ Γ'.bit0)
    (hpair_bit1 : pairSep ≠ γ'ToChainΓ Γ'.bit1)
    (block : List ChainΓ) (n : ℕ)
    (hInv : pairedSepInvSep pairSep block) :
    pairedSepInvSep pairSep
      ((pairedDecrLeftIncrRightSep pairSep)^[n] block) := by
  induction n with
  | zero =>
      simpa
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact pairedDecrLeftIncrRightSep_pairedSepInvSep
        pairSep _ 
        (fun left => by
          unfold binPred
          exact chainBinaryRepr_no_of_ne_bits pairSep hpair_bit0 hpair_bit1
            (decodeBinaryBlock left - 1))
        (fun right _hright_npair =>
          binSucc_no_of_ne_bits hpair_bit0 hpair_bit1
            (normalizeBlock right)
            (normalizeBlock_no_of_ne_bits pairSep hpair_bit0 hpair_bit1 right))
        ih

theorem binAddPairedWhileSep_ne_default
    (pairSep : ChainΓ) (hpair_nd : pairSep ≠ default)
    (block : List ChainΓ) (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ binAddPairedWhileSep pairSep block, g ≠ default := by
  have h_ind :
      ∀ (n : ℕ) (block : List ChainΓ), (∀ g ∈ block, g ≠ default) →
        ∀ g ∈ blockIterateWhile (pairedDecrLeftIncrRightSep pairSep)
          (pairedAddCondSep pairSep) n block, g ≠ default := by
    intro n
    induction n with
    | zero =>
        intro block hblock
        simpa [blockIterateWhile] using hblock
    | succ n ih =>
        intro block hblock
        by_cases hcond : pairedAddCondSep pairSep block
        · simp [blockIterateWhile, hcond]
          exact ih _ (pairedDecrLeftIncrRightSep_ne_default
            pairSep hpair_nd block hblock hcond)
        · simpa [blockIterateWhile, hcond] using hblock
  unfold binAddPairedWhileSep
  exact h_ind (decodeBinaryBlock (splitAtSep pairSep block).1) block hblock

theorem extractPairedRightSep_ne_default
    (pairSep : ChainΓ) (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ dropUntilFirstSep pairSep block, g ≠ default :=
  dropUntilFirstSep_ne_default pairSep block hblock

theorem dropUntilFirstSep_eq_splitAtSep_snd_of_mem
    {Γ : Type} [DecidableEq Γ] (sep : Γ) (block : List Γ)
    (hmem : sep ∈ block) :
    dropUntilFirstSep sep block = (splitAtSep sep block).2 := by
  conv_lhs =>
    rw [splitAtSep_reconstruct_of_mem sep block hmem]
  exact dropUntilFirstSep_append_cons sep
    (splitAtSep sep block).1 (splitAtSep sep block).2
    (splitAtSep_fst_no_sep sep block)

theorem binAddPairedSep_eq_while_decomp
    (pairSep : ChainΓ) (block : List ChainΓ)
    (hpair_bit0 : pairSep ≠ γ'ToChainΓ Γ'.bit0)
    (hpair_bit1 : pairSep ≠ γ'ToChainΓ Γ'.bit1)
    (hInv : pairedSepInvSep pairSep block) :
    binAddPairedSep pairSep block =
      (normalizeBlock ∘ dropUntilFirstSep pairSep ∘
        binAddPairedWhileSep pairSep) block := by
  rcases hsplit : splitAtSep pairSep block with ⟨left, right⟩
  unfold binAddPairedSep binAddPairedWhileSep normalizeBlock Function.comp
  simp [hsplit]
  have h_iter :
      blockIterateWhile (pairedDecrLeftIncrRightSep pairSep)
        (pairedAddCondSep pairSep)
        (decodeBinaryBlock left) block =
      (pairedDecrLeftIncrRightSep pairSep)^[
        decodeBinaryBlock left] block := by
    apply blockIterateWhile_eq_iterate_of_cond
    intro k hk
    unfold pairedAddCondSep blockValueLeqBeforeSep
    have hdec := (pairedDecrLeftIncrRightSep_iterate_decode
      pairSep hpair_bit0 hpair_bit1 block k hInv (by
        simpa [hsplit] using Nat.le_of_lt hk)).1
    simp [hdec, hsplit]
    omega
  rw [h_iter]
  have hInv_iter :=
    pairedDecrLeftIncrRightSep_iterate_pairedSepInvSep
      pairSep hpair_bit0 hpair_bit1 block
      (decodeBinaryBlock left) hInv
  rw [dropUntilFirstSep_eq_splitAtSep_snd_of_mem pairSep _ hInv_iter.1]
  have hright := (pairedDecrLeftIncrRightSep_iterate_decode
    pairSep hpair_bit0 hpair_bit1 block
    (decodeBinaryBlock left) hInv (by simp [hsplit])).2
  rw [hright]
  simp [hsplit, Nat.add_comm]

theorem binAddPairedWhileSep_ne_marker
    (pairSep marker : ChainΓ)
    (hpair_marker : pairSep ≠ marker)
    (hmarker_bit0 : marker ≠ γ'ToChainΓ Γ'.bit0)
    (hmarker_bit1 : marker ≠ γ'ToChainΓ Γ'.bit1)
    (block : List ChainΓ) (hblock : ∀ g ∈ block, g ≠ marker) :
    ∀ g ∈ binAddPairedWhileSep pairSep block, g ≠ marker := by
  have h_ind :
      ∀ (n : ℕ) (block : List ChainΓ), (∀ g ∈ block, g ≠ marker) →
        ∀ g ∈ blockIterateWhile (pairedDecrLeftIncrRightSep pairSep)
          (pairedAddCondSep pairSep) n block, g ≠ marker := by
    intro n
    induction n with
    | zero =>
        intro block hblock
        simpa [blockIterateWhile] using hblock
    | succ n ih =>
        intro block hblock
        by_cases hcond : pairedAddCondSep pairSep block
        · simp [blockIterateWhile, hcond]
          exact ih _ (pairedDecrLeftIncrRightSep_ne_marker
            pairSep marker hpair_marker hmarker_bit0 hmarker_bit1
            block hblock hcond)
        · simpa [blockIterateWhile, hcond] using hblock
  unfold binAddPairedWhileSep
  exact h_ind (decodeBinaryBlock (splitAtSep pairSep block).1) block hblock

theorem tm0_normalizeBlockSepAnySuffix {sep : ChainΓ}
    (hsep0 : sep ≠ γ'ToChainΓ Γ'.bit0)
    (hsep1 : sep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesBlockSepAnySuffix ChainΓ sep normalizeBlock :=
  tm0_normalizeBlockSep_anySuffix hsep0 hsep1

theorem tm0RealizesPairedBlockBeforeSep_comp_blockSepAnySuffix
    {pairSep outerSep : ChainΓ} {f g : List ChainΓ → List ChainΓ}
    (hpair_nd : pairSep ≠ default)
    (hpair_outer : pairSep ≠ outerSep)
    (hf : TM0RealizesPairedBlockBeforeSepAnySuffix pairSep outerSep f)
    (hg : TM0RealizesBlockSepAnySuffix ChainΓ outerSep g)
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default)
    (hf_nouter : ∀ block, (∀ x ∈ block, x ≠ outerSep) →
      ∀ x ∈ f block, x ≠ outerSep)
    (hgf_nouter : ∀ block, (∀ x ∈ block, x ≠ outerSep) →
      ∀ x ∈ g (f block), x ≠ outerSep) :
    TM0RealizesPairedBlockBeforeSepAnySuffix pairSep outerSep (g ∘ f) := by
  obtain ⟨Λf, hΛfi, hΛff, Mf, hMf⟩ := hf
  obtain ⟨Λg, hΛgi, hΛgf, Mg, hMg⟩ := hg
  let hsum : Inhabited (Λf ⊕ Λg) := ⟨Sum.inl (@default _ hΛfi)⟩
  let Mcomp : TM0.Machine ChainΓ (Λf ⊕ Λg) :=
    @TM0Seq.compose ChainΓ Λf hΛfi Λg hΛgi Mf Mg
  refine ⟨Λf ⊕ Λg, hsum, inferInstance, Mcomp, ?_⟩
  intro left right suffix
    hleft_nd hleft_npair hleft_nouter
    hright_nd hright_npair hright_nouter hgf_nd
  set block := left ++ pairSep :: right with hblock_def
  have hblock_nd : ∀ x ∈ block, x ≠ default := by
    intro x hx
    simp [block, List.mem_append] at hx
    rcases hx with hx | rfl | hx
    · exact hleft_nd x hx
    · exact hpair_nd
    · exact hright_nd x hx
  have hblock_nouter : ∀ x ∈ block, x ≠ outerSep := by
    intro x hx
    simp [block, List.mem_append] at hx
    rcases hx with hx | rfl | hx
    · exact hleft_nouter x hx
    · exact hpair_outer
    · exact hright_nouter x hx
  have hfblock_nd := hf_nd block hblock_nd
  have hfblock_nouter := hf_nouter block hblock_nouter
  obtain ⟨hf_dom, hf_tape⟩ :=
    hMf left right suffix
      hleft_nd hleft_npair hleft_nouter
      hright_nd hright_npair hright_nouter hfblock_nd
  obtain ⟨hg_dom, hg_tape⟩ :=
    hMg (f block) suffix hfblock_nd hfblock_nouter hgf_nd
      (hgf_nouter block hblock_nouter)
  have hg_from_cfg :
      (TM0Seq.evalFromCfg Mg
        ⟨default, ((TM0Seq.evalCfg Mf
          (left ++ pairSep :: right ++ outerSep :: suffix)).get
          hf_dom).Tape⟩).Dom := by
    rw [hf_tape hf_dom]
    change (TM0Seq.evalFromCfg Mg
      (TM0.init (f block ++ outerSep :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    simpa [block, List.append_assoc] using hg_dom
  have hcomp_dom :
      (TM0Seq.evalCfg Mcomp
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff Mcomp
      (left ++ pairSep :: right ++ outerSep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts Mf Mg
        (left ++ pairSep :: right ++ outerSep :: suffix)
        hf_dom hg_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have ht := TM0Seq.compose_evalCfg_tape Mf Mg
    (left ++ pairSep :: right ++ outerSep :: suffix)
    (f block ++ outerSep :: suffix)
    hf_dom (hf_tape hf_dom) hg_dom h
  rw [ht, hg_tape hg_dom]
  simp [block]

theorem tm0RealizesPairedBlockBeforeSep_congr
    {pairSep outerSep : ChainΓ} {f g : List ChainΓ → List ChainΓ}
    (hf : TM0RealizesPairedBlockBeforeSepAnySuffix pairSep outerSep f)
    (hfg : ∀ left right, (∀ x ∈ left, x ≠ pairSep) →
      (∀ x ∈ right, x ≠ pairSep) →
      f (left ++ pairSep :: right) = g (left ++ pairSep :: right)) :
    TM0RealizesPairedBlockBeforeSepAnySuffix pairSep outerSep g := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro left right suffix
    hleft_nd hleft_npair hleft_nouter
      hright_nd hright_npair hright_nouter hg_nd
  have hfg_lr := hfg left right hleft_npair hright_npair
  have hf_nd : ∀ x ∈ f (left ++ pairSep :: right), x ≠ default := by
    simpa [hfg_lr] using hg_nd
  obtain ⟨hdom, htape⟩ :=
    hM left right suffix
      hleft_nd hleft_npair hleft_nouter
      hright_nd hright_npair hright_nouter hf_nd
  refine ⟨hdom, ?_⟩
  intro h
  rw [htape h, hfg_lr]

/-- Apply `dropUntilFirstSep sep` to the inner block between two separators,
then replace the left boundary separator by `sep`.

The transformation is
`pfx ++ boundarySep :: inner ++ outerSep :: suffix`
to
`pfx ++ sep :: dropUntilFirstSep sep inner ++ outerSep :: suffix`.
All separators are explicit; callers supply the freshness facts needed by the
inner-block lift and the final boundary replacement. -/
theorem tm0_dropUntilFirstSep_inner_replaceBoundary
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep boundarySep outerSep : Γ}
    (hsep_nd : sep ≠ default)
    (hboundary_nd : boundarySep ≠ default)
    (hboundary_outer : boundarySep ≠ outerSep) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine Γ Λ),
      ∀ (pfx inner suffix : List Γ),
        (∀ g ∈ pfx, g ≠ default) →
        (∀ g ∈ pfx, g ≠ outerSep) →
        (∀ g ∈ pfx, g ≠ boundarySep) →
        (∀ g ∈ inner, g ≠ default) →
        (∀ g ∈ inner, g ≠ outerSep) →
        (∀ g ∈ inner, g ≠ boundarySep) →
        (∀ g ∈ suffix, g ≠ default) →
        (TM0Seq.evalCfg M
          (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M
          (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).Dom),
          ((TM0Seq.evalCfg M
            (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).get h).Tape =
            Tape.mk₁ (pfx ++ sep :: dropUntilFirstSep sep inner ++
              outerSep :: suffix) := by
  have hdropAny :
      TM0RealizesBlockSepAnySuffix Γ boundarySep (dropUntilFirstSep sep) :=
    tm0_dropUntilFirstSep_blockSepAnySuffix
      (sep := sep) (outerSep := boundarySep) hsep_nd
  have hinner : TM0RealizesInnerBlockSep Γ outerSep boundarySep
      (dropUntilFirstSep sep) :=
    tm0RealizesInnerBlockSep_of_anySuffix
      (tm0RealizesBlockSepAnySuffix_toInner
        (sep₁ := outerSep) (sep₂ := boundarySep)
        hboundary_nd (Ne.symm hboundary_outer) hdropAny
        (fun block hblock => dropUntilFirstSep_ne_default sep block hblock)
        (fun block hblock => dropUntilFirstSep_ne_marker sep boundarySep block hblock))
  obtain ⟨Λi, hΛii, hΛif, Mi, hMi⟩ := hinner
  let Mpost := boundaryReplaceMachine boundarySep sep
  let hsum : Inhabited (Λi ⊕ BoundaryReplaceSt) :=
    ⟨Sum.inl (@default _ hΛii)⟩
  let Mcomp : TM0.Machine Γ (Λi ⊕ BoundaryReplaceSt) :=
    @TM0Seq.compose Γ Λi hΛii BoundaryReplaceSt inferInstance Mi Mpost
  refine ⟨Λi ⊕ BoundaryReplaceSt, hsum, inferInstance, Mcomp, ?_⟩
  intro pfx inner suffix
    hpfx_nd hpfx_nouter hpfx_ncopy
    hinner_nd hinner_nouter hinner_ncopy hsuffix_nd
  have hdrop_nd : ∀ g ∈ dropUntilFirstSep sep inner, g ≠ default :=
    dropUntilFirstSep_ne_default sep inner hinner_nd
  have hdrop_nouter : ∀ g ∈ dropUntilFirstSep sep inner, g ≠ outerSep :=
    dropUntilFirstSep_ne_marker sep outerSep inner hinner_nouter
  have hdrop_ncopy : ∀ g ∈ dropUntilFirstSep sep inner, g ≠ boundarySep :=
    dropUntilFirstSep_ne_marker sep boundarySep inner hinner_ncopy
  obtain ⟨hi_dom, hi_tape⟩ :=
    hMi pfx inner suffix
      hpfx_nd
      hpfx_nouter
      hpfx_ncopy
      hinner_nd hinner_nouter hinner_ncopy
      hsuffix_nd
      hdrop_nd hdrop_nouter hdrop_ncopy
  have hi_dom' :
      (TM0Seq.evalCfg Mi
        (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).Dom := hi_dom
  have hi_tape' :
      ((TM0Seq.evalCfg Mi
        (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).get hi_dom').Tape =
        Tape.mk₁ (pfx ++ boundarySep :: dropUntilFirstSep sep inner ++
          outerSep :: suffix) := hi_tape hi_dom
  have hpost := tm0_boundaryReplace boundarySep sep
    pfx (dropUntilFirstSep sep inner ++ outerSep :: suffix) hpfx_nd hpfx_ncopy
  have hpost_from_cfg :
      (TM0Seq.evalFromCfg Mpost
        ⟨default, ((TM0Seq.evalCfg Mi
          (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).get
          hi_dom').Tape⟩).Dom := by
    rw [hi_tape']
    show (TM0Seq.evalFromCfg Mpost
      (TM0.init (pfx ++ boundarySep :: dropUntilFirstSep sep inner ++
        outerSep :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    simpa [Mpost, List.append_assoc] using hpost.1
  have hcomp_dom :
      (TM0Seq.evalCfg Mcomp
        (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff Mcomp
      (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts Mi Mpost
        (pfx ++ boundarySep :: inner ++ outerSep :: suffix)
        hi_dom' hpost_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have hcomp_tape :=
    TM0Seq.compose_evalCfg_tape Mi Mpost
      (pfx ++ boundarySep :: inner ++ outerSep :: suffix)
      (pfx ++ boundarySep :: dropUntilFirstSep sep inner ++ outerSep :: suffix)
      hi_dom' hi_tape' (by simpa [Mpost, List.append_assoc] using hpost.1) h
  rw [hcomp_tape]
  simpa [List.append_assoc] using hpost.2 hpost.1

/-- Suffix-opaque version of `tm0_dropUntilFirstSep_inner_replaceBoundary`.

The implementation should be the same reverse/inner-block construction as
`tm0RealizesBlockSepAnySuffix_toInner`, but exposed without the stale
`∀ g ∈ suffix, g ≠ default` premise. -/
theorem tm0_dropUntilFirstSep_inner_replaceBoundary_anySuffix
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep boundarySep outerSep : Γ}
    (hsep_nd : sep ≠ default)
    (hboundary_nd : boundarySep ≠ default)
    (hboundary_outer : boundarySep ≠ outerSep) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine Γ Λ),
      ∀ (pfx inner suffix : List Γ),
        (∀ g ∈ pfx, g ≠ default) →
        (∀ g ∈ pfx, g ≠ outerSep) →
        (∀ g ∈ pfx, g ≠ boundarySep) →
        (∀ g ∈ inner, g ≠ default) →
        (∀ g ∈ inner, g ≠ outerSep) →
        (∀ g ∈ inner, g ≠ boundarySep) →
        (TM0Seq.evalCfg M
          (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M
          (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).Dom),
          ((TM0Seq.evalCfg M
            (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).get h).Tape =
            Tape.mk₁ (pfx ++ sep :: dropUntilFirstSep sep inner ++
              outerSep :: suffix) := by
  have hdropAny :
      TM0RealizesBlockSepAnySuffix Γ boundarySep (dropUntilFirstSep sep) :=
    tm0_dropUntilFirstSep_blockSepAnySuffix
      (sep := sep) (outerSep := boundarySep) hsep_nd
  have hinner : TM0RealizesInnerBlockSepAnySuffix Γ outerSep boundarySep
      (dropUntilFirstSep sep) :=
    tm0RealizesBlockSepAnySuffix_toInner
      (sep₁ := outerSep) (sep₂ := boundarySep)
      hboundary_nd (Ne.symm hboundary_outer) hdropAny
      (fun block hblock => dropUntilFirstSep_ne_default sep block hblock)
      (fun block hblock => dropUntilFirstSep_ne_marker sep boundarySep block hblock)
  obtain ⟨Λi, hΛii, hΛif, Mi, hMi⟩ := hinner
  let Mpost := boundaryReplaceMachine boundarySep sep
  let hsum : Inhabited (Λi ⊕ BoundaryReplaceSt) :=
    ⟨Sum.inl (@default _ hΛii)⟩
  let Mcomp : TM0.Machine Γ (Λi ⊕ BoundaryReplaceSt) :=
    @TM0Seq.compose Γ Λi hΛii BoundaryReplaceSt inferInstance Mi Mpost
  refine ⟨Λi ⊕ BoundaryReplaceSt, hsum, inferInstance, Mcomp, ?_⟩
  intro pfx inner suffix
    hpfx_nd hpfx_nouter hpfx_ncopy
    hinner_nd hinner_nouter hinner_ncopy
  have hdrop_nd : ∀ g ∈ dropUntilFirstSep sep inner, g ≠ default :=
    dropUntilFirstSep_ne_default sep inner hinner_nd
  have hdrop_nouter : ∀ g ∈ dropUntilFirstSep sep inner, g ≠ outerSep :=
    dropUntilFirstSep_ne_marker sep outerSep inner hinner_nouter
  have hdrop_ncopy : ∀ g ∈ dropUntilFirstSep sep inner, g ≠ boundarySep :=
    dropUntilFirstSep_ne_marker sep boundarySep inner hinner_ncopy
  obtain ⟨hi_dom, hi_tape⟩ :=
    hMi pfx inner suffix
      hpfx_nd
      hpfx_nouter
      hpfx_ncopy
      hinner_nd hinner_nouter hinner_ncopy
      hdrop_nd hdrop_nouter hdrop_ncopy
  have hi_dom' :
      (TM0Seq.evalCfg Mi
        (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).Dom := hi_dom
  have hi_tape' :
      ((TM0Seq.evalCfg Mi
        (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).get hi_dom').Tape =
        Tape.mk₁ (pfx ++ boundarySep :: dropUntilFirstSep sep inner ++
          outerSep :: suffix) := hi_tape hi_dom
  have hpost := tm0_boundaryReplace boundarySep sep
    pfx (dropUntilFirstSep sep inner ++ outerSep :: suffix) hpfx_nd hpfx_ncopy
  have hpost_from_cfg :
      (TM0Seq.evalFromCfg Mpost
        ⟨default, ((TM0Seq.evalCfg Mi
          (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).get
          hi_dom').Tape⟩).Dom := by
    rw [hi_tape']
    show (TM0Seq.evalFromCfg Mpost
      (TM0.init (pfx ++ boundarySep :: dropUntilFirstSep sep inner ++
        outerSep :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    simpa [Mpost, List.append_assoc] using hpost.1
  have hcomp_dom :
      (TM0Seq.evalCfg Mcomp
        (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff Mcomp
      (pfx ++ boundarySep :: inner ++ outerSep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts Mi Mpost
        (pfx ++ boundarySep :: inner ++ outerSep :: suffix)
        hi_dom' hpost_from_cfg)
  refine ⟨hcomp_dom, ?_⟩
  intro h
  have hcomp_tape :=
    TM0Seq.compose_evalCfg_tape Mi Mpost
      (pfx ++ boundarySep :: inner ++ outerSep :: suffix)
      (pfx ++ boundarySep :: dropUntilFirstSep sep inner ++ outerSep :: suffix)
      hi_dom' hi_tape' (by simpa [Mpost, List.append_assoc] using hpost.1) h
  rw [hcomp_tape]
  simpa [List.append_assoc] using hpost.2 hpost.1

/-- Separator-parametric, suffix-opaque paired addition.

This is the theorem needed between the copy phase and the copied-tail cleanup
in `tm0_binAddPairedKeepRightSep_beforeSep_viaCopySep`. Its successor step is
intended to use `tm0_binSucc_blockSepAnySuffix`, so `pairSep` must be a
non-binary separator. -/
theorem tm0_binAddPairedSep_beforeSep_anySuffix
    {pairSep outerSep : ChainΓ}
    (hpair_nd : pairSep ≠ default)
    (houter_nd : outerSep ≠ default)
    (hpair_outer : pairSep ≠ outerSep)
    (hpair_bit0 : pairSep ≠ γ'ToChainΓ Γ'.bit0)
    (hpair_bit1 : pairSep ≠ γ'ToChainΓ Γ'.bit1)
    (houter_bit0 : outerSep ≠ γ'ToChainΓ Γ'.bit0)
    (houter_bit1 : outerSep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesPairedBlockBeforeSepAnySuffix pairSep outerSep
      (binAddPairedSep pairSep) := by
  have hbody :
      TM0RealizesPairedBlockBeforeSepCond pairSep outerSep
        (pairedDecrLeftIncrRightSep pairSep) (pairedAddCondSep pairSep) :=
    tm0_pairedDecrLeftIncrRightSep_beforeSepCond
      hpair_nd hpair_outer hpair_bit0 hpair_bit1 houter_bit0 houter_bit1
  have hloop :
      TM0RealizesPairedBlockBeforeSepAnySuffix pairSep outerSep
        (binAddPairedWhileSep pairSep) :=
    tm0RealizesPairedBlockBeforeSep_while_pairedSepInvSep
      (pairSep := pairSep) (outerSep := outerSep)
      hpair_nd hpair_outer
      (pairedDecrLeftIncrRightSep pairSep)
      (binAddPairedWhileSep pairSep)
      (pairedAddCondSep pairSep)
      hbody
      (fun block hInv _hblock _hcond =>
        pairedDecrLeftIncrRightSep_pairedSepInvSep
          pairSep block
          (fun left => by
            unfold binPred
            exact chainBinaryRepr_no_of_ne_bits pairSep hpair_bit0 hpair_bit1
              (decodeBinaryBlock left - 1))
          (fun right hright_npair =>
            binSucc_no_of_ne_bits hpair_bit0 hpair_bit1
              (normalizeBlock right)
              (normalizeBlock_no_of_ne_bits pairSep hpair_bit0 hpair_bit1 right))
          hInv)
      (pairedDecrLeftIncrRightSep_ne_default pairSep hpair_nd)
      (pairedDecrLeftIncrRightSep_ne_marker pairSep outerSep hpair_outer
        houter_bit0 houter_bit1)
      (binAddPairedWhileSep_eq_iterate pairSep · hpair_bit0 hpair_bit1)
  have hdrop :
      TM0RealizesBlockSepAnySuffix ChainΓ outerSep
        (dropUntilFirstSep pairSep) :=
    tm0_dropUntilFirstSep_blockSepAnySuffix pairSep outerSep hpair_nd
  have hloop_drop :
      TM0RealizesPairedBlockBeforeSepAnySuffix pairSep outerSep
        (dropUntilFirstSep pairSep ∘ binAddPairedWhileSep pairSep) :=
    tm0RealizesPairedBlockBeforeSep_comp_blockSepAnySuffix
      hpair_nd hpair_outer hloop hdrop
      (binAddPairedWhileSep_ne_default pairSep hpair_nd)
      (fun block hblock =>
        binAddPairedWhileSep_ne_marker pairSep outerSep hpair_outer
          houter_bit0 houter_bit1 block hblock)
      (fun block hblock =>
        dropUntilFirstSep_ne_marker pairSep outerSep
          (binAddPairedWhileSep pairSep block)
          (binAddPairedWhileSep_ne_marker pairSep outerSep hpair_outer
            houter_bit0 houter_bit1 block hblock))
  have hnorm :
      TM0RealizesBlockSepAnySuffix ChainΓ outerSep normalizeBlock :=
    tm0_normalizeBlockSep_anySuffix houter_bit0 houter_bit1
  have hcomposed :
      TM0RealizesPairedBlockBeforeSepAnySuffix pairSep outerSep
        (normalizeBlock ∘ (dropUntilFirstSep pairSep ∘
          binAddPairedWhileSep pairSep)) :=
    tm0RealizesPairedBlockBeforeSep_comp_blockSepAnySuffix
      hpair_nd hpair_outer hloop_drop hnorm
      (fun block hblock =>
        dropUntilFirstSep_ne_default pairSep
          (binAddPairedWhileSep pairSep block)
          (binAddPairedWhileSep_ne_default pairSep hpair_nd block hblock))
      (fun block hblock =>
        dropUntilFirstSep_ne_marker pairSep outerSep
          (binAddPairedWhileSep pairSep block)
          (binAddPairedWhileSep_ne_marker pairSep outerSep hpair_outer
            houter_bit0 houter_bit1 block hblock))
      (fun block _hblock =>
        normalizeBlock_no_of_ne_bits outerSep houter_bit0 houter_bit1
          (dropUntilFirstSep pairSep
            (binAddPairedWhileSep pairSep block)))
  refine tm0RealizesPairedBlockBeforeSep_congr hcomposed ?_
  intro left right hleft_npair hright_npair
  have hInv : pairedSepInvSep pairSep (left ++ pairSep :: right) := by
    constructor
    · simp
    · rw [show splitAtSep pairSep (left ++ pairSep :: right) = (left, right) by
        simpa using splitAtSep_general_cons pairSep left right hleft_npair]
      exact hright_npair
  have hdecomp :=
    binAddPairedSep_eq_while_decomp pairSep
      (left ++ pairSep :: right) hpair_bit0 hpair_bit1 hInv
  exact hdecomp.symm

/-- Copy/delete construction for keep-right paired addition, stated with an
explicit fresh copy separator.

This is the version that can use `tm0_copyWithSep_blockSepAnySuffix_outer`:
the suffix after `outerSep` is opaque throughout the copy phase, and `copySep`
is kept distinct from all data that the later delete-through-separator phase
must inspect. -/
theorem tm0_binAddPairedKeepRightSep_beforeSep_viaCopySep
    {pairSep copySep outerSep : ChainΓ}
    (hpair_nd : pairSep ≠ default)
    (hcopy_nd : copySep ≠ default)
    (houter_nd : outerSep ≠ default)
    (hpair_copy : pairSep ≠ copySep)
    (hpair_outer : pairSep ≠ outerSep)
    (hcopy_outer : copySep ≠ outerSep)
    (hpair_bit0 : pairSep ≠ γ'ToChainΓ Γ'.bit0)
    (hpair_bit1 : pairSep ≠ γ'ToChainΓ Γ'.bit1)
    (hcopy_bit0 : copySep ≠ γ'ToChainΓ Γ'.bit0)
    (hcopy_bit1 : copySep ≠ γ'ToChainΓ Γ'.bit1)
    (houter_bit0 : outerSep ≠ γ'ToChainΓ Γ'.bit0)
    (houter_bit1 : outerSep ≠ γ'ToChainΓ Γ'.bit1) :
    TM0RealizesPairedBlockBeforeSepViaCopySep pairSep copySep outerSep
      (binAddPairedKeepRightSep pairSep) := by
  obtain ⟨Λcopy, hΛcopyi, hΛcopyf, Mcopy, hMcopy⟩ :=
    tm0_copyWithSep_blockSepAnySuffix_outer
      (sep2 := copySep) (outerSep := outerSep) hcopy_nd houter_nd
  obtain ⟨Λadd, hΛaddi, hΛaddf, Madd, hMadd⟩ :=
    tm0_binAddPairedSep_beforeSep_anySuffix
      hpair_nd hcopy_nd hpair_copy hpair_bit0 hpair_bit1
      hcopy_bit0 hcopy_bit1
  obtain ⟨Λdrop, hΛdropi, hΛdropf, Mdrop, hMdrop⟩ :=
    tm0_dropUntilFirstSep_inner_replaceBoundary_anySuffix
      (sep := pairSep) (boundarySep := copySep) (outerSep := outerSep)
      hpair_nd hcopy_nd hcopy_outer
  let h12i : Inhabited (Λcopy ⊕ Λadd) := ⟨Sum.inl (@default _ hΛcopyi)⟩
  let M12 : TM0.Machine ChainΓ (Λcopy ⊕ Λadd) :=
    @TM0Seq.compose ChainΓ Λcopy hΛcopyi Λadd hΛaddi Mcopy Madd
  let h123i : Inhabited ((Λcopy ⊕ Λadd) ⊕ Λdrop) :=
    ⟨Sum.inl (@default _ h12i)⟩
  let M123 : TM0.Machine ChainΓ ((Λcopy ⊕ Λadd) ⊕ Λdrop) :=
    @TM0Seq.compose ChainΓ (Λcopy ⊕ Λadd) h12i Λdrop hΛdropi M12 Mdrop
  refine ⟨(Λcopy ⊕ Λadd) ⊕ Λdrop, h123i, inferInstance, M123, ?_⟩
  intro left right suffix
    hleft_nd hleft_npair hleft_ncopy hleft_nouter
    hright_nd hright_npair hright_ncopy hright_nouter hf_nd
  set block := left ++ pairSep :: right with hblock_def
  set sum := binAddPairedSep pairSep block with hsum_def
  have hblock_nd : ∀ g ∈ block, g ≠ default := by
    intro g hg
    simp [block, List.mem_append] at hg
    rcases hg with hg | rfl | hg
    · exact hleft_nd g hg
    · exact hpair_nd
    · exact hright_nd g hg
  have hblock_ncopy : ∀ g ∈ block, g ≠ copySep := by
    intro g hg
    simp [block, List.mem_append] at hg
    rcases hg with hg | rfl | hg
    · exact hleft_ncopy g hg
    · exact hpair_copy
    · exact hright_ncopy g hg
  have hblock_nouter : ∀ g ∈ block, g ≠ outerSep := by
    intro g hg
    simp [block, List.mem_append] at hg
    rcases hg with hg | rfl | hg
    · exact hleft_nouter g hg
    · exact hpair_outer
    · exact hright_nouter g hg
  have hsum_nd : ∀ g ∈ sum, g ≠ default := by
    simpa [sum] using binAddPairedSep_ne_default pairSep block hblock_nd
  have hsum_ncopy : ∀ g ∈ sum, g ≠ copySep := by
    unfold sum binAddPairedSep
    rcases splitAtSep pairSep block with ⟨l, r⟩
    exact chainBinaryRepr_no_of_ne_bits copySep hcopy_bit0 hcopy_bit1
      (decodeBinaryBlock l + decodeBinaryBlock r)
  have hsum_nouter : ∀ g ∈ sum, g ≠ outerSep := by
    unfold sum binAddPairedSep
    rcases splitAtSep pairSep block with ⟨l, r⟩
    exact chainBinaryRepr_no_of_ne_bits outerSep houter_bit0 houter_bit1
      (decodeBinaryBlock l + decodeBinaryBlock r)
  obtain ⟨hcopy_dom, hcopy_tape⟩ :=
    hMcopy block suffix hblock_nd hblock_nouter
      (copyWithSep_ne_default hcopy_nd block hblock_nd)
      (copyWithSep_ne_sep hcopy_outer block hblock_nouter)
  have hcopy_dom' :
      (TM0Seq.evalCfg Mcopy
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom := by
    simpa [block, List.append_assoc] using hcopy_dom
  have hcopy_tape' :
      ((TM0Seq.evalCfg Mcopy
        (left ++ pairSep :: right ++ outerSep :: suffix)).get hcopy_dom').Tape =
        Tape.mk₁ (left ++ pairSep :: right ++ copySep ::
          left ++ pairSep :: right ++ outerSep :: suffix) := by
    have hget :
        (TM0Seq.evalCfg Mcopy
          (left ++ pairSep :: right ++ outerSep :: suffix)).get hcopy_dom' =
          (TM0Seq.evalCfg Mcopy (block ++ outerSep :: suffix)).get hcopy_dom := by
      apply Part.get_eq_get_of_eq
      simp [block, List.append_assoc]
    rw [hget, hcopy_tape hcopy_dom]
    simp [block, copyWithSep, List.append_assoc]
  obtain ⟨hadd_dom, hadd_tape⟩ :=
    hMadd left right (block ++ outerSep :: suffix)
      hleft_nd hleft_npair hleft_ncopy
      hright_nd hright_npair hright_ncopy
      (by simpa [block, sum] using hsum_nd)
  have hadd_dom' :
      (TM0Seq.evalCfg Madd
        (left ++ pairSep :: right ++ copySep ::
          left ++ pairSep :: right ++ outerSep :: suffix)).Dom := by
    simpa [block, List.append_assoc] using hadd_dom
  have hadd_tape' :
      ((TM0Seq.evalCfg Madd
        (left ++ pairSep :: right ++ copySep ::
          left ++ pairSep :: right ++ outerSep :: suffix)).get hadd_dom').Tape =
        Tape.mk₁ (sum ++ copySep ::
          left ++ pairSep :: right ++ outerSep :: suffix) := by
    have hget :
        (TM0Seq.evalCfg Madd
          (left ++ pairSep :: right ++ copySep ::
            left ++ pairSep :: right ++ outerSep :: suffix)).get hadd_dom' =
          (TM0Seq.evalCfg Madd
            (left ++ pairSep :: right ++ copySep :: (block ++ outerSep :: suffix))).get
              hadd_dom := by
      apply Part.get_eq_get_of_eq
      simp [block, List.append_assoc]
    rw [hget, hadd_tape hadd_dom]
    simp [block, sum, List.append_assoc]
  obtain ⟨hdrop_dom, hdrop_tape⟩ :=
    hMdrop sum block suffix
      hsum_nd hsum_nouter hsum_ncopy
      hblock_nd hblock_nouter hblock_ncopy
  have hdrop_dom' :
      (TM0Seq.evalCfg Mdrop
        (sum ++ copySep :: left ++ pairSep :: right ++ outerSep :: suffix)).Dom := by
    simpa [block, List.append_assoc] using hdrop_dom
  have hdrop_tape' :
      ((TM0Seq.evalCfg Mdrop
        (sum ++ copySep :: left ++ pairSep :: right ++ outerSep :: suffix)).get
          hdrop_dom').Tape =
        Tape.mk₁ (sum ++ pairSep :: right ++ outerSep :: suffix) := by
    have hget :
        (TM0Seq.evalCfg Mdrop
          (sum ++ copySep :: left ++ pairSep :: right ++ outerSep :: suffix)).get
            hdrop_dom' =
          (TM0Seq.evalCfg Mdrop
            (sum ++ copySep :: block ++ outerSep :: suffix)).get hdrop_dom := by
      apply Part.get_eq_get_of_eq
      simp [block, List.append_assoc]
    rw [hget, hdrop_tape hdrop_dom]
    have hdrop_right :
        dropUntilFirstSep pairSep block = right := by
      simpa [block] using
        dropUntilFirstSep_append_cons pairSep left right hleft_npair
    simp [block, hdrop_right, List.append_assoc]
  have hadd_from_cfg :
      (TM0Seq.evalFromCfg Madd
        ⟨default, ((TM0Seq.evalCfg Mcopy
          (left ++ pairSep :: right ++ outerSep :: suffix)).get
          hcopy_dom').Tape⟩).Dom := by
    rw [hcopy_tape']
    change (TM0Seq.evalFromCfg Madd
      (TM0.init (left ++ pairSep :: right ++ copySep ::
        left ++ pairSep :: right ++ outerSep :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hadd_dom'
  have hM12_dom :
      (TM0Seq.evalCfg M12
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M12
      (left ++ pairSep :: right ++ outerSep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts Mcopy Madd
        (left ++ pairSep :: right ++ outerSep :: suffix)
        hcopy_dom' hadd_from_cfg)
  have hM12_tape :
      ((TM0Seq.evalCfg M12
        (left ++ pairSep :: right ++ outerSep :: suffix)).get hM12_dom).Tape =
        Tape.mk₁ (sum ++ copySep ::
          left ++ pairSep :: right ++ outerSep :: suffix) := by
    have ht := TM0Seq.compose_evalCfg_tape Mcopy Madd
      (left ++ pairSep :: right ++ outerSep :: suffix)
      (left ++ pairSep :: right ++ copySep ::
        left ++ pairSep :: right ++ outerSep :: suffix)
      hcopy_dom' hcopy_tape' hadd_dom' hM12_dom
    rw [ht, hadd_tape']
  have hdrop_from_cfg :
      (TM0Seq.evalFromCfg Mdrop
        ⟨default, ((TM0Seq.evalCfg M12
          (left ++ pairSep :: right ++ outerSep :: suffix)).get
          hM12_dom).Tape⟩).Dom := by
    rw [hM12_tape]
    change (TM0Seq.evalFromCfg Mdrop
      (TM0.init (sum ++ copySep ::
        left ++ pairSep :: right ++ outerSep :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hdrop_dom'
  have hM123_dom :
      (TM0Seq.evalCfg M123
        (left ++ pairSep :: right ++ outerSep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M123
      (left ++ pairSep :: right ++ outerSep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts M12 Mdrop
        (left ++ pairSep :: right ++ outerSep :: suffix)
        hM12_dom hdrop_from_cfg)
  refine ⟨hM123_dom, ?_⟩
  intro h
  have ht := TM0Seq.compose_evalCfg_tape M12 Mdrop
      (left ++ pairSep :: right ++ outerSep :: suffix)
      (sum ++ copySep :: left ++ pairSep :: right ++ outerSep :: suffix)
      hM12_dom hM12_tape hdrop_dom' h
  rw [ht, hdrop_tape']
  have hkeep :
      binAddPairedKeepRightSep pairSep block = sum ++ pairSep :: right := by
    simpa [sum, block] using
      binAddPairedKeepRightSep_eq_cons pairSep left right hleft_npair
  simpa [block, hkeep, List.append_assoc]

theorem tm0_binPred_afterMulSep₂_innerBlockSep_outer {outerSep : ChainΓ}
    (houter_nd : outerSep ≠ default)
    (houter_ne_sep₂ : outerSep ≠ binMulStateSep₂) :
    TM0RealizesInnerBlockSep ChainΓ outerSep binMulStateSep₂ binPred := by
  exact tm0RealizesBlockSep_toInnerOuterSep
    houter_nd
    (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
    houter_ne_sep₂
    tm0_binPred_blockSep_mulSep₂
    binPred_ne_default
    (fun block _hblock => binPred_no_mulSep₂ block)

theorem tm0_binPred_afterMulSep₂_innerBlockSep_outer_anySuffix
    {outerSep : ChainΓ}
    (houter_ne_sep₂ : outerSep ≠ binMulStateSep₂) :
    TM0RealizesInnerBlockSepAnySuffix ChainΓ outerSep binMulStateSep₂
      binPred := by
  exact tm0RealizesBlockSepAnySuffix_toInner
    (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
    houter_ne_sep₂
    (tm0_binPred_blockSepAnySuffix_of_ne_bits
      (sep := binMulStateSep₂)
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit0)
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit1))
    binPred_ne_default
    (fun block _hblock => binPred_no_mulSep₂ block)

theorem tm0_binPred_afterMulSep₂_innerDefaultViaConsBottom :
    TM0RealizesInnerBlockDefaultViaSep ChainΓ chainConsBottom
      binMulStateSep₂ binPred := by
  exact tm0RealizesBlockSep_toInnerDefaultViaSep
    chainConsBottom_ne_default
    (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
    (by
      intro h
      exact chainMulSep₂_ne_chainConsBottom (by simpa [binMulStateSep₂] using h.symm))
    tm0_binPred_blockSep_mulSep₂
    binPred_ne_default
    (fun block _hblock => binPred_no_mulSep₂ block)

theorem tm0_binPred_afterMulSep₂_beforeMulSep₁ :
    TM0RealizesInnerBlockSep ChainΓ binMulStateSep₁ binMulStateSep₂ binPred := by
  exact tm0_binPred_afterMulSep₂_innerBlockSep_outer
    (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default)
    (by simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂)

/-- Separator-bounded split form of the arithmetic update in one
three-separator multiplication iteration.

This deliberately keeps the freshness obligations for the outer separator
explicit. After the paired-add phase the prefix contains `binMulStateSep₁`, so
that separator is not a valid outer separator for the fuel-decrement phase; a
caller must supply a genuinely fresh separator for `pref'` and `fuel`. -/
theorem tm0_binMulPairedStep3_update_splitBeforeSep
    {copySep outerSep : ChainΓ}
    (hcopy_nd : copySep ≠ default)
    (hsep₁_copy : binMulStateSep₁ ≠ copySep)
    (hcopy_sep₂ : copySep ≠ binMulStateSep₂)
    (hcopy_bit0 : copySep ≠ γ'ToChainΓ Γ'.bit0)
    (hcopy_bit1 : copySep ≠ γ'ToChainΓ Γ'.bit1)
    (houter_ne_sep₂ : outerSep ≠ binMulStateSep₂) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ),
      ∀ (acc addend fuel suffix : List ChainΓ),
        (∀ g ∈ acc, g ≠ default) →
        (∀ g ∈ acc, g ≠ binMulStateSep₁) →
        (∀ g ∈ acc, g ≠ copySep) →
        (∀ g ∈ acc, g ≠ binMulStateSep₂) →
        (∀ g ∈ addend, g ≠ default) →
        (∀ g ∈ addend, g ≠ binMulStateSep₁) →
        (∀ g ∈ addend, g ≠ copySep) →
        (∀ g ∈ addend, g ≠ binMulStateSep₂) →
        (∀ g ∈ fuel, g ≠ default) →
        (∀ g ∈ fuel, g ≠ outerSep) →
        (∀ g ∈ fuel, g ≠ binMulStateSep₂) →
        (∀ g ∈ binAddPairedKeepRightSep binMulStateSep₁
            (acc ++ binMulStateSep₁ :: addend), g ≠ outerSep) →
        (∀ g ∈ binPred fuel, g ≠ outerSep) →
        (TM0Seq.evalCfg M
          (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
            fuel ++ outerSep :: suffix)).Dom ∧
        ∀ (h : (TM0Seq.evalCfg M
          (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
            fuel ++ outerSep :: suffix)).Dom),
          ((TM0Seq.evalCfg M
            (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
              fuel ++ outerSep :: suffix)).get h).Tape =
            Tape.mk₁ (binMulPairedStep3
          (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ :: fuel) ++
              outerSep :: suffix) := by
  obtain ⟨Λa, hΛai, hΛaf, Ma, hMa⟩ :=
    tm0_binAddPairedKeepRightSep_beforeSep_viaCopySep
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default)
      hcopy_nd
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
      hsep₁_copy
      (by simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂)
      hcopy_sep₂
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_bit0)
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_bit1)
      hcopy_bit0
      hcopy_bit1
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit0)
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit1)
  obtain ⟨Λp, hΛpi, hΛpf, Mp, hMp⟩ :=
    tm0_binPred_afterMulSep₂_innerBlockSep_outer_anySuffix
      houter_ne_sep₂
  let h12i : Inhabited (Λa ⊕ Λp) := ⟨Sum.inl (@default _ hΛai)⟩
  let M12 : TM0.Machine ChainΓ (Λa ⊕ Λp) :=
    @TM0Seq.compose ChainΓ Λa hΛai Λp hΛpi Ma Mp
  refine ⟨Λa ⊕ Λp, h12i, inferInstance, M12, ?_⟩
  intro acc addend fuel suffix
    hacc_nd hacc_no_sep₁ hacc_no_copy hacc_no_sep₂
    hadd_nd hadd_no_sep₁ hadd_no_copy hadd_no_sep₂
    hfuel_nd hfuel_no_outer hfuel_no_sep₂
    hpref'_no_outer hpred_no_outer
  let pref := acc ++ binMulStateSep₁ :: addend
  let pref' := binAddPairedKeepRightSep binMulStateSep₁ pref
  have hpref_nd : ∀ x ∈ pref, x ≠ (default : ChainΓ) := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact hacc_nd x hx
    · simpa [binMulStateSep₁] using chainMulSep₁_ne_default
    · exact hadd_nd x hx
  have hpref_no_sep₂ : ∀ x ∈ pref, x ≠ binMulStateSep₂ := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact hacc_no_sep₂ x hx
    · simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂
    · exact hadd_no_sep₂ x hx
  have hpref'_nd : ∀ x ∈ pref', x ≠ (default : ChainΓ) := by
    exact binAddPairedKeepRightSep_ne_default binMulStateSep₁ pref
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default) hpref_nd
  have hpref'_no_sep₂ : ∀ x ∈ pref', x ≠ binMulStateSep₂ := by
    exact binAddPairedKeepRightSep_no_mulSep₂ pref hpref_no_sep₂
  have hpred_nd : ∀ x ∈ binPred fuel, x ≠ (default : ChainΓ) :=
    binPred_ne_default fuel hfuel_nd
  have hpred_no_sep₂ : ∀ x ∈ binPred fuel, x ≠ binMulStateSep₂ :=
    binPred_no_mulSep₂ fuel
  obtain ⟨ha_dom, ha_tape⟩ :=
    hMa acc addend (fuel ++ outerSep :: suffix)
      hacc_nd hacc_no_sep₁ hacc_no_copy hacc_no_sep₂
      hadd_nd hadd_no_sep₁ hadd_no_copy hadd_no_sep₂
        (by
          have := binAddPairedKeepRightSep_ne_default binMulStateSep₁
            (acc ++ binMulStateSep₁ :: addend)
          simpa [pref] using this
            (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default) hpref_nd)
  have ha_dom' :
      (TM0Seq.evalCfg Ma
        (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
          fuel ++ outerSep :: suffix)).Dom := by
    simpa [List.append_assoc] using ha_dom
  have ha_tape' :
      ((TM0Seq.evalCfg Ma
        (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
          fuel ++ outerSep :: suffix)).get ha_dom').Tape =
        Tape.mk₁ (pref' ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix) := by
    have hget :
        (TM0Seq.evalCfg Ma
          (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
            fuel ++ outerSep :: suffix)).get ha_dom' =
          (TM0Seq.evalCfg Ma
            (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
              (fuel ++ outerSep :: suffix))).get ha_dom := by
      apply Part.get_eq_get_of_eq
      simp [List.append_assoc]
    rw [hget]
    simpa [pref, pref', List.append_assoc] using ha_tape ha_dom
  obtain ⟨hp_dom, hp_tape⟩ :=
    hMp pref' fuel suffix
      hpref'_nd hpref'_no_outer hpref'_no_sep₂
      hfuel_nd hfuel_no_outer hfuel_no_sep₂
      hpred_nd hpred_no_outer hpred_no_sep₂
  have hp_from_cfg :
      (TM0Seq.evalFromCfg Mp
        ⟨default, ((TM0Seq.evalCfg Ma
          (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
            fuel ++ outerSep :: suffix)).get ha_dom').Tape⟩).Dom := by
    rw [ha_tape']
    change (TM0Seq.evalFromCfg Mp
      (TM0.init (pref' ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hp_dom
  have hM12_dom :
      (TM0Seq.evalCfg M12
        (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
          fuel ++ outerSep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M12
      (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
        fuel ++ outerSep :: suffix)).mpr
      (@TM0Seq.compose_dom_of_parts ChainΓ _ Λa hΛai Λp hΛpi
          Ma Mp
          (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
            fuel ++ outerSep :: suffix)
          ha_dom' hp_from_cfg)
  refine ⟨hM12_dom, ?_⟩
  intro h
  have hcomp_tape :=
    @TM0Seq.compose_evalCfg_tape ChainΓ _ Λa hΛai Λp hΛpi Ma Mp
        (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
          fuel ++ outerSep :: suffix)
        (pref' ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix)
        ha_dom' ha_tape' hp_dom h
  rw [hcomp_tape, hp_tape hp_dom]
  have hstep_eq :
      binMulPairedStep3
          (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ :: fuel) =
        pref' ++ binMulStateSep₂ :: binPred fuel := by
    have hsplit₁ :
        splitAtSep binMulStateSep₁
            (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ :: fuel) =
          (acc, addend ++ binMulStateSep₂ :: fuel) := by
      simpa [List.append_assoc] using
        splitAtSep_general_cons binMulStateSep₁ acc
          (addend ++ binMulStateSep₂ :: fuel) hacc_no_sep₁
    have hsplit₂ :
        splitAtSep binMulStateSep₂ (addend ++ binMulStateSep₂ :: fuel) =
          (addend, fuel) := by
      exact splitAtSep_general_cons binMulStateSep₂ addend fuel hadd_no_sep₂
    have hsplit₁' :
        splitAtSep binMulStateSep₁
            (acc ++ binMulStateSep₁ :: (addend ++ binMulStateSep₂ :: fuel)) =
          (acc, addend ++ binMulStateSep₂ :: fuel) := by
      simpa [List.append_assoc] using hsplit₁
    unfold binMulPairedStep3
    simp [hsplit₁', hsplit₂, pref, pref', List.append_assoc]
  have hstep_eq' :
      binMulPairedStep3
          (acc ++ binMulStateSep₁ :: (addend ++ binMulStateSep₂ :: fuel)) =
        pref' ++ binMulStateSep₂ :: binPred fuel := by
    simpa [List.append_assoc] using hstep_eq
  simpa [hstep_eq', List.append_assoc]

/-- Suffix-preserving conditional body for the three-separator multiplication
state predicate.

This is the mirrored condition-only variant: the predicate machine decides
`blockValueLeq 0` on the fuel field after `binMulStateSep₂`, so the continuing
state is the `false` result of that decider because `binMulPairedCond3` is the
negation of that fuel test. -/
theorem tm0_binMulPairedCond3_blockCondInvSuffix :
    TM0RealizesBlockCondInvSuffix (fun block => block) binMulPairedCond3
      binMulPairedStateInv3 := by
  obtain ⟨Λp, hΛpi, hΛpf, Mp, q_le, q_gt, hne, hp⟩ :=
    tm0_blockValueLeq_afterSep_decidable_2 0 binMulStateSep₂
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
  refine ⟨Λp, hΛpi, hΛpf, Mp, q_gt, ?_⟩
  intro block suffix hInv hblock hsuffix _hstep_nd
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have hreconstruct :
      block = acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ :: fuel := by
    simpa [hsplit, hrest, List.append_assoc] using
      binMulPairedStateInv3_reconstruct block hInv
  let pref := acc ++ binMulStateSep₁ :: addend
  have hpref_nd : ∀ x ∈ pref, x ≠ (default : ChainΓ) := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact binMulPairedStateInv3_acc_ne_default block hblock x (by simpa [hsplit] using hx)
    · simpa [binMulStateSep₁] using chainMulSep₁_ne_default
    · exact binMulPairedStateInv3_addend_ne_default block hblock x (by
        simpa [hsplit, hrest] using hx)
  have hpref_no_sep₂ : ∀ x ∈ pref, x ≠ binMulStateSep₂ := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact binMulPairedStateInv3_acc_no_sep₂ block hInv x (by simpa [hsplit] using hx)
    · simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂
    · exact binMulPairedStateInv3_addend_no_sep₂ block hInv x (by
        simpa [hsplit, hrest] using hx)
  have hfuel_nd : ∀ x ∈ fuel, x ≠ (default : ChainΓ) := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_ne_default block hblock
  obtain ⟨hp_dom, hp_spec⟩ := hp pref fuel suffix hpref_nd hpref_no_sep₂ hfuel_nd hsuffix
  have hinput :
      pref ++ binMulStateSep₂ :: fuel ++ default :: suffix =
        block ++ default :: suffix := by
    simp [pref, hreconstruct, List.append_assoc]
  refine ⟨?_, ?_⟩
  · simpa [hinput] using hp_dom
  · intro h
    have h' : (TM0Seq.evalCfg Mp
        (pref ++ binMulStateSep₂ :: fuel ++ default :: suffix)).Dom := by
      simpa [hinput] using h
    have hspec := hp_spec h'
    have htape :
        ((TM0Seq.evalCfg Mp (block ++ default :: suffix)).get h).Tape =
          Tape.mk₁ (block ++ default :: suffix) := by
      have hget :
          (TM0Seq.evalCfg Mp (block ++ default :: suffix)).get h =
            (TM0Seq.evalCfg Mp
              (pref ++ binMulStateSep₂ :: fuel ++ default :: suffix)).get h' := by
        apply Part.get_eq_get_of_eq
        simp [hinput]
      rw [hget]
      simpa [hinput] using hspec.1
    have hq_le :
        blockValueLeq 0 fuel →
          ((TM0Seq.evalCfg Mp (block ++ default :: suffix)).get h).q = q_le := by
      intro hle
      have hget :
          (TM0Seq.evalCfg Mp (block ++ default :: suffix)).get h =
            (TM0Seq.evalCfg Mp
              (pref ++ binMulStateSep₂ :: fuel ++ default :: suffix)).get h' := by
        apply Part.get_eq_get_of_eq
        simp [hinput]
      rw [hget]
      exact hspec.2.1 hle
    have hq_gt :
        ¬ blockValueLeq 0 fuel →
          ((TM0Seq.evalCfg Mp (block ++ default :: suffix)).get h).q = q_gt := by
      intro hle
      have hget :
          (TM0Seq.evalCfg Mp (block ++ default :: suffix)).get h =
            (TM0Seq.evalCfg Mp
              (pref ++ binMulStateSep₂ :: fuel ++ default :: suffix)).get h' := by
        apply Part.get_eq_get_of_eq
        simp [hinput]
      rw [hget]
      exact hspec.2.2 hle
    have hcond_iff :
        binMulPairedCond3 block ↔ ¬ blockValueLeq 0 fuel := by
      simp [binMulPairedCond3, binMulPairedFuel3, hsplit, hrest]
    by_cases hcond : binMulPairedCond3 block
    · simp [hcond]
      exact ⟨hq_gt (hcond_iff.mp hcond), htape⟩
    · simp [hcond]
      constructor
      · intro hq
        apply hne
        have hle : blockValueLeq 0 fuel := by
          by_contra hle
          exact hcond ((hcond_iff.mpr hle))
        exact (hq_le hle).symm.trans hq
      · exact htape

theorem tm0_binMulPairedCond3_blockCondInvSepAnySuffix
    {outerSep : ChainΓ} :
    TM0RealizesBlockCondInvSepAnySuffix outerSep
      (fun block => block) binMulPairedCond3 binMulPairedStateInv3 := by
  obtain ⟨Λp, hΛpi, hΛpf, Mp, q_le, q_gt, hne, hp⟩ :=
    tm0_blockValueLeq_betweenSep_decidable_2 0
      binMulStateSep₂ outerSep
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
  refine ⟨Λp, hΛpi, hΛpf, Mp, q_gt, ?_⟩
  intro block suffix hInv hblock hblock_nouter _hstep_nd _hstep_nouter
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have hreconstruct :
      block = acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ :: fuel := by
    simpa [hsplit, hrest, List.append_assoc] using
      binMulPairedStateInv3_reconstruct block hInv
  let pref := acc ++ binMulStateSep₁ :: addend
  have hpref_nd : ∀ x ∈ pref, x ≠ (default : ChainΓ) := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact binMulPairedStateInv3_acc_ne_default block hblock x
        (by simpa [hsplit] using hx)
    · simpa [binMulStateSep₁] using chainMulSep₁_ne_default
    · exact binMulPairedStateInv3_addend_ne_default block hblock x (by
        simpa [hsplit, hrest] using hx)
  have hpref_no_sep₂ : ∀ x ∈ pref, x ≠ binMulStateSep₂ := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact binMulPairedStateInv3_acc_no_sep₂ block hInv x
        (by simpa [hsplit] using hx)
    · simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂
    · exact binMulPairedStateInv3_addend_no_sep₂ block hInv x (by
        simpa [hsplit, hrest] using hx)
  have hfuel_nd : ∀ x ∈ fuel, x ≠ (default : ChainΓ) := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_ne_default block hblock
  have hfuel_no_outer : ∀ x ∈ fuel, x ≠ outerSep := by
    intro x hx
    exact hblock_nouter x (by
      rw [hreconstruct]
      simp [hx, List.append_assoc])
  obtain ⟨hp_dom, hp_spec⟩ :=
    hp pref fuel suffix hpref_nd hpref_no_sep₂ hfuel_nd hfuel_no_outer
  have hinput :
      pref ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix =
        block ++ outerSep :: suffix := by
    simp [pref, hreconstruct, List.append_assoc]
  refine ⟨?_, ?_⟩
  · simpa [hinput] using hp_dom
  · intro h
    have h' : (TM0Seq.evalCfg Mp
        (pref ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix)).Dom := by
      simpa [hinput] using h
    have hspec := hp_spec h'
    have htape :
        ((TM0Seq.evalCfg Mp (block ++ outerSep :: suffix)).get h).Tape =
          Tape.mk₁ (block ++ outerSep :: suffix) := by
      have hget :
          (TM0Seq.evalCfg Mp (block ++ outerSep :: suffix)).get h =
            (TM0Seq.evalCfg Mp
              (pref ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix)).get h' := by
        apply Part.get_eq_get_of_eq
        simp [hinput]
      rw [hget]
      simpa [hinput] using hspec.1
    have hq_le :
        blockValueLeq 0 fuel →
          ((TM0Seq.evalCfg Mp (block ++ outerSep :: suffix)).get h).q = q_le := by
      intro hle
      have hget :
          (TM0Seq.evalCfg Mp (block ++ outerSep :: suffix)).get h =
            (TM0Seq.evalCfg Mp
              (pref ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix)).get h' := by
        apply Part.get_eq_get_of_eq
        simp [hinput]
      rw [hget]
      exact hspec.2.1 hle
    have hq_gt :
        ¬ blockValueLeq 0 fuel →
          ((TM0Seq.evalCfg Mp (block ++ outerSep :: suffix)).get h).q = q_gt := by
      intro hle
      have hget :
          (TM0Seq.evalCfg Mp (block ++ outerSep :: suffix)).get h =
            (TM0Seq.evalCfg Mp
              (pref ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix)).get h' := by
        apply Part.get_eq_get_of_eq
        simp [hinput]
      rw [hget]
      exact hspec.2.2 hle
    have hcond_iff :
        binMulPairedCond3 block ↔ ¬ blockValueLeq 0 fuel := by
      simp [binMulPairedCond3, binMulPairedFuel3, hsplit, hrest]
    by_cases hcond : binMulPairedCond3 block
    · simp [hcond]
      exact ⟨hq_gt (hcond_iff.mp hcond), htape⟩
    · simp [hcond]
      constructor
      · intro hq
        apply hne
        have hle : blockValueLeq 0 fuel := by
          by_contra hle
          exact hcond ((hcond_iff.mpr hle))
        exact (hq_le hle).symm.trans hq
      · exact htape

theorem tm0_binMulPairedStep3_update_blockInvSepAnySuffix
    {outerSep : ChainΓ}
    (houter_ne_sep₂ : outerSep ≠ binMulStateSep₂) :
    TM0RealizesBlockInvSepAnySuffix outerSep
      binMulPairedStep3 binMulPairedStateInv3 := by
  obtain ⟨Λs, hΛsi, hΛsf, Ms, hMs⟩ :=
    tm0_binMulPairedStep3_update_splitBeforeSep
      (copySep := chainConsBottom) (outerSep := outerSep)
      chainConsBottom_ne_default
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_chainConsBottom)
      (by simpa [binMulStateSep₂] using Ne.symm chainMulSep₂_ne_chainConsBottom)
      (by decide)
      (by decide)
      houter_ne_sep₂
  refine ⟨Λs, hΛsi, hΛsf, Ms, ?_⟩
  intro block suffix hInv hblock hblock_nouter hstep_nd hstep_nouter
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have hreconstruct :
      block = acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ :: fuel := by
    simpa [hsplit, hrest, List.append_assoc] using
      binMulPairedStateInv3_reconstruct block hInv
  let pref := acc ++ binMulStateSep₁ :: addend
  let pref' := binAddPairedKeepRightSep binMulStateSep₁ pref
  have hacc_nd : ∀ x ∈ acc, x ≠ (default : ChainΓ) := by
    intro x hx
    exact binMulPairedStateInv3_acc_ne_default block hblock x
      (by simpa [hsplit] using hx)
  have hacc_no_sep₁ : ∀ x ∈ acc, x ≠ binMulStateSep₁ := by
    simpa [hsplit] using binMulPairedStateInv3_acc_no_sep₁ block hInv
  have hacc_no_copy : ∀ x ∈ acc, x ≠ chainConsBottom := by
    simpa [hsplit] using binMulPairedStateInv3_acc_no_consBottom block hInv
  have hacc_no_sep₂ : ∀ x ∈ acc, x ≠ binMulStateSep₂ := by
    simpa [hsplit] using binMulPairedStateInv3_acc_no_sep₂ block hInv
  have hadd_nd : ∀ x ∈ addend, x ≠ (default : ChainΓ) := by
    intro x hx
    exact binMulPairedStateInv3_addend_ne_default block hblock x
      (by simpa [hsplit, hrest] using hx)
  have hadd_no_sep₁ : ∀ x ∈ addend, x ≠ binMulStateSep₁ := by
    simpa [hsplit, hrest] using binMulPairedStateInv3_addend_no_sep₁ block hInv
  have hadd_no_copy : ∀ x ∈ addend, x ≠ chainConsBottom := by
    simpa [hsplit, hrest] using
      binMulPairedStateInv3_addend_no_consBottom block hInv
  have hadd_no_sep₂ : ∀ x ∈ addend, x ≠ binMulStateSep₂ := by
    simpa [hsplit, hrest] using binMulPairedStateInv3_addend_no_sep₂ block hInv
  have hfuel_nd : ∀ x ∈ fuel, x ≠ (default : ChainΓ) := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_ne_default block hblock
  have hfuel_no_outer : ∀ x ∈ fuel, x ≠ outerSep := by
    intro x hx
    exact hblock_nouter x (by
      rw [hreconstruct]
      simp [hx, List.append_assoc])
  have hfuel_no_sep₂ : ∀ x ∈ fuel, x ≠ binMulStateSep₂ := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_no_sep₂ block hInv
  have hpref'_no_outer : ∀ x ∈ pref', x ≠ outerSep := by
    intro x hx
    exact hstep_nouter x (by
      have hx' : x ∈ pref' ++ binMulStateSep₂ :: binPred fuel := by
        simp [hx]
      have hstep_eq :
          binMulPairedStep3 block =
            pref' ++ binMulStateSep₂ :: binPred fuel := by
        unfold binMulPairedStep3
        simp [hsplit, hrest, pref, pref', List.append_assoc]
      simpa [hstep_eq] using hx')
  have hpred_no_outer : ∀ x ∈ binPred fuel, x ≠ outerSep := by
    intro x hx
    exact hstep_nouter x (by
      have hx' : x ∈ pref' ++ binMulStateSep₂ :: binPred fuel := by
        simp [hx]
      have hstep_eq :
          binMulPairedStep3 block =
            pref' ++ binMulStateSep₂ :: binPred fuel := by
        unfold binMulPairedStep3
        simp [hsplit, hrest, pref, pref', List.append_assoc]
      simpa [hstep_eq] using hx')
  obtain ⟨hdom, htape⟩ :=
    hMs acc addend fuel suffix
      hacc_nd hacc_no_sep₁ hacc_no_copy hacc_no_sep₂
      hadd_nd hadd_no_sep₁ hadd_no_copy hadd_no_sep₂
      hfuel_nd hfuel_no_outer hfuel_no_sep₂
      hpref'_no_outer hpred_no_outer
  have hinput :
      block ++ outerSep :: suffix =
        acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
          fuel ++ outerSep :: suffix := by
    simp [hreconstruct, List.append_assoc]
  refine ⟨?_, ?_⟩
  · simpa [hinput, List.append_assoc] using hdom
  · intro h
    have h' : (TM0Seq.evalCfg Ms
        (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
          fuel ++ outerSep :: suffix)).Dom := by
      simpa [hinput, List.append_assoc] using h
    have hget :
        (TM0Seq.evalCfg Ms (block ++ outerSep :: suffix)).get h =
          (TM0Seq.evalCfg Ms
            (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
              fuel ++ outerSep :: suffix)).get h' := by
      apply Part.get_eq_get_of_eq
      simp [hinput, List.append_assoc]
    rw [hget]
    simpa [hreconstruct, List.append_assoc] using htape h'

theorem tm0_binMulPairedStep3_blockCondInvSepAnySuffix
    {outerSep : ChainΓ} (houterSep₂ : outerSep ≠ binMulStateSep₂) :
    TM0RealizesBlockCondInvSepAnySuffix outerSep
      binMulPairedStep3 binMulPairedCond3 binMulPairedStateInv3 := by
  obtain ⟨Λp, hΛpi, hΛpf, Mp, q_le, q_gt, hne, hp⟩ :=
    tm0_blockValueLeq_betweenSep_decidable_2 0
      binMulStateSep₂ outerSep
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
  obtain ⟨Λs, hΛsi, hΛsf, Ms, hMs⟩ :=
    tm0_binMulPairedStep3_update_blockInvSepAnySuffix
      (outerSep := outerSep)
      houterSep₂
  haveI : DecidableEq Λp := Classical.decEq Λp
  let hΛsFi : Inhabited (Λs ⊕ FinalizeSt) := ⟨Sum.inl (@default _ hΛsi)⟩
  let MsF : TM0.Machine ChainΓ (Λs ⊕ FinalizeSt) :=
    @TM0Seq.compose ChainΓ Λs hΛsi FinalizeSt inferInstance Ms finalizeMachine
  let Mcond : TM0.Machine ChainΓ (Λp ⊕ FinalizeSt ⊕ (Λs ⊕ FinalizeSt)) :=
    @tm0CondCompose Λp FinalizeSt (Λs ⊕ FinalizeSt)
      hΛpi inferInstance hΛsFi inferInstance
      Mp finalizeMachine MsF q_le q_gt
  refine ⟨Λp ⊕ FinalizeSt ⊕ (Λs ⊕ FinalizeSt), inferInstance, inferInstance,
    Mcond, Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)), ?_⟩
  intro block suffix hInv hblock hblock_nsep hstep_nd hstep_nsep
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have hreconstruct :
      block = acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ :: fuel := by
    simpa [hsplit, hrest, List.append_assoc] using
      binMulPairedStateInv3_reconstruct block hInv
  let pref := acc ++ binMulStateSep₁ :: addend
  have hpref_nd : ∀ x ∈ pref, x ≠ (default : ChainΓ) := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact binMulPairedStateInv3_acc_ne_default block hblock x
        (by simpa [hsplit] using hx)
    · simpa [binMulStateSep₁] using chainMulSep₁_ne_default
    · exact binMulPairedStateInv3_addend_ne_default block hblock x (by
        simpa [hsplit, hrest] using hx)
  have hpref_no_sep₂ : ∀ x ∈ pref, x ≠ binMulStateSep₂ := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact binMulPairedStateInv3_acc_no_sep₂ block hInv x
        (by simpa [hsplit] using hx)
    · simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂
    · exact binMulPairedStateInv3_addend_no_sep₂ block hInv x (by
        simpa [hsplit, hrest] using hx)
  have hfuel_nd : ∀ x ∈ fuel, x ≠ (default : ChainΓ) := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_ne_default block hblock
  have hfuel_nouter : ∀ x ∈ fuel, x ≠ outerSep := by
    intro x hx
    exact hblock_nsep x (by
      rw [hreconstruct]
      simp [List.append_assoc, hx])
  obtain ⟨hp_dom, hp_spec⟩ :=
    hp pref fuel suffix hpref_nd hpref_no_sep₂ hfuel_nd hfuel_nouter
  have hinput :
      pref ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix =
        block ++ outerSep :: suffix := by
    simp [pref, hreconstruct, List.append_assoc]
  have hp_dom_block : (TM0Seq.evalCfg Mp (block ++ outerSep :: suffix)).Dom := by
    simpa [hinput] using hp_dom
  set cp := (TM0Seq.evalCfg Mp (block ++ outerSep :: suffix)).get hp_dom_block
  have hcp_get :
      cp =
        (TM0Seq.evalCfg Mp
          (pref ++ binMulStateSep₂ :: fuel ++ outerSep :: suffix)).get hp_dom := by
    apply Part.get_eq_get_of_eq
    simp [hinput]
  have hcp_tape : cp.Tape = Tape.mk₁ (block ++ outerSep :: suffix) := by
    rw [hcp_get]
    simpa [hinput] using (hp_spec hp_dom).1
  have hq_le :
      blockValueLeq 0 fuel → cp.q = q_le := by
    intro hle
    rw [hcp_get]
    exact (hp_spec hp_dom).2.1 hle
  have hq_gt :
      ¬ blockValueLeq 0 fuel → cp.q = q_gt := by
    intro hle
    rw [hcp_get]
    exact (hp_spec hp_dom).2.2 hle
  have hcond_iff :
      binMulPairedCond3 block ↔ ¬ blockValueLeq 0 fuel := by
    simp [binMulPairedCond3, binMulPairedFuel3, hsplit, hrest]
  have hcp_mem : cp ∈ TM0Seq.evalCfg Mp (block ++ outerSep :: suffix) :=
    Part.get_mem hp_dom_block
  have hcp_eval := Turing.mem_eval.mp hcp_mem
  have hcp_halt : TM0.step Mp cp = none := hcp_eval.2
  have hcp_reaches : Reaches (TM0.step Mp)
      (TM0.init (block ++ outerSep :: suffix)) cp := hcp_eval.1
  have hphase1 := condCompose_phase1_reaches Mp finalizeMachine MsF q_le q_gt
    cp (block ++ outerSep :: suffix) hcp_reaches
  change Reaches (TM0.step Mcond) (TM0.init (block ++ outerSep :: suffix))
    { q := Sum.inl cp.q, Tape := cp.Tape } at hphase1
  have heval_rewrite :
      TM0Seq.evalCfg Mcond (block ++ outerSep :: suffix) =
        Turing.eval (TM0.step Mcond) ⟨Sum.inl cp.q, cp.Tape⟩ := by
    exact Turing.reaches_eval hphase1
  by_cases hcond : binMulPairedCond3 block
  · have hq : cp.q = q_gt := hq_gt (hcond_iff.mp hcond)
    have hhalt_q : TM0.step Mp ⟨q_gt, cp.Tape⟩ = none := hq ▸ hcp_halt
    have hstep_block_nd : ∀ g ∈ binMulPairedStep3 block, g ≠ default :=
      hstep_nd hcond
    have hstep_block_nsep : ∀ g ∈ binMulPairedStep3 block, g ≠ outerSep :=
      hstep_nsep hcond
    obtain ⟨hMs_dom, hMs_spec⟩ :=
      hMs block suffix hInv hblock hblock_nsep hstep_block_nd hstep_block_nsep
    have hfinal := compose_finalize_evalCfg Ms (block ++ outerSep :: suffix)
      (binMulPairedStep3 block ++ outerSep :: suffix)
      hMs_dom (hMs_spec hMs_dom)
    have hbranch_dom :
        (TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩).Dom := by
      rw [hcp_tape]
      change (TM0Seq.evalFromCfg MsF
        (TM0.init (block ++ outerSep :: suffix))).Dom
      rw [TM0Seq.evalFromCfg_init]
      exact hfinal.1
    have hbranch_spec :
        ∀ h, (TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩).get h =
          ⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (binMulPairedStep3 block ++ outerSep :: suffix)⟩ := by
      intro h
      have heq :
          TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩ =
            TM0Seq.evalCfg MsF (block ++ outerSep :: suffix) := by
        rw [hcp_tape]
        exact TM0Seq.evalFromCfg_init (M := MsF)
          (l := block ++ outerSep :: suffix)
      have hget :
          (TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩).get h =
            (TM0Seq.evalCfg MsF (block ++ outerSep :: suffix)).get hfinal.1 := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hfinal.2 hfinal.1
    have hbranch_step :
        ∃ c₂, TM0.step MsF ⟨default, cp.Tape⟩ = some c₂ := by
      rw [hcp_tape]
      change ∃ c₂, TM0.step MsF (TM0.init (block ++ outerSep :: suffix)) = some c₂
      change ∃ c₂, TM0.step MsF
        ⟨default, Tape.mk₁ (block ++ outerSep :: suffix)⟩ = some c₂
      rcases hfirst : TM0.step Ms
          ⟨default, Tape.mk₁ (block ++ outerSep :: suffix)⟩ with _ | c₂
      · refine ⟨(⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (block ++ outerSep :: suffix)⟩ :
            TM0.Cfg ChainΓ (Λs ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λs hΛsi FinalizeSt inferInstance
          Ms finalizeMachine) ⟨Sum.inl default,
            Tape.mk₁ (block ++ outerSep :: suffix)⟩ =
          some ⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (block ++ outerSep :: suffix)⟩
        rw [TM0Seq.compose_step_on_halt Ms finalizeMachine default
          (Tape.mk₁ (block ++ outerSep :: suffix)) hfirst]
        change Option.map
          (fun c₂ : TM0.Cfg ChainΓ FinalizeSt =>
            ({ q := Sum.inr c₂.q, Tape := c₂.Tape } :
              TM0.Cfg ChainΓ (Λs ⊕ FinalizeSt)))
          (TM0.step finalizeMachine
            ⟨FinalizeSt.start, Tape.mk₁ (block ++ outerSep :: suffix)⟩) =
          some ⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (block ++ outerSep :: suffix)⟩
        rw [finalize_step_start]
        rfl
      · refine ⟨(⟨Sum.inl c₂.q, c₂.Tape⟩ :
            TM0.Cfg ChainΓ (Λs ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λs hΛsi FinalizeSt inferInstance
          Ms finalizeMachine) ⟨Sum.inl default,
            Tape.mk₁ (block ++ outerSep :: suffix)⟩ =
          some ⟨Sum.inl c₂.q, c₂.Tape⟩
        simpa using TM0Seq.compose_step_inl Ms finalizeMachine
          (⟨default, Tape.mk₁ (block ++ outerSep :: suffix)⟩ :
            TM0.Cfg ChainΓ Λs) c₂ hfirst
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MsF q_le q_gt))
        ⟨Sum.inl q_gt, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_false Mp finalizeMachine MsF q_le q_gt hne
        cp.Tape hhalt_q).mpr hbranch_dom
    have hdom : (TM0Seq.evalCfg Mcond (block ++ outerSep :: suffix)).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_false_of_step
      Mp finalizeMachine MsF q_le q_gt hne (Sum.inr FinalizeSt.done) cp.Tape
      (Tape.mk₁ (binMulPairedStep3 block ++ outerSep :: suffix))
      hhalt_q hbranch_step hbranch_dom hbranch_spec
    have hcfg' : (TM0Seq.evalCfg Mcond (block ++ outerSep :: suffix)).get h =
        ⟨Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)),
          Tape.mk₁ (binMulPairedStep3 block ++ outerSep :: suffix)⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond (block ++ outerSep :: suffix) =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond (block ++ outerSep :: suffix)).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    simp [hcond, hcfg']
  · have hle : blockValueLeq 0 fuel := by
      by_contra hle
      exact hcond (hcond_iff.mpr hle)
    have hq : cp.q = q_le := hq_le hle
    have hhalt_q : TM0.step Mp ⟨q_le, cp.Tape⟩ = none := hq ▸ hcp_halt
    obtain ⟨hid_dom, hid_spec⟩ := finalize_evalFromCfg cp.Tape
    have hid_step : ∃ c₂, TM0.step finalizeMachine ⟨default, cp.Tape⟩ = some c₂ := by
      exact ⟨⟨FinalizeSt.done, cp.Tape⟩, finalize_step_start cp.Tape⟩
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MsF q_le q_gt))
        ⟨Sum.inl q_le, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_true Mp finalizeMachine MsF q_le q_gt
        cp.Tape hhalt_q).mpr hid_dom
    have hdom : (TM0Seq.evalCfg Mcond (block ++ outerSep :: suffix)).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_true_of_step
      Mp finalizeMachine MsF q_le q_gt FinalizeSt.done cp.Tape cp.Tape
      hhalt_q hid_step hid_dom (fun h => hid_spec h)
    have hcfg' : (TM0Seq.evalCfg Mcond (block ++ outerSep :: suffix)).get h =
        ⟨Sum.inr (Sum.inl FinalizeSt.done), cp.Tape⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond (block ++ outerSep :: suffix) =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond (block ++ outerSep :: suffix)).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    have hq_ne :
        Sum.inr (Sum.inl FinalizeSt.done) ≠
          (Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)) :
            Λp ⊕ FinalizeSt ⊕ (Λs ⊕ FinalizeSt)) := by
      simp
    simp [hcond, hcfg', hq_ne, hcp_tape]

theorem tm0_binMulPairedStep3_blockCondInvSepAnySuffix_default :
    TM0RealizesBlockCondInvSepAnySuffix (default : ChainΓ)
      binMulPairedStep3 binMulPairedCond3 binMulPairedStateInv3 :=
  tm0_binMulPairedStep3_blockCondInvSepAnySuffix
    (by simpa [binMulStateSep₂] using Ne.symm chainMulSep₂_ne_default)


/-- TODO: unconditional suffix-preserving body for the three-separator
multiplication step.

This is the remaining arithmetic-machine obligation after the condition wrapper
has been separated out. It should be proved by composing:

* a separator-parametric paired-add machine over the prefix before
  `binMulStateSep₂`, using `binMulStateSep₁` as the paired separator, and
* a generic `binPred` machine over the fuel after `binMulStateSep₂`.

Semantically it transforms
`acc sep₁ addend sep₂ fuel` into
`(acc + addend) sep₁ addend sep₂ (fuel - 1)`, preserving the
default-delimited suffix. -/
theorem tm0_binMulPairedStep3_update_blockInvSuffixFixed :
    TM0RealizesBlockInvSuffixFixed binMulPairedStep3 binMulPairedStateInv3 := by
  obtain ⟨Λa, hΛai, hΛaf, Ma, hMa⟩ :=
    tm0_binAddPairedKeepRightSep_beforeSep_viaCopySep
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default)
      chainConsBottom_ne_default
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_chainConsBottom)
      (by simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂)
      (by simpa [binMulStateSep₂] using Ne.symm chainMulSep₂_ne_chainConsBottom)
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_bit0)
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_bit1)
      (by decide)
      (by decide)
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit0)
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_bit1)
  obtain ⟨Λp, hΛpi, hΛpf, Mp, hMp⟩ :=
    tm0_binPred_afterMulSep₂_innerDefaultViaConsBottom
  let h12i : Inhabited (Λa ⊕ Λp) := ⟨Sum.inl (@default _ hΛai)⟩
  let M12 : TM0.Machine ChainΓ (Λa ⊕ Λp) :=
    @TM0Seq.compose ChainΓ Λa hΛai Λp hΛpi Ma Mp
  let h12Fi : Inhabited ((Λa ⊕ Λp) ⊕ FinalizeSt) :=
    ⟨Sum.inl (@default _ h12i)⟩
  let M12F : TM0.Machine ChainΓ ((Λa ⊕ Λp) ⊕ FinalizeSt) :=
    @TM0Seq.compose ChainΓ (Λa ⊕ Λp) h12i FinalizeSt inferInstance
      M12 finalizeMachine
  refine ⟨(Λa ⊕ Λp) ⊕ FinalizeSt, h12Fi, inferInstance, M12F,
    Sum.inr FinalizeSt.done, ?_⟩
  intro block suffix hInv hblock hsuffix hstep_nd
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have hreconstruct :
      block = acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ :: fuel := by
    simpa [hsplit, hrest, List.append_assoc] using
      binMulPairedStateInv3_reconstruct block hInv
  let pref := acc ++ binMulStateSep₁ :: addend
  let pref' := binAddPairedKeepRightSep binMulStateSep₁ pref
  have hacc_nd : ∀ x ∈ acc, x ≠ (default : ChainΓ) := by
    intro x hx
    exact binMulPairedStateInv3_acc_ne_default block hblock x
      (by simpa [hsplit] using hx)
  have hacc_no_sep₁ : ∀ x ∈ acc, x ≠ binMulStateSep₁ := by
    simpa [hsplit] using binMulPairedStateInv3_acc_no_sep₁ block hInv
  have hacc_no_sep₂ : ∀ x ∈ acc, x ≠ binMulStateSep₂ := by
    simpa [hsplit] using binMulPairedStateInv3_acc_no_sep₂ block hInv
  have hacc_no_consBottom : ∀ x ∈ acc, x ≠ chainConsBottom := by
    simpa [hsplit] using binMulPairedStateInv3_acc_no_consBottom block hInv
  have hadd_nd : ∀ x ∈ addend, x ≠ (default : ChainΓ) := by
    intro x hx
    exact binMulPairedStateInv3_addend_ne_default block hblock x
      (by simpa [hsplit, hrest] using hx)
  have hadd_no_sep₁ : ∀ x ∈ addend, x ≠ binMulStateSep₁ := by
    simpa [hsplit, hrest] using binMulPairedStateInv3_addend_no_sep₁ block hInv
  have hadd_no_sep₂ : ∀ x ∈ addend, x ≠ binMulStateSep₂ := by
    simpa [hsplit, hrest] using binMulPairedStateInv3_addend_no_sep₂ block hInv
  have hadd_no_consBottom : ∀ x ∈ addend, x ≠ chainConsBottom := by
    simpa [hsplit, hrest] using
      binMulPairedStateInv3_addend_no_consBottom block hInv
  have hfuel_nd : ∀ x ∈ fuel, x ≠ (default : ChainΓ) := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_ne_default block hblock
  have hfuel_no_sep₂ : ∀ x ∈ fuel, x ≠ binMulStateSep₂ := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_no_sep₂ block hInv
  have hfuel_no_consBottom : ∀ x ∈ fuel, x ≠ chainConsBottom := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_no_consBottom block hInv
  have hpref_nd : ∀ x ∈ pref, x ≠ (default : ChainΓ) := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact hacc_nd x hx
    · simpa [binMulStateSep₁] using chainMulSep₁_ne_default
    · exact hadd_nd x hx
  have hpref_no_sep₂ : ∀ x ∈ pref, x ≠ binMulStateSep₂ := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact hacc_no_sep₂ x hx
    · simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂
    · exact hadd_no_sep₂ x hx
  have hpref_no_consBottom : ∀ x ∈ pref, x ≠ chainConsBottom := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact hacc_no_consBottom x hx
    · simpa [binMulStateSep₁] using chainMulSep₁_ne_chainConsBottom
    · exact hadd_no_consBottom x hx
  have hpref'_nd : ∀ x ∈ pref', x ≠ (default : ChainΓ) := by
    exact binAddPairedKeepRightSep_ne_default binMulStateSep₁ pref
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default) hpref_nd
  have hpref'_no_sep₂ : ∀ x ∈ pref', x ≠ binMulStateSep₂ := by
    exact binAddPairedKeepRightSep_no_mulSep₂ pref hpref_no_sep₂
  have hpref'_no_consBottom : ∀ x ∈ pref', x ≠ chainConsBottom := by
    exact binAddPairedKeepRightSep_no_consBottom binMulStateSep₁ pref
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_chainConsBottom)
      hpref_no_consBottom
  have hpred_nd : ∀ x ∈ binPred fuel, x ≠ (default : ChainΓ) :=
    binPred_ne_default fuel hfuel_nd
  have hpred_no_sep₂ : ∀ x ∈ binPred fuel, x ≠ binMulStateSep₂ :=
    binPred_no_mulSep₂ fuel
  have hpred_no_consBottom : ∀ x ∈ binPred fuel, x ≠ chainConsBottom :=
    binPred_no_consBottom fuel
  obtain ⟨ha_dom, ha_tape⟩ :=
    hMa acc addend (fuel ++ default :: suffix)
      hacc_nd hacc_no_sep₁ hacc_no_consBottom hacc_no_sep₂
      hadd_nd hadd_no_sep₁ hadd_no_consBottom hadd_no_sep₂
      (by
        have := binAddPairedKeepRightSep_ne_default binMulStateSep₁
          (acc ++ binMulStateSep₁ :: addend)
        simpa [pref] using this
          (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default) hpref_nd)
  have hinput :
      block ++ default :: suffix =
        acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
          (fuel ++ default :: suffix) := by
    simp [hreconstruct, List.append_assoc]
  have ha_dom' :
      (TM0Seq.evalCfg Ma (block ++ default :: suffix)).Dom := by
    simpa [hinput]
      using ha_dom
  have ha_tape' :
      ((TM0Seq.evalCfg Ma (block ++ default :: suffix)).get ha_dom').Tape =
        Tape.mk₁ (pref' ++ binMulStateSep₂ :: fuel ++ default :: suffix) := by
      have hget :
          (TM0Seq.evalCfg Ma (block ++ default :: suffix)).get ha_dom' =
            (TM0Seq.evalCfg Ma
              (acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ ::
                (fuel ++ default :: suffix))).get ha_dom := by
        apply Part.get_eq_get_of_eq
        simp [hinput]
      rw [hget]
      simpa [pref, pref', List.append_assoc] using ha_tape ha_dom
  obtain ⟨hp_dom, hp_tape⟩ :=
    hMp pref' fuel suffix
      hpref'_nd hpref'_no_consBottom hpref'_no_sep₂
      hfuel_nd hfuel_no_consBottom hfuel_no_sep₂
      hsuffix hpred_nd hpred_no_consBottom hpred_no_sep₂
  have hp_from_cfg :
      (TM0Seq.evalFromCfg Mp
        ⟨default, ((TM0Seq.evalCfg Ma
          (block ++ default :: suffix)).get ha_dom').Tape⟩).Dom := by
    rw [ha_tape']
    change (TM0Seq.evalFromCfg Mp
      (TM0.init (pref' ++ binMulStateSep₂ :: fuel ++ default :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hp_dom
  have hM12_dom :
      (TM0Seq.evalCfg M12 (block ++ default :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M12 (block ++ default :: suffix)).mpr
      (@TM0Seq.compose_dom_of_parts ChainΓ _ Λa hΛai Λp hΛpi
        Ma Mp (block ++ default :: suffix) ha_dom' hp_from_cfg)
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (block ++ default :: suffix)).get hM12_dom).Tape =
        Tape.mk₁ (pref' ++ binMulStateSep₂ :: binPred fuel ++ default :: suffix) := by
    have hcomp_tape :=
      @TM0Seq.compose_evalCfg_tape ChainΓ _ Λa hΛai Λp hΛpi Ma Mp
        (block ++ default :: suffix)
        (pref' ++ binMulStateSep₂ :: fuel ++ default :: suffix)
        ha_dom' ha_tape' hp_dom hM12_dom
    rw [hcomp_tape, hp_tape hp_dom]
  have hstep_eq :
      binMulPairedStep3 block =
        pref' ++ binMulStateSep₂ :: binPred fuel := by
    unfold binMulPairedStep3
    simp [hsplit, hrest, pref, pref', List.append_assoc]
  have hfinal := compose_finalize_evalCfg M12
    (block ++ default :: suffix)
    (binMulPairedStep3 block ++ default :: suffix)
    hM12_dom
    (by
      simpa [hstep_eq, List.append_assoc] using hM12_tape)
  refine ⟨hfinal.1, ?_⟩
  intro h
  have hcfg := hfinal.2 h
  change
    let cfg := (TM0Seq.evalCfg (TM0Seq.compose M12 finalizeMachine)
      (block ++ default :: suffix)).get h
    cfg.q = Sum.inr FinalizeSt.done ∧
      cfg.Tape = Tape.mk₁ (binMulPairedStep3 block ++ default :: suffix)
  rw [hcfg]
  simp

/-- Suffix-preserving conditional body for the three-separator multiplication
step. The condition is decided by the mirrored fuel test after
`binMulStateSep₂`; the continuing branch then runs the unconditional update
machine above. -/
theorem tm0_binMulPairedStep3_blockCondInvSuffix :
    TM0RealizesBlockCondInvSuffix binMulPairedStep3 binMulPairedCond3
      binMulPairedStateInv3 := by
  obtain ⟨Λp, hΛpi, hΛpf, Mp, q_le, q_gt, hne, hp⟩ :=
    tm0_blockValueLeq_afterSep_decidable_2 0 binMulStateSep₂
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
  obtain ⟨Λs, hΛsi, hΛsf, Ms, q_done, hMs⟩ :=
    tm0_binMulPairedStep3_update_blockInvSuffixFixed
  haveI : DecidableEq Λp := Classical.decEq Λp
  let hΛsFi : Inhabited (Λs ⊕ FinalizeSt) := ⟨Sum.inl (@default _ hΛsi)⟩
  let MsF : TM0.Machine ChainΓ (Λs ⊕ FinalizeSt) :=
    @TM0Seq.compose ChainΓ Λs hΛsi FinalizeSt inferInstance Ms finalizeMachine
  let Mcond : TM0.Machine ChainΓ (Λp ⊕ FinalizeSt ⊕ (Λs ⊕ FinalizeSt)) :=
    @tm0CondCompose Λp FinalizeSt (Λs ⊕ FinalizeSt)
      hΛpi inferInstance hΛsFi inferInstance
      Mp finalizeMachine MsF q_le q_gt
  refine ⟨Λp ⊕ FinalizeSt ⊕ (Λs ⊕ FinalizeSt), inferInstance, inferInstance,
    Mcond, Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)), ?_⟩
  intro block suffix hInv hblock hsuffix hstep_nd
  rcases hsplit : splitAtSep binMulStateSep₁ block with ⟨acc, rest⟩
  rcases hrest : splitAtSep binMulStateSep₂ rest with ⟨addend, fuel⟩
  have hreconstruct :
      block = acc ++ binMulStateSep₁ :: addend ++ binMulStateSep₂ :: fuel := by
    simpa [hsplit, hrest, List.append_assoc] using
      binMulPairedStateInv3_reconstruct block hInv
  let pref := acc ++ binMulStateSep₁ :: addend
  have hpref_nd : ∀ x ∈ pref, x ≠ (default : ChainΓ) := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact binMulPairedStateInv3_acc_ne_default block hblock x (by simpa [hsplit] using hx)
    · simpa [binMulStateSep₁] using chainMulSep₁_ne_default
    · exact binMulPairedStateInv3_addend_ne_default block hblock x (by
        simpa [hsplit, hrest] using hx)
  have hpref_no_sep₂ : ∀ x ∈ pref, x ≠ binMulStateSep₂ := by
    intro x hx
    simp [pref] at hx
    rcases hx with hx | rfl | hx
    · exact binMulPairedStateInv3_acc_no_sep₂ block hInv x (by simpa [hsplit] using hx)
    · simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂
    · exact binMulPairedStateInv3_addend_no_sep₂ block hInv x (by
        simpa [hsplit, hrest] using hx)
  have hfuel_nd : ∀ x ∈ fuel, x ≠ (default : ChainΓ) := by
    simpa [binMulPairedFuel3, hsplit, hrest] using
      binMulPairedStateInv3_fuel_ne_default block hblock
  obtain ⟨hp_dom, hp_spec⟩ := hp pref fuel suffix hpref_nd hpref_no_sep₂ hfuel_nd hsuffix
  have hinput :
      pref ++ binMulStateSep₂ :: fuel ++ default :: suffix =
        block ++ default :: suffix := by
    simp [pref, hreconstruct, List.append_assoc]
  have hp_dom_block : (TM0Seq.evalCfg Mp (block ++ default :: suffix)).Dom := by
    simpa [hinput] using hp_dom
  set cp := (TM0Seq.evalCfg Mp (block ++ default :: suffix)).get hp_dom_block
  have hcp_get :
      cp =
        (TM0Seq.evalCfg Mp
          (pref ++ binMulStateSep₂ :: fuel ++ default :: suffix)).get hp_dom := by
    apply Part.get_eq_get_of_eq
    simp [hinput]
  have hcp_tape : cp.Tape = Tape.mk₁ (block ++ default :: suffix) := by
    rw [hcp_get]
    simpa [hinput] using (hp_spec hp_dom).1
  have hq_le :
      blockValueLeq 0 fuel → cp.q = q_le := by
    intro hle
    rw [hcp_get]
    exact (hp_spec hp_dom).2.1 hle
  have hq_gt :
      ¬ blockValueLeq 0 fuel → cp.q = q_gt := by
    intro hle
    rw [hcp_get]
    exact (hp_spec hp_dom).2.2 hle
  have hcond_iff :
      binMulPairedCond3 block ↔ ¬ blockValueLeq 0 fuel := by
    simp [binMulPairedCond3, binMulPairedFuel3, hsplit, hrest]
  have hcp_mem : cp ∈ TM0Seq.evalCfg Mp (block ++ default :: suffix) :=
    Part.get_mem hp_dom_block
  have hcp_eval := Turing.mem_eval.mp hcp_mem
  have hcp_halt : TM0.step Mp cp = none := hcp_eval.2
  have hcp_reaches : Reaches (TM0.step Mp)
      (TM0.init (block ++ default :: suffix)) cp := hcp_eval.1
  have hphase1 := condCompose_phase1_reaches Mp finalizeMachine MsF q_le q_gt
    cp (block ++ default :: suffix) hcp_reaches
  change Reaches (TM0.step Mcond) (TM0.init (block ++ default :: suffix))
    { q := Sum.inl cp.q, Tape := cp.Tape } at hphase1
  have heval_rewrite :
      TM0Seq.evalCfg Mcond (block ++ default :: suffix) =
        Turing.eval (TM0.step Mcond) ⟨Sum.inl cp.q, cp.Tape⟩ := by
    exact Turing.reaches_eval hphase1
  by_cases hcond : binMulPairedCond3 block
  · have hq : cp.q = q_gt := hq_gt (hcond_iff.mp hcond)
    have hhalt_q : TM0.step Mp ⟨q_gt, cp.Tape⟩ = none := hq ▸ hcp_halt
    have hstep_block_nd : ∀ g ∈ binMulPairedStep3 block, g ≠ default :=
      hstep_nd hcond
    obtain ⟨hMs_dom, hMs_spec⟩ :=
      hMs block suffix hInv hblock hsuffix hstep_block_nd
    have hfinal := compose_finalize_evalCfg Ms (block ++ default :: suffix)
      (binMulPairedStep3 block ++ default :: suffix)
      hMs_dom (hMs_spec hMs_dom).2
    have hbranch_dom :
        (TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩).Dom := by
      rw [hcp_tape]
      change (TM0Seq.evalFromCfg MsF
        (TM0.init (block ++ default :: suffix))).Dom
      rw [TM0Seq.evalFromCfg_init]
      exact hfinal.1
    have hbranch_spec :
        ∀ h, (TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩).get h =
          ⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (binMulPairedStep3 block ++ default :: suffix)⟩ := by
      intro h
      have heq :
          TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩ =
            TM0Seq.evalCfg MsF (block ++ default :: suffix) := by
        rw [hcp_tape]
        exact TM0Seq.evalFromCfg_init (M := MsF)
          (l := block ++ default :: suffix)
      have hget :
          (TM0Seq.evalFromCfg MsF ⟨default, cp.Tape⟩).get h =
            (TM0Seq.evalCfg MsF (block ++ default :: suffix)).get hfinal.1 := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hfinal.2 hfinal.1
    have hbranch_step :
        ∃ c₂, TM0.step MsF ⟨default, cp.Tape⟩ = some c₂ := by
      rw [hcp_tape]
      change ∃ c₂, TM0.step MsF (TM0.init (block ++ default :: suffix)) = some c₂
      change ∃ c₂, TM0.step MsF
        ⟨default, Tape.mk₁ (block ++ default :: suffix)⟩ = some c₂
      rcases hfirst : TM0.step Ms
          ⟨default, Tape.mk₁ (block ++ default :: suffix)⟩ with _ | c₂
      · refine ⟨(⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (block ++ default :: suffix)⟩ :
            TM0.Cfg ChainΓ (Λs ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λs hΛsi FinalizeSt inferInstance
          Ms finalizeMachine) ⟨Sum.inl default,
            Tape.mk₁ (block ++ default :: suffix)⟩ =
          some ⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (block ++ default :: suffix)⟩
        rw [TM0Seq.compose_step_on_halt Ms finalizeMachine default
          (Tape.mk₁ (block ++ default :: suffix)) hfirst]
        change Option.map
          (fun c₂ : TM0.Cfg ChainΓ FinalizeSt =>
            ({ q := Sum.inr c₂.q, Tape := c₂.Tape } :
              TM0.Cfg ChainΓ (Λs ⊕ FinalizeSt)))
          (TM0.step finalizeMachine
            ⟨FinalizeSt.start, Tape.mk₁ (block ++ default :: suffix)⟩) =
          some ⟨Sum.inr FinalizeSt.done,
            Tape.mk₁ (block ++ default :: suffix)⟩
        rw [finalize_step_start]
        rfl
      · refine ⟨(⟨Sum.inl c₂.q, c₂.Tape⟩ :
            TM0.Cfg ChainΓ (Λs ⊕ FinalizeSt)), ?_⟩
        change TM0.step (@TM0Seq.compose ChainΓ Λs hΛsi FinalizeSt inferInstance
          Ms finalizeMachine) ⟨Sum.inl default,
            Tape.mk₁ (block ++ default :: suffix)⟩ =
          some ⟨Sum.inl c₂.q, c₂.Tape⟩
        simpa using TM0Seq.compose_step_inl Ms finalizeMachine
          (⟨default, Tape.mk₁ (block ++ default :: suffix)⟩ :
            TM0.Cfg ChainΓ Λs) c₂ hfirst
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MsF q_le q_gt))
        ⟨Sum.inl q_gt, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_false Mp finalizeMachine MsF q_le q_gt hne
        cp.Tape hhalt_q).mpr hbranch_dom
    have hdom : (TM0Seq.evalCfg Mcond (block ++ default :: suffix)).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_false_of_step
      Mp finalizeMachine MsF q_le q_gt hne (Sum.inr FinalizeSt.done) cp.Tape
      (Tape.mk₁ (binMulPairedStep3 block ++ default :: suffix))
      hhalt_q hbranch_step hbranch_dom hbranch_spec
    have hcfg' : (TM0Seq.evalCfg Mcond (block ++ default :: suffix)).get h =
        ⟨Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)),
          Tape.mk₁ (binMulPairedStep3 block ++ default :: suffix)⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond (block ++ default :: suffix) =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond (block ++ default :: suffix)).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_gt, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    simp [hcond, hcfg']
  · have hle : blockValueLeq 0 fuel := by
      by_contra hle
      exact hcond (hcond_iff.mpr hle)
    have hq : cp.q = q_le := hq_le hle
    have hhalt_q : TM0.step Mp ⟨q_le, cp.Tape⟩ = none := hq ▸ hcp_halt
    obtain ⟨hid_dom, hid_spec⟩ := finalize_evalFromCfg cp.Tape
    have hid_step : ∃ c₂, TM0.step finalizeMachine ⟨default, cp.Tape⟩ = some c₂ := by
      exact ⟨⟨FinalizeSt.done, cp.Tape⟩, finalize_step_start cp.Tape⟩
    have hbranch_eval_dom :
        (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).Dom := by
      change (Turing.eval
        (TM0.step (tm0CondCompose Mp finalizeMachine MsF q_le q_gt))
        ⟨Sum.inl q_le, cp.Tape⟩).Dom
      exact (condCompose_eval_at_halt_true Mp finalizeMachine MsF q_le q_gt
        cp.Tape hhalt_q).mpr hid_dom
    have hdom : (TM0Seq.evalCfg Mcond (block ++ default :: suffix)).Dom := by
      rw [heval_rewrite, hq]
      exact hbranch_eval_dom
    refine ⟨hdom, ?_⟩
    intro h
    have hcfg := condCompose_fixed_at_halt_true_of_step
      Mp finalizeMachine MsF q_le q_gt FinalizeSt.done cp.Tape cp.Tape
      hhalt_q hid_step hid_dom (fun h => hid_spec h)
    have hcfg' : (TM0Seq.evalCfg Mcond (block ++ default :: suffix)).get h =
        ⟨Sum.inr (Sum.inl FinalizeSt.done), cp.Tape⟩ := by
      have heq :
          TM0Seq.evalCfg Mcond (block ++ default :: suffix) =
            Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩ := by
        rw [heval_rewrite, hq]
      have hget :
          (TM0Seq.evalCfg Mcond (block ++ default :: suffix)).get h =
            (Turing.eval (TM0.step Mcond) ⟨Sum.inl q_le, cp.Tape⟩).get
              hbranch_eval_dom := by
        apply Part.get_eq_get_of_eq
        exact heq
      rw [hget]
      exact hcfg hbranch_eval_dom
    have hq_ne :
        Sum.inr (Sum.inl FinalizeSt.done) ≠
          (Sum.inr (Sum.inr (Sum.inr FinalizeSt.done)) :
            Λp ⊕ FinalizeSt ⊕ (Λs ⊕ FinalizeSt)) := by
      simp
    simp [hcond, hcfg', hq_ne, hcp_tape]
