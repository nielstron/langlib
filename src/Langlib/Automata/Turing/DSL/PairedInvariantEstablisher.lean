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
`fuel ++ default :: suffix`, so requiring it to be blank-free would be the
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

/-- TODO: generalize the paired-add-keep-right machine to an arbitrary internal
paired separator and a distinct outer separator. This is the real machine
obligation; concrete multiplication separators should only be specializations
of this theorem. -/
theorem tm0_binAddPairedKeepRightSep_beforeSep
    {pairSep outerSep : ChainΓ}
    (hpair_nd : pairSep ≠ default)
    (houter_nd : outerSep ≠ default)
    (hpair_outer : pairSep ≠ outerSep) :
    TM0RealizesPairedBlockBeforeSep pairSep outerSep
      (binAddPairedKeepRightSep pairSep) := by
  sorry

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
    {outerSep : ChainΓ}
    (houter_nd : outerSep ≠ default)
    (houter_ne_sep₂ : outerSep ≠ binMulStateSep₂) :
    ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
      (M : TM0.Machine ChainΓ Λ),
      ∀ (acc addend fuel suffix : List ChainΓ),
        (∀ g ∈ acc, g ≠ default) →
        (∀ g ∈ acc, g ≠ binMulStateSep₁) →
        (∀ g ∈ acc, g ≠ binMulStateSep₂) →
        (∀ g ∈ addend, g ≠ default) →
        (∀ g ∈ addend, g ≠ binMulStateSep₁) →
        (∀ g ∈ addend, g ≠ binMulStateSep₂) →
        (∀ g ∈ fuel, g ≠ default) →
        (∀ g ∈ fuel, g ≠ outerSep) →
        (∀ g ∈ fuel, g ≠ binMulStateSep₂) →
        (∀ g ∈ suffix, g ≠ default) →
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
    tm0_binAddPairedKeepRightSep_beforeSep
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default)
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
      (by simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂)
  obtain ⟨Λp, hΛpi, hΛpf, Mp, hMp⟩ :=
    tm0_binPred_afterMulSep₂_innerBlockSep_outer
      houter_nd houter_ne_sep₂
  let h12i : Inhabited (Λa ⊕ Λp) := ⟨Sum.inl (@default _ hΛai)⟩
  let M12 : TM0.Machine ChainΓ (Λa ⊕ Λp) :=
    @TM0Seq.compose ChainΓ Λa hΛai Λp hΛpi Ma Mp
  refine ⟨Λa ⊕ Λp, h12i, inferInstance, M12, ?_⟩
  intro acc addend fuel suffix
    hacc_nd hacc_no_sep₁ hacc_no_sep₂
    hadd_nd hadd_no_sep₁ hadd_no_sep₂
    hfuel_nd hfuel_no_outer hfuel_no_sep₂ hsuffix_nd
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
      hacc_nd hacc_no_sep₁ hacc_no_sep₂
      hadd_nd hadd_no_sep₁ hadd_no_sep₂
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
      hsuffix_nd hpred_nd hpred_no_outer hpred_no_sep₂
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
    tm0_binAddPairedKeepRightSep_beforeSep
      (by simpa [binMulStateSep₁] using chainMulSep₁_ne_default)
      (by simpa [binMulStateSep₂] using chainMulSep₂_ne_default)
      (by simpa [binMulStateSep₁, binMulStateSep₂] using chainMulSep₁_ne_chainMulSep₂)
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
      hacc_nd hacc_no_sep₁ hacc_no_sep₂
      hadd_nd hadd_no_sep₁ hadd_no_sep₂
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
