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
