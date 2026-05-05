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
    (block : List ChainΓ) (_hInv : pairedSepInv block)
    (_hblock : ∀ g ∈ block, g ≠ default) (_hcond : pairedAddCond block) :
    pairedSepInv (pairedDecrLeftIncrRight block) :=
  pairedDecrLeftIncrRight_pairedSepInv block

/-! ## Invariant-restricted block machines

The paired arithmetic body only has to run on default-delimited blocks that
already contain the paired separator.  The following local abstraction keeps
that weaker proof obligation explicit: machines are only specified on blocks
satisfying `blockInv`, and only with the empty suffix shape used by
`tm0RealizesBlock_while_inv`.
-/

def TM0RealizesBlockInv {Γ : Type} [Inhabited Γ]
    (f : List Γ → List Γ) (blockInv : List Γ → Prop) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (block : List Γ),
      blockInv block →
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ f block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ [default])).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ [default])).Dom),
        ((TM0Seq.evalCfg M (block ++ [default])).get h).Tape =
          Tape.mk₁ (f block ++ [default])

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

theorem tm0RealizesBlockInv_comp {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlockInv f blockInv)
    (hg : TM0RealizesBlockInv g blockInv)
    (hf_inv : ∀ block, blockInv block → (∀ x ∈ block, x ≠ default) → blockInv (f block))
    (hf_nd : ∀ block, (∀ x ∈ block, x ≠ default) → ∀ x ∈ f block, x ≠ default) :
    TM0RealizesBlockInv (g ∘ f) blockInv := by
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

theorem tm0RealizesBlockInv_congr {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ} {blockInv : List Γ → Prop}
    (hf : TM0RealizesBlockInv f blockInv)
    (hfg : ∀ block, blockInv block → f block = g block) :
    TM0RealizesBlockInv g blockInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block hInv hblock hgblock
  have hfblock : ∀ x ∈ f block, x ≠ default := by
    simpa [hfg block hInv] using hgblock
  obtain ⟨hdom, htape⟩ := hM block hInv hblock hfblock
  refine ⟨hdom, ?_⟩
  intro h
  rw [htape h, hfg block hInv]

/-- Decrement only the left side of a paired block.  On malformed inputs this
    still uses `splitAtConsBottom`, but the machine theorem below only exposes
    the paired-invariant case. -/
noncomputable def pairedDecrLeftOnly (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  binPred left ++ [chainConsBottom] ++ right

/-- Increment, with normalization, only the right side of a paired block. -/
noncomputable def pairedIncrRightNormalize (block : List ChainΓ) : List ChainΓ :=
  let (left, right) := splitAtConsBottom block
  left ++ [chainConsBottom] ++ (binSucc ∘ normalizeBlock) right

theorem pairedDecrLeftOnly_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ pairedDecrLeftOnly block, g ≠ default := by
  intro g hg
  unfold pairedDecrLeftOnly at hg
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  simp [hsplit] at hg
  rcases hg with hg | rfl | hg
  · exact binPred_ne_default _ (fun x hx =>
      hblock x (splitAtConsBottom_fst_subset block x (by simpa [hsplit] using hx))) g hg
  · exact chainConsBottom_ne_default
  · exact hblock g (splitAtConsBottom_snd_subset block g (by simpa [hsplit] using hg))

theorem pairedIncrRightNormalize_ne_default (block : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ pairedIncrRightNormalize block, g ≠ default := by
  intro g hg
  unfold pairedIncrRightNormalize at hg
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  simp [hsplit] at hg
  rcases hg with hg | rfl | hg
  · exact hblock g (splitAtConsBottom_fst_subset block g (by simpa [hsplit] using hg))
  · exact chainConsBottom_ne_default
  · exact binSucc_ne_default _ (normalizeBlock_ne_default _) g hg

theorem pairedDecrLeftOnly_pairedSepInv (block : List ChainΓ)
    (hInv : pairedSepInv block) :
    pairedSepInv (pairedDecrLeftOnly block) := by
  unfold pairedSepInv hasConsBottom pairedDecrLeftOnly
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  constructor
  · simp
  · intro g hg
    exact hInv.2 g (by simpa [hsplit] using hg)

theorem pairedIncrRightNormalize_pairedSepInv (block : List ChainΓ)
    (_hInv : pairedSepInv block) :
    pairedSepInv (pairedIncrRightNormalize block) := by
  unfold pairedSepInv hasConsBottom pairedIncrRightNormalize
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  have hleft_nsep : ∀ g ∈ left, g ≠ chainConsBottom := by
    simpa [hsplit] using splitAtConsBottom_fst_no_sep block
  constructor
  · simp
  · rw [splitAtConsBottom_general left ((binSucc ∘ normalizeBlock) right) hleft_nsep]
    exact binSucc_no_consBottom _ (normalizeBlock_no_consBottom right)

theorem tm0_pairedDecrLeftOnly_blockInv :
    TM0RealizesBlockInv pairedDecrLeftOnly pairedSepInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0_incBeforeSep_present_blockSep
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block hInv hblock hfblock
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  have hmem : chainConsBottom ∈ block := hInv.1
  have hblock_reconstruct :
      block = left ++ chainConsBottom :: right := by
    simpa [hsplit] using splitAtConsBottom_reconstruct_of_mem block hmem
  have hleft_nd : ∀ g ∈ left, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_left _ hg)
  have hleft_nsep : ∀ g ∈ left, g ≠ chainConsBottom := by
    simpa [hsplit] using splitAtConsBottom_fst_no_sep block
  have hright_nd : ∀ g ∈ right, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have hbinPred_nd : ∀ g ∈ binPred left, g ≠ default :=
    binPred_ne_default left hleft_nd
  have hbinPred_nsep : ∀ g ∈ binPred left, g ≠ chainConsBottom :=
    binPred_no_consBottom left
  obtain ⟨hdom, htape⟩ :=
    hM left right hleft_nd hleft_nsep hright_nd hbinPred_nd hbinPred_nsep
  have hdom' : (TM0Seq.evalCfg M (block ++ [default])).Dom := by
    rw [hblock_reconstruct]
    simpa [List.append_assoc] using
      (show (TM0Seq.evalCfg M ((left ++ chainConsBottom :: right) ++ [default])).Dom from by
        rw [evalCfg_append_default]
        exact hdom)
  refine ⟨hdom', ?_⟩
  intro h
  have hget :
      (TM0Seq.evalCfg M (block ++ [default])).get h =
        (TM0Seq.evalCfg M (left ++ chainConsBottom :: right)).get hdom := by
    apply Part.get_eq_get_of_eq
    rw [hblock_reconstruct]
    simpa [List.append_assoc] using
      (evalCfg_append_default M (left ++ chainConsBottom :: right))
  rw [hget, htape hdom]
  unfold pairedDecrLeftOnly
  rw [hsplit]
  simpa [List.append_assoc] using
    (tape_mk₁_append_default (binPred left ++ chainConsBottom :: right)).symm

theorem tm0_pairedIncrRightNormalize_blockInv :
    TM0RealizesBlockInv pairedIncrRightNormalize pairedSepInv := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := tm0_binSuccNormalize_afterConsBottom_innerDefault
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro block hInv hblock hfblock
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  have hmem : chainConsBottom ∈ block := hInv.1
  have hblock_reconstruct :
      block = left ++ chainConsBottom :: right := by
    simpa [hsplit] using splitAtConsBottom_reconstruct_of_mem block hmem
  have hleft_nd : ∀ g ∈ left, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_left _ hg)
  have hleft_nsep : ∀ g ∈ left, g ≠ chainConsBottom := by
    simpa [hsplit] using splitAtConsBottom_fst_no_sep block
  have hright_nd : ∀ g ∈ right, g ≠ default := by
    intro g hg
    exact hblock g (by
      rw [hblock_reconstruct]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have hright_nsep : ∀ g ∈ right, g ≠ chainConsBottom := by
    intro g hg
    exact hInv.2 g (by simpa [hsplit] using hg)
  have hf_nd : ∀ g ∈ (binSucc ∘ normalizeBlock) right, g ≠ default :=
    binSucc_ne_default _ (normalizeBlock_ne_default right)
  have hf_nsep : ∀ g ∈ (binSucc ∘ normalizeBlock) right, g ≠ chainConsBottom :=
    binSucc_no_consBottom _ (normalizeBlock_no_consBottom right)
  obtain ⟨hdom, htape⟩ :=
    hM left right hleft_nd hleft_nsep hright_nd hright_nsep hf_nd hf_nsep
  have hdom' : (TM0Seq.evalCfg M (block ++ [default])).Dom := by
    rw [hblock_reconstruct]
    simpa [List.append_assoc] using hdom
  refine ⟨hdom', ?_⟩
  intro h
  have hget :
      (TM0Seq.evalCfg M (block ++ [default])).get h =
        (TM0Seq.evalCfg M (left ++ chainConsBottom :: right ++ [default])).get hdom := by
    apply Part.get_eq_get_of_eq
    rw [hblock_reconstruct]
  rw [hget, htape hdom]
  unfold pairedIncrRightNormalize
  rw [hsplit]
  simp [List.append_assoc]

theorem pairedIncrRightNormalize_decrLeftOnly_eq
    (block : List ChainΓ) (_hInv : pairedSepInv block) :
    pairedIncrRightNormalize (pairedDecrLeftOnly block) =
      pairedDecrLeftIncrRight block := by
  rw [pairedDecrLeftIncrRight_eq_binPred_binSuccNormalize]
  unfold pairedIncrRightNormalize pairedDecrLeftOnly
  rcases hsplit : splitAtConsBottom block with ⟨left, right⟩
  simp [Function.comp, List.append_assoc]

/-- The paired transfer step is realizable on blocks satisfying the paired
    separator invariant.  This is the useful machine-level core for the
    invariant while loop: decrement the left sub-block, then increment the
    right sub-block under the default-delimited inner-block lift. -/
theorem tm0_pairedDecrLeftIncrRight_blockInv :
    TM0RealizesBlockInv pairedDecrLeftIncrRight pairedSepInv :=
  tm0RealizesBlockInv_congr
    (tm0RealizesBlockInv_comp
      tm0_pairedDecrLeftOnly_blockInv
      tm0_pairedIncrRightNormalize_blockInv
      (fun block hInv _hblock => pairedDecrLeftOnly_pairedSepInv block hInv)
      pairedDecrLeftOnly_ne_default)
    pairedIncrRightNormalize_decrLeftOnly_eq

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
        exact ih _ (pairedDecrLeftIncrRight_pairedSepInv block)
      · rw [blockIterateWhile_succ_false _ _ _ _ hcond]
        exact hInv

theorem binAddPairedWhile_pairedSepInv
    (block : List ChainΓ)
    (hInv : pairedSepInv block)
    (hblock : ∀ g ∈ block, g ≠ default) :
    pairedSepInv (binAddPairedWhile block) := by
  obtain ⟨n, hn, _hstop⟩ := binAddPairedWhile_eq_iterate block hblock
  rw [hn]
  exact blockIterateWhile_pairedSepInv n block hInv
