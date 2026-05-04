import Mathlib
import Langlib.Automata.Turing.DSL.TM0Compose
import Langlib.Automata.Turing.DSL.TM0BuildingBlocks
import Langlib.Automata.Turing.DSL.ReverseBlock

/-! # Block Realizability Framework

This file defines block-realizability abstractions for composing TM0 machines
that operate on contiguous blocks.

## Main definitions

- `TM0RealizesBlockSep Γ sep f`: a TM0 machine processes the cells before
  the first designated separator `sep`, preserving the separator and tail.
- `TM0RealizesBlock Γ f`: the old blank-delimited specialization where
  `sep = default`.

## Main results

- `tm0RealizesBlock_comp`: sequential composition of block-realizable functions
- `tm0RealizesBlock_iterate`: iterated application
- `tm0_reverse_block`: list reverse is block-realizable
- `tm0_cons_block`: prepending a constant is block-realizable
-/

open Turing

/-! ### Block Realizability Definitions -/

/-- A TM0 that operates on a block ending at a designated separator.

Given a tape `block ++ [sep] ++ suffix`, the TM0 transforms it to
`f block ++ [sep] ++ suffix`. The assumptions state that the input block is
really the part before the first separator, that the active finite tape has no
interior blanks, and that `f block` is again a valid block for the same
separator. -/
def TM0RealizesBlockSep (Γ : Type) [Inhabited Γ] (sep : Γ)
    (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (block suffix : List Γ),
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ block, g ≠ sep) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f block, g ≠ default) →
      (∀ g ∈ f block, g ≠ sep) →
      (TM0Seq.evalCfg M (block ++ sep :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ sep :: suffix)).Dom),
        ((TM0Seq.evalCfg M (block ++ sep :: suffix)).get h).Tape =
          Tape.mk₁ (f block ++ sep :: suffix)

/-- A TM0 that operates on a contiguous block of non-default cells,
    preserving everything after the first blank.

    Given a tape `block ++ [default] ++ suffix`, the TM0 transforms
    it to `f(block) ++ [default] ++ suffix`, leaving suffix unchanged.
    This enables "serialized" composition of elementary operations. -/
def TM0RealizesBlock (Γ : Type) [Inhabited Γ] (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (block suffix : List Γ),
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f block, g ≠ default) →
      (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (block ++ default :: suffix)).Dom),
        ((TM0Seq.evalCfg M (block ++ default :: suffix)).get h).Tape =
          Tape.mk₁ (f block ++ default :: suffix)

theorem tm0RealizesBlockSep_default_of_block {Γ : Type} [Inhabited Γ]
    {f : List Γ → List Γ} (hf : TM0RealizesBlock Γ f) :
    TM0RealizesBlockSep Γ default f := by
  obtain ⟨Λ, hΛ, hΛfin, M, hM⟩ := hf
  exact ⟨Λ, hΛ, hΛfin, M, fun block suffix hblock _hblock_sep hsuffix hfblock _hfblock_sep =>
    hM block suffix hblock hsuffix hfblock⟩

theorem tm0RealizesBlock_of_sep_default {Γ : Type} [Inhabited Γ]
    {f : List Γ → List Γ} (hf : TM0RealizesBlockSep Γ default f) :
    TM0RealizesBlock Γ f := by
  obtain ⟨Λ, hΛ, hΛfin, M, hM⟩ := hf
  exact ⟨Λ, hΛ, hΛfin, M, fun block suffix hblock hsuffix hfblock =>
    hM block suffix hblock hblock hsuffix hfblock hfblock⟩

/-! ### Composition -/

/-- Composition for separator-delimited block-realizable functions. -/
theorem tm0RealizesBlockSep_comp {Γ : Type} [Inhabited Γ]
    {sep : Γ} {f g : List Γ → List Γ}
    (hf : TM0RealizesBlockSep Γ sep f) (hg : TM0RealizesBlockSep Γ sep g)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep) → ∀ g ∈ f block, g ≠ sep) :
    TM0RealizesBlockSep Γ sep (g ∘ f) := by
  apply Classical.byContradiction
  intro h_contra
  obtain ⟨Λ_f, h_f_inhabited, h_f_fintype, M_f, hM_f⟩ := hf
  obtain ⟨Λ_g, h_g_inhabited, h_g_fintype, M_g, hM_g⟩ := hg
  refine' h_contra ⟨_, _, _, TM0Seq.compose M_f M_g, _⟩
  · infer_instance
  · intro block suffix hblock_nd hblock_nsep hsuffix hgf_nd hgf_nsep
    obtain ⟨hM_f_dom, hM_f_tape⟩ :=
      hM_f block suffix hblock_nd hblock_nsep hsuffix
        (hf_nd block hblock_nd) (hf_nsep block hblock_nsep)
    obtain ⟨hM_g_dom, hM_g_tape⟩ :=
      hM_g (f block) suffix (hf_nd block hblock_nd) (hf_nsep block hblock_nsep)
        hsuffix hgf_nd hgf_nsep
    refine' ⟨_, _⟩
    · apply TM0Seq.compose_dom_of_parts
      any_goals assumption
      convert hM_g_dom using 1
      exact hM_f_tape hM_f_dom ▸ rfl
    · intro h
      convert TM0Seq.compose_evalCfg_tape M_f M_g
        (block ++ sep :: suffix) (f block ++ sep :: suffix)
        hM_f_dom (hM_f_tape hM_f_dom) hM_g_dom h using 1
      exact hM_g_tape hM_g_dom ▸ rfl

/-- Composition of block-realizable functions.
    Requires `f` to preserve non-defaultness so that `M_g` can process
    `f(block)` as a valid block. -/
theorem tm0RealizesBlock_comp {Γ : Type} [Inhabited Γ]
    {f g : List Γ → List Γ}
    (hf : TM0RealizesBlock Γ f) (hg : TM0RealizesBlock Γ g)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default) :
    TM0RealizesBlock Γ (g ∘ f) := by
  apply Classical.byContradiction
  intro h_contra;
  obtain ⟨ Λ_f, h_f_inhabited, h_f_fintype, M_f, hM_f ⟩ := hf
  obtain ⟨ Λ_g, h_g_inhabited, h_g_fintype, M_g, hM_g ⟩ := hg;
  refine' h_contra ⟨ _, _, _, TM0Seq.compose M_f M_g, _ ⟩;
  · infer_instance;
  · intro block suffix hblock hsuffix hgf
    obtain ⟨hM_f_dom, hM_f_tape⟩ := hM_f block suffix hblock hsuffix (hf_nd block hblock)
    obtain ⟨hM_g_dom, hM_g_tape⟩ := hM_g (f block) suffix (hf_nd block hblock) hsuffix hgf;
    refine' ⟨ _, _ ⟩;
    · apply TM0Seq.compose_dom_of_parts;
      any_goals assumption;
      convert hM_g_dom using 1;
      exact hM_f_tape hM_f_dom ▸ rfl;
    · intro h;
      convert TM0Seq.compose_evalCfg_tape M_f M_g ( block ++ default :: suffix ) ( f block ++ default :: suffix ) hM_f_dom ( hM_f_tape hM_f_dom ) hM_g_dom h using 1;
      exact hM_g_tape hM_g_dom ▸ rfl

/-! ### Iteration -/

/-- Iterated separator-delimited block operations preserve realizability. -/
theorem tm0RealizesBlockSep_iterate {Γ : Type} [Inhabited Γ]
    {sep : Γ} {f : List Γ → List Γ} (hf : TM0RealizesBlockSep Γ sep f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep) → ∀ g ∈ f block, g ≠ sep)
    (n : ℕ) :
    TM0RealizesBlockSep Γ sep (Nat.iterate f n) := by
  induction' n with n ih
  · refine' ⟨Fin 2, inferInstance, inferInstance, fun _ _ => none, ?_⟩
    intro block suffix hblock_nd hblock_nsep hsuffix hfblock_nd hfblock_nsep
    unfold TM0Seq.evalCfg
    simp +decide [TM0Seq.evalCfg]
    unfold eval
    simp +decide [TM0.step]
    unfold PFun.fix
    simp +decide [TM0.init]
    grind +suggestions
  · convert tm0RealizesBlockSep_comp hf ih hf_nd hf_nsep using 1

/-- Iterated block operations preserve block-realizability. -/
theorem tm0RealizesBlock_iterate {Γ : Type} [Inhabited Γ]
    {f : List Γ → List Γ} (hf : TM0RealizesBlock Γ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (n : ℕ) :
    TM0RealizesBlock Γ (Nat.iterate f n) := by
  induction' n with n ih;
  · refine' ⟨ _, _, _, _, _ ⟩;
    exact Fin 2;
    exact inferInstance;
    exact inferInstance;
    exact fun _ _ => none;
    unfold TM0Seq.evalCfg; simp +decide [ TM0Seq.evalCfg ] ;
    unfold eval; simp +decide [ TM0.step ] ;
    unfold PFun.fix; simp +decide [ TM0.init ] ;
    grind +suggestions;
  · convert tm0RealizesBlock_comp hf ih _ using 1;
    exact hf_nd

/-- Iteration of a non-defaultness-preserving function preserves non-defaultness. -/
theorem iterate_preserves_nd {Γ₀ : Type} [Inhabited Γ₀]
    {f : List Γ₀ → List Γ₀}
    (hf : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (n : ℕ) (block : List Γ₀) (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ f^[n] block, g ≠ default := by
  induction' n with n ih generalizing block <;> simp_all +decide [ Function.iterate_succ_apply' ];
  exact hf _ ( ih _ hblock )

/-- Iteration preserves the "not equal to separator" invariant. -/
theorem iterate_preserves_nsep {Γ₀ : Type} [Inhabited Γ₀]
    {f : List Γ₀ → List Γ₀} {sep : Γ₀}
    (hf : ∀ block, (∀ g ∈ block, g ≠ sep) → ∀ g ∈ f block, g ≠ sep)
    (n : ℕ) (block : List Γ₀) (hblock : ∀ g ∈ block, g ≠ sep) :
    ∀ g ∈ f^[n] block, g ≠ sep := by
  induction' n with n ih generalizing block <;> simp_all +decide [ Function.iterate_succ_apply' ];
  exact hf _ ( ih _ hblock )

/-! ### Utility Lemmas -/

/-- Generic: appending default to a ListBlank is identity. -/
theorem listBlank_mk_append_default {Γ : Type} [Inhabited Γ] (l : List Γ) :
    (ListBlank.mk (l ++ [default]) : ListBlank Γ) = ListBlank.mk l := by
  apply Quot.sound; exact Or.inr ⟨1, by simp⟩

/-- Generic: Tape.mk₁ with trailing default is identity. -/
theorem tape_mk₁_append_default {Γ : Type} [Inhabited Γ] (l : List Γ) :
    Tape.mk₁ (l ++ [default]) = (Tape.mk₁ l : Tape Γ) := by
  cases l with
  | nil => simp [Tape.mk₁, Tape.mk₂, Tape.mk']
  | cons a l => simp [Tape.mk₁, Tape.mk₂, Tape.mk']; exact listBlank_mk_append_default l

/-- TM0Seq.evalCfg with trailing default input is the same. -/
theorem evalCfg_append_default {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : TM0.Machine Γ Λ) (l : List Γ) :
    TM0Seq.evalCfg M (l ++ [default]) = TM0Seq.evalCfg M l := by
  unfold TM0Seq.evalCfg; congr 1; unfold TM0.init; congr 1
  exact tape_mk₁_append_default l

/-- Reverse preserves non-defaultness. -/
theorem reverse_ne_default {Γ : Type} [Inhabited Γ]
    (block : List Γ) (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ block.reverse, g ≠ default := by
  simp_all

/-! ### Reverse is block-realizable -/

/-- List reverse is block-realizable. A TM0 can reverse a contiguous
    block of non-default cells while preserving the suffix. -/
theorem tm0_reverse_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ] :
    TM0RealizesBlock Γ List.reverse := by
  use RevBlock.RSt Γ, inferInstance, inferInstance, RevBlock.M Γ
  intro block suffix hblock hsuffix hfblock
  have h_reaches := RevBlock.full_reaches block suffix hblock hsuffix
  constructor
  · apply Part.dom_iff_mem.mpr
    exact ⟨_, Turing.mem_eval.mpr ⟨h_reaches, RevBlock.step_rewindDone _⟩⟩
  · intro h
    have h_mem := Part.get_mem h
    have h_eval := Turing.mem_eval.mpr ⟨h_reaches, RevBlock.step_rewindDone _⟩
    exact (Part.mem_unique h_mem h_eval).symm ▸ rfl

/-! ### Cons (prepend) is block-realizable -/

/-- The simple cons machine: move left, write c, halt.
    Prepends `c` to the tape by writing at position −1. -/
noncomputable def consSimpleMachine {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (c : Γ) : @TM0.Machine Γ (Fin 3) ⟨0⟩ := fun q _ =>
  match q with
  | (0 : Fin 3) => some (1, TM0.Stmt.move Dir.left)
  | (1 : Fin 3) => some (2, TM0.Stmt.write c)
  | (2 : Fin 3) => none

theorem consSimpleMachine_halts {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (c : Γ) (l : List Γ) :
    (TM0Seq.evalCfg (consSimpleMachine c) l).Dom := by
  refine' Part.dom_iff_mem.mpr _
  refine' ⟨ _, Turing.mem_eval.mpr ⟨ _, _ ⟩ ⟩
  exact ⟨ 2, Tape.write c ( Tape.move Dir.left ( Tape.mk₁ l ) ) ⟩
  · refine' Relation.ReflTransGen.head _ _
    exact ⟨ 1, Tape.move Dir.left ( Tape.mk₁ l ) ⟩
    · exact?
    · exact .single ( by tauto )
  · exact?

/-- Writing c after moving left from `Tape.mk₁ l` gives `Tape.mk₁ (c :: l)`. -/
theorem tape_write_move_left_mk₁ {Γ : Type} [Inhabited Γ]
    (c : Γ) (l : List Γ) :
    Tape.write c (Tape.move Dir.left (Tape.mk₁ l)) = Tape.mk₁ (c :: l) := by
  cases l <;> simp [Tape.mk₁, ListBlank.mk, Tape.move, Tape.write];
  · unfold Tape.mk₂;
    unfold Tape.mk'; simp +decide [ ListBlank.mk ] ;
    exact ⟨ rfl, rfl, rfl ⟩;
  · congr

theorem consSimpleMachine_eval_eq {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (c : Γ) (l : List Γ) :
    ⟨(2 : Fin 3), Tape.write c (Tape.move Dir.left (Tape.mk₁ l))⟩ ∈
      TM0Seq.evalCfg (consSimpleMachine c) l := by
  refine' Turing.mem_eval.mpr _
  unfold consSimpleMachine; simp +decide [ TM0.step ]
  constructor
  rotate_right
  exact ⟨ 1, Tape.move Dir.left ( Tape.mk₁ l ) ⟩
  · apply_rules [ Relation.ReflTransGen.single ]
  · exact?

theorem consSimpleMachine_tape {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (c : Γ) (l : List Γ)
    (h : (TM0Seq.evalCfg (consSimpleMachine c) l).Dom) :
    ((TM0Seq.evalCfg (consSimpleMachine c) l).get h).Tape =
      Tape.mk₁ (c :: l) := by
  have hmem := consSimpleMachine_eval_eq c l
  rw [Part.mem_unique (Part.get_mem h) hmem]
  exact tape_write_move_left_mk₁ c l

/-- Prepending a fixed element is block-realizable before any separator.

The cons machine (`consSimpleMachine`) moves left, writes `c`, and halts.
It never inspects any cell to detect a block boundary, so it works with
any separator. -/
theorem tm0_cons_blockSep {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} (c : Γ) :
    TM0RealizesBlockSep Γ sep (c :: ·) := by
  refine ⟨Fin 3, ⟨0⟩, inferInstance, consSimpleMachine c,
    fun block suffix _hblock_nd _hblock_nsep _hsuffix _hfblock_nd _hfblock_nsep => ?_⟩
  exact ⟨consSimpleMachine_halts c _,
    fun h => by rw [consSimpleMachine_tape]; simp⟩

/-- Prepending a fixed non-default element is block-realizable. -/
theorem tm0_cons_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (c : Γ) (_hc : c ≠ default) :
    TM0RealizesBlock Γ (c :: ·) :=
  tm0RealizesBlock_of_sep_default (tm0_cons_blockSep c)

/-! ### Identity is block-realizable -/

/-- The identity function is realizable before any separator.

A trivial TM0 machine that halts immediately on any input tape. -/
theorem tm0_id_blockSep {Γ : Type} [Inhabited Γ]
    {sep : Γ} :
    TM0RealizesBlockSep Γ sep id := by
  refine ⟨Fin 2, inferInstance, inferInstance, fun _ _ => none, ?_⟩
  intro block suffix _hblock_nd _hblock_nsep _hsuffix _hfblock_nd _hfblock_nsep
  unfold TM0Seq.evalCfg
  simp +decide [TM0Seq.evalCfg]
  unfold eval
  simp +decide [TM0.step]
  unfold PFun.fix
  simp +decide [TM0.init]
  grind +suggestions

/-- The identity function is block-realizable. -/
theorem tm0_id_block {Γ : Type} [Inhabited Γ] :
    TM0RealizesBlock Γ id :=
  tm0RealizesBlock_of_sep_default tm0_id_blockSep

/-! ### Prepend list is block-realizable -/

/-- Appending a non-default prefix preserves non-defaultness. -/
theorem prependList_ne_default' {Γ : Type} [Inhabited Γ] (pref block : List Γ)
    (hpref : ∀ g ∈ pref, g ≠ default)
    (hblock : ∀ g ∈ block, g ≠ default) :
    ∀ g ∈ pref ++ block, g ≠ default := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hpref g hg
  · exact hblock g hg

/-- Reverse preserves the "not equal to separator" invariant. -/
theorem reverse_ne_sep {Γ : Type}
    {sep : Γ} (block : List Γ) (hblock : ∀ g ∈ block, g ≠ sep) :
    ∀ g ∈ block.reverse, g ≠ sep := by
  simp_all

/-- Prepending a fixed non-default, non-sep list is realizable before a separator. -/
theorem tm0_prependList_blockSep {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} (pref : List Γ)
    (hpref_nd : ∀ g ∈ pref, g ≠ default)
    (hpref_nsep : ∀ g ∈ pref, g ≠ sep) :
    TM0RealizesBlockSep Γ sep (fun block => pref ++ block) := by
  induction pref with
  | nil => simpa using (tm0_id_blockSep (Γ := Γ) (sep := sep))
  | cons c rest ih =>
    have hc_nd : c ≠ default := hpref_nd c List.mem_cons_self
    have hc_nsep : c ≠ sep := hpref_nsep c List.mem_cons_self
    have hrest_nd : ∀ g ∈ rest, g ≠ default := fun g hg => hpref_nd g (List.mem_cons_of_mem _ hg)
    have hrest_nsep : ∀ g ∈ rest, g ≠ sep := fun g hg => hpref_nsep g (List.mem_cons_of_mem _ hg)
    have hcomp := tm0RealizesBlockSep_comp (ih hrest_nd hrest_nsep) (tm0_cons_blockSep c)
      (fun block hblock => prependList_ne_default' rest block hrest_nd hblock)
      (fun block hblock g hg => by
        simp [List.mem_append] at hg
        rcases hg with hg | hg
        · exact hrest_nsep g hg
        · exact hblock g hg)
    simpa [Function.comp, List.cons_append] using hcomp
