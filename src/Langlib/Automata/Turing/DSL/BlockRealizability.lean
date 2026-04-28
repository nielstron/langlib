import Mathlib
import Langlib.Automata.Turing.DSL.TM0Compose
import Langlib.Automata.Turing.DSL.TM0BuildingBlocks
import Langlib.Automata.Turing.DSL.ReverseBlock

/-! # Block Realizability Framework

This file defines `TM0RealizesBlock`, the core abstraction for composing
TM0 machines that operate on contiguous blocks of non-default cells.

## Main definitions

- `TM0RealizesBlock Γ f`: a TM0 machine processes the first contiguous
  block of non-default cells according to `f`, preserving everything
  after the first blank.

## Main results

- `tm0RealizesBlock_comp`: sequential composition of block-realizable functions
- `tm0RealizesBlock_iterate`: iterated application
- `tm0_reverse_block`: list reverse is block-realizable
- `tm0_cons_block`: prepending a constant is block-realizable
-/

open Turing

/-! ### Block Realizability Definition -/

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

/-! ### Composition -/

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

/-- Prepending a fixed non-default element is block-realizable. -/
theorem tm0_cons_block {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (c : Γ) (hc : c ≠ default) :
    TM0RealizesBlock Γ (c :: ·) := by
  refine ⟨Fin 3, ⟨0⟩, inferInstance, consSimpleMachine c,
    fun block suffix hblock hsuffix hcons => ?_⟩
  exact ⟨consSimpleMachine_halts c _,
    fun h => by rw [consSimpleMachine_tape]; simp⟩
