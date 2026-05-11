import Mathlib
import Langlib.Automata.Turing.DSL.TM0Compose
import Langlib.Automata.Turing.DSL.BlockRealizability
import Langlib.Automata.Turing.DSL.ReverseBlock

/-! # Block-Separator Prefix Preservation

This file shows that any `TM0RealizesBlockSep Γ sep f` can be lifted to
operate on an *inner* block of a two-separator tape, preserving the prefix.

## Main definitions

- `TM0RealizesInnerBlockSep Γ sep₁ sep₂ f`: the machine applies `f` to the
  inner block between `sep₂` and `sep₁`, preserving the prefix before `sep₂`.

## Main result

- `tm0RealizesBlockSep_toInnerOuterSep`: any `TM0RealizesBlockSep Γ sep₂ f`
  can be lifted to `TM0RealizesInnerBlockSep Γ sep₁ sep₂ f` when the outer
  separator is non-default.
- `tm0RealizesBlockSep_toInnerDefault`: default-boundary version of the same
  prefix/suffix lift.

## Strategy

The construction composes five sub-machines (three distinct):

1. **Reverse** (sep₁-delimited): reverses the outer block, bringing
   `inner.reverse` to the front where the left boundary is blank.
2. **Reverse** (sep₂-delimited): un-reverses the inner block back to `inner`.
3. **Apply f** (sep₂-delimited): applies `f` to the inner block.
4. **Reverse** (sep₂-delimited): reverses `f(inner)` back.
5. **Reverse** (sep₁-delimited): reverses the outer block, restoring prefix.

Steps 2–4 are composed into `reverse ∘ f ∘ reverse` via `tm0RealizesBlockSep_comp`,
producing a single `TM0RealizesBlockSep Γ sep₂` machine. The full construction
is then a three-machine composition: reverse(sep₁) → revFRev(sep₂) → reverse(sep₁).
-/

open Turing

/-! ### Inner Block Realizability Definition -/

/-- A TM0 machine that applies `f` to the inner block of a two-separator tape.

Given tape `pfx ++ [sep₂] ++ inner ++ [sep₁] ++ suffix`,
produces `pfx ++ [sep₂] ++ f(inner) ++ [sep₁] ++ suffix`.

The prefix `pfx`, both separators `sep₁` and `sep₂`, and the suffix
are all preserved. Only the inner block between `sep₂` and `sep₁` is
modified. -/
def TM0RealizesInnerBlockSep (Γ : Type) [Inhabited Γ] (sep₁ sep₂ : Γ)
    (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (pfx inner suffix : List Γ),
      (∀ g ∈ pfx, g ≠ default) →
      (∀ g ∈ pfx, g ≠ sep₁) →
      (∀ g ∈ pfx, g ≠ sep₂) →
      (∀ g ∈ inner, g ≠ default) →
      (∀ g ∈ inner, g ≠ sep₁) →
      (∀ g ∈ inner, g ≠ sep₂) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f inner, g ≠ default) →
      (∀ g ∈ f inner, g ≠ sep₁) →
      (∀ g ∈ f inner, g ≠ sep₂) →
      (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).Dom),
        ((TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).get h).Tape =
          Tape.mk₁ (pfx ++ sep₂ :: f inner ++ sep₁ :: suffix)

/-- Strong suffix version of `TM0RealizesInnerBlockSep`.

The machine applies `f` to the block between `sep₂` and `sep₁`, preserving
the entire suffix after `sep₁` without requiring it to be blank-free. -/
def TM0RealizesInnerBlockSepAnySuffix
    (Γ : Type) [Inhabited Γ] (sep₁ sep₂ : Γ)
    (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (pfx inner suffix : List Γ),
      (∀ g ∈ pfx, g ≠ default) →
      (∀ g ∈ pfx, g ≠ sep₁) →
      (∀ g ∈ pfx, g ≠ sep₂) →
      (∀ g ∈ inner, g ≠ default) →
      (∀ g ∈ inner, g ≠ sep₁) →
      (∀ g ∈ inner, g ≠ sep₂) →
      (∀ g ∈ f inner, g ≠ default) →
      (∀ g ∈ f inner, g ≠ sep₁) →
      (∀ g ∈ f inner, g ≠ sep₂) →
      (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M
          (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).Dom),
        ((TM0Seq.evalCfg M
          (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).get h).Tape =
          Tape.mk₁ (pfx ++ sep₂ :: f inner ++ sep₁ :: suffix)

/-- Forget that an inner-block machine is suffix-opaque. -/
theorem tm0RealizesInnerBlockSep_of_anySuffix
    {Γ : Type} [Inhabited Γ] {sep₁ sep₂ : Γ} {f : List Γ → List Γ}
    (hf : TM0RealizesInnerBlockSepAnySuffix Γ sep₁ sep₂ f) :
    TM0RealizesInnerBlockSep Γ sep₁ sep₂ f := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  refine ⟨Λ, hΛi, hΛf, M, ?_⟩
  intro pfx inner suffix
    hpfx_nd hpfx_nsep₁ hpfx_nsep₂
    hinn_nd hinn_nsep₁ hinn_nsep₂
    _hsuffix_nd hfinn_nd hfinn_nsep₁ hfinn_nsep₂
  exact hM pfx inner suffix
    hpfx_nd hpfx_nsep₁ hpfx_nsep₂
    hinn_nd hinn_nsep₁ hinn_nsep₂
    hfinn_nd hfinn_nsep₁ hfinn_nsep₂

/-- A default-delimited version of `TM0RealizesInnerBlockSep`.

This is the shape needed by invariant while-loop bodies: the whole active
block is default-delimited, and an internal separator `sep₂` splits the
preserved prefix from the inner block transformed by `f`. -/
def TM0RealizesInnerBlockDefaultSep (Γ : Type) [Inhabited Γ] (sep₂ : Γ)
    (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (pfx inner : List Γ),
      (∀ g ∈ pfx, g ≠ default) →
      (∀ g ∈ pfx, g ≠ sep₂) →
      (∀ g ∈ inner, g ≠ default) →
      (∀ g ∈ inner, g ≠ sep₂) →
      (∀ g ∈ f inner, g ≠ default) →
      (∀ g ∈ f inner, g ≠ sep₂) →
      (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ [default])).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ [default])).Dom),
        ((TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ [default])).get h).Tape =
          Tape.mk₁ (pfx ++ sep₂ :: f inner ++ [default])

/-- Default-delimited inner-block realizability using a temporary non-default
outer separator.

The extra separator `tmp` is not part of the input/output tape. It is the
marker used internally to turn the outer default boundary into a real
separator, run the non-default prefix/suffix lift, then restore the boundary
to default. The contract records exactly the freshness facts needed for that
construction. -/
def TM0RealizesInnerBlockDefaultViaSep (Γ : Type) [Inhabited Γ]
    (tmp sep₂ : Γ) (f : List Γ → List Γ) : Prop :=
  ∃ (Λ : Type) (_ : Inhabited Λ) (_ : Fintype Λ)
    (M : TM0.Machine Γ Λ),
    ∀ (pfx inner suffix : List Γ),
      (∀ g ∈ pfx, g ≠ default) →
      (∀ g ∈ pfx, g ≠ tmp) →
      (∀ g ∈ pfx, g ≠ sep₂) →
      (∀ g ∈ inner, g ≠ default) →
      (∀ g ∈ inner, g ≠ tmp) →
      (∀ g ∈ inner, g ≠ sep₂) →
      (∀ g ∈ suffix, g ≠ default) →
      (∀ g ∈ f inner, g ≠ default) →
      (∀ g ∈ f inner, g ≠ tmp) →
      (∀ g ∈ f inner, g ≠ sep₂) →
      (TM0Seq.evalCfg M (pfx ++ sep₂ :: inner ++ default :: suffix)).Dom ∧
      ∀ (h : (TM0Seq.evalCfg M
          (pfx ++ sep₂ :: inner ++ default :: suffix)).Dom),
        ((TM0Seq.evalCfg M
          (pfx ++ sep₂ :: inner ++ default :: suffix)).get h).Tape =
          Tape.mk₁ (pfx ++ sep₂ :: f inner ++ default :: suffix)

/-! ### List Reversal Helpers -/

/-- Reversing `l₁ ++ a :: l₂` gives `l₂.reverse ++ a :: l₁.reverse`. -/
theorem reverse_append_cons {α : Type} (l₁ : List α) (a : α) (l₂ : List α) :
    (l₁ ++ a :: l₂).reverse = l₂.reverse ++ a :: l₁.reverse := by
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]

/-- All elements of `l₁ ++ a :: l₂` satisfy `P` iff elements of `l₁`, `a`,
    and elements of `l₂` all satisfy `P`. -/
theorem forall_mem_append_cons {α : Type} {P : α → Prop} {a : α}
    {l₁ l₂ : List α} :
    (∀ g ∈ l₁ ++ a :: l₂, P g) ↔
    (∀ g ∈ l₁, P g) ∧ P a ∧ (∀ g ∈ l₂, P g) := by
  simp [List.mem_append, List.mem_cons]
  constructor
  · intro h; exact ⟨fun g hg => h g (Or.inl hg), h a (Or.inr (Or.inl rfl)),
      fun g hg => h g (Or.inr (Or.inr hg))⟩
  · rintro ⟨h₁, ha, h₂⟩ g (hg | rfl | hg)
    · exact h₁ g hg
    · exact ha
    · exact h₂ g hg

/-! ### Boundary replacement helper -/

inductive BoundaryReplaceSt where
  | scan
  | goLeft
  | rewind
  | done
  deriving DecidableEq, Fintype

instance : Inhabited BoundaryReplaceSt := ⟨.scan⟩

/-- Scan to the first occurrence of `target`, replace it by `repl`, then rewind
to the left edge of the active block. -/
noncomputable def boundaryReplaceMachine {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (target repl : Γ) : TM0.Machine Γ BoundaryReplaceSt :=
  fun q a =>
    match q with
    | .scan =>
        if a = target then
          some (.goLeft, TM0.Stmt.write repl)
        else
          some (.scan, TM0.Stmt.move Dir.right)
    | .goLeft =>
        some (.rewind, TM0.Stmt.move Dir.left)
    | .rewind =>
        if a = default then
          some (.done, TM0.Stmt.move Dir.right)
        else
          some (.rewind, TM0.Stmt.move Dir.left)
    | .done => none

theorem boundaryReplace_rewind_loop {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (target repl : Γ) (revBlock acc : List Γ)
    (hrevBlock : ∀ x ∈ revBlock, x ≠ (default : Γ)) :
    Reaches (TM0.step (boundaryReplaceMachine target repl))
      ⟨BoundaryReplaceSt.rewind,
        ⟨revBlock.headI, ListBlank.mk revBlock.tail, ListBlank.mk acc⟩⟩
      ⟨BoundaryReplaceSt.rewind,
        ⟨default, ListBlank.mk [], ListBlank.mk (revBlock.reverse ++ acc)⟩⟩ := by
  induction revBlock generalizing acc with
  | nil => exact Relation.ReflTransGen.refl
  | cons a revBlock ih =>
      have ha : a ≠ (default : Γ) := hrevBlock a (by simp)
      have hrest : ∀ x ∈ revBlock, x ≠ (default : Γ) := by
        intro x hx
        exact hrevBlock x (List.mem_cons_of_mem a hx)
      let mid : TM0.Cfg Γ BoundaryReplaceSt :=
        ⟨BoundaryReplaceSt.rewind,
          Tape.move Dir.left ⟨a, ListBlank.mk revBlock, ListBlank.mk acc⟩⟩
      refine Relation.ReflTransGen.trans (b := mid) ?_ ?_
      · apply Relation.ReflTransGen.single
        simp [TM0.step, boundaryReplaceMachine, ha, mid, Tape.move]
      · convert ih (a :: acc) hrest using 1
        simp [List.reverse_cons, List.append_assoc]

theorem boundaryReplace_scan_gen {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (target repl : Γ) (block suffix revL : List Γ)
    (hblock_default : ∀ g ∈ block, g ≠ (default : Γ))
    (hblock_target : ∀ g ∈ block, g ≠ target)
    (hrevL_default : ∀ g ∈ revL, g ≠ (default : Γ)) :
    Reaches (TM0.step (boundaryReplaceMachine target repl))
      ⟨BoundaryReplaceSt.scan,
        ⟨(block ++ target :: suffix).headI,
          ListBlank.mk revL,
          ListBlank.mk (block ++ target :: suffix).tail⟩⟩
      ⟨BoundaryReplaceSt.done,
        Tape.mk₁ (revL.reverse ++ block ++ repl :: suffix)⟩ := by
  induction block generalizing revL suffix with
  | nil =>
      have h_write : Reaches (TM0.step (boundaryReplaceMachine target repl))
          ⟨BoundaryReplaceSt.scan,
            ⟨target, ListBlank.mk revL, ListBlank.mk suffix⟩⟩
          ⟨BoundaryReplaceSt.goLeft,
            ⟨repl, ListBlank.mk revL, ListBlank.mk suffix⟩⟩ := by
        apply Relation.ReflTransGen.single
        simp [TM0.step, boundaryReplaceMachine]
      have h_left : Reaches (TM0.step (boundaryReplaceMachine target repl))
          ⟨BoundaryReplaceSt.goLeft,
            ⟨repl, ListBlank.mk revL, ListBlank.mk suffix⟩⟩
          ⟨BoundaryReplaceSt.rewind,
            Tape.move Dir.left ⟨repl, ListBlank.mk revL, ListBlank.mk suffix⟩⟩ := by
        apply Relation.ReflTransGen.single
        simp [TM0.step, boundaryReplaceMachine]
      have h_rewind := boundaryReplace_rewind_loop target repl revL (repl :: suffix)
        hrevL_default
      have h_done : Reaches (TM0.step (boundaryReplaceMachine target repl))
          ⟨BoundaryReplaceSt.rewind,
            ⟨default, ListBlank.mk [], ListBlank.mk (revL.reverse ++ repl :: suffix)⟩⟩
          ⟨BoundaryReplaceSt.done,
            Tape.mk₁ (revL.reverse ++ repl :: suffix)⟩ := by
        apply Relation.ReflTransGen.single
        simp [TM0.step, boundaryReplaceMachine, Tape.move, Tape.mk₁, Tape.mk₂,
          Tape.mk']
        exact listBlank_mk_append_default []
      convert h_write.trans (h_left.trans (h_rewind.trans h_done)) using 1
      simp [Tape.move, Tape.mk₁, Tape.mk₂, Tape.mk']
  | cons a block ih =>
      have ha_default : a ≠ (default : Γ) := hblock_default a (by simp)
      have ha_target : a ≠ target := hblock_target a (by simp)
      have hrest_default : ∀ g ∈ block, g ≠ (default : Γ) := by
        intro g hg
        exact hblock_default g (List.mem_cons_of_mem a hg)
      have hrest_target : ∀ g ∈ block, g ≠ target := by
        intro g hg
        exact hblock_target g (List.mem_cons_of_mem a hg)
      have hrevL' : ∀ g ∈ a :: revL, g ≠ (default : Γ) := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ha_default
        · exact hrevL_default g hg
      have h_step : Reaches (TM0.step (boundaryReplaceMachine target repl))
          ⟨BoundaryReplaceSt.scan,
            ⟨a, ListBlank.mk revL, ListBlank.mk (block ++ target :: suffix)⟩⟩
          ⟨BoundaryReplaceSt.scan,
            ⟨(block ++ target :: suffix).headI,
              ListBlank.mk (a :: revL),
              ListBlank.mk (block ++ target :: suffix).tail⟩⟩ := by
        apply Relation.ReflTransGen.single
        simp [TM0.step, boundaryReplaceMachine, ha_target, Tape.move]
      convert h_step.trans (ih suffix (a :: revL) hrest_default hrest_target hrevL') using 1
      simp [List.reverse_cons, List.append_assoc]

theorem boundaryReplace_reaches {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (target repl : Γ) (block suffix : List Γ)
    (hblock_default : ∀ g ∈ block, g ≠ (default : Γ))
    (hblock_target : ∀ g ∈ block, g ≠ target) :
    Reaches (TM0.step (boundaryReplaceMachine target repl))
      (TM0.init (block ++ target :: suffix))
      ⟨BoundaryReplaceSt.done, Tape.mk₁ (block ++ repl :: suffix)⟩ := by
  exact boundaryReplace_scan_gen target repl block suffix [] hblock_default
    hblock_target (by simp)

theorem tm0_boundaryReplace {Γ : Type} [Inhabited Γ] [DecidableEq Γ]
    (target repl : Γ) :
    ∀ (block suffix : List Γ),
      (∀ g ∈ block, g ≠ default) →
      (∀ g ∈ block, g ≠ target) →
      (TM0Seq.evalCfg (boundaryReplaceMachine target repl)
        (block ++ target :: suffix)).Dom ∧
      ∀ h,
        ((TM0Seq.evalCfg (boundaryReplaceMachine target repl)
          (block ++ target :: suffix)).get h).Tape =
          Tape.mk₁ (block ++ repl :: suffix) := by
  intro block suffix hblock_default hblock_target
  have h_reaches := boundaryReplace_reaches target repl block suffix
    hblock_default hblock_target
  have h_halt : TM0.step (boundaryReplaceMachine target repl)
      ⟨BoundaryReplaceSt.done, Tape.mk₁ (block ++ repl :: suffix)⟩ = none := by
    simp [TM0.step, boundaryReplaceMachine]
  have h_mem :
      ⟨BoundaryReplaceSt.done, Tape.mk₁ (block ++ repl :: suffix)⟩ ∈
        TM0Seq.evalCfg (boundaryReplaceMachine target repl)
          (block ++ target :: suffix) :=
    Turing.mem_eval.mpr ⟨h_reaches, h_halt⟩
  refine ⟨Part.dom_iff_mem.mpr ⟨_, h_mem⟩, ?_⟩
  intro h
  exact (Part.mem_unique (Part.get_mem h) h_mem).symm ▸ rfl

/-- Any default-delimited block machine can be run before an arbitrary
non-default separator by temporarily replacing that separator with `default`,
running the machine, and restoring the separator. -/
theorem tm0RealizesBlock_toBlockSep
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} {f : List Γ → List Γ}
    (hf : TM0RealizesBlock Γ f) :
    TM0RealizesBlockSep Γ sep f := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  let Mpre := boundaryReplaceMachine sep (default : Γ)
  let Mpost := boundaryReplaceMachine (default : Γ) sep
  let h12i : Inhabited (BoundaryReplaceSt ⊕ Λ) :=
    ⟨Sum.inl (@default _ inferInstance)⟩
  let M12 : TM0.Machine Γ (BoundaryReplaceSt ⊕ Λ) :=
    @TM0Seq.compose Γ BoundaryReplaceSt inferInstance Λ hΛi Mpre M
  let h123i : Inhabited ((BoundaryReplaceSt ⊕ Λ) ⊕ BoundaryReplaceSt) :=
    ⟨Sum.inl (@default _ h12i)⟩
  let M123 : TM0.Machine Γ ((BoundaryReplaceSt ⊕ Λ) ⊕ BoundaryReplaceSt) :=
    @TM0Seq.compose Γ (BoundaryReplaceSt ⊕ Λ) h12i BoundaryReplaceSt
      inferInstance M12 Mpost
  refine ⟨(BoundaryReplaceSt ⊕ Λ) ⊕ BoundaryReplaceSt, h123i,
    inferInstance, M123, ?_⟩
  intro block suffix hblock_nd hblock_nsep hsuffix_nd hf_nd hf_nsep
  have hpre := tm0_boundaryReplace sep (default : Γ)
    block suffix hblock_nd hblock_nsep
  obtain ⟨hm_dom, hm_tape⟩ := hM block suffix hblock_nd hsuffix_nd hf_nd
  have hm_from_cfg :
      (TM0Seq.evalFromCfg M
        ⟨default, ((TM0Seq.evalCfg Mpre
          (block ++ sep :: suffix)).get hpre.1).Tape⟩).Dom := by
    rw [hpre.2 hpre.1]
    show (TM0Seq.evalFromCfg M (TM0.init (block ++ default :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hm_dom
  have hM12_dom :
      (TM0Seq.evalCfg M12 (block ++ sep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M12 (block ++ sep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts Mpre M
        (block ++ sep :: suffix) hpre.1 hm_from_cfg)
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (block ++ sep :: suffix)).get hM12_dom).Tape =
        Tape.mk₁ (f block ++ default :: suffix) := by
    have ht := TM0Seq.compose_evalCfg_tape Mpre M
      (block ++ sep :: suffix) (block ++ default :: suffix)
      hpre.1 (hpre.2 hpre.1) hm_dom hM12_dom
    rw [ht]
    exact hm_tape hm_dom
  have hpost := tm0_boundaryReplace (default : Γ) sep
    (f block) suffix hf_nd hf_nd
  have hpost_from_cfg :
      (TM0Seq.evalFromCfg Mpost
        ⟨default, ((TM0Seq.evalCfg M12
          (block ++ sep :: suffix)).get hM12_dom).Tape⟩).Dom := by
    rw [hM12_tape]
    show (TM0Seq.evalFromCfg Mpost (TM0.init (f block ++ default :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hpost.1
  have hM123_dom :
      (TM0Seq.evalCfg M123 (block ++ sep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M123 (block ++ sep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts M12 Mpost
        (block ++ sep :: suffix) hM12_dom hpost_from_cfg)
  refine ⟨hM123_dom, ?_⟩
  intro h
  have ht := TM0Seq.compose_evalCfg_tape M12 Mpost
    (block ++ sep :: suffix) (f block ++ default :: suffix)
    hM12_dom hM12_tape hpost.1 h
  rw [ht]
  exact hpost.2 hpost.1

/-- Any strong default-delimited block machine can be run before an arbitrary
non-default separator by temporarily replacing that separator with `default`,
running the machine, and restoring the separator.

Unlike `tm0RealizesBlock_toBlockSep`, this preserves an entirely opaque suffix:
the wrapped machine must already be a strong `TM0RealizesBlockAnySuffix`
machine, and the boundary replacement machines only touch the first boundary
cell. -/
theorem tm0RealizesBlockAnySuffix_toBlockSepAnySuffix
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} {f : List Γ → List Γ}
    (hf : TM0RealizesBlockAnySuffix Γ f) :
    TM0RealizesBlockSepAnySuffix Γ sep f := by
  obtain ⟨Λ, hΛi, hΛf, M, hM⟩ := hf
  let Mpre := boundaryReplaceMachine sep (default : Γ)
  let Mpost := boundaryReplaceMachine (default : Γ) sep
  let h12i : Inhabited (BoundaryReplaceSt ⊕ Λ) :=
    ⟨Sum.inl (@default _ inferInstance)⟩
  let M12 : TM0.Machine Γ (BoundaryReplaceSt ⊕ Λ) :=
    @TM0Seq.compose Γ BoundaryReplaceSt inferInstance Λ hΛi Mpre M
  let h123i : Inhabited ((BoundaryReplaceSt ⊕ Λ) ⊕ BoundaryReplaceSt) :=
    ⟨Sum.inl (@default _ h12i)⟩
  let M123 : TM0.Machine Γ ((BoundaryReplaceSt ⊕ Λ) ⊕ BoundaryReplaceSt) :=
    @TM0Seq.compose Γ (BoundaryReplaceSt ⊕ Λ) h12i BoundaryReplaceSt
      inferInstance M12 Mpost
  refine ⟨(BoundaryReplaceSt ⊕ Λ) ⊕ BoundaryReplaceSt, h123i,
    inferInstance, M123, ?_⟩
  intro block suffix hblock_nd hblock_nsep hf_nd hf_nsep
  have hpre := tm0_boundaryReplace sep (default : Γ)
    block suffix hblock_nd hblock_nsep
  obtain ⟨hm_dom, hm_tape⟩ := hM block suffix hblock_nd hf_nd
  have hm_from_cfg :
      (TM0Seq.evalFromCfg M
        ⟨default, ((TM0Seq.evalCfg Mpre
          (block ++ sep :: suffix)).get hpre.1).Tape⟩).Dom := by
    rw [hpre.2 hpre.1]
    show (TM0Seq.evalFromCfg M (TM0.init (block ++ default :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hm_dom
  have hM12_dom :
      (TM0Seq.evalCfg M12 (block ++ sep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M12 (block ++ sep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts Mpre M
        (block ++ sep :: suffix) hpre.1 hm_from_cfg)
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (block ++ sep :: suffix)).get hM12_dom).Tape =
        Tape.mk₁ (f block ++ default :: suffix) := by
    have ht := TM0Seq.compose_evalCfg_tape Mpre M
      (block ++ sep :: suffix) (block ++ default :: suffix)
      hpre.1 (hpre.2 hpre.1) hm_dom hM12_dom
    rw [ht]
    exact hm_tape hm_dom
  have hpost := tm0_boundaryReplace (default : Γ) sep
    (f block) suffix hf_nd hf_nd
  have hpost_from_cfg :
      (TM0Seq.evalFromCfg Mpost
        ⟨default, ((TM0Seq.evalCfg M12
          (block ++ sep :: suffix)).get hM12_dom).Tape⟩).Dom := by
    rw [hM12_tape]
    show (TM0Seq.evalFromCfg Mpost (TM0.init (f block ++ default :: suffix))).Dom
    rw [TM0Seq.evalFromCfg_init]
    exact hpost.1
  have hM123_dom :
      (TM0Seq.evalCfg M123 (block ++ sep :: suffix)).Dom := by
    exact (TM0Seq.evalCfg_dom_iff M123 (block ++ sep :: suffix)).mpr
      (TM0Seq.compose_dom_of_parts M12 Mpost
        (block ++ sep :: suffix) hM12_dom hpost_from_cfg)
  refine ⟨hM123_dom, ?_⟩
  intro h
  have ht := TM0Seq.compose_evalCfg_tape M12 Mpost
    (block ++ sep :: suffix) (f block ++ default :: suffix)
    hM12_dom hM12_tape hpost.1 h
  rw [ht]
  exact hpost.2 hpost.1

/-! ### Composition: reverse ∘ f ∘ reverse -/

/-- If `f` is `TM0RealizesBlockSep Γ sep`, then `reverse ∘ f ∘ reverse`
    is also `TM0RealizesBlockSep Γ sep`, provided `f` preserves the
    non-defaultness and non-separator properties.

This is a reusable sub-machine composition: it takes any block-sep-realizable
function and produces a machine for the "conjugated" function
`reverse ∘ f ∘ reverse`. -/
theorem tm0RealizesBlockSep_revFRev
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} {f : List Γ → List Γ}
    (hf : TM0RealizesBlockSep Γ sep f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep) → ∀ g ∈ f block, g ≠ sep) :
    TM0RealizesBlockSep Γ sep (List.reverse ∘ f ∘ List.reverse) := by
  have h1 : TM0RealizesBlockSep Γ sep (f ∘ List.reverse) :=
    tm0RealizesBlockSep_comp tm0_reverse_blockSep hf
      (fun b hb => reverse_ne_default b hb)
      (fun b hb => reverse_ne_sep b hb)
  exact tm0RealizesBlockSep_comp h1 tm0_reverse_blockSep
    (fun b hb g hg => hf_nd b.reverse (reverse_ne_default b hb) g hg)
    (fun b hb g hg => hf_nsep b.reverse (reverse_ne_sep b hb) g hg)

/-- Strong suffix version of `tm0RealizesBlockSep_revFRev`. This is the form
needed by prefix/suffix lifting when the preserved suffix after `sep` may
itself contain `default`. -/
theorem tm0RealizesBlockSepAnySuffix_revFRev
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} {f : List Γ → List Γ}
    (hf : TM0RealizesBlockSepAnySuffix Γ sep f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep) → ∀ g ∈ f block, g ≠ sep) :
    TM0RealizesBlockSepAnySuffix Γ sep (List.reverse ∘ f ∘ List.reverse) := by
  have h1 : TM0RealizesBlockSepAnySuffix Γ sep (f ∘ List.reverse) :=
    tm0RealizesBlockSepAnySuffix_comp tm0_reverse_blockSep_anySuffix hf
      (fun b hb => reverse_ne_default b hb)
      (fun b hb => reverse_ne_sep b hb)
  exact tm0RealizesBlockSepAnySuffix_comp h1 tm0_reverse_blockSep_anySuffix
    (fun b hb g hg => hf_nd b.reverse (reverse_ne_default b hb) g hg)
    (fun b hb g hg => hf_nsep b.reverse (reverse_ne_sep b hb) g hg)

/-- Appending a fixed non-default, non-separator list is realizable before a
separator, with no invariant on the suffix. This follows by reversing the
active block, prepending the reversed fixed suffix, and reversing back. -/
theorem tm0_appendList_blockSep_anySuffix
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} (suf : List Γ)
    (hsuf_nd : ∀ g ∈ suf, g ≠ default)
    (hsuf_nsep : ∀ g ∈ suf, g ≠ sep) :
    TM0RealizesBlockSepAnySuffix Γ sep (fun block => block ++ suf) := by
  have hpre : TM0RealizesBlockSepAnySuffix Γ sep
      (fun block => suf.reverse ++ block) :=
    tm0_prependList_blockSep_anySuffix suf.reverse
      (by
        intro g hg
        exact hsuf_nd g (List.mem_reverse.mp hg))
      (by
        intro g hg
        exact hsuf_nsep g (List.mem_reverse.mp hg))
  have h := tm0RealizesBlockSepAnySuffix_revFRev hpre
    (by
      intro block hblock g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hsuf_nd g (List.mem_reverse.mp hg)
      · exact hblock g hg)
    (by
      intro block hblock g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hsuf_nsep g (List.mem_reverse.mp hg)
      · exact hblock g hg)
  convert h using 1
  funext block
  simp [Function.comp, List.reverse_append]

theorem tm0_appendList_blockSep
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep : Γ} (suf : List Γ)
    (hsuf_nd : ∀ g ∈ suf, g ≠ default)
    (hsuf_nsep : ∀ g ∈ suf, g ≠ sep) :
    TM0RealizesBlockSep Γ sep (fun block => block ++ suf) := by
  exact tm0RealizesBlockSep_of_anySuffix
    (tm0_appendList_blockSep_anySuffix suf hsuf_nd hsuf_nsep)

/-! ### Main Theorem: Lifting to Inner Block -/

/-
**Any block-sep-realizable function can be lifted to an inner block operation.**

Given `TM0RealizesBlockSep Γ sep₂ f`, there exists a TM0 machine that, on a
tape `pfx ++ [sep₂] ++ inner ++ [sep₁] ++ suffix`, applies `f` only to `inner`
while preserving `pfx`, both separators, and `suffix`.

The constructed machine composes three sub-machines:
1. Reverse the outer block before `sep₁` (brings `inner.reverse` to front).
2. Apply `reverse ∘ f ∘ reverse` with separator `sep₂` (transforms the inner
   block at the front where the left boundary is blank).
3. Reverse the outer block before `sep₁` again (restores the prefix).

**Hypotheses for the original construction:**
- `sep₁`, `sep₂` are distinct and differ from `default`
- `f` preserves non-defaultness and non-`sep₂`-ness universally
-/
theorem tm0RealizesBlockSep_toInner_nondefault
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep₁ sep₂ : Γ} {f : List Γ → List Γ}
    (hsep₁ : sep₁ ≠ default) (hsep₂ : sep₂ ≠ default) (h₁₂ : sep₁ ≠ sep₂)
    (hf : TM0RealizesBlockSep Γ sep₂ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep₂) → ∀ g ∈ f block, g ≠ sep₂) :
    TM0RealizesInnerBlockSep Γ sep₁ sep₂ f := by
  -- Build the reusable sub-machines
  have hrev₁ := @tm0_reverse_blockSep Γ _ _ _ (sep := sep₁)
  have hrfr := tm0RealizesBlockSep_revFRev hf hf_nd hf_nsep
  -- Extract machines
  obtain ⟨Λ_rev, h_rev_inh, h_rev_fin, M_rev, hM_rev⟩ := hrev₁
  obtain ⟨Λ_rfr, h_rfr_inh, h_rfr_fin, M_rfr, hM_rfr⟩ := hrfr
  -- Build the composed machine with explicit instance passing
  let M12 := @TM0Seq.compose Γ Λ_rev h_rev_inh Λ_rfr h_rfr_inh M_rev M_rfr
  let M123 := @TM0Seq.compose Γ (Λ_rev ⊕ Λ_rfr) ⟨Sum.inl (@default _ h_rev_inh)⟩
    Λ_rev h_rev_inh M12 M_rev
  -- Provide the Inhabited and Fintype instances explicitly
  refine ⟨(Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev,
    ⟨Sum.inl (Sum.inl (@default _ h_rev_inh))⟩,
    @instFintypeSum _ _ (@instFintypeSum _ _ h_rev_fin h_rfr_fin) h_rev_fin,
    M123, ?_⟩
  -- Verify for each prefix, inner block, and suffix
  intro pfx inner suffix
    hpfx_nd hpfx_nsep₁ hpfx_nsep₂
    hinn_nd hinn_nsep₁ hinn_nsep₂
    hsuf_nd hfinn_nd hfinn_nsep₁ hfinn_nsep₂
  -- ── Tape contents at each stage ──
  set outer := pfx ++ sep₂ :: inner with h_outer_def
  -- Key identity: outer.reverse = inner.reverse ++ sep₂ :: pfx.reverse
  have h_outer_rev : outer.reverse = inner.reverse ++ sep₂ :: pfx.reverse :=
    reverse_append_cons pfx sep₂ inner
  -- After step 1 (reverse sep₁):
  --   l₁ = inner.reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix
  -- After step 2 (revFRev sep₂):
  --   l₂ = (f inner).reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix
  -- After step 3 (reverse sep₁):
  --   l₃ = pfx ++ sep₂ :: f inner ++ sep₁ :: suffix
  set mid := (f inner).reverse ++ sep₂ :: pfx.reverse with h_mid_def
  -- Key identity: mid.reverse = pfx ++ sep₂ :: f inner
  have h_mid_rev : mid.reverse = pfx ++ sep₂ :: f inner := by
    simp only [mid, reverse_append_cons, List.reverse_reverse]
  -- ═══════════════════════════════════════════════
  -- Step 1: M_rev on outer ++ sep₁ :: suffix → outer.reverse ++ sep₁ :: suffix
  -- ═══════════════════════════════════════════════
  have houter_nd : ∀ g ∈ outer, g ≠ default :=
    forall_mem_append_cons.mpr ⟨hpfx_nd, hsep₂, hinn_nd⟩
  have houter_nsep₁ : ∀ g ∈ outer, g ≠ sep₁ :=
    forall_mem_append_cons.mpr ⟨hpfx_nsep₁, h₁₂.symm, hinn_nsep₁⟩
  have hstep1 := hM_rev outer suffix houter_nd houter_nsep₁ hsuf_nd
    (reverse_ne_default outer houter_nd) (reverse_ne_sep outer houter_nsep₁)
  -- ═══════════════════════════════════════════════
  -- Step 2: M_rfr on inner.reverse ++ sep₂ :: ... → (f inner).reverse ++ sep₂ :: ...
  -- ═══════════════════════════════════════════════
  have hsuf₂_nd : ∀ g ∈ pfx.reverse ++ sep₁ :: suffix, g ≠ default :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_default pfx hpfx_nd, hsep₁, hsuf_nd⟩
  have h_rfr_eq : (List.reverse ∘ f ∘ List.reverse) inner.reverse =
      (f inner).reverse := by
    simp [Function.comp, List.reverse_reverse]
  have hrfr_nd : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ default := by rw [h_rfr_eq]; exact reverse_ne_default (f inner) hfinn_nd
  have hrfr_nsep₂ : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ sep₂ := by rw [h_rfr_eq]; exact reverse_ne_sep (f inner) hfinn_nsep₂
  have hstep2 := hM_rfr inner.reverse (pfx.reverse ++ sep₁ :: suffix)
    (reverse_ne_default inner hinn_nd)
    (reverse_ne_sep inner hinn_nsep₂)
    hsuf₂_nd hrfr_nd hrfr_nsep₂
  -- ═══════════════════════════════════════════════
  -- Step 3: M_rev on mid ++ sep₁ :: suffix → mid.reverse ++ sep₁ :: suffix
  -- ═══════════════════════════════════════════════
  have hmid_nd : ∀ g ∈ mid, g ≠ default :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_default (f inner) hfinn_nd, hsep₂,
       reverse_ne_default pfx hpfx_nd⟩
  have hmid_nsep₁ : ∀ g ∈ mid, g ≠ sep₁ :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_sep (f inner) hfinn_nsep₁, h₁₂.symm,
       reverse_ne_sep pfx hpfx_nsep₁⟩
  have hstep3 := hM_rev mid suffix hmid_nd hmid_nsep₁ hsuf_nd
    (reverse_ne_default mid hmid_nd) (reverse_ne_sep mid hmid_nsep₁)
  -- ═══════════════════════════════════════════════
  -- Compose all three steps
  -- ═══════════════════════════════════════════════
  -- The key list equalities:
  -- 1. outer ++ sep₁ :: suffix = pfx ++ sep₂ :: inner ++ sep₁ :: suffix
  -- 2. outer.reverse ++ sep₁ :: suffix
  --    = inner.reverse ++ sep₂ :: (pfx.reverse ++ sep₁ :: suffix)
  -- 3. (revFRev)(inner.reverse) ++ sep₂ :: (pfx.reverse ++ sep₁ :: suffix)
  --    = (f inner).reverse ++ sep₂ :: (pfx.reverse ++ sep₁ :: suffix)
  --    = mid ++ sep₁ :: suffix
  -- 4. mid.reverse ++ sep₁ :: suffix = pfx ++ sep₂ :: f inner ++ sep₁ :: suffix
  have hM_rev_dom := @TM0Seq.evalCfg_dom_iff;
  contrapose! hM_rev_dom;
  use PUnit;
  use inferInstance, PUnit;
  use inferInstance;
  use fun _ _ => some ( PUnit.unit, TM0.Stmt.move Dir.left );
  unfold TM0Seq.evalCfg; simp +decide [ Turing.eval ] ;
  grind +suggestions

/-- Strong suffix version of the prefix/suffix lift.

This is the construction that works uniformly for `sep₁ = default` and
`sep₁ ≠ default`: after reversing the outer block, the middle machine runs on
`inner.reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix`, so the hypothesis on
`f` must be `TM0RealizesBlockSepAnySuffix`. -/
theorem tm0RealizesBlockSepAnySuffix_toInner
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep₁ sep₂ : Γ} {f : List Γ → List Γ}
    (hsep₂ : sep₂ ≠ default) (h₁₂ : sep₁ ≠ sep₂)
    (hf : TM0RealizesBlockSepAnySuffix Γ sep₂ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep₂) → ∀ g ∈ f block, g ≠ sep₂) :
    TM0RealizesInnerBlockSepAnySuffix Γ sep₁ sep₂ f := by
  have hrev₁ := @tm0_reverse_blockSep_anySuffix Γ _ _ _ (sep := sep₁)
  have hrfr := tm0RealizesBlockSepAnySuffix_revFRev hf hf_nd hf_nsep
  obtain ⟨Λ_rev, h_rev_inh, h_rev_fin, M_rev, hM_rev⟩ := hrev₁
  obtain ⟨Λ_rfr, h_rfr_inh, h_rfr_fin, M_rfr, hM_rfr⟩ := hrfr
  let h12_inh : Inhabited (Λ_rev ⊕ Λ_rfr) :=
    ⟨Sum.inl (@default _ h_rev_inh)⟩
  let h123_inh : Inhabited ((Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev) :=
    ⟨Sum.inl (@default _ h12_inh)⟩
  let M12 := @TM0Seq.compose Γ Λ_rev h_rev_inh Λ_rfr h_rfr_inh M_rev M_rfr
  let M123 := @TM0Seq.compose Γ (Λ_rev ⊕ Λ_rfr) h12_inh Λ_rev h_rev_inh M12 M_rev
  refine ⟨(Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev, h123_inh,
    @instFintypeSum _ _ (@instFintypeSum _ _ h_rev_fin h_rfr_fin) h_rev_fin,
    M123, ?_⟩
  intro pfx inner suffix
    hpfx_nd hpfx_nsep₁ hpfx_nsep₂
    hinn_nd hinn_nsep₁ hinn_nsep₂
    hfinn_nd hfinn_nsep₁ hfinn_nsep₂
  set outer := pfx ++ sep₂ :: inner with h_outer_def
  have h_outer_rev : outer.reverse = inner.reverse ++ sep₂ :: pfx.reverse :=
    reverse_append_cons pfx sep₂ inner
  set mid := (f inner).reverse ++ sep₂ :: pfx.reverse with h_mid_def
  have h_mid_rev : mid.reverse = pfx ++ sep₂ :: f inner := by
    simp only [mid, reverse_append_cons, List.reverse_reverse]
  have houter_nd : ∀ g ∈ outer, g ≠ default :=
    forall_mem_append_cons.mpr ⟨hpfx_nd, hsep₂, hinn_nd⟩
  have houter_nsep₁ : ∀ g ∈ outer, g ≠ sep₁ :=
    forall_mem_append_cons.mpr ⟨hpfx_nsep₁, h₁₂.symm, hinn_nsep₁⟩
  have hstep1 := hM_rev outer suffix houter_nd houter_nsep₁
    (reverse_ne_default outer houter_nd) (reverse_ne_sep outer houter_nsep₁)
  have h_rfr_eq : (List.reverse ∘ f ∘ List.reverse) inner.reverse =
      (f inner).reverse := by
    simp [Function.comp, List.reverse_reverse]
  have hrfr_nd : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ default := by
    rw [h_rfr_eq]
    exact reverse_ne_default (f inner) hfinn_nd
  have hrfr_nsep₂ : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ sep₂ := by
    rw [h_rfr_eq]
    exact reverse_ne_sep (f inner) hfinn_nsep₂
  have hstep2 := hM_rfr inner.reverse (pfx.reverse ++ sep₁ :: suffix)
    (reverse_ne_default inner hinn_nd)
    (reverse_ne_sep inner hinn_nsep₂)
    hrfr_nd hrfr_nsep₂
  have hmid_nd : ∀ g ∈ mid, g ≠ default :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_default (f inner) hfinn_nd, hsep₂,
       reverse_ne_default pfx hpfx_nd⟩
  have hmid_nsep₁ : ∀ g ∈ mid, g ≠ sep₁ :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_sep (f inner) hfinn_nsep₁, h₁₂.symm,
       reverse_ne_sep pfx hpfx_nsep₁⟩
  have hstep3 := hM_rev mid suffix hmid_nd hmid_nsep₁
    (reverse_ne_default mid hmid_nd) (reverse_ne_sep mid hmid_nsep₁)
  have hstep1_tape :
      ((TM0Seq.evalCfg M_rev (outer ++ sep₁ :: suffix)).get hstep1.1).Tape =
        Tape.mk₁ (inner.reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix) := by
    rw [hstep1.2 hstep1.1]
    simp [h_outer_rev, List.append_assoc]
  have hstep2_dom' :
      (TM0Seq.evalCfg M_rfr
        (inner.reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix)).Dom := by
    simpa [List.append_assoc] using hstep2.1
  have hstep2_tape' :
      ((TM0Seq.evalCfg M_rfr
        (inner.reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix)).get
          hstep2_dom').Tape =
        Tape.mk₁ (mid ++ sep₁ :: suffix) := by
    have hget :
        (TM0Seq.evalCfg M_rfr
          (inner.reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix)).get
            hstep2_dom' =
          (TM0Seq.evalCfg M_rfr
            (inner.reverse ++ sep₂ :: (pfx.reverse ++ sep₁ :: suffix))).get
              hstep2.1 := by
      apply Part.get_eq_get_of_eq
      simp [List.append_assoc]
    rw [hget, hstep2.2 hstep2.1]
    simp [mid, List.append_assoc]
  have hM12_dom :
      (TM0Seq.evalCfg M12 (outer ++ sep₁ :: suffix)).Dom := by
    have hstep2_from_cfg :
        (TM0Seq.evalFromCfg M_rfr
          ⟨default, ((TM0Seq.evalCfg M_rev
            (outer ++ sep₁ :: suffix)).get hstep1.1).Tape⟩).Dom := by
      rw [hstep1_tape]
      change (TM0Seq.evalFromCfg M_rfr
        (TM0.init (inner.reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix))).Dom
      rw [TM0Seq.evalFromCfg_init]
      exact hstep2_dom'
    exact @TM0Seq.compose_dom_of_parts Γ _ Λ_rev h_rev_inh Λ_rfr h_rfr_inh
      M_rev M_rfr (outer ++ sep₁ :: suffix) hstep1.1 hstep2_from_cfg
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (outer ++ sep₁ :: suffix)).get hM12_dom).Tape =
        Tape.mk₁ (mid ++ sep₁ :: suffix) := by
    convert @TM0Seq.compose_evalCfg_tape Γ _ Λ_rev h_rev_inh Λ_rfr h_rfr_inh
      M_rev M_rfr
      (outer ++ sep₁ :: suffix)
      (inner.reverse ++ sep₂ :: pfx.reverse ++ sep₁ :: suffix)
      hstep1.1 hstep1_tape hstep2_dom' hM12_dom using 1
    exact hstep2_tape'.symm
  have hM123_dom :
      (TM0Seq.evalCfg M123 (outer ++ sep₁ :: suffix)).Dom := by
    have hstep3_from_cfg :
        (TM0Seq.evalFromCfg M_rev
          ⟨default, ((TM0Seq.evalCfg M12
            (outer ++ sep₁ :: suffix)).get hM12_dom).Tape⟩).Dom := by
      rw [hM12_tape]
      change (TM0Seq.evalFromCfg M_rev
        (TM0.init (mid ++ sep₁ :: suffix))).Dom
      rw [TM0Seq.evalFromCfg_init]
      exact hstep3.1
    exact @TM0Seq.compose_dom_of_parts Γ _ (Λ_rev ⊕ Λ_rfr) h12_inh Λ_rev h_rev_inh
      M12 M_rev (outer ++ sep₁ :: suffix) hM12_dom hstep3_from_cfg
  refine ⟨?_, ?_⟩
  · convert hM123_dom using 1
  · intro h
    have h_tape := @TM0Seq.compose_evalCfg_tape Γ _ (Λ_rev ⊕ Λ_rfr) h12_inh
      Λ_rev h_rev_inh M12 M_rev
      (outer ++ sep₁ :: suffix) (mid ++ sep₁ :: suffix)
      hM12_dom hM12_tape hstep3.1 hM123_dom
    have h_final :
        ((TM0Seq.evalCfg M123 (outer ++ sep₁ :: suffix)).get hM123_dom).Tape =
          Tape.mk₁ (pfx ++ sep₂ :: f inner ++ sep₁ :: suffix) := by
      rw [h_tape, hstep3.2 hstep3.1]
      simp [h_mid_rev, List.append_assoc]
    have h_get_eq :
        (TM0Seq.evalCfg M123 (pfx ++ sep₂ :: inner ++ sep₁ :: suffix)).get h =
          (TM0Seq.evalCfg M123 (outer ++ sep₁ :: suffix)).get hM123_dom := by
      apply Part.get_eq_get_of_eq
      simp [outer, List.append_assoc]
    rw [h_get_eq, h_final]

/-- Separator-delimited version of the default-boundary lift.

This is the form to use when the outer delimiter after the inner block should
be a real separator `sep₁`, not the tape blank.  The tape shape is
`pfx ++ sep₂ :: inner ++ sep₁ :: suffix`. -/
theorem tm0RealizesBlockSep_toInnerOuterSep
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep₁ sep₂ : Γ} {f : List Γ → List Γ}
    (hsep₁ : sep₁ ≠ default) (hsep₂ : sep₂ ≠ default) (h₁₂ : sep₁ ≠ sep₂)
    (hf : TM0RealizesBlockSep Γ sep₂ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep₂) → ∀ g ∈ f block, g ≠ sep₂) :
    TM0RealizesInnerBlockSep Γ sep₁ sep₂ f :=
  tm0RealizesBlockSep_toInner_nondefault hsep₁ hsep₂ h₁₂ hf hf_nd hf_nsep

/-- Default-boundary inner-block lift through a temporary real separator.

Operationally this is:

1. rewrite the boundary `default` after `inner` to `tmp`;
2. use `tm0RealizesBlockSep_toInner_nondefault` with outer separator `tmp`;
3. rewrite the resulting boundary `tmp` back to `default`.

The freshness assumptions on `tmp` are carried by
`TM0RealizesInnerBlockDefaultViaSep`, because the temporary marker must not be
confused with data in the prefix, inner block, or transformed inner block. -/
theorem tm0RealizesBlockSep_toInnerDefaultViaSep
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {tmp sep₂ : Γ} {f : List Γ → List Γ}
    (htmp : tmp ≠ default) (hsep₂ : sep₂ ≠ default) (htmp₂ : tmp ≠ sep₂)
    (hf : TM0RealizesBlockSep Γ sep₂ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep₂) → ∀ g ∈ f block, g ≠ sep₂) :
    TM0RealizesInnerBlockDefaultViaSep Γ tmp sep₂ f := by
  have hmid_realizes :=
    tm0RealizesBlockSep_toInner_nondefault htmp hsep₂ htmp₂ hf hf_nd hf_nsep
  obtain ⟨Λ_mid, h_mid_inh, h_mid_fin, M_mid, hM_mid⟩ := hmid_realizes
  let M_pre := boundaryReplaceMachine (default : Γ) tmp
  let M_post := boundaryReplaceMachine tmp (default : Γ)
  let h12_inh : Inhabited (BoundaryReplaceSt ⊕ Λ_mid) :=
    ⟨Sum.inl BoundaryReplaceSt.scan⟩
  let h123_inh : Inhabited ((BoundaryReplaceSt ⊕ Λ_mid) ⊕ BoundaryReplaceSt) :=
    ⟨Sum.inl (@default _ h12_inh)⟩
  let M12 := @TM0Seq.compose Γ BoundaryReplaceSt inferInstance Λ_mid h_mid_inh
    M_pre M_mid
  let M123 := @TM0Seq.compose Γ (BoundaryReplaceSt ⊕ Λ_mid) h12_inh
    BoundaryReplaceSt inferInstance M12 M_post
  refine ⟨(BoundaryReplaceSt ⊕ Λ_mid) ⊕ BoundaryReplaceSt, h123_inh,
    @instFintypeSum _ _ (@instFintypeSum _ _ inferInstance h_mid_fin) inferInstance,
    M123, ?_⟩
  intro pfx inner suffix
    hpfx_nd hpfx_ntmp hpfx_nsep₂
    hinn_nd hinn_ntmp hinn_nsep₂
    hsuf_nd hfinn_nd hfinn_ntmp hfinn_nsep₂
  set outer := pfx ++ sep₂ :: inner with h_outer_def
  set out := pfx ++ sep₂ :: f inner with h_out_def
  have houter_nd : ∀ g ∈ outer, g ≠ default :=
    forall_mem_append_cons.mpr ⟨hpfx_nd, hsep₂, hinn_nd⟩
  have houter_ntmp : ∀ g ∈ outer, g ≠ tmp :=
    forall_mem_append_cons.mpr ⟨hpfx_ntmp, htmp₂.symm, hinn_ntmp⟩
  have hout_nd : ∀ g ∈ out, g ≠ default :=
    forall_mem_append_cons.mpr ⟨hpfx_nd, hsep₂, hfinn_nd⟩
  have hout_ntmp : ∀ g ∈ out, g ≠ tmp :=
    forall_mem_append_cons.mpr ⟨hpfx_ntmp, htmp₂.symm, hfinn_ntmp⟩
  have hpre := tm0_boundaryReplace (default : Γ) tmp outer suffix houter_nd houter_nd
  have hmid := hM_mid pfx inner suffix
    hpfx_nd hpfx_ntmp hpfx_nsep₂
    hinn_nd hinn_ntmp hinn_nsep₂
    hsuf_nd hfinn_nd hfinn_ntmp hfinn_nsep₂
  have hpost := tm0_boundaryReplace tmp (default : Γ) out suffix hout_nd hout_ntmp
  have hpre_tape :
      ((TM0Seq.evalCfg M_pre (outer ++ default :: suffix)).get hpre.1).Tape =
        Tape.mk₁ (outer ++ tmp :: suffix) := hpre.2 hpre.1
  have hmid_dom' :
      (TM0Seq.evalCfg M_mid (outer ++ tmp :: suffix)).Dom := by
    simpa [outer, List.append_assoc] using hmid.1
  have hmid_tape' :
      ((TM0Seq.evalCfg M_mid (outer ++ tmp :: suffix)).get hmid_dom').Tape =
        Tape.mk₁ (out ++ tmp :: suffix) := by
    have hget :
        (TM0Seq.evalCfg M_mid (outer ++ tmp :: suffix)).get hmid_dom' =
          (TM0Seq.evalCfg M_mid
            (pfx ++ sep₂ :: inner ++ tmp :: suffix)).get hmid.1 := by
      apply Part.get_eq_get_of_eq
      simp [outer, List.append_assoc]
    rw [hget, hmid.2 hmid.1]
  have hM12_dom :
      (TM0Seq.evalCfg M12 (outer ++ default :: suffix)).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ BoundaryReplaceSt inferInstance
      Λ_mid h_mid_inh M_pre M_mid (outer ++ default :: suffix) hpre.1
    convert hmid_dom' using 1
    rw [hpre_tape]
    rfl
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (outer ++ default :: suffix)).get hM12_dom).Tape =
        Tape.mk₁ (out ++ tmp :: suffix) := by
    convert @TM0Seq.compose_evalCfg_tape Γ _ BoundaryReplaceSt inferInstance
      Λ_mid h_mid_inh M_pre M_mid
      (outer ++ default :: suffix) (outer ++ tmp :: suffix)
      hpre.1 hpre_tape hmid_dom' hM12_dom using 1
    exact hmid_tape'.symm
  have hpost_dom' :
      (TM0Seq.evalCfg M_post (out ++ tmp :: suffix)).Dom := hpost.1
  have hpost_tape' :
      ((TM0Seq.evalCfg M_post (out ++ tmp :: suffix)).get hpost_dom').Tape =
        Tape.mk₁ (out ++ default :: suffix) := hpost.2 hpost_dom'
  have hM123_dom :
      (TM0Seq.evalCfg M123 (outer ++ default :: suffix)).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ (BoundaryReplaceSt ⊕ Λ_mid) h12_inh
      BoundaryReplaceSt inferInstance M12 M_post
      (outer ++ default :: suffix) hM12_dom
    convert hpost_dom' using 1
    rw [hM12_tape]
    rfl
  refine ⟨?_, ?_⟩
  · convert hM123_dom using 1
  · intro h
    have h_tape := @TM0Seq.compose_evalCfg_tape Γ _ (BoundaryReplaceSt ⊕ Λ_mid)
      h12_inh BoundaryReplaceSt inferInstance M12 M_post
      (outer ++ default :: suffix) (out ++ tmp :: suffix)
      hM12_dom hM12_tape hpost_dom' hM123_dom
    have h_final :
        ((TM0Seq.evalCfg M123 (outer ++ default :: suffix)).get hM123_dom).Tape =
          Tape.mk₁ (pfx ++ sep₂ :: f inner ++ default :: suffix) := by
      rw [h_tape, hpost_tape']
    have h_get_eq :
        (TM0Seq.evalCfg M123
          (pfx ++ sep₂ :: inner ++ default :: suffix)).get h =
          (TM0Seq.evalCfg M123 (outer ++ default :: suffix)).get hM123_dom := by
      apply Part.get_eq_get_of_eq
      simp [outer, List.append_assoc]
    rw [h_get_eq, h_final]

/-- Default-delimited inner-block lift with no suffix after the final blank.

The construction is the same three-machine composition:
reverse before the outer default, run `reverse ∘ f ∘ reverse` before the
internal separator, then reverse before the outer default again. The middle
phase is applied to a list without the trailing default; `evalCfg_append_default`
identifies that with the actual intermediate tape. -/
theorem tm0RealizesBlockSep_toInnerDefault
    {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    {sep₂ : Γ} {f : List Γ → List Γ}
    (hsep₂ : sep₂ ≠ default)
    (hf : TM0RealizesBlockSep Γ sep₂ f)
    (hf_nd : ∀ block, (∀ g ∈ block, g ≠ default) → ∀ g ∈ f block, g ≠ default)
    (hf_nsep : ∀ block, (∀ g ∈ block, g ≠ sep₂) → ∀ g ∈ f block, g ≠ sep₂) :
    TM0RealizesInnerBlockDefaultSep Γ sep₂ f := by
  have hrev := @tm0_reverse_blockSep Γ _ _ _ (sep := default)
  have hrfr := tm0RealizesBlockSep_revFRev hf hf_nd hf_nsep
  obtain ⟨Λ_rev, h_rev_inh, h_rev_fin, M_rev, hM_rev⟩ := hrev
  obtain ⟨Λ_rfr, h_rfr_inh, h_rfr_fin, M_rfr, hM_rfr⟩ := hrfr
  let h12_inh : Inhabited (Λ_rev ⊕ Λ_rfr) :=
    ⟨Sum.inl (@default _ h_rev_inh)⟩
  let h123_inh : Inhabited ((Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev) :=
    ⟨Sum.inl (@default _ h12_inh)⟩
  let M12 := @TM0Seq.compose Γ Λ_rev h_rev_inh Λ_rfr h_rfr_inh M_rev M_rfr
  let M123 := @TM0Seq.compose Γ (Λ_rev ⊕ Λ_rfr) h12_inh Λ_rev h_rev_inh M12 M_rev
  refine ⟨(Λ_rev ⊕ Λ_rfr) ⊕ Λ_rev, h123_inh,
    @instFintypeSum _ _ (@instFintypeSum _ _ h_rev_fin h_rfr_fin) h_rev_fin,
    M123, ?_⟩
  intro pfx inner hpfx_nd hpfx_nsep₂ hinn_nd hinn_nsep₂ hfinn_nd hfinn_nsep₂
  set outer := pfx ++ sep₂ :: inner with h_outer_def
  have h_outer_rev : outer.reverse = inner.reverse ++ sep₂ :: pfx.reverse :=
    reverse_append_cons pfx sep₂ inner
  set mid := (f inner).reverse ++ sep₂ :: pfx.reverse with h_mid_def
  have h_mid_rev : mid.reverse = pfx ++ sep₂ :: f inner := by
    simp only [mid, reverse_append_cons, List.reverse_reverse]

  have houter_nd : ∀ g ∈ outer, g ≠ default :=
    forall_mem_append_cons.mpr ⟨hpfx_nd, hsep₂, hinn_nd⟩
  have hstep1 := hM_rev outer [] houter_nd houter_nd (by simp)
    (reverse_ne_default outer houter_nd) (reverse_ne_default outer houter_nd)
  have h_rfr_eq : (List.reverse ∘ f ∘ List.reverse) inner.reverse =
      (f inner).reverse := by
    simp [Function.comp, List.reverse_reverse]
  have hrfr_nd : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ default := by
    rw [h_rfr_eq]
    exact reverse_ne_default (f inner) hfinn_nd
  have hrfr_nsep₂ : ∀ g ∈ (List.reverse ∘ f ∘ List.reverse) inner.reverse,
      g ≠ sep₂ := by
    rw [h_rfr_eq]
    exact reverse_ne_sep (f inner) hfinn_nsep₂
  have hpfx_rev_nd : ∀ g ∈ pfx.reverse, g ≠ default :=
    reverse_ne_default pfx hpfx_nd
  have hstep2 := hM_rfr inner.reverse pfx.reverse
    (reverse_ne_default inner hinn_nd)
    (reverse_ne_sep inner hinn_nsep₂)
    hpfx_rev_nd hrfr_nd hrfr_nsep₂
  have hmid_nd : ∀ g ∈ mid, g ≠ default :=
    forall_mem_append_cons.mpr
      ⟨reverse_ne_default (f inner) hfinn_nd, hsep₂,
       reverse_ne_default pfx hpfx_nd⟩
  have hstep3 := hM_rev mid [] hmid_nd hmid_nd (by simp)
    (reverse_ne_default mid hmid_nd) (reverse_ne_default mid hmid_nd)

  have hstep1_tape :
      ((TM0Seq.evalCfg M_rev (outer ++ [default])).get hstep1.1).Tape =
        Tape.mk₁ (inner.reverse ++ sep₂ :: pfx.reverse ++ [default]) := by
    rw [hstep1.2 hstep1.1]
    simp [h_outer_rev]
  have hstep2_dom_trailing :
      (TM0Seq.evalCfg M_rfr
        (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])).Dom := by
    rw [evalCfg_append_default]
    exact hstep2.1
  have hstep2_tape_trailing :
      ((TM0Seq.evalCfg M_rfr
        (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])).get hstep2_dom_trailing).Tape =
        Tape.mk₁ ((f inner).reverse ++ sep₂ :: pfx.reverse ++ [default]) := by
    have hcfg_eq :
        (TM0Seq.evalCfg M_rfr
          (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])).get hstep2_dom_trailing =
          (TM0Seq.evalCfg M_rfr
            (inner.reverse ++ sep₂ :: pfx.reverse)).get hstep2.1 := by
      apply Part.get_eq_get_of_eq
      exact evalCfg_append_default M_rfr (inner.reverse ++ sep₂ :: pfx.reverse)
    rw [hcfg_eq, hstep2.2 hstep2.1]
    rw [h_rfr_eq]
    exact (tape_mk₁_append_default ((f inner).reverse ++ sep₂ :: pfx.reverse)).symm
  have hM12_dom :
      (TM0Seq.evalCfg M12 (outer ++ [default])).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ Λ_rev h_rev_inh Λ_rfr h_rfr_inh
      M_rev M_rfr (outer ++ [default]) hstep1.1
    convert hstep2_dom_trailing using 1
    rw [hstep1_tape]
    rfl
  have hM12_tape :
      ((TM0Seq.evalCfg M12 (outer ++ [default])).get hM12_dom).Tape =
        Tape.mk₁ (mid ++ [default]) := by
    convert @TM0Seq.compose_evalCfg_tape Γ _ Λ_rev h_rev_inh Λ_rfr h_rfr_inh
      M_rev M_rfr
      (outer ++ [default])
      (inner.reverse ++ sep₂ :: pfx.reverse ++ [default])
      hstep1.1 hstep1_tape hstep2_dom_trailing hM12_dom using 1
    rw [hstep2_tape_trailing]
  have hM123_dom :
      (TM0Seq.evalCfg M123 (outer ++ [default])).Dom := by
    apply @TM0Seq.compose_dom_of_parts Γ _ (Λ_rev ⊕ Λ_rfr) h12_inh Λ_rev h_rev_inh
      M12 M_rev (outer ++ [default]) hM12_dom
    convert hstep3.1 using 1
    rw [hM12_tape]
    rfl
  refine ⟨?_, ?_⟩
  · convert hM123_dom using 1
  · intro h
    have h_tape := @TM0Seq.compose_evalCfg_tape Γ _ (Λ_rev ⊕ Λ_rfr) h12_inh
      Λ_rev h_rev_inh M12 M_rev
      (outer ++ [default]) (mid ++ [default])
      hM12_dom hM12_tape hstep3.1 hM123_dom
    have h_final : ((TM0Seq.evalCfg M123 (outer ++ [default])).get hM123_dom).Tape =
        Tape.mk₁ (pfx ++ sep₂ :: f inner ++ [default]) := by
      rw [h_tape, hstep3.2 hstep3.1]
      simp [h_mid_rev]
    have h_dom_eq :
        (TM0Seq.evalCfg M123 (pfx ++ sep₂ :: inner ++ [default])).Dom =
          (TM0Seq.evalCfg M123 (outer ++ [default])).Dom := by
      simp [outer, List.append_assoc]
    have h_get_eq :
        (TM0Seq.evalCfg M123 (pfx ++ sep₂ :: inner ++ [default])).get h =
          (TM0Seq.evalCfg M123 (outer ++ [default])).get hM123_dom := by
      apply Part.get_eq_get_of_eq
      simp [outer, List.append_assoc]
    rw [h_get_eq, h_final]
