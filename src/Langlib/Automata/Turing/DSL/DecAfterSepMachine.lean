import Mathlib
import Langlib.Automata.Turing.DSL.SplitAtSep
import Langlib.Automata.Turing.DSL.TakeWhileBlock
import Langlib.Automata.Turing.DSL.BinaryArithmeticSep
import Langlib.Automata.Turing.DSL.BlockSepPrefix

/-! # Increment-After-Separator Machine

`decAfterSep` scans to the first `chainConsBottom`. If it finds one, it
delegates to `binSuccMachine` on the right sub-block, using the already-proved
framed successor lemma. If no separator is present, it rewinds and leaves the
block unchanged.
-/

open Turing PartrecToTM2 TM2to1

/-- Prefix-lifting machinery can run binary successor on the sub-block between
    `chainConsBottom` and an outer separator, preserving both sides. -/
theorem tm0_binSucc_afterConsBottom_innerBlockSep {sep₁ : ChainΓ}
    (hsep₁_cons : sep₁ ≠ chainConsBottom) :
    TM0RealizesInnerBlockSep ChainΓ sep₁ chainConsBottom binSucc := by
  exact tm0RealizesBlockSep_toInner
    chainConsBottom_ne_default hsep₁_cons
    (tm0_binSucc_blockSep (sep := chainConsBottom) (by decide) (by decide))
    binSucc_ne_default
    (fun block hblock => binSucc_no_consBottom block hblock)

/-- On a default-delimited paired block, run normalized binary successor on the
    sub-block after `chainConsBottom`, preserving the prefix before it. -/
theorem tm0_binSuccNormalize_afterConsBottom_innerBlockSep {sep₁ : ChainΓ}
    (hsep₁ : sep₁ ≠ default) (hsep₁_cons : sep₁ ≠ chainConsBottom) :
    TM0RealizesInnerBlockSep ChainΓ sep₁ chainConsBottom (binSucc ∘ normalizeBlock) := by
  refine tm0RealizesBlockSep_toInnerOuterSep
    hsep₁
    chainConsBottom_ne_default
    hsep₁_cons
    (tm0RealizesBlockSep_comp
      (tm0_normalizeBlockSep (sep := chainConsBottom) (by decide) (by decide))
      (tm0_binSucc_blockSep (sep := chainConsBottom) (by decide) (by decide))
      (fun _ _ => normalizeBlock_ne_default _)
      (fun _ _ => ?_))
    ?_ ?_
  · unfold normalizeBlock
    exact chainBinaryRepr_no_consBottom _
  · intro block _hblock
    exact binSucc_ne_default _ (normalizeBlock_ne_default block)
  · intro block _hblock
    exact binSucc_no_consBottom _ (by
      unfold normalizeBlock
      exact chainBinaryRepr_no_consBottom _)

/-- On a default-delimited paired block, run normalized binary successor on the
    sub-block after `chainConsBottom`, preserving the prefix before it. -/
theorem tm0_binSuccNormalize_afterConsBottom_innerDefault :
    TM0RealizesInnerBlockDefaultSep ChainΓ chainConsBottom (binSucc ∘ normalizeBlock) := by
  refine tm0RealizesBlockSep_toInnerDefault
    chainConsBottom_ne_default
    (tm0RealizesBlockSep_comp
      (tm0_normalizeBlockSep (sep := chainConsBottom) (by decide) (by decide))
      (tm0_binSucc_blockSep (sep := chainConsBottom) (by decide) (by decide))
      (fun _ _ => normalizeBlock_ne_default _)
      (fun _ _ => ?_))
    ?_ ?_
  · unfold normalizeBlock
    exact chainBinaryRepr_no_consBottom _
  · intro block _hblock
    exact binSucc_ne_default _ (normalizeBlock_ne_default block)
  · intro block _hblock
    exact binSucc_no_consBottom _ (by
      unfold normalizeBlock
      exact chainBinaryRepr_no_consBottom _)

inductive DecAfterSepSt where
  | scan | succ (q : BinSuccSt) | rewind | done

noncomputable instance : DecidableEq DecAfterSepSt := Classical.typeDecidableEq _
noncomputable instance : Inhabited DecAfterSepSt := ⟨.scan⟩
noncomputable instance : Fintype DecAfterSepSt := by
  exact
  { elems := {.scan, .rewind, .done}
      ∪ Finset.univ.map ⟨DecAfterSepSt.succ, fun a b h => by cases h; rfl⟩
    complete := by
      intro x
      cases x <;> simp [Finset.mem_map, Finset.mem_insert] }

noncomputable def decAfterSepMachine : @TM0.Machine ChainΓ DecAfterSepSt ⟨.scan⟩ :=
  fun q a =>
    match q with
    | .scan =>
      if a = chainConsBottom then some (.succ .carry, .move Dir.right)
      else if a = default then some (.rewind, .move Dir.left)
      else some (.scan, .move Dir.right)
    | .succ q =>
      match binSuccMachine q a with
      | some (q', stmt) => some (.succ q', stmt)
      | none => none
    | .rewind =>
      if a = default then some (.done, .move Dir.right)
      else some (.rewind, .move Dir.left)
    | .done => none

theorem decAfterSep_succ_lift {c d : TM0.Cfg ChainΓ BinSuccSt}
    (h : Reaches (TM0.step binSuccMachine) c d) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨DecAfterSepSt.succ c.q, c.Tape⟩
      ⟨DecAfterSepSt.succ d.q, d.Tape⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      refine ih.tail ?_
      unfold TM0.step at hstep ⊢
      simp [decAfterSepMachine] at hstep ⊢
      rcases hstep with ⟨q', stmt, hstep, hcfg⟩
      exact ⟨stmt, by rw [hstep]; cases hcfg; simp⟩

/- The old total proof of `TM0RealizesBlock ChainΓ decAfterSep` required
   proving both branches of the scanner: the paired-block branch and the
   no-separator identity branch. Paired arithmetic only needs the former
   under a well-formedness invariant, so this file no longer exposes that
   too-strong theorem. -/

theorem decAfterSep_step_done (T : Tape ChainΓ) :
    TM0.step decAfterSepMachine ⟨DecAfterSepSt.done, T⟩ = none := by
  simp [TM0.step, decAfterSepMachine]

theorem decAfterSep_step_succ_done (T : Tape ChainΓ) :
    TM0.step decAfterSepMachine ⟨DecAfterSepSt.succ BinSuccSt.done, T⟩ = none := by
  simp [TM0.step, decAfterSepMachine, binSuccMachine]
