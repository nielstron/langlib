import Mathlib
import Langlib.Automata.Turing.DSL.SplitAtSep
import Langlib.Automata.Turing.DSL.TakeWhileBlock

/-! # Increment-After-Separator Machine

`decAfterSep` scans to the first `chainConsBottom`. If it finds one, it
delegates to `binSuccMachine` on the right sub-block, using the already-proved
framed successor lemma. If no separator is present, it rewinds and leaves the
block unchanged.
-/

open Turing PartrecToTM2 TM2to1

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
      cases x <;> simp [Finset.mem_union, Finset.mem_map, Finset.mem_insert] <;> aesop }

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
  sorry

theorem decAfterSep_scan_right
    (L pfx rest : List ChainΓ)
    (hpfx_nsep : ∀ g ∈ pfx, g ≠ chainConsBottom)
    (hpfx_nd : ∀ g ∈ pfx, g ≠ default) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨.scan, Tape.mk₂ L (pfx ++ rest)⟩
      ⟨.scan, Tape.mk₂ (pfx.reverse ++ L) rest⟩ := by
  sorry

theorem decAfterSep_rewind_after_left
    (L R : List ChainΓ) (hL : ∀ g ∈ L, g ≠ default) :
    Reaches (TM0.step decAfterSepMachine)
      ⟨.rewind, Tape.move Dir.left (Tape.mk₂ L R)⟩
      ⟨.done, Tape.mk₁ (L.reverse ++ R)⟩ := by
  sorry

theorem decAfterSep_reaches_no_sep (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hnot : chainConsBottom ∉ block) :
    Reaches (TM0.step decAfterSepMachine)
      (TM0.init (block ++ default :: suffix))
      ⟨.done, Tape.mk₁ (block ++ default :: suffix)⟩ := by
  sorry

theorem decAfterSep_reaches_sep (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hmem : chainConsBottom ∈ block) :
    Reaches (TM0.step decAfterSepMachine)
      (TM0.init (block ++ default :: suffix))
      ⟨.succ .done, Tape.mk₁ (decAfterSep block ++ default :: suffix)⟩ := by
  sorry

theorem decAfterSep_step_done (T : Tape ChainΓ) :
    TM0.step decAfterSepMachine ⟨DecAfterSepSt.done, T⟩ = none := by
  simp [TM0.step, decAfterSepMachine]

theorem decAfterSep_step_succ_done (T : Tape ChainΓ) :
    TM0.step decAfterSepMachine ⟨DecAfterSepSt.succ BinSuccSt.done, T⟩ = none := by
  simp [TM0.step, decAfterSepMachine, binSuccMachine]

theorem decAfterSep_full_reaches (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    ∃ q,
      Reaches (TM0.step decAfterSepMachine)
        (TM0.init (block ++ default :: suffix))
        ⟨q, Tape.mk₁ (decAfterSep block ++ default :: suffix)⟩ ∧
      TM0.step decAfterSepMachine ⟨q, Tape.mk₁ (decAfterSep block ++ default :: suffix)⟩ = none := by
  by_cases hmem : chainConsBottom ∈ block
  · exact ⟨.succ .done, decAfterSep_reaches_sep block suffix hblock hsuffix hmem,
      decAfterSep_step_succ_done _⟩
  · have hreach := decAfterSep_reaches_no_sep block suffix hblock hmem
    refine ⟨.done, ?_, decAfterSep_step_done _⟩
    convert hreach using 1
    simp [decAfterSep, hmem]

theorem tm0_decAfterSep_block : TM0RealizesBlock ChainΓ decAfterSep := by
  refine ⟨DecAfterSepSt, inferInstance, inferInstance, decAfterSepMachine, ?_⟩
  intro block suffix hblock hsuffix _hresult
  obtain ⟨q, hreach, hhalt⟩ := decAfterSep_full_reaches block suffix hblock hsuffix
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr ⟨hreach, hhalt⟩⟩
  · intro h
    exact (Part.mem_unique (Part.get_mem h)
      (Turing.mem_eval.mpr ⟨hreach, hhalt⟩)).symm ▸ rfl
