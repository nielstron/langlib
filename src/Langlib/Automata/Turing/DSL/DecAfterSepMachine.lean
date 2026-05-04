import Mathlib
import Langlib.Automata.Turing.DSL.SplitAtSep
import Langlib.Automata.Turing.DSL.TakeWhileBlock

/-! # Increment-After-Separator Machine

`incAfterSep` scans to the first `chainConsBottom`. If it finds one, it
delegates to `binSuccMachine` on the right sub-block, using the already-proved
framed successor lemma. If no separator is present, it rewinds and leaves the
block unchanged.
-/

open Turing PartrecToTM2 TM2to1

inductive IncAfterSepSt where
  | scan | succ (q : BinSuccSt) | rewind | done

noncomputable instance : DecidableEq IncAfterSepSt := Classical.typeDecidableEq _
noncomputable instance : Inhabited IncAfterSepSt := ⟨.scan⟩
noncomputable instance : Fintype IncAfterSepSt := by
  exact
  { elems := {.scan, .rewind, .done}
      ∪ Finset.univ.map ⟨IncAfterSepSt.succ, fun a b h => by cases h; rfl⟩
    complete := by
      intro x
      cases x <;> simp [Finset.mem_union, Finset.mem_map, Finset.mem_insert] <;> aesop }

noncomputable def incAfterSepMachine : @TM0.Machine ChainΓ IncAfterSepSt ⟨.scan⟩ :=
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

theorem incAfterSep_succ_lift {c d : TM0.Cfg ChainΓ BinSuccSt}
    (h : Reaches (TM0.step binSuccMachine) c d) :
    Reaches (TM0.step incAfterSepMachine)
      ⟨IncAfterSepSt.succ c.q, c.Tape⟩
      ⟨IncAfterSepSt.succ d.q, d.Tape⟩ := by
  sorry

theorem incAfterSep_scan_right
    (L pfx rest : List ChainΓ)
    (hpfx_nsep : ∀ g ∈ pfx, g ≠ chainConsBottom)
    (hpfx_nd : ∀ g ∈ pfx, g ≠ default) :
    Reaches (TM0.step incAfterSepMachine)
      ⟨.scan, Tape.mk₂ L (pfx ++ rest)⟩
      ⟨.scan, Tape.mk₂ (pfx.reverse ++ L) rest⟩ := by
  sorry

theorem incAfterSep_rewind_after_left
    (L R : List ChainΓ) (hL : ∀ g ∈ L, g ≠ default) :
    Reaches (TM0.step incAfterSepMachine)
      ⟨.rewind, Tape.move Dir.left (Tape.mk₂ L R)⟩
      ⟨.done, Tape.mk₁ (L.reverse ++ R)⟩ := by
  sorry

theorem incAfterSep_reaches_no_sep (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hnot : chainConsBottom ∉ block) :
    Reaches (TM0.step incAfterSepMachine)
      (TM0.init (block ++ default :: suffix))
      ⟨.done, Tape.mk₁ (block ++ default :: suffix)⟩ := by
  sorry

theorem incAfterSep_reaches_sep (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default)
    (hmem : chainConsBottom ∈ block) :
    Reaches (TM0.step incAfterSepMachine)
      (TM0.init (block ++ default :: suffix))
      ⟨.succ .done, Tape.mk₁ (incAfterSep block ++ default :: suffix)⟩ := by
  sorry

theorem incAfterSep_step_done (T : Tape ChainΓ) :
    TM0.step incAfterSepMachine ⟨IncAfterSepSt.done, T⟩ = none := by
  simp [TM0.step, incAfterSepMachine]

theorem incAfterSep_step_succ_done (T : Tape ChainΓ) :
    TM0.step incAfterSepMachine ⟨IncAfterSepSt.succ BinSuccSt.done, T⟩ = none := by
  simp [TM0.step, incAfterSepMachine, binSuccMachine]

theorem incAfterSep_full_reaches (block suffix : List ChainΓ)
    (hblock : ∀ g ∈ block, g ≠ default)
    (hsuffix : ∀ g ∈ suffix, g ≠ default) :
    ∃ q,
      Reaches (TM0.step incAfterSepMachine)
        (TM0.init (block ++ default :: suffix))
        ⟨q, Tape.mk₁ (incAfterSep block ++ default :: suffix)⟩ ∧
      TM0.step incAfterSepMachine ⟨q, Tape.mk₁ (incAfterSep block ++ default :: suffix)⟩ = none := by
  by_cases hmem : chainConsBottom ∈ block
  · exact ⟨.succ .done, incAfterSep_reaches_sep block suffix hblock hsuffix hmem,
      incAfterSep_step_succ_done _⟩
  · have hreach := incAfterSep_reaches_no_sep block suffix hblock hmem
    refine ⟨.done, ?_, incAfterSep_step_done _⟩
    convert hreach using 1
    simp [incAfterSep, mapAfterConsBottom, hmem]

theorem tm0_incAfterSep_block : TM0RealizesBlock ChainΓ incAfterSep := by
  refine ⟨IncAfterSepSt, inferInstance, inferInstance, incAfterSepMachine, ?_⟩
  intro block suffix hblock hsuffix _hresult
  obtain ⟨q, hreach, hhalt⟩ := incAfterSep_full_reaches block suffix hblock hsuffix
  constructor
  · exact Part.dom_iff_mem.mpr ⟨_, Turing.mem_eval.mpr ⟨hreach, hhalt⟩⟩
  · intro h
    exact (Part.mem_unique (Part.get_mem h)
      (Turing.mem_eval.mpr ⟨hreach, hhalt⟩)).symm ▸ rfl
