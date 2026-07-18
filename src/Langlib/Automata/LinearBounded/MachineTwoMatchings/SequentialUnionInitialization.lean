module

public import Langlib.Automata.LinearBounded.MachineTwoMatchings.SequentialUnion
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical initialization of the sequential two-matching scheduler

The sequential scheduler starts on the ordinary endmarker tape over its enlarged backup
alphabet.  Its first rightward sweep replaces every canonical raw symbol by a packed cell whose
immutable and mutable tracks both contain the corresponding source symbol.  This file proves the
exact end-to-end initialization reachability theorem, including the empty input.
-/

namespace LBA.MachineTwoMatchings

open Classical Relation

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]

private abbrev SourceInitTape (input : List T) :=
  DLBA.BoundedTape (EndAlpha T Γ) (input.length + 1)

private abbrev TargetInitTape (input : List T) :=
  DLBA.BoundedTape (BackupAlpha T Γ) (input.length + 1)

private noncomputable def sourceInitTape (input : List T) : SourceInitTape (Γ := Γ) input :=
  LBA.loadEnd (T := T) (Γ := Γ) input

private noncomputable def targetInitTape (input : List T) : TargetInitTape (Γ := Γ) input :=
  LBA.loadEnd (T := T) (Γ := BackupCell T Γ) input

/-- The packed representation installed at one canonical input position. -/
private noncomputable def initializedCell (input : List T)
    (index : Fin (input.length + 2)) : BackupCell T Γ :=
  { original := (sourceInitTape (Γ := Γ) input).contents index
    current := (sourceInitTape (Γ := Γ) input).contents index
    boundary := boundaryAt (input.length + 1) index }

/-- Exactly the positions strictly below `converted` have been packed. -/
private noncomputable def sweepAt (input : List T) (converted : ℕ)
    (index : Fin (input.length + 2)) : BackupAlpha T Γ :=
  if index.val < converted then pack (initializedCell (Γ := Γ) input index)
  else (targetInitTape (Γ := Γ) input).contents index

private theorem cfg_eq {A Q : Type*} {n : ℕ}
    {state state' : Q} {contents contents' : Fin (n + 1) → A}
    {head head' : Fin (n + 1)}
    (hstate : state = state') (hcontents : contents = contents') (hhead : head = head') :
    (⟨state, ⟨contents, head⟩⟩ : DLBA.Cfg A Q n) = ⟨state', ⟨contents', head'⟩⟩ := by
  subst state'
  subst contents'
  subst head'
  rfl

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
/-- A canonical raw target symbol decodes to the corresponding source symbol. -/
private theorem rawSourceSymbol_targetInit (input : List T)
    (index : Fin (input.length + 2)) :
    rawSourceSymbol ((targetInitTape (Γ := Γ) input).contents index) =
      some ((sourceInitTape (Γ := Γ) input).contents index) := by
  unfold targetInitTape sourceInitTape LBA.loadEnd
  dsimp only
  split <;> rename_i hleft
  · rfl
  · split <;> rfl

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
/-- Updating the cell under the head extends the packed prefix by one. -/
private theorem sweepAt_update (input : List T) (index : Fin (input.length + 2)) :
    Function.update (sweepAt (Γ := Γ) input index.val) index
        (pack (initializedCell (Γ := Γ) input index)) =
      sweepAt (Γ := Γ) input (index.val + 1) := by
  funext other
  rw [Function.update_apply]
  by_cases heq : other = index
  · subst other
    simp [sweepAt]
  · have hval : other.val ≠ index.val := fun h => heq (Fin.ext h)
    rw [if_neg heq]
    simp only [sweepAt]
    by_cases hlt : other.val < index.val
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
private theorem sweepAt_full (input : List T) :
    sweepAt (Γ := Γ) input (input.length + 2) =
      fun index => pack (initializedCell (Γ := Γ) input index) := by
  funext index
  simp only [sweepAt]
  rw [if_pos index.isLt]

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
/-- At a genuine interior position, the initialization table installs the canonical packed
source symbol and moves right. -/
private theorem initializeCell_targetInit_middle (input : List T)
    (index : Fin (input.length + 2))
    (hpos : 0 < index.val) (hlt : index.val < input.length + 1) :
    initializeCell ((targetInitTape (Γ := Γ) input).contents index) .middle =
      some (pack (initializedCell (Γ := Γ) input index)) := by
  have hzero : index.val ≠ 0 := by omega
  have hlast : index.val ≠ input.length + 1 := by omega
  simp only [initializeCell, rawSourceSymbol_targetInit]
  simp [initializedCell, boundaryAt, hzero, hlast]

omit [DecidableEq Λ] in
private theorem step_initializeLeft
    (M : Machine (EndAlpha T Γ) Λ) (input : List T) :
    Step (sequentialUnion M)
      (LBA.initCfgEnd (sequentialUnion M) input)
      ⟨.initializeRight,
        ⟨sweepAt (Γ := Γ) input 1, ⟨1, by omega⟩⟩⟩ := by
  let zero : Fin (input.length + 2) := ⟨0, by omega⟩
  refine ⟨.initializeRight,
    pack (initializedCell (Γ := Γ) input zero), .right, ?_, ?_⟩
  · change
      (.initializeRight, pack (initializedCell (Γ := Γ) input zero), .right) ∈
        sequentialTransition M .initializeLeft
          ((targetInitTape (Γ := Γ) input).contents zero)
    have hread :
        (targetInitTape (Γ := Γ) input).contents zero =
          (leftMark : BackupAlpha T Γ) := by
      simp [targetInitTape, LBA.loadEnd, zero]
    have hcell : initializedCell (Γ := Γ) input zero =
        { original := leftMark, current := leftMark, boundary := .left } := by
      simp [initializedCell, sourceInitTape, LBA.loadEnd, boundaryAt, zero]
    rw [hread]
    simp [sequentialTransition, hcell]
  · change
      (⟨.initializeRight,
          ⟨sweepAt (Γ := Γ) input 1, ⟨1, by omega⟩⟩⟩ :
        DLBA.Cfg (BackupAlpha T Γ) (SequentialState T Γ Λ) (input.length + 1)) =
        ⟨.initializeRight,
          ((targetInitTape (Γ := Γ) input).write
            (pack (initializedCell (Γ := Γ) input zero))).moveHead .right⟩
    symm
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    apply cfg_eq rfl
    · have hzero :
          sweepAt (Γ := Γ) input 0 =
            (targetInitTape (Γ := Γ) input).contents := by
        funext index
        simp [sweepAt]
      rw [← hzero]
      simpa [zero] using sweepAt_update (Γ := Γ) input zero
    · apply Fin.ext
      simp [targetInitTape, LBA.loadEnd]

omit [DecidableEq Λ] in
private theorem step_initializeRight
    (M : Machine (EndAlpha T Γ) Λ) (input : List T)
    (index : Fin (input.length + 2))
    (hpos : 0 < index.val) (hlt : index.val < input.length + 1) :
    Step (sequentialUnion M)
      ⟨.initializeRight,
        ⟨sweepAt (Γ := Γ) input index.val, index⟩⟩
      ⟨.initializeRight,
        ⟨sweepAt (Γ := Γ) input (index.val + 1),
          ⟨index.val + 1, by omega⟩⟩⟩ := by
  refine ⟨.initializeRight,
    pack (initializedCell (Γ := Γ) input index), .right, ?_, ?_⟩
  · change
      (.initializeRight, pack (initializedCell (Γ := Γ) input index), .right) ∈
        sequentialTransition M .initializeRight
          (sweepAt (Γ := Γ) input index.val index)
    have hsweep : sweepAt (Γ := Γ) input index.val index =
        (targetInitTape (Γ := Γ) input).contents index := by
      simp [sweepAt]
    rw [hsweep]
    rw [sequentialTransition]
    have hnotRight :
        (targetInitTape (Γ := Γ) input).contents index ≠
          (rightMark : BackupAlpha T Γ) := by
      unfold targetInitTape LBA.loadEnd
      dsimp only
      rw [if_neg (by omega)]
      split
      · simp
      · omega
    rw [if_neg hnotRight, initializeCell_targetInit_middle (Γ := Γ) input index hpos hlt]
    simp
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, dif_pos hlt,
      sweepAt_update]

omit [DecidableEq Λ] in
private theorem reaches_initializeRight_last
    (M : Machine (EndAlpha T Γ) Λ) (input : List T) :
    Reaches (sequentialUnion M)
      ⟨.initializeRight,
        ⟨sweepAt (Γ := Γ) input 1, ⟨1, by omega⟩⟩⟩
      ⟨.initializeRight,
        ⟨sweepAt (Γ := Γ) input (input.length + 1),
          Fin.last (input.length + 1)⟩⟩ := by
  suffices hreach :
      ∀ distance, ∀ index : Fin (input.length + 2),
        1 ≤ index.val →
        input.length + 1 - index.val = distance →
        Reaches (sequentialUnion M)
          ⟨.initializeRight,
            ⟨sweepAt (Γ := Γ) input index.val, index⟩⟩
          ⟨.initializeRight,
            ⟨sweepAt (Γ := Γ) input (input.length + 1),
              Fin.last (input.length + 1)⟩⟩ from
    hreach input.length ⟨1, by omega⟩ (by simp) (by simp)
  intro distance
  induction distance with
  | zero =>
      intro index hpos hdistance
      have hlast : index.val = input.length + 1 := by
        have := index.isLt
        omega
      have hindex : index = Fin.last (input.length + 1) := Fin.ext (by simpa using hlast)
      subst index
      exact .refl
  | succ distance ih =>
      intro index hpos hdistance
      have hlt : index.val < input.length + 1 := by omega
      let next : Fin (input.length + 2) := ⟨index.val + 1, by omega⟩
      exact ReflTransGen.head
        (step_initializeRight M input index (by omega) hlt)
        (ih next (by simp [next]) (by simp [next]; omega))

/-- Canonical source contents with the head one cell left of the right endmarker, exactly where
the initialization sweep leaves it. -/
@[expose]
public noncomputable def postInitializationTape (input : List T) :
    DLBA.BoundedTape (EndAlpha T Γ) (input.length + 1) :=
  ⟨(LBA.loadEnd (T := T) (Γ := Γ) input).contents, ⟨input.length, by omega⟩⟩

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
@[simp]
public theorem postInitializationTape_contents (input : List T) :
    (postInitializationTape (Γ := Γ) input).contents =
      (LBA.loadEnd (T := T) (Γ := Γ) input).contents := rfl

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
@[simp]
public theorem postInitializationTape_head_val (input : List T) :
    (postInitializationTape (Γ := Γ) input).head.val = input.length := rfl

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
@[simp]
public theorem leftBoundedTape_loadEnd_contents (input : List T) :
    leftBoundedTape (LBA.loadEnd (T := T) (Γ := Γ) input).contents =
      LBA.loadEnd (T := T) (Γ := Γ) input := rfl

omit [DecidableEq Λ] in
private theorem step_finish_initialization
    (M : Machine (EndAlpha T Γ) Λ) (input : List T) :
    Step (sequentialUnion M)
      ⟨.initializeRight,
        ⟨sweepAt (Γ := Γ) input (input.length + 1),
          Fin.last (input.length + 1)⟩⟩
      ⟨.rewind 0,
        packedTape (sourceInitTape (Γ := Γ) input).contents
          (postInitializationTape (Γ := Γ) input)⟩ := by
  let last : Fin (input.length + 2) := Fin.last (input.length + 1)
  refine ⟨.rewind 0,
    pack (initializedCell (Γ := Γ) input last), .left, ?_, ?_⟩
  · change
      (.rewind 0, pack (initializedCell (Γ := Γ) input last), .left) ∈
        sequentialTransition M .initializeRight
          (sweepAt (Γ := Γ) input (input.length + 1) last)
    have hsweep : sweepAt (Γ := Γ) input (input.length + 1) last =
        (rightMark : BackupAlpha T Γ) := by
      simp [sweepAt, last, targetInitTape, LBA.loadEnd]
    have hcell : initializedCell (Γ := Γ) input last =
        { original := rightMark, current := rightMark, boundary := .right } := by
      simp [initializedCell, sourceInitTape, LBA.loadEnd, boundaryAt, last]
    rw [hsweep]
    simp [sequentialTransition, hcell]
  · change
      (⟨.rewind 0,
          packedTape (sourceInitTape (Γ := Γ) input).contents
            (postInitializationTape (Γ := Γ) input)⟩ :
        DLBA.Cfg (BackupAlpha T Γ) (SequentialState T Γ Λ) (input.length + 1)) =
        ⟨.rewind 0,
          ((⟨sweepAt (Γ := Γ) input (input.length + 1), last⟩ :
              DLBA.BoundedTape (BackupAlpha T Γ) (input.length + 1)).write
            (pack (initializedCell (Γ := Γ) input last))).moveHead .left⟩
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    apply cfg_eq rfl
    · change
        (fun index => pack {
          original := (sourceInitTape (Γ := Γ) input).contents index
          current := (sourceInitTape (Γ := Γ) input).contents index
          boundary := boundaryAt (input.length + 1) index }) =
          Function.update (sweepAt (Γ := Γ) input (input.length + 1)) last
            (pack (initializedCell (Γ := Γ) input last))
      calc
        _ = sweepAt (Γ := Γ) input (input.length + 2) :=
          (sweepAt_full (Γ := Γ) input).symm
        _ = sweepAt (Γ := Γ) input (last.val + 1) := by simp [last]
        _ = Function.update (sweepAt (Γ := Γ) input last.val) last
              (pack (initializedCell (Γ := Γ) input last)) :=
          (sweepAt_update (Γ := Γ) input last).symm
        _ = _ := by simp [last]
    · apply Fin.ext
      simp [postInitializationTape, last]

omit [DecidableEq Λ] in
/-- Canonical initialization reaches the fully packed source tape in the first rewind phase.
The statement includes `input = []`, whose physical endmarker tape still has two cells. -/
public theorem reaches_rewind_zero_init
    (M : Machine (EndAlpha T Γ) Λ) (input : List T) :
    Reaches (sequentialUnion M)
      (LBA.initCfgEnd (sequentialUnion M) input)
      ⟨.rewind 0,
        packedTape (LBA.loadEnd (T := T) (Γ := Γ) input).contents
          (postInitializationTape (Γ := Γ) input)⟩ := by
  exact (ReflTransGen.head (step_initializeLeft M input)
    (reaches_initializeRight_last M input)).tail
      (step_finish_initialization M input)

end LBA.MachineTwoMatchings

end
