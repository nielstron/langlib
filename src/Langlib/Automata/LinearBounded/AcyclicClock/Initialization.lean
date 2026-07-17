module

public import Langlib.Automata.LinearBounded.AcyclicClock.ReadyEncoding
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical initialization of the operational clock compiler

The compiler begins on the ordinary canonical target tape `⊢ w ⊣`.  This file gives explicit
intermediate tapes for its two initialization sweeps:

* `sweepAt k` has converted exactly the cells with index below `k`;
* `backAt i` has installed the actual right endpoint and has already cleared the initialization
  bit strictly to the right of `i`.

The resulting end-to-end theorem proves that the compiled machine reaches the clean zero-clock
encoding of the source machine's own canonical initial configuration.  No language-equivalence or
global-acyclicity claim is made here.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}

section

variable [Fintype T] [Fintype Γ] [Fintype Λ]

private abbrev SourceInitTape (input : List T) :=
  DLBA.BoundedTape (SourceAlpha T Γ) (input.length + 1)

private abbrev TargetInitTape (input : List T) :=
  DLBA.BoundedTape (TapeAlpha T Γ Λ) (input.length + 1)

private noncomputable def sourceInitTape (input : List T) :
    SourceInitTape (Γ := Γ) input :=
  LBA.loadEnd (T := T) (Γ := Γ) input

private noncomputable def targetInitTape (input : List T) :
    TargetInitTape (Γ := Γ) (Λ := Λ) input :=
  LBA.loadEnd (T := T) (Γ := WorkCell T Γ Λ) input

/-- Work cell written by the rightward conversion sweep.  The actual right bit is installed only
after physical right clamping is detected. -/
private noncomputable def initCell
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (index : Fin (input.length + 2)) :
    WorkCell T Γ Λ :=
  freshCell (clockZero M) ((sourceInitTape (Γ := Γ) input).contents index)
    (decide (index.val = 0)) (decide (index.val = 0))

/-- Exactly the prefix of length `converted` has been converted to work symbols. -/
private noncomputable def sweepAt
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (converted : ℕ) (index : Fin (input.length + 2)) :
    TapeAlpha T Γ Λ :=
  if index.val < converted then
    workSymbol (initCell M input index)
  else
    (targetInitTape (Γ := Γ) (Λ := Λ) input).contents index

/-- During the return sweep, cells at or left of `current` retain `init = true`; cells strictly
to its right are already canonical. -/
private noncomputable def backCell
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (current : ℕ) (index : Fin (input.length + 2)) :
    WorkCell T Γ Λ :=
  { canonicalCell M (sourceInitTape (Γ := Γ) input) index with
    init := decide (index.val ≤ current) }

private noncomputable def backAt
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (current : ℕ) (index : Fin (input.length + 2)) :
    TapeAlpha T Γ Λ :=
  workSymbol (backCell M input current index)

private theorem cfg_eq {A Q : Type*} {n : ℕ}
    {s s' : Q} {contents contents' : Fin (n + 1) → A}
    {head head' : Fin (n + 1)}
    (hs : s = s') (hc : contents = contents') (hh : head = head') :
    (⟨s, ⟨contents, head⟩⟩ : DLBA.Cfg A Q n) =
      ⟨s', ⟨contents', head'⟩⟩ := by
  subst s'
  subst contents'
  subst head'
  rfl

/-- Raw target endmarker symbols decode to the corresponding source endmarker symbols. -/
private theorem asRawSource_targetInit
    (input : List T) (index : Fin (input.length + 2)) :
    asRawSource
        ((targetInitTape (Γ := Γ) (Λ := Λ) input).contents index) =
      some ((sourceInitTape (Γ := Γ) input).contents index) := by
  unfold targetInitTape sourceInitTape LBA.loadEnd
  dsimp only
  split <;> rename_i hleft
  · rfl
  · split <;> rfl

private theorem transition_initSweep_of_asRawSource
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {symbol : TapeAlpha T Γ Λ} {source : SourceAlpha T Γ}
    (hsource : asRawSource symbol = some source) :
    transition M .initSweep symbol =
      {(.initSweep,
        workSymbol (freshCell (clockZero M) source false false),
        .right)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rcases symbol with inner | boundary
  · cases inner with
    | none =>
        simp only [asRawSource, Option.some.injEq] at hsource
        subst source
        rfl
    | some tagged =>
        cases tagged with
        | inl input =>
            simp only [asRawSource, Option.some.injEq] at hsource
            subst source
            rfl
        | inr cell =>
            cases hsource
  · simp only [asRawSource, Option.some.injEq] at hsource
    subst source
    rfl

/-- Updating the current raw cell extends the converted prefix by one. -/
private theorem sweepAt_update
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (index : Fin (input.length + 2)) :
    Function.update (sweepAt M input index.val) index
        (workSymbol (initCell M input index)) =
      sweepAt M input (index.val + 1) := by
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

private theorem sweepAt_full
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    sweepAt M input (input.length + 2) =
      fun index => workSymbol (initCell M input index) := by
  funext index
  simp only [sweepAt]
  rw [if_pos index.isLt]

private theorem initCell_source_matches_raw
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (index : Fin (input.length + 2)) (hpos : 0 < index.val) :
    transition M .initSweep
        ((targetInitTape (Γ := Γ) (Λ := Λ) input).contents index) =
      {(.initSweep, workSymbol (initCell M input index), .right)} := by
  rw [transition_initSweep_of_asRawSource M
    (asRawSource_targetInit (Γ := Γ) (Λ := Λ) input index)]
  congr 3
  simp [initCell, hpos.ne']

private theorem convert_step_right
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (index : Fin (input.length + 2))
    (hpos : 0 < index.val)
    (hlt : index.val < input.length + 1) :
    LBA.Step (machine M)
      ⟨.initSweep, ⟨sweepAt M input index.val, index⟩⟩
      ⟨.initSweep,
        ⟨sweepAt M input (index.val + 1),
          ⟨index.val + 1, by omega⟩⟩⟩ := by
  refine ⟨.initSweep, workSymbol (initCell M input index), .right, ?_, ?_⟩
  · change
      (.initSweep, workSymbol (initCell M input index), .right) ∈
        transition M .initSweep (sweepAt M input index.val index)
    rw [show sweepAt M input index.val index =
        (targetInitTape (Γ := Γ) (Λ := Λ) input).contents index by
      simp [sweepAt]]
    rw [initCell_source_matches_raw M input index hpos]
    simp
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
      dif_pos hlt, sweepAt_update]

private theorem convert_step_last
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (index : Fin (input.length + 2))
    (hpos : 0 < index.val)
    (hlast : index.val = input.length + 1) :
    LBA.Step (machine M)
      ⟨.initSweep, ⟨sweepAt M input index.val, index⟩⟩
      ⟨.initSweep, ⟨sweepAt M input (index.val + 1), index⟩⟩ := by
  refine ⟨.initSweep, workSymbol (initCell M input index), .right, ?_, ?_⟩
  · change
      (.initSweep, workSymbol (initCell M input index), .right) ∈
        transition M .initSweep (sweepAt M input index.val index)
    rw [show sweepAt M input index.val index =
        (targetInitTape (Γ := Γ) (Λ := Λ) input).contents index by
      simp [sweepAt]]
    rw [initCell_source_matches_raw M input index hpos]
    simp
  · have hnot : ¬ index.val < input.length + 1 := by omega
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
      dif_neg hnot, sweepAt_update]

private theorem convert_sweep
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    ∀ index : Fin (input.length + 2), 1 ≤ index.val →
      LBA.Reaches (machine M)
        ⟨.initSweep, ⟨sweepAt M input index.val, index⟩⟩
        ⟨.initSweep,
          ⟨sweepAt M input (input.length + 2),
            Fin.last (input.length + 1)⟩⟩ := by
  suffices H :
      ∀ distance, ∀ index : Fin (input.length + 2),
        1 ≤ index.val →
        input.length + 1 - index.val = distance →
        LBA.Reaches (machine M)
          ⟨.initSweep, ⟨sweepAt M input index.val, index⟩⟩
          ⟨.initSweep,
            ⟨sweepAt M input (input.length + 2),
              Fin.last (input.length + 1)⟩⟩ from
    fun index hindex =>
      H (input.length + 1 - index.val) index hindex rfl
  intro distance
  induction distance with
  | zero =>
      intro index hindex hdistance
      have hlast : index.val = input.length + 1 := by
        have := index.isLt
        omega
      have hfin : index = Fin.last (input.length + 1) := by
        apply Fin.ext
        simpa using hlast
      have hcfg :
          (⟨State.initSweep,
              ⟨sweepAt M input (index.val + 1), index⟩⟩ :
            DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) (input.length + 1)) =
            ⟨.initSweep,
              ⟨sweepAt M input (input.length + 2),
                Fin.last (input.length + 1)⟩⟩ := by
        rw [hfin]
        simp
      exact .single
        (hcfg ▸ convert_step_last M input index (by omega) hlast)
  | succ distance ih =>
      intro index hindex hdistance
      have hlt : index.val < input.length + 1 := by omega
      let next : Fin (input.length + 2) :=
        ⟨index.val + 1, by omega⟩
      exact ReflTransGen.head
        (convert_step_right M input index (by omega) hlt)
        (ih next (by simp [next])
          (by simp [next]; omega))

private theorem step_initFirst
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    LBA.Step (machine M)
      (LBA.initCfgEnd (machine M) input)
      ⟨.initSweep,
        ⟨sweepAt M input 1, ⟨1, by omega⟩⟩⟩ := by
  let zero : Fin (input.length + 2) := ⟨0, by omega⟩
  have hsource :
      (sourceInitTape (Γ := Γ) input).contents zero =
        LBA.leftMark (T := T) (Γ := Γ) := by
    simp [sourceInitTape, LBA.loadEnd, zero]
  have hcell :
      initCell M input zero =
        freshCell (clockZero M)
          (LBA.leftMark (T := T) (Γ := Γ)) true true := by
    unfold initCell
    rw [hsource]
    simp [zero]
  refine ⟨.initSweep, workSymbol (initCell M input zero), .right, ?_, ?_⟩
  · change
      (.initSweep, workSymbol (initCell M input zero), .right) ∈
        transition M .initFirst
          ((targetInitTape (Γ := Γ) (Λ := Λ) input).contents zero)
    have hread :
        (targetInitTape (Γ := Γ) (Λ := Λ) input).contents zero =
          LBA.leftMark (T := T) (Γ := WorkCell T Γ Λ) := by
      simp [targetInitTape, LBA.loadEnd, zero]
    rw [hread, transition_initFirst_leftMark, hcell]
    simp
  · change
      (⟨State.initSweep, ⟨sweepAt M input 1, ⟨1, by omega⟩⟩⟩ :
        DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) (input.length + 1)) =
        ⟨.initSweep,
          ((LBA.loadEnd (T := T) (Γ := WorkCell T Γ Λ) input).write
            (workSymbol (initCell M input zero))).moveHead .right⟩
    symm
    simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    apply cfg_eq rfl
    · have hhead :
          (LBA.loadEnd (T := T) (Γ := WorkCell T Γ Λ) input).head = zero := rfl
      have hzero :
          sweepAt M input 0 =
            (LBA.loadEnd (T := T) (Γ := WorkCell T Γ Λ) input).contents := by
        funext index
        simp [sweepAt, targetInitTape]
      rw [hhead, ← hzero]
      simpa [zero] using sweepAt_update M input zero
    · apply Fin.ext
      simp [LBA.loadEnd]

private theorem reaches_full_sweep
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    LBA.Reaches (machine M)
      (LBA.initCfgEnd (machine M) input)
      ⟨.initSweep,
        ⟨sweepAt M input (input.length + 2),
          Fin.last (input.length + 1)⟩⟩ := by
  exact ReflTransGen.head (step_initFirst M input)
    (convert_sweep M input ⟨1, by omega⟩ (by simp))

private theorem detected_eq_backAt_last
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    Function.update
        (sweepAt M input (input.length + 2))
        (Fin.last (input.length + 1))
        (workSymbol
          { initCell M input (Fin.last (input.length + 1)) with right := true }) =
      backAt M input (input.length + 1) := by
  funext index
  rw [Function.update_apply]
  by_cases hlast : index = Fin.last (input.length + 1)
  · subst index
    simp [backAt, backCell, initCell, canonicalCell, sourceInitTape,
      freshCell, LBA.loadEnd]
  · rw [if_neg hlast]
    rw [sweepAt_full]
    have hval : index.val ≠ input.length + 1 := by
      intro h
      exact hlast (Fin.ext (by simpa using h))
    have hle : index.val ≤ input.length + 1 := by
      have := index.isLt
      omega
    simp [backAt, backCell, initCell, canonicalCell, sourceInitTape,
      freshCell, LBA.loadEnd, hval, hle]

private theorem step_detect_right
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    LBA.Step (machine M)
      ⟨.initSweep,
        ⟨sweepAt M input (input.length + 2),
          Fin.last (input.length + 1)⟩⟩
      ⟨.initBack,
        ⟨backAt M input (input.length + 1),
          Fin.last (input.length + 1)⟩⟩ := by
  let last := Fin.last (input.length + 1)
  let cell := initCell M input last
  refine ⟨.initBack, workSymbol { cell with right := true }, .stay, ?_, ?_⟩
  · change
      (.initBack, workSymbol { cell with right := true }, .stay) ∈
        transition M .initSweep
          (sweepAt M input (input.length + 2) last)
    rw [sweepAt_full]
    change
      (.initBack, workSymbol { cell with right := true }, .stay) ∈
        transition M .initSweep (workSymbol cell)
    rw [transition_initSweep_work, if_pos]
    · simp
    · simp [cell, initCell, freshCell]
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    apply cfg_eq rfl
    · exact (detected_eq_backAt_last M input).symm
    · rfl

private theorem backAt_update
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (index : Fin (input.length + 2)) (hpos : 0 < index.val) :
    Function.update (backAt M input index.val) index
        (workSymbol { backCell M input index.val index with init := false }) =
      backAt M input (index.val - 1) := by
  funext other
  rw [Function.update_apply]
  by_cases heq : other = index
  · subst other
    simp [backAt, backCell, canonicalCell,
      show ¬ index.val ≤ index.val - 1 by omega]
  · rw [if_neg heq]
    have hval : other.val ≠ index.val := fun h => heq (Fin.ext h)
    simp only [backAt]
    apply congrArg workSymbol
    simp only [backCell]
    by_cases hlt : other.val < index.val
    · rw [show decide (other.val ≤ index.val) = true by
          simp [Nat.le_of_lt hlt],
        show decide (other.val ≤ index.val - 1) = true by
          simp [show other.val ≤ index.val - 1 by omega]]
    · rw [show decide (other.val ≤ index.val) = false by
          simp [show ¬ other.val ≤ index.val by omega],
        show decide (other.val ≤ index.val - 1) = false by
          simp [show ¬ other.val ≤ index.val - 1 by omega]]

private theorem back_step_left
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T)
    (index : Fin (input.length + 2)) (hpos : 0 < index.val) :
    LBA.Step (machine M)
      ⟨.initBack, ⟨backAt M input index.val, index⟩⟩
      ⟨.initBack,
        ⟨backAt M input (index.val - 1),
          ⟨index.val - 1, by omega⟩⟩⟩ := by
  let cell := backCell M input index.val index
  refine ⟨.initBack, workSymbol { cell with init := false }, .left, ?_, ?_⟩
  · change
      (.initBack, workSymbol { cell with init := false }, .left) ∈
        transition M .initBack (backAt M input index.val index)
    change
      (.initBack, workSymbol { cell with init := false }, .left) ∈
        transition M .initBack (workSymbol cell)
    rw [transition_initBack_work, if_neg, if_pos]
    · simp
    · simp [cell, backCell]
    · simp [cell, backCell, canonicalCell, hpos.ne']
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
      dif_pos hpos]
    exact cfg_eq rfl (backAt_update M input index hpos).symm rfl

private theorem back_sweep
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    ∀ index : Fin (input.length + 2),
      LBA.Reaches (machine M)
        ⟨.initBack, ⟨backAt M input index.val, index⟩⟩
        ⟨.initBack, ⟨backAt M input 0, ⟨0, by omega⟩⟩⟩ := by
  suffices H :
      ∀ value, ∀ index : Fin (input.length + 2), index.val = value →
        LBA.Reaches (machine M)
          ⟨.initBack, ⟨backAt M input value, index⟩⟩
          ⟨.initBack, ⟨backAt M input 0, ⟨0, by omega⟩⟩⟩ from
    fun index => H index.val index rfl
  intro value
  induction value with
  | zero =>
      intro index hvalue
      have hindex : index = ⟨0, by omega⟩ := by
        apply Fin.ext
        simpa using hvalue
      rw [hindex]
      exact .refl
  | succ value ih =>
      intro index hvalue
      have hpos : 0 < index.val := by omega
      let previous : Fin (input.length + 2) :=
        ⟨index.val - 1, by omega⟩
      have hprevious : previous.val = value := by
        simp [previous]
        omega
      have hstep := back_step_left M input index hpos
      have hstep' :
          LBA.Step (machine M)
            ⟨.initBack, ⟨backAt M input (value + 1), index⟩⟩
            ⟨.initBack, ⟨backAt M input value, previous⟩⟩ := by
        simpa [hvalue, hprevious, previous] using hstep
      exact ReflTransGen.head hstep' (ih previous hprevious)

private theorem finish_back_eq_canonical
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    Function.update (backAt M input 0) (⟨0, by omega⟩)
        (workSymbol
          (backCell M input 0 (⟨0, by omega⟩)).clearTransient) =
      (canonicalTape M (sourceInitTape (Γ := Γ) input)).contents := by
  funext index
  rw [Function.update_apply]
  by_cases hzero : index = ⟨0, by omega⟩
  · subst index
    change
      workSymbol
          (backCell M input 0 (⟨0, by omega⟩)).clearTransient =
        workSymbol
          (canonicalCell M (sourceInitTape (Γ := Γ) input)
            (⟨0, by omega⟩))
    apply congrArg workSymbol
    simp only [backCell]
    rw [show decide ((0 : ℕ) ≤ 0) = true by simp]
    unfold WorkCell.clearTransient canonicalCell
    rfl
  · rw [if_neg hzero]
    have hval : index.val ≠ 0 := by
      intro h
      exact hzero (Fin.ext h)
    change
      workSymbol (backCell M input 0 index) =
        workSymbol
          (canonicalCell M (sourceInitTape (Γ := Γ) input) index)
    apply congrArg workSymbol
    simp only [backCell]
    rw [show decide (index.val ≤ 0) = false by simp [hval]]
    rfl

private theorem step_finish_back
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    LBA.Step (machine M)
      ⟨.initBack, ⟨backAt M input 0, ⟨0, by omega⟩⟩⟩
      (canonicalCfg M (LBA.initCfgEnd M input)) := by
  let zero : Fin (input.length + 2) := ⟨0, by omega⟩
  let cell := backCell M input 0 zero
  refine ⟨.ready M.initial, workSymbol cell.clearTransient, .stay, ?_, ?_⟩
  · change
      (.ready M.initial, workSymbol cell.clearTransient, .stay) ∈
        transition M .initBack (backAt M input 0 zero)
    change
      (.ready M.initial, workSymbol cell.clearTransient, .stay) ∈
        transition M .initBack (workSymbol cell)
    rw [transition_initBack_work, if_pos, if_pos]
    · simp
    · simp [cell, backCell, zero]
    · simp [cell, backCell, canonicalCell, zero]
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    change
      canonicalCfg M (LBA.initCfgEnd M input) =
        (⟨State.ready M.initial,
          ⟨Function.update (backAt M input 0) zero
              (workSymbol cell.clearTransient), zero⟩⟩ :
        DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) (input.length + 1))
    symm
    apply cfg_eq rfl
    · exact finish_back_eq_canonical M input
    · rfl

/-- Canonical initialization reaches the clean zero-clock encoding of the source machine's
canonical initial configuration.

The theorem holds for every input, including the empty word; in particular it implies the
requested nonempty-input statement.
-/
public theorem reaches_canonicalCfg_init
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    LBA.Reaches (machine M)
      (LBA.initCfgEnd (machine M) input)
      (canonicalCfg M (LBA.initCfgEnd M input)) := by
  exact (reaches_full_sweep M input).trans
    ((ReflTransGen.single (step_detect_right M input)).trans
      ((back_sweep M input (Fin.last (input.length + 1))).trans
        (ReflTransGen.single (step_finish_back M input))))

/-- Canonical initialization also reaches the operational Ready checkpoint representation.  The
two endpoint encodings coincide because the source head initially lies on the left endmarker. -/
public theorem reaches_checkpointCfg_init
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : List T) :
    LBA.Reaches (machine M)
      (LBA.initCfgEnd (machine M) input)
      (checkpointCfg (LBA.initCfgEnd M input) (fun _ => clockZero M)
        (ReadyTrails.clear (input.length + 1))) := by
  rw [← canonicalCfg_eq_checkpointCfg_clear_zero]
  exact reaches_canonicalCfg_init M input

end

end LBA.AcyclicClock

end
