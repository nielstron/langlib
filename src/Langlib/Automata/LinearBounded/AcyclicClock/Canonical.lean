module

public import Langlib.Automata.LinearBounded.AcyclicClock.Construction
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical zero-clock ready configurations for the operational clock compiler

This file packages the well-formed zero-clock configuration produced by canonical
initialization.  It is not the general `ready` representation after simulated steps, whose clock
row is nonzero.  The zero-clock target tape stores:

* exactly the source tape symbol in every work cell;
* the all-zero concrete clock row;
* true left/right bits exactly at the physical endpoints;
* one simulated-head mark exactly at the source head;
* no transient initialization or sweep bits.

The target's physical head is placed on the simulated-head mark, so a `ready q` state can perform
the source write-and-move half-step directly.

The results here are representation facts only.  They neither assert global acyclicity nor claim
that every target configuration is canonical.
-/

open Classical

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}

section

variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- The canonical clean work cell for source tape position `index`. -/
public def canonicalCell
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    WorkCell T Γ Λ where
  src := tape.contents index
  digit := clockZero M
  left := decide (index.val = 0)
  right := decide (index.val = n)
  mark := decide (index = tape.head)
  init := false
  seek := false
  norm := false
  carry := false
  post := false
  scan := false

/-- Encode a complete source bounded tape as a canonical target work tape. -/
public def canonicalTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n where
  contents index := workSymbol (canonicalCell M tape index)
  head := tape.head

/-- Encode a source configuration as a clean zero-clock target configuration.

This is the representation used for canonical initialization, not the general nonzero-layer
encoding after a completed simulated step.
-/
public def canonicalCfg
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n :=
  ⟨.ready cfg.state, canonicalTape M cfg.tape⟩

/-- Decode the source symbol when a target symbol is a converted work cell. -/
public def projectedSourceSymbol
    (symbol : TapeAlpha T Γ Λ) : Option (SourceAlpha T Γ) :=
  (asWork symbol).map WorkCell.src

@[simp]
public theorem projectedSourceSymbol_workSymbol
    (cell : WorkCell T Γ Λ) :
    projectedSourceSymbol (workSymbol cell) = some cell.src := rfl

@[simp]
public theorem canonicalCell_src
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).src = tape.contents index := rfl

@[simp]
public theorem canonicalCell_digit
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).digit = clockZero M := rfl

@[simp]
public theorem canonicalCell_left_iff
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).left = true ↔ index.val = 0 := by
  simp [canonicalCell]

@[simp]
public theorem canonicalCell_right_iff
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).right = true ↔ index.val = n := by
  simp [canonicalCell]

@[simp]
public theorem canonicalCell_mark_iff
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).mark = true ↔ index = tape.head := by
  simp [canonicalCell]

@[simp]
public theorem canonicalCell_init
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).init = false := rfl

@[simp]
public theorem canonicalCell_seek
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).seek = false := rfl

@[simp]
public theorem canonicalCell_norm
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).norm = false := rfl

@[simp]
public theorem canonicalCell_carry
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).carry = false := rfl

@[simp]
public theorem canonicalCell_post
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).post = false := rfl

@[simp]
public theorem canonicalCell_scan
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).scan = false := rfl

@[simp]
public theorem canonicalCell_clearTransient
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    (canonicalCell M tape index).clearTransient =
      canonicalCell M tape index := by
  rfl

@[simp]
public theorem asWork_canonicalTape_contents
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    asWork ((canonicalTape M tape).contents index) =
      some (canonicalCell M tape index) := rfl

@[simp]
public theorem projectedSourceSymbol_canonicalTape_contents
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    projectedSourceSymbol ((canonicalTape M tape).contents index) =
      some (tape.contents index) := rfl

@[simp]
public theorem canonicalTape_head
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n) :
    (canonicalTape M tape).head = tape.head := rfl

@[simp]
public theorem canonicalTape_read
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n) :
    (canonicalTape M tape).read =
      workSymbol (canonicalCell M tape tape.head) := rfl

@[simp]
public theorem canonicalCell_mark_head
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n) :
    (canonicalCell M tape tape.head).mark = true := by
  simp

/-- The canonical work tape has exactly one simulated-head mark. -/
public theorem canonicalCell_mark_unique
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    {left right : Fin (n + 1)}
    (hleft : (canonicalCell M tape left).mark = true)
    (hright : (canonicalCell M tape right).mark = true) :
    left = right := by
  rw [canonicalCell_mark_iff] at hleft hright
  exact hleft.trans hright.symm

/-- The left boundary bit is unique. -/
public theorem canonicalCell_left_unique
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    {left right : Fin (n + 1)}
    (hleft : (canonicalCell M tape left).left = true)
    (hright : (canonicalCell M tape right).left = true) :
    left = right := by
  rw [canonicalCell_left_iff] at hleft hright
  exact Fin.ext (hleft.trans hright.symm)

/-- The right boundary bit is unique. -/
public theorem canonicalCell_right_unique
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    {left right : Fin (n + 1)}
    (hleft : (canonicalCell M tape left).right = true)
    (hright : (canonicalCell M tape right).right = true) :
    left = right := by
  rw [canonicalCell_right_iff] at hleft hright
  exact Fin.ext (hleft.trans hright.symm)

/-- Canonical tape encoding is injective: no source contents or head information is lost. -/
public theorem canonicalTape_injective
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ} :
    Function.Injective
      (canonicalTape M :
        DLBA.BoundedTape (SourceAlpha T Γ) n →
          DLBA.BoundedTape (TapeAlpha T Γ Λ) n) := by
  intro left right heq
  have hhead : left.head = right.head := by
    exact congrArg
      (fun tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n => tape.head) heq
  have hcontents : left.contents = right.contents := by
    funext index
    have hcell :=
      congrFun (congrArg DLBA.BoundedTape.contents heq) index
    change
      workSymbol (canonicalCell M left index) =
        workSymbol (canonicalCell M right index) at hcell
    have hwork :
        canonicalCell M left index =
          canonicalCell M right index := by
      simpa [workSymbol] using hcell
    exact congrArg WorkCell.src hwork
  cases left
  cases right
  simp_all

/-- Canonical configuration encoding is injective. -/
public theorem canonicalCfg_injective
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ} :
    Function.Injective
      (canonicalCfg M :
        DLBA.Cfg (SourceAlpha T Γ) Λ n →
          DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) := by
  intro left right heq
  have hstate : left.state = right.state := by
    have := congrArg (fun cfg => cfg.state) heq
    simpa [canonicalCfg] using this
  have htape : left.tape = right.tape := by
    apply canonicalTape_injective M
    exact congrArg (fun cfg => cfg.tape) heq
  cases left
  cases right
  simp_all

@[simp]
public theorem canonicalCfg_state
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    (canonicalCfg M cfg).state = .ready cfg.state := rfl

@[simp]
public theorem canonicalCfg_tape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    (canonicalCfg M cfg).tape = canonicalTape M cfg.tape := rfl

end

end LBA.AcyclicClock

end
