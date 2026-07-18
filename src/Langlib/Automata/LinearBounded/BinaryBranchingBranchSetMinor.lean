module

public import Langlib.Automata.LinearBounded.BinaryBranching
public import Langlib.Automata.LinearBounded.BranchSetMinor
import Mathlib.Tactic

@[expose]
public section

/-!
# The outgoing serializer preserves the source configuration graph as a minor

The binary-branching serializer replaces the outgoing edges of one source configuration by a
finite scan gadget.  This file gives a branch-set model for that replacement on every bounded
configuration graph.

The branch set of an original configuration consists of its `ready` image and all well-formed
scan configurations carrying exactly the same control state and tape.  The remaining-move set
is deliberately unrestricted.  Every such scan drains by skip edges to the empty set, so the
whole branch set is connected.  An original move is represented by the apply edge from the scan
whose remaining set is the singleton containing that move.

Malformed scan configurations are outside all branch sets.  No injectivity property of bounded
head movement is used, so endpoint clamping (including the one-cell tape) does not identify
branch sets.
-/

namespace LBA

open Classical
open Relation

variable {Γ Λ : Type*}

/-- The scan configuration owned by `cfg` with the specified remaining-move set. -/
public def binaryScanCfg {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (remaining : Finset (Move Γ Λ)) :
    DLBA.Cfg Γ (BinaryBranchState Γ Λ) n :=
  ⟨.scan cfg.state cfg.tape.read remaining, cfg.tape⟩

/-- The branch set representing one original configuration in the outgoing serializer. -/
public def binaryBranchSet {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    Set (DLBA.Cfg Γ (BinaryBranchState Γ Λ) n) :=
  {encoded | encoded = binaryLiftCfg cfg ∨
    ∃ remaining, encoded = binaryScanCfg cfg remaining}

@[simp]
public theorem binaryLiftCfg_mem_binaryBranchSet {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) :
    binaryLiftCfg cfg ∈ binaryBranchSet cfg :=
  Or.inl rfl

@[simp]
public theorem binaryScanCfg_mem_binaryBranchSet {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) (remaining : Finset (Move Γ Λ)) :
    binaryScanCfg cfg remaining ∈ binaryBranchSet cfg :=
  Or.inr ⟨remaining, rfl⟩

/-- Every member of a branch set projects to the configuration represented by that set. -/
public theorem binaryProjectCfg_eq_of_mem_binaryBranchSet {n : ℕ}
    {cfg : DLBA.Cfg Γ Λ n}
    {encoded : DLBA.Cfg Γ (BinaryBranchState Γ Λ) n}
    (hencoded : encoded ∈ binaryBranchSet cfg) :
    binaryProjectCfg encoded = cfg := by
  rcases hencoded with rfl | ⟨remaining, rfl⟩ <;> rfl

private theorem write_read_stay {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    (tape.write tape.read).moveHead .stay = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
    Function.update_eq_self]

/-- One canonical skip step inside the scan gadget. -/
private theorem Machine.step_binaryScanCfg_erase
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (remaining : Finset (Move Γ Λ)) (move : Move Γ Λ)
    (hpick : pickMove remaining = some move) :
    Step M.binaryBranch (binaryScanCfg cfg remaining)
      (binaryScanCfg cfg (remaining.erase move)) := by
  refine ⟨.scan cfg.state cfg.tape.read (remaining.erase move),
    cfg.tape.read, .stay, ?_, ?_⟩
  · simp [Machine.binaryBranch, binaryScanCfg, hpick]
  · exact congrArg
      (fun tape =>
        (⟨.scan cfg.state cfg.tape.read (remaining.erase move), tape⟩ :
          DLBA.Cfg Γ (BinaryBranchState Γ Λ) n))
      (write_read_stay cfg.tape).symm

private theorem mem_of_pickMove_eq_some
    [DecidableEq Γ] [DecidableEq Λ]
    {remaining : Finset (Move Γ Λ)} {move : Move Γ Λ}
    (hpick : pickMove remaining = some move) :
    move ∈ remaining := by
  rw [pickMove, List.head?_eq_some_iff] at hpick
  obtain ⟨tail, hlist⟩ := hpick
  rw [← Finset.mem_toList, hlist]
  simp

/-- Every owned scan configuration reaches the empty scan through edges that stay in its branch
set. -/
private theorem Machine.binaryScanCfg_reaches_empty_inside
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    (remaining : Finset (Move Γ Λ)) :
    ReflTransGen
      (Restricted (binaryBranchSet cfg)
        (SymmetricClosure (Step M.binaryBranch)))
      (binaryScanCfg cfg remaining) (binaryScanCfg cfg ∅) := by
  induction hcard : remaining.card using Nat.strong_induction_on generalizing remaining with
  | h card ih =>
      by_cases hempty : remaining = ∅
      · subst remaining
        exact .refl
      · have hpickNe : pickMove remaining ≠ none := by
          intro hpickNone
          apply hempty
          exact Finset.toList_eq_nil.mp
            (List.head?_eq_none_iff.mp hpickNone)
        obtain ⟨selected, hselectedRev⟩ :=
          Option.ne_none_iff_exists.mp hpickNe
        have hpick : pickMove remaining = some selected := hselectedRev.symm
        have hselected : selected ∈ remaining := mem_of_pickMove_eq_some hpick
        have hsmaller : (remaining.erase selected).card < card := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hselected
        exact ReflTransGen.head
          ⟨binaryScanCfg_mem_binaryBranchSet cfg remaining,
            Or.inl (M.step_binaryScanCfg_erase cfg remaining selected hpick),
            binaryScanCfg_mem_binaryBranchSet cfg (remaining.erase selected)⟩
          (ih (remaining.erase selected).card hsmaller
            (remaining.erase selected) rfl)

/-- The ready representative reaches the common empty-scan hub inside its branch set. -/
private theorem Machine.binaryLiftCfg_reaches_empty_inside
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    ReflTransGen
      (Restricted (binaryBranchSet cfg)
        (SymmetricClosure (Step M.binaryBranch)))
      (binaryLiftCfg cfg) (binaryScanCfg cfg ∅) := by
  have hready :
      Step M.binaryBranch (binaryLiftCfg cfg)
        (binaryScanCfg cfg Finset.univ) := by
    refine ⟨.scan cfg.state cfg.tape.read Finset.univ,
      cfg.tape.read, .stay, ?_, ?_⟩
    · simp [Machine.binaryBranch, binaryLiftCfg]
    · exact congrArg
        (fun tape =>
          (⟨.scan cfg.state cfg.tape.read Finset.univ, tape⟩ :
            DLBA.Cfg Γ (BinaryBranchState Γ Λ) n))
        (write_read_stay cfg.tape).symm
  exact ReflTransGen.head
    ⟨binaryLiftCfg_mem_binaryBranchSet cfg, Or.inl hready,
      binaryScanCfg_mem_binaryBranchSet cfg Finset.univ⟩
    (M.binaryScanCfg_reaches_empty_inside cfg Finset.univ)

private theorem restricted_symmetricClosure_symmetric {V : Type*}
    (vertices : Set V) (edge : V → V → Prop) :
    Symmetric (Restricted vertices (SymmetricClosure edge)) := by
  intro left right hstep
  exact ⟨hstep.2.2,
    hstep.2.1.elim Or.inr Or.inl,
    hstep.1⟩

/-- Every representative of a branch set reaches its common empty-scan hub. -/
private theorem Machine.binaryBranchSet_reaches_empty_inside
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    {encoded : DLBA.Cfg Γ (BinaryBranchState Γ Λ) n}
    (hencoded : encoded ∈ binaryBranchSet cfg) :
    ReflTransGen
      (Restricted (binaryBranchSet cfg)
        (SymmetricClosure (Step M.binaryBranch)))
      encoded (binaryScanCfg cfg ∅) := by
  rcases hencoded with rfl | ⟨remaining, rfl⟩
  · exact M.binaryLiftCfg_reaches_empty_inside cfg
  · exact M.binaryScanCfg_reaches_empty_inside cfg remaining

/-- One directed source step is represented by a directed apply edge between its two branch
sets. -/
private theorem Machine.exists_binaryBranch_apply_edge
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg Γ Λ n} (hstep : Step M source target) :
    ∃ sourceRep ∈ binaryBranchSet source,
      ∃ targetRep ∈ binaryBranchSet target,
        Step M.binaryBranch sourceRep targetRep := by
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  let move : Move Γ Λ := (next, written, direction)
  let sourceRep := binaryScanCfg source {move}
  let targetCfg : DLBA.Cfg Γ Λ n :=
    ⟨next, (source.tape.write written).moveHead direction⟩
  let targetRep := binaryLiftCfg targetCfg
  have hpick : pickMove ({move} : Finset (Move Γ Λ)) = some move := by
    simp [pickMove]
  have happly : Step M.binaryBranch sourceRep targetRep := by
    refine ⟨.ready next, written, direction, ?_, rfl⟩
    simpa [Machine.binaryBranch, binaryScanCfg, sourceRep, targetRep,
      targetCfg, hpick, move] using henabled
  exact ⟨sourceRep, binaryScanCfg_mem_binaryBranchSet source {move},
    targetRep, binaryLiftCfg_mem_binaryBranchSet targetCfg, happly⟩

/-- The symmetric closure of every fixed-width configuration graph is a branch-set minor of the
outgoing-degree serializer's fixed-width configuration graph.

The theorem is uniform in the tape parameter `n`; in particular it includes the clamped
one-cell graph at `n = 0`. -/
public def Machine.binaryBranchStepBranchSetMinorModel
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (n : ℕ) :
    BranchSetMinorModel
      (SymmetricClosure (Step (n := n) M))
      (Step (n := n) M.binaryBranch) where
  branchSet := binaryBranchSet
  nonempty cfg := ⟨binaryLiftCfg cfg, binaryLiftCfg_mem_binaryBranchSet cfg⟩
  disjoint {left right} hne := by
    rw [Set.disjoint_left]
    intro encoded hleft hright
    exact hne ((binaryProjectCfg_eq_of_mem_binaryBranchSet hleft).symm.trans
      (binaryProjectCfg_eq_of_mem_binaryBranchSet hright))
  connected cfg {source target} hsource htarget := by
    have hsourcePath := M.binaryBranchSet_reaches_empty_inside cfg hsource
    have htargetPath := M.binaryBranchSet_reaches_empty_inside cfg htarget
    exact hsourcePath.trans
      (ReflTransGen.symmetric
        (restricted_symmetricClosure_symmetric (binaryBranchSet cfg)
          (Step M.binaryBranch)) htargetPath)
  map_edge {source target} hedge := by
    rcases hedge with hforward | hbackward
    · rcases M.exists_binaryBranch_apply_edge hforward with
        ⟨sourceRep, hsourceRep, targetRep, htargetRep, hlarge⟩
      exact ⟨sourceRep, hsourceRep, targetRep, htargetRep, Or.inl hlarge⟩
    · rcases M.exists_binaryBranch_apply_edge hbackward with
        ⟨targetRep, htargetRep, sourceRep, hsourceRep, hlarge⟩
      exact ⟨sourceRep, hsourceRep, targetRep, htargetRep, Or.inr hlarge⟩

end LBA

end
