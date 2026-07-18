module

public import Langlib.Automata.LinearBounded.Equivalence.EndmarkerToFlag
public import Langlib.Automata.LinearBounded.Functional
import Mathlib.Tactic

@[expose]
public section

/-!
# Deterministically folding endmarkers into a bounded input tape

`EndmarkerToFlag.flagMachine` finds the right end of the marker-free tape by guessing a cell and
then checking whether a right move clamps.  For a functional source machine that initialization
is the only source of nondeterminism.  This file replaces it by a deterministic probe.

Canonical unread input cells have the form `some (Sum.inl input)`, whereas a cell already folded
by the initializer has the disjoint form `some (Sum.inr work)`.  The initializer folds the current
cell and moves right.  Reading another raw cell means that the move advanced; rereading a folded
cell means that the move clamped at the right boundary.  It then installs the folded right marker,
rewinds to the folded left marker, and delegates the simulation phase verbatim to `flagTransition`.
-/

namespace LBA

open DLBA

variable {T Γ Λ : Type*}

/-- The deterministic endmarker-folding transition table.

Outside the scan phase it is exactly `flagTransition`.  During the scan it selects the continuing
edge on a raw input cell and the right-marker edge on a folded cell.  `none` cannot occur on a
canonical nonempty input and is made terminal. -/
public def deterministicFlagTransition (M' : Machine (EndAlpha T Γ) Λ) :
    FState Λ → FAlpha T Γ → Set (FState Λ × FAlpha T Γ × DLBA.Dir)
  | .setup, symbol => flagTransition M' .setup symbol
  | .scan, none => ∅
  | .scan, symbol@(some (Sum.inl _)) =>
      {(.scan,
        some (Sum.inr (cellCur symbol, cellLeft symbol, none)),
        DLBA.Dir.right)}
  | .scan, symbol@(some (Sum.inr _)) =>
      {(.verify,
        some (Sum.inr (cellCur symbol, cellLeft symbol, some rightMark)),
        DLBA.Dir.right)}
  | .verify, symbol => flagTransition M' .verify symbol
  | .rewind, symbol => flagTransition M' .rewind symbol
  | .sim state mode, symbol => flagTransition M' (.sim state mode) symbol

/-- A marker-free LBA that deterministically initializes the folded endmarkers and then simulates
the supplied endmarker machine. -/
public def deterministicFlagMachine (M' : Machine (EndAlpha T Γ) Λ) :
    Machine (FAlpha T Γ) (FState Λ) where
  transition := deterministicFlagTransition M'
  accept := (flagMachine M').accept
  initial := .setup

@[simp]
public theorem deterministicFlagMachine_accept_sim
    (M' : Machine (EndAlpha T Γ) Λ) (state : Λ) (mode : FMode) :
    (deterministicFlagMachine M').accept (.sim state mode) = M'.accept state := rfl

/-- Every deterministic-fold transition is one of the transitions of the existing nondeterministic
folding simulator. -/
public theorem deterministicFlagTransition_sub_flagTransition
    (M' : Machine (EndAlpha T Γ) Λ) (state : FState Λ) (symbol : FAlpha T Γ) :
    deterministicFlagTransition M' state symbol ⊆ flagTransition M' state symbol := by
  intro move hmove
  cases state with
  | setup => exact hmove
  | scan =>
      cases symbol with
      | none => simp [deterministicFlagTransition] at hmove
      | some symbol =>
          cases symbol with
          | inl input =>
              simp only [deterministicFlagTransition, Set.mem_singleton_iff] at hmove
              subst move
              simp [flagTransition]
          | inr work =>
              simp only [deterministicFlagTransition, Set.mem_singleton_iff] at hmove
              subst move
              simp [flagTransition]
  | verify => exact hmove
  | rewind => exact hmove
  | sim state mode => exact hmove

/-- Functionality of the source transition table is preserved by deterministic folding. -/
public theorem deterministicFlagMachine_functional
    (M' : Machine (EndAlpha T Γ) Λ) (hfunctional : M'.Functional) :
    (deterministicFlagMachine M').Functional := by
  intro state symbol left hleft right hright
  cases state with
  | setup =>
      simp [deterministicFlagMachine, deterministicFlagTransition, flagTransition] at hleft hright
      exact hleft.trans hright.symm
  | scan =>
      cases symbol with
      | none =>
          simp [deterministicFlagMachine, deterministicFlagTransition] at hleft
      | some symbol =>
          cases symbol <;>
            simp [deterministicFlagMachine, deterministicFlagTransition] at hleft hright
          all_goals exact hleft.trans hright.symm
  | verify =>
      simp only [deterministicFlagMachine, deterministicFlagTransition, flagTransition] at hleft hright
      split at hleft <;> simp_all
  | rewind =>
      simp only [deterministicFlagMachine, deterministicFlagTransition, flagTransition] at hleft hright
      split at hleft <;> simp_all
  | sim state mode =>
      cases mode with
      | onLeft =>
          simp only [deterministicFlagMachine, deterministicFlagTransition, flagTransition,
            Set.mem_setOf_eq] at hleft hright
          obtain ⟨leftMove, hleftMove, rfl⟩ := hleft
          obtain ⟨rightMove, hrightMove, rfl⟩ := hright
          have hmoves : leftMove = rightMove :=
            hfunctional state ((cellLeft symbol).getD leftMark) hleftMove hrightMove
          subst rightMove
          rfl
      | mid =>
          simp only [deterministicFlagMachine, deterministicFlagTransition, flagTransition,
            Set.mem_setOf_eq] at hleft hright
          obtain ⟨leftMove, hleftMove, rfl⟩ := hleft
          obtain ⟨rightMove, hrightMove, rfl⟩ := hright
          have hmoves : leftMove = rightMove :=
            hfunctional state (cellCur symbol) hleftMove hrightMove
          subst rightMove
          rfl
      | onRight =>
          simp only [deterministicFlagMachine, deterministicFlagTransition, flagTransition,
            Set.mem_setOf_eq] at hleft hright
          obtain ⟨leftMove, hleftMove, rfl⟩ := hleft
          obtain ⟨rightMove, hrightMove, rfl⟩ := hright
          have hmoves : leftMove = rightMove :=
            hfunctional state ((cellRight symbol).getD rightMark) hleftMove hrightMove
          subst rightMove
          rfl

/-! ## Relation to the existing folding simulator -/

/-- A deterministic-fold machine step is also a step of the existing folding simulator. -/
public theorem step_flagMachine_of_step_deterministicFlagMachine
    (M' : Machine (EndAlpha T Γ) Λ) {n : ℕ}
    {source target : DLBA.Cfg (FAlpha T Γ) (FState Λ) n}
    (hstep : Step (deterministicFlagMachine M') source target) :
    Step (flagMachine M') source target := by
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  exact ⟨next, written, direction,
    deterministicFlagTransition_sub_flagTransition M' _ _ henabled, rfl⟩

/-- Every deterministic-fold run is a run of the existing folding simulator. -/
public theorem reaches_flagMachine_of_reaches_deterministicFlagMachine
    (M' : Machine (EndAlpha T Γ) Λ) {n : ℕ}
    {source target : DLBA.Cfg (FAlpha T Γ) (FState Λ) n}
    (hreach : Reaches (deterministicFlagMachine M') source target) :
    Reaches (flagMachine M') source target := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.tail (step_flagMachine_of_step_deterministicFlagMachine M' hstep)

/-- Outside the scan state the deterministic and existing folding simulators have identical
one-step relations. -/
private theorem step_deterministicFlagMachine_iff_flagMachine_of_not_scan
    (M' : Machine (EndAlpha T Γ) Λ) {n : ℕ}
    (source target : DLBA.Cfg (FAlpha T Γ) (FState Λ) n)
    (hsource : source.state ≠ .scan) :
    Step (deterministicFlagMachine M') source target ↔
      Step (flagMachine M') source target := by
  rcases source with ⟨state, tape⟩
  cases state <;>
    simp_all [Step, deterministicFlagMachine, deterministicFlagTransition, flagMachine]

/-- In the simulation phase, an endmarker-machine step is reproduced by the deterministic fold. -/
public theorem deterministicFlagMachine_fold_step
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    {source target : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2)}
    (hstep : Step M' source target) :
    Step (deterministicFlagMachine M') (fold source) (fold target) := by
  apply (step_deterministicFlagMachine_iff_flagMachine_of_not_scan
    M' (fold source) (fold target) (by simp [fold])).2
  exact fold_step M' hstep

/-- Endmarker-machine reachability is reproduced in the deterministic simulation phase. -/
public theorem deterministicFlagMachine_fold_reaches
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    {source target : DLBA.Cfg (EndAlpha T Γ) Λ (m + 2)}
    (hreach : Reaches M' source target) :
    Reaches (deterministicFlagMachine M') (fold source) (fold target) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (deterministicFlagMachine_fold_step M' hstep)

/-! ## Deterministic initialization -/

/-- Every cell of a canonical nonempty marker-free input is an unread input cell. -/
public def RawFlagTape {m : ℕ} (contents : Fin (m + 1) → FAlpha T Γ) : Prop :=
  ∀ index, ∃ input, contents index = some (Sum.inl input)

private theorem RawFlagTape.cellLeft_eq_none {m : ℕ}
    {contents : Fin (m + 1) → FAlpha T Γ} (hraw : RawFlagTape contents)
    (index : Fin (m + 1)) :
    cellLeft (contents index) = none := by
  obtain ⟨input, hinput⟩ := hraw index
  rw [hinput]
  rfl

private theorem RawFlagTape.cellRight_eq_none {m : ℕ}
    {contents : Fin (m + 1) → FAlpha T Γ} (hraw : RawFlagTape contents)
    (index : Fin (m + 1)) :
    cellRight (contents index) = none := by
  obtain ⟨input, hinput⟩ := hraw index
  rw [hinput]
  rfl

/-- On a tape with at least two cells, deterministic setup marks cell zero and advances to the
first still-raw cell. -/
private theorem deterministic_setup_step
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ) (hm : 1 ≤ m) :
    Step (deterministicFlagMachine M')
      ⟨FState.setup, ⟨contents, ⟨0, by omega⟩⟩⟩
      ⟨FState.scan, ⟨partialTape contents 1, ⟨1, by omega⟩⟩⟩ := by
  apply (step_deterministicFlagMachine_iff_flagMachine_of_not_scan M' _ _ (by simp)).2
  exact setup_step M' contents hm

/-- On a one-cell tape, setup marks the unique cell with the folded left marker and its right move
clamps back onto that newly folded cell. -/
private theorem deterministic_setup_zero_step
    (M' : Machine (EndAlpha T Γ) Λ)
    (contents : Fin (0 + 1) → FAlpha T Γ) :
    Step (deterministicFlagMachine M')
      ⟨FState.setup, ⟨contents, ⟨0, by omega⟩⟩⟩
      ⟨FState.scan, ⟨scanLast contents, ⟨0, by omega⟩⟩⟩ := by
  refine ⟨FState.scan,
    some (Sum.inr (cellCur (contents ⟨0, by omega⟩), some leftMark, none)),
    DLBA.Dir.right, ?_, ?_⟩
  · show _ ∈ deterministicFlagTransition M' FState.setup (contents ⟨0, by omega⟩)
    rfl
  · apply cfg_ext'
    · rfl
    · show scanLast contents = Function.update contents ⟨0, by omega⟩
          (some (Sum.inr (cellCur (contents ⟨0, by omega⟩), some leftMark, none)))
      funext index
      have hzero : index = (⟨0, by omega⟩ : Fin (0 + 1)) :=
        Fin.ext (by have := index.isLt; omega)
      subst index
      rw [Function.update_self]
      simp [scanLast]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      rw [dif_neg (by omega)]

/-- One deterministic scan step initializes a raw non-final cell and advances right. -/
private theorem deterministic_scan_step
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ) (hraw : RawFlagTape contents)
    (index : ℕ) (hpositive : 1 ≤ index) (hbeforeLast : index < m) :
    Step (deterministicFlagMachine M')
      ⟨FState.scan, ⟨partialTape contents index, ⟨index, by omega⟩⟩⟩
      ⟨FState.scan, ⟨partialTape contents (index + 1), ⟨index + 1, by omega⟩⟩⟩ := by
  let position : Fin (m + 1) := ⟨index, by omega⟩
  have hread : partialTape contents index position = contents position := by
    simp [partialTape, position]
  obtain ⟨input, hinput⟩ := hraw position
  have hleft : cellLeft (contents position) = none := by rw [hinput]; rfl
  refine ⟨FState.scan,
    some (Sum.inr
      (cellCur (partialTape contents index position),
        cellLeft (partialTape contents index position), none)),
    DLBA.Dir.right, ?_, ?_⟩
  · show _ ∈ deterministicFlagTransition M' FState.scan
        (partialTape contents index position)
    rw [hread, hinput]
    rfl
  · apply cfg_ext'
    · rfl
    · show partialTape contents (index + 1) =
          Function.update (partialTape contents index) position
            (some (Sum.inr
              (cellCur (partialTape contents index position),
                cellLeft (partialTape contents index position), none)))
      rw [hread, hleft]
      funext other
      rw [Function.update_apply]
      by_cases heq : other = position
      · subst other
        rw [if_pos rfl]
        simp only [partialTape, foldedTape]
        rw [if_pos (by simp [position]), if_neg (by simp [position]; omega),
          if_neg (by simp [position]; omega)]
      · rw [if_neg heq]
        have hne : other.val ≠ index := fun h => heq (Fin.ext h)
        simp only [partialTape]
        by_cases hlt : other.val < index
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt, if_neg (by omega)]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      rw [dif_pos hbeforeLast]

/-- Repeated deterministic raw-cell steps reach the last raw cell. -/
private theorem deterministic_scan_reach
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ) (hraw : RawFlagTape contents)
    (index : ℕ) (hpositive : 1 ≤ index) (hatMostLast : index ≤ m) :
    Reaches (deterministicFlagMachine M')
      ⟨FState.scan, ⟨partialTape contents 1, ⟨1, by omega⟩⟩⟩
      ⟨FState.scan, ⟨partialTape contents index, ⟨index, by omega⟩⟩⟩ := by
  induction index, hpositive using Nat.le_induction with
  | base => exact .refl
  | succ index hindex ih =>
      exact (ih (by omega)).tail
        (deterministic_scan_step M' contents hraw index hindex (by omega))

/-- Continuing once at the last raw cell initializes it; the right move clamps, so the scan state
immediately rereads the fully initialized tape with no right marker yet. -/
private theorem deterministic_overscan_step
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ) (hraw : RawFlagTape contents)
    (hm : 1 ≤ m) :
    Step (deterministicFlagMachine M')
      ⟨FState.scan, ⟨partialTape contents m, ⟨m, by omega⟩⟩⟩
      ⟨FState.scan, ⟨scanLast contents, ⟨m, by omega⟩⟩⟩ := by
  let last : Fin (m + 1) := ⟨m, by omega⟩
  have hread : partialTape contents m last = contents last := by
    simp [partialTape, last]
  obtain ⟨input, hinput⟩ := hraw last
  have hleft : cellLeft (contents last) = none := by rw [hinput]; rfl
  refine ⟨FState.scan,
    some (Sum.inr
      (cellCur (partialTape contents m last),
        cellLeft (partialTape contents m last), none)),
    DLBA.Dir.right, ?_, ?_⟩
  · show _ ∈ deterministicFlagTransition M' FState.scan
        (partialTape contents m last)
    rw [hread, hinput]
    rfl
  · apply cfg_ext'
    · rfl
    · show scanLast contents = Function.update (partialTape contents m) last
          (some (Sum.inr
            (cellCur (partialTape contents m last),
              cellLeft (partialTape contents m last), none)))
      rw [hread, hleft]
      funext other
      rw [Function.update_apply]
      by_cases heq : other = last
      · subst other
        rw [if_pos rfl]
        simp [scanLast, last, hinput, show m ≠ 0 by omega]
      · rw [if_neg heq]
        have hne : other.val ≠ m := fun h => heq (Fin.ext h)
        have hlt : other.val < m := by
          have := other.isLt
          omega
        simp [partialTape, scanLast, foldedTape, hlt, hne]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      rw [dif_neg (by simp)]

/-- Seeing a folded cell in scan state proves that the preceding right probe clamped.  The machine
installs the right marker and uses the existing verification state. -/
private theorem deterministic_commit_right_step
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ) :
    Step (deterministicFlagMachine M')
      ⟨FState.scan, ⟨scanLast contents, ⟨m, by omega⟩⟩⟩
      ⟨FState.verify, ⟨foldedTape contents, ⟨m, by omega⟩⟩⟩ := by
  let last : Fin (m + 1) := ⟨m, by omega⟩
  refine ⟨FState.verify,
    some (Sum.inr
      (cellCur (scanLast contents last), cellLeft (scanLast contents last), some rightMark)),
    DLBA.Dir.right, ?_, ?_⟩
  · show _ ∈ deterministicFlagTransition M' FState.scan (scanLast contents last)
    rfl
  · apply cfg_ext'
    · rfl
    · show foldedTape contents = Function.update (scanLast contents) last
          (some (Sum.inr
            (cellCur (scanLast contents last),
              cellLeft (scanLast contents last), some rightMark)))
      funext other
      rw [Function.update_apply]
      by_cases heq : other = last
      · subst other
        rw [if_pos rfl]
        simp [foldedTape, scanLast, cellCur, cellLeft, last]
      · rw [if_neg heq]
        have hne : other.val ≠ m := fun h => heq (Fin.ext h)
        simp [foldedTape, scanLast, hne]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      rw [dif_neg (by simp)]

/-- Verification of the deterministically discovered right boundary moves into rewind.  This
uniform statement includes the one-cell case, where the left move clamps. -/
private theorem deterministic_verify_step
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ) :
    Step (deterministicFlagMachine M')
      ⟨FState.verify, ⟨foldedTape contents, ⟨m, by omega⟩⟩⟩
      ⟨FState.rewind, ⟨foldedTape contents, ⟨m - 1, by omega⟩⟩⟩ := by
  let last : Fin (m + 1) := ⟨m, by omega⟩
  have hright : (cellRight (foldedTape contents last)).isSome = true := by
    simp [foldedTape, cellRight, last]
  refine ⟨FState.rewind, foldedTape contents last, DLBA.Dir.left, ?_, ?_⟩
  · show _ ∈ deterministicFlagTransition M' FState.verify (foldedTape contents last)
    simp [deterministicFlagTransition, flagTransition, hright]
  · apply cfg_ext'
    · rfl
    · show foldedTape contents =
          Function.update (foldedTape contents) last (foldedTape contents last)
      rw [Function.update_eq_self]
    · apply Fin.ext
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
      by_cases hm : 0 < m
      · rw [dif_pos hm]
      · rw [dif_neg (by simpa using hm)]
        omega

/-- One deterministic rewind step at a positive tape position. -/
private theorem deterministic_rewind_step
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ)
    (index : ℕ) (hpositive : 1 ≤ index) (hatMostLast : index ≤ m) :
    Step (deterministicFlagMachine M')
      ⟨FState.rewind, ⟨foldedTape contents, ⟨index, by omega⟩⟩⟩
      ⟨FState.rewind, ⟨foldedTape contents, ⟨index - 1, by omega⟩⟩⟩ := by
  apply (step_deterministicFlagMachine_iff_flagMachine_of_not_scan M' _ _ (by simp)).2
  exact rewind_step M' contents index hpositive hatMostLast

/-- Rewind from any tape position to the folded left marker at cell zero. -/
private theorem deterministic_rewind_reach
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ)
    (index : ℕ) (hatMostLast : index ≤ m) :
    Reaches (deterministicFlagMachine M')
      ⟨FState.rewind, ⟨foldedTape contents, ⟨index, by omega⟩⟩⟩
      ⟨FState.rewind, ⟨foldedTape contents, ⟨0, by omega⟩⟩⟩ := by
  induction index with
  | zero => exact .refl
  | succ index ih =>
      exact .head
        (deterministic_rewind_step M' contents (index + 1) (by omega) (by omega))
        (ih (by omega))

/-- At cell zero, rewind finds the folded left marker and enters the simulation phase. -/
private theorem deterministic_rewind_zero_step
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ) :
    Step (deterministicFlagMachine M')
      ⟨FState.rewind, ⟨foldedTape contents, ⟨0, by omega⟩⟩⟩
      ⟨FState.sim M'.initial FMode.onLeft,
        ⟨foldedTape contents, ⟨0, by omega⟩⟩⟩ := by
  apply (step_deterministicFlagMachine_iff_flagMachine_of_not_scan M' _ _ (by simp)).2
  exact rewind0_step M' contents

/-- The deterministic probe initializes both folded endmarkers and enters the simulation phase. -/
public theorem deterministicFlagMachine_init_reach
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ) (hraw : RawFlagTape contents) :
    Reaches (deterministicFlagMachine M')
      ⟨FState.setup, ⟨contents, ⟨0, by omega⟩⟩⟩
      ⟨FState.sim M'.initial FMode.onLeft,
        ⟨foldedTape contents, ⟨0, by omega⟩⟩⟩ := by
  by_cases hzero : m = 0
  · subst m
    exact .head (deterministic_setup_zero_step M' contents)
      (.head (deterministic_commit_right_step M' contents)
        (.head (deterministic_verify_step M' contents)
          (.single (deterministic_rewind_zero_step M' contents))))
  · have hm : 1 ≤ m := by omega
    exact .head (deterministic_setup_step M' contents hm)
      ((deterministic_scan_reach M' contents hraw m hm le_rfl).trans
        (.head (deterministic_overscan_step M' contents hraw hm)
          (.head (deterministic_commit_right_step M' contents)
            (.head (deterministic_verify_step M' contents)
              ((deterministic_rewind_reach M' contents (m - 1) (by omega)).trans
                (.single (deterministic_rewind_zero_step M' contents)))))))

/-! ## Acceptance and language equivalence -/

/-- On a raw marker-free tape, the deterministic folding machine accepts exactly when the
source machine accepts the corresponding endmarker expansion. -/
public theorem deterministicFlagMachine_accepts_iff
    (M' : Machine (EndAlpha T Γ) Λ) {m : ℕ}
    (contents : Fin (m + 1) → FAlpha T Γ) (hraw : RawFlagTape contents) :
    Accepts (deterministicFlagMachine M')
        ⟨FState.setup, ⟨contents, ⟨0, by omega⟩⟩⟩
      ↔ Accepts M' ⟨M'.initial, ⟨expand contents, ⟨0, by omega⟩⟩⟩ := by
  constructor
  · rintro ⟨target, hreach, haccept⟩
    apply (flag_accepts_iff M' contents hraw.cellLeft_eq_none hraw.cellRight_eq_none).mp
    exact ⟨target, reaches_flagMachine_of_reaches_deterministicFlagMachine M' hreach,
      haccept⟩
  · rintro ⟨target, hreach, haccept⟩
    have hstart :
        (⟨FState.sim M'.initial FMode.onLeft,
            ⟨foldedTape contents, ⟨0, by omega⟩⟩⟩ :
          DLBA.Cfg (FAlpha T Γ) (FState Λ) m) =
          fold (⟨M'.initial, ⟨expand contents, ⟨0, by omega⟩⟩⟩ :
            DLBA.Cfg (EndAlpha T Γ) Λ (m + 2)) := by
      apply cfg_ext'
      · simp [fold, foldMode]
      · exact foldedTape_eq_foldContents_expand contents
      · simp [fold, foldHead]
    refine ⟨fold target, ?_, ?_⟩
    · refine (deterministicFlagMachine_init_reach M' contents hraw).trans ?_
      rw [hstart]
      exact deterministicFlagMachine_fold_reaches M' hreach
    · simpa [fold] using haccept

/-- On a canonical nonempty input, deterministic folding preserves acceptance of the bracketed
endmarker input. -/
public theorem deterministicFlagMachine_accepts_input
    (M' : Machine (EndAlpha T Γ) Λ) (w : List T)
    (hv : w.map (fun input => (some (Sum.inl input) : FAlpha T Γ)) ≠ []) :
    Accepts (deterministicFlagMachine M')
        (initCfgList (deterministicFlagMachine M')
          (w.map (fun input => (some (Sum.inl input) : FAlpha T Γ))) hv)
      ↔ Accepts M' (initCfgEnd M' w) := by
  set embed : T → FAlpha T Γ := fun input => some (Sum.inl input) with hembed
  have hwne : w ≠ [] := by
    rintro rfl
    simp [hembed] at hv
  have hpos : 0 < w.length := List.length_pos_of_ne_nil hwne
  have hlen : (w.map embed).length = w.length := by simp
  set contents := (loadList (w.map embed) hv).contents with hcontents
  have hrawAt : ∀ index,
      contents index = some (Sum.inl (w.get ⟨index.val, by
        have := index.isLt
        omega⟩)) := by
    intro index
    rw [hcontents]
    show (w.map embed).get _ = _
    simp only [List.get_eq_getElem, List.getElem_map, hembed]
  have hraw : RawFlagTape contents := by
    intro index
    exact ⟨w.get ⟨index.val, by have := index.isLt; omega⟩, hrawAt index⟩
  rw [show initCfgList (deterministicFlagMachine M') (w.map embed) hv =
        (⟨FState.setup, ⟨contents, ⟨0, by omega⟩⟩⟩ :
          DLBA.Cfg (FAlpha T Γ) (FState Λ) ((w.map embed).length - 1)) from rfl]
  rw [deterministicFlagMachine_accepts_iff M' contents hraw]
  refine accepts_heq M' (by rw [hlen]; omega) ?_
  refine cfg_heq (by rw [hlen]; omega) rfl ?_
  refine boundedtape_heq (by rw [hlen]; omega) ?_ ?_
  · refine (Fin.heq_fun_iff (by rw [hlen]; omega)).mpr (fun index => ?_)
    have hindex := index.isLt
    have hmappedPositive : 0 < (w.map embed).length := by
      rw [hlen]
      exact hpos
    show expand contents index = (loadEnd w).contents _
    simp only [loadEnd, expand]
    by_cases hzero : index.val = 0
    · rw [if_pos hzero, if_pos hzero]
    · rw [if_neg hzero, if_neg hzero]
      by_cases hinterior : index.val - 1 < w.length
      · rw [dif_pos (show index.val - 1 < (w.map embed).length - 1 + 1 by omega),
          dif_pos hinterior, hcontents]
        simp only [loadList, List.get_eq_getElem, List.getElem_map, hembed]
        rfl
      · rw [dif_neg (show ¬ index.val - 1 < (w.map embed).length - 1 + 1 by omega),
          dif_neg hinterior]
  · rfl

/-- Deterministic folding recognizes exactly the language of the source endmarker machine. -/
public theorem language_deterministicFlagMachine_eq
    (M' : Machine (EndAlpha T Γ) Λ) (acceptEmpty : Bool)
    (hempty : acceptEmpty = true ↔ Accepts M' (initCfgEnd M' [])) :
    LanguageRecognized (deterministicFlagMachine M')
        (fun input => some (Sum.inl input)) acceptEmpty =
      LanguageEnd M' := by
  funext w
  apply propext
  show (acceptEmpty = true ∧ w = []) ∨
      LanguageViaEmbed (deterministicFlagMachine M')
        (fun input => some (Sum.inl input)) w
    ↔ Accepts M' (initCfgEnd M' w)
  rcases w with _ | ⟨input, rest⟩
  · constructor
    · rintro (⟨htrue, _⟩ | ⟨hnonempty, _⟩)
      · exact hempty.mp htrue
      · exact absurd
          (by simp : ([] : List T).map
            (fun input => (some (Sum.inl input) : FAlpha T Γ)) = []) hnonempty
    · intro haccept
      exact Or.inl ⟨hempty.mpr haccept, rfl⟩
  · constructor
    · rintro (⟨_, hnil⟩ | ⟨hnonempty, haccept⟩)
      · exact absurd hnil (by simp)
      · exact (deterministicFlagMachine_accepts_input M' (input :: rest) hnonempty).mp haccept
    · intro haccept
      exact Or.inr ⟨by simp,
        (deterministicFlagMachine_accepts_input M' (input :: rest) (by simp)).mpr haccept⟩

end LBA

variable {T Γ Λ : Type}
  [Fintype T] [DecidableEq T]
  [Fintype Γ] [Fintype Λ] [DecidableEq Λ]

/-- Every language presented by a finite functional endmarker LBA is a deterministic-LBA
language.  The endmarker-to-marker-free conversion itself remains functional, and its explicit
empty-word bit is obtained by bounded simulation of the finite deterministic source. -/
public theorem is_DLBA_languageEnd_of_functional
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ) (hfunctional : M.Functional) :
    is_DLBA (LBA.LanguageEnd M) := by
  classical
  let acceptEmpty : Bool :=
    DLBA.acceptsBoundedBool M.toDLBA (LBA.initCfgEnd M [])
  have hempty : acceptEmpty = true ↔ LBA.Accepts M (LBA.initCfgEnd M []) := by
    exact (DLBA.acceptsBoundedBool_eq_true_iff M.toDLBA (LBA.initCfgEnd M [])).trans
      (M.accepts_toDLBA_iff hfunctional (LBA.initCfgEnd M []))
  rw [← LBA.language_deterministicFlagMachine_eq M acceptEmpty hempty]
  exact is_DLBA_languageRecognized_of_functional
    (LBA.deterministicFlagMachine M)
    (LBA.deterministicFlagMachine_functional M hfunctional)
    acceptEmpty

end
