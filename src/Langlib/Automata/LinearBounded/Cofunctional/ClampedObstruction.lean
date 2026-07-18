module

public import Langlib.Automata.LinearBounded.Cofunctional
import Mathlib.Tactic

@[expose]
public section

/-!
# Global cofunctionality and clamped head moves

The complete configuration relation of the clamped bounded-tape model ranges over every raw
configuration, not just a compiler's well-formed encodings.  This makes global cofunctionality
incompatible with every enabled directional transition.  On a two-cell tape, a left move from
the left cell clamps while the same move from the right cell advances to the left.  Choosing the
two source tapes so that the symbol written by either move is already present at the other source
position makes their targets identical.  Right moves have the mirrored collision.

Consequently, a departure-marker microcompiler cannot make its complete low-level step relation
cofunctional: the marker written by its directional step may already occur at the neighbouring
cell of a malformed raw tape.  Boundary-safe reversibility would need either a well-formedness-
restricted relation, an unclamped/endmarker tape semantics, or a weaker invariant than global
`Machine.Cofunctional`.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- Contents used by the clamped-left collision: the boundary-headed source reads `read`, while
the neighbour-headed source reads `read` on the other cell.  The symbol `written` is placed at
the cell not currently under the head. -/
private def leftBoundaryContents (read written : Γ) : Fin 2 → Γ :=
  fun index => if index.val = 0 then read else written

private def leftNeighborContents (read written : Γ) : Fin 2 → Γ :=
  fun index => if index.val = 0 then written else read

/-- The mirrored contents for the right-boundary collision. -/
private def rightNeighborContents (read written : Γ) : Fin 2 → Γ :=
  fun index => if index.val = 0 then read else written

private def rightBoundaryContents (read written : Γ) : Fin 2 → Γ :=
  fun index => if index.val = 0 then written else read

/-- A left-moving local transition has two distinct predecessors of one target in the complete
width-two configuration graph. -/
public theorem Machine.exists_distinct_predecessors_of_mem_transition_left
    (M : Machine Γ Λ) {source target : Λ} {read written : Γ}
    (henabled : (target, written, DLBA.Dir.left) ∈ M.transition source read) :
    ∃ (boundary neighbor destination : DLBA.Cfg Γ Λ 1),
      boundary ≠ neighbor ∧ Step M boundary destination ∧ Step M neighbor destination := by
  let boundaryTape : DLBA.BoundedTape Γ 1 :=
    ⟨leftBoundaryContents read written, ⟨0, by omega⟩⟩
  let neighborTape : DLBA.BoundedTape Γ 1 :=
    ⟨leftNeighborContents read written, ⟨1, by omega⟩⟩
  let destinationTape : DLBA.BoundedTape Γ 1 :=
    ⟨fun _ => written, ⟨0, by omega⟩⟩
  have hboundaryRead : boundaryTape.read = read := by
    simp [boundaryTape, leftBoundaryContents, DLBA.BoundedTape.read]
  have hneighborRead : neighborTape.read = read := by
    rfl
  have hboundaryMove :
      (boundaryTape.write written).moveHead .left = destinationTape := by
    simp only [boundaryTape, destinationTape, DLBA.BoundedTape.write,
      DLBA.BoundedTape.moveHead]
    congr 1
    funext index
    fin_cases index <;> simp [leftBoundaryContents]
  have hneighborMove :
      (neighborTape.write written).moveHead .left = destinationTape := by
    simp only [neighborTape, destinationTape, DLBA.BoundedTape.write,
      DLBA.BoundedTape.moveHead]
    congr 1
    funext index
    fin_cases index <;> simp [leftNeighborContents]
  have hboundaryStep :
      Step M ⟨source, boundaryTape⟩ ⟨target, destinationTape⟩ := by
    refine ⟨target, written, .left, ?_, ?_⟩
    · simpa [hboundaryRead] using henabled
    · exact congrArg (fun tape => (⟨target, tape⟩ : DLBA.Cfg Γ Λ 1)) hboundaryMove.symm
  have hneighborStep :
      Step M ⟨source, neighborTape⟩ ⟨target, destinationTape⟩ := by
    refine ⟨target, written, .left, ?_, ?_⟩
    · simpa [hneighborRead] using henabled
    · exact congrArg (fun tape => (⟨target, tape⟩ : DLBA.Cfg Γ Λ 1)) hneighborMove.symm
  refine ⟨⟨source, boundaryTape⟩, ⟨source, neighborTape⟩,
    ⟨target, destinationTape⟩, ?_, hboundaryStep, hneighborStep⟩
  intro heq
  have hhead := congrArg (fun cfg => cfg.tape.head.val) heq
  simp [boundaryTape, neighborTape] at hhead

/-- Hence every enabled left-moving local transition rules out global cofunctionality. -/
public theorem Machine.not_cofunctional_of_mem_transition_left
    (M : Machine Γ Λ) {source target : Λ} {read written : Γ}
    (henabled : (target, written, DLBA.Dir.left) ∈ M.transition source read) :
    ¬ M.Cofunctional := by
  intro hco
  obtain ⟨boundary, neighbor, destination, hne, hboundary, hneighbor⟩ :=
    M.exists_distinct_predecessors_of_mem_transition_left henabled
  exact hne (hco hboundary hneighbor)

/-- A right-moving local transition has the mirrored pair of distinct predecessors in the
complete width-two configuration graph. -/
public theorem Machine.exists_distinct_predecessors_of_mem_transition_right
    (M : Machine Γ Λ) {source target : Λ} {read written : Γ}
    (henabled : (target, written, DLBA.Dir.right) ∈ M.transition source read) :
    ∃ (neighbor boundary destination : DLBA.Cfg Γ Λ 1),
      neighbor ≠ boundary ∧ Step M neighbor destination ∧ Step M boundary destination := by
  let neighborTape : DLBA.BoundedTape Γ 1 :=
    ⟨rightNeighborContents read written, ⟨0, by omega⟩⟩
  let boundaryTape : DLBA.BoundedTape Γ 1 :=
    ⟨rightBoundaryContents read written, ⟨1, by omega⟩⟩
  let destinationTape : DLBA.BoundedTape Γ 1 :=
    ⟨fun _ => written, ⟨1, by omega⟩⟩
  have hneighborRead : neighborTape.read = read := by
    simp [neighborTape, rightNeighborContents, DLBA.BoundedTape.read]
  have hboundaryRead : boundaryTape.read = read := by
    rfl
  have hneighborMove :
      (neighborTape.write written).moveHead .right = destinationTape := by
    simp only [neighborTape, destinationTape, DLBA.BoundedTape.write,
      DLBA.BoundedTape.moveHead]
    congr 1
    funext index
    fin_cases index <;> simp [rightNeighborContents]
  have hboundaryMove :
      (boundaryTape.write written).moveHead .right = destinationTape := by
    simp only [boundaryTape, destinationTape, DLBA.BoundedTape.write,
      DLBA.BoundedTape.moveHead]
    congr 1
    funext index
    fin_cases index <;> simp [rightBoundaryContents]
  have hneighborStep :
      Step M ⟨source, neighborTape⟩ ⟨target, destinationTape⟩ := by
    refine ⟨target, written, .right, ?_, ?_⟩
    · simpa [hneighborRead] using henabled
    · exact congrArg (fun tape => (⟨target, tape⟩ : DLBA.Cfg Γ Λ 1)) hneighborMove.symm
  have hboundaryStep :
      Step M ⟨source, boundaryTape⟩ ⟨target, destinationTape⟩ := by
    refine ⟨target, written, .right, ?_, ?_⟩
    · simpa [hboundaryRead] using henabled
    · exact congrArg (fun tape => (⟨target, tape⟩ : DLBA.Cfg Γ Λ 1)) hboundaryMove.symm
  refine ⟨⟨source, neighborTape⟩, ⟨source, boundaryTape⟩,
    ⟨target, destinationTape⟩, ?_, hneighborStep, hboundaryStep⟩
  intro heq
  have hhead := congrArg (fun cfg => cfg.tape.head.val) heq
  simp [neighborTape, boundaryTape] at hhead

/-- Hence every enabled right-moving local transition rules out global cofunctionality. -/
public theorem Machine.not_cofunctional_of_mem_transition_right
    (M : Machine Γ Λ) {source target : Λ} {read written : Γ}
    (henabled : (target, written, DLBA.Dir.right) ∈ M.transition source read) :
    ¬ M.Cofunctional := by
  intro hco
  obtain ⟨neighbor, boundary, destination, hne, hneighbor, hboundary⟩ :=
    M.exists_distinct_predecessors_of_mem_transition_right henabled
  exact hne (hco hneighbor hboundary)

/-- Every enabled transition of a globally cofunctional clamped LBA is stationary. -/
public theorem Machine.direction_eq_stay_of_cofunctional
    (M : Machine Γ Λ) (hco : M.Cofunctional)
    {source target : Λ} {read written : Γ} {direction : DLBA.Dir}
    (henabled : (target, written, direction) ∈ M.transition source read) :
    direction = .stay := by
  cases direction with
  | stay => rfl
  | left => exact False.elim (M.not_cofunctional_of_mem_transition_left henabled hco)
  | right => exact False.elim (M.not_cofunctional_of_mem_transition_right henabled hco)

/-- Pointwise form of the clamping obstruction: global cofunctionality forces every enabled
transition to be stationary. -/
public theorem Machine.all_enabled_directions_stay_of_cofunctional
    (M : Machine Γ Λ) (hco : M.Cofunctional) :
    ∀ source read target written direction,
      (target, written, direction) ∈ M.transition source read → direction = .stay := by
  intro source read target written direction henabled
  exact M.direction_eq_stay_of_cofunctional hco henabled

/-- A globally cofunctional machine preserves the physical head in every low-level step. -/
public theorem Machine.step_head_eq_of_cofunctional
    (M : Machine Γ Λ) (hco : M.Cofunctional) {n : ℕ}
    {source target : DLBA.Cfg Γ Λ n} (hstep : Step M source target) :
    target.tape.head = source.tape.head := by
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  have hdirection : direction = .stay :=
    M.direction_eq_stay_of_cofunctional hco henabled
  subst direction
  rfl

/-- Consequently the physical head is invariant along every finite run of a globally
cofunctional machine. -/
public theorem Machine.reaches_head_eq_of_cofunctional
    (M : Machine Γ Λ) (hco : M.Cofunctional) {n : ℕ}
    {source target : DLBA.Cfg Γ Λ n} (hreach : Reaches M source target) :
    target.tape.head = source.tape.head := by
  induction hreach with
  | refl => rfl
  | tail _ hstep ih =>
      exact (M.step_head_eq_of_cofunctional hco hstep).trans ih

/-- A step of a globally cofunctional machine can be replayed at any tape width from a
configuration with the same control state and scanned symbol.  Since every enabled move is
stationary, the replay sees the same written symbol afterwards. -/
public theorem Machine.exists_step_of_step_of_same_state_read_of_cofunctional
    (M : Machine Γ Λ) (hco : M.Cofunctional) {leftWidth rightWidth : ℕ}
    {leftSource leftTarget : DLBA.Cfg Γ Λ leftWidth}
    (rightSource : DLBA.Cfg Γ Λ rightWidth)
    (hstate : rightSource.state = leftSource.state)
    (hread : rightSource.tape.read = leftSource.tape.read)
    (hstep : Step M leftSource leftTarget) :
    ∃ rightTarget : DLBA.Cfg Γ Λ rightWidth,
      Step M rightSource rightTarget ∧
        rightTarget.state = leftTarget.state ∧
        rightTarget.tape.read = leftTarget.tape.read := by
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  have hdirection : direction = .stay :=
    M.direction_eq_stay_of_cofunctional hco henabled
  subst direction
  let rightTarget : DLBA.Cfg Γ Λ rightWidth :=
    ⟨next, (rightSource.tape.write written).moveHead .stay⟩
  refine ⟨rightTarget, ?_, rfl, ?_⟩
  · refine ⟨next, written, .stay, ?_, rfl⟩
    change (next, written, DLBA.Dir.stay) ∈
      M.transition rightSource.state rightSource.tape.read
    rw [hstate, hread]
    exact henabled
  · simp [rightTarget, DLBA.BoundedTape.read, DLBA.BoundedTape.write,
      DLBA.BoundedTape.moveHead]

/-- Runs of a globally cofunctional machine depend only on the initial control state and scanned
symbol, not on the tape width or the contents away from the head. -/
public theorem Machine.exists_reaches_of_reaches_of_same_state_read_of_cofunctional
    (M : Machine Γ Λ) (hco : M.Cofunctional) {leftWidth rightWidth : ℕ}
    {leftSource leftTarget : DLBA.Cfg Γ Λ leftWidth}
    (rightSource : DLBA.Cfg Γ Λ rightWidth)
    (hstate : rightSource.state = leftSource.state)
    (hread : rightSource.tape.read = leftSource.tape.read)
    (hreach : Reaches M leftSource leftTarget) :
    ∃ rightTarget : DLBA.Cfg Γ Λ rightWidth,
      Reaches M rightSource rightTarget ∧
        rightTarget.state = leftTarget.state ∧
        rightTarget.tape.read = leftTarget.tape.read := by
  induction hreach generalizing rightSource with
  | refl => exact ⟨rightSource, .refl, hstate, hread⟩
  | @tail middle target hreach hstep ih =>
      obtain ⟨rightMiddle, hrightReach, hmiddleState, hmiddleRead⟩ :=
        ih rightSource hstate hread
      obtain ⟨rightTarget, hrightStep, htargetState, htargetRead⟩ :=
        M.exists_step_of_step_of_same_state_read_of_cofunctional
          hco rightMiddle hmiddleState hmiddleRead hstep
      exact ⟨rightTarget, hrightReach.tail hrightStep, htargetState, htargetRead⟩

/-- Acceptance by a globally cofunctional machine is identical at configurations with the same
control state and scanned symbol, even when their tape widths differ. -/
public theorem Machine.accepts_iff_of_same_state_read_of_cofunctional
    (M : Machine Γ Λ) (hco : M.Cofunctional) {leftWidth rightWidth : ℕ}
    (left : DLBA.Cfg Γ Λ leftWidth) (right : DLBA.Cfg Γ Λ rightWidth)
    (hstate : left.state = right.state) (hread : left.tape.read = right.tape.read) :
    Accepts M left ↔ Accepts M right := by
  constructor
  · rintro ⟨leftTarget, hleftReach, hleftAccept⟩
    obtain ⟨rightTarget, hrightReach, hstateTarget, _⟩ :=
      M.exists_reaches_of_reaches_of_same_state_read_of_cofunctional
        hco right hstate.symm hread.symm hleftReach
    exact ⟨rightTarget, hrightReach, by simpa [hstateTarget] using hleftAccept⟩
  · rintro ⟨rightTarget, hrightReach, hrightAccept⟩
    obtain ⟨leftTarget, hleftReach, hstateTarget, _⟩ :=
      M.exists_reaches_of_reaches_of_same_state_read_of_cofunctional
        hco left hstate hread hrightReach
    exact ⟨leftTarget, hleftReach, by simpa [hstateTarget] using hrightAccept⟩

end LBA
