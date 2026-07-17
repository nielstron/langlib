module

public import Langlib.Automata.DeterministicLinearBounded.Inclusion.LinearBounded
public import Langlib.Automata.LinearBounded.Definition
public import Mathlib.Data.Set.Card
import Mathlib.Tactic

@[expose]
public section

/-!
# Reducing LBA branching degree to two

Every finite LBA can be transformed, without changing its tape alphabet or language, into an LBA
with at most two local successors.  One original step is serialized as follows.

* A `ready q` state enters `scan q expected univ` deterministically without changing the tape.
* A scan state canonically selects one still-unexamined potential move.
* It has a skip edge, which erases that move from the finite set, and—when the selected move is
  genuinely enabled—an apply edge performing the original transition.

Thus each local transition set has cardinality at most two.  Accepting states are only ready
states, so the extra scan configurations cannot create spurious acceptance.

This reduction shows that bounding the local branching degree by two does not weaken the first
LBA problem: all of its nondeterministic power remains in repeated binary choices along a run.
-/

namespace LBA

open Classical

variable {Γ Λ : Type*}

/-- A potential move of an LBA with tape alphabet `Γ` and state type `Λ`. -/
public abbrev Move (Γ Λ : Type*) := Λ × Γ × DLBA.Dir

/-- Control states for the binary-branching simulation.

`scan q expected remaining` remembers the original state and scanned tape symbol while it
serializes the finite set of possible moves. -/
public inductive BinaryBranchState (Γ Λ : Type*) where
  | ready (state : Λ)
  | scan (state : Λ) (expected : Γ) (remaining : Finset (Move Γ Λ))
  deriving DecidableEq

public noncomputable instance [Fintype Γ] [Fintype Λ] :
    Fintype (BinaryBranchState Γ Λ) :=
  Fintype.ofEquiv
    (Λ ⊕ (Λ × Γ × Finset (Move Γ Λ)))
    { toFun := fun
        | .inl q => .ready q
        | .inr (q, expected, remaining) => .scan q expected remaining
      invFun := fun
        | .ready q => .inl q
        | .scan q expected remaining => .inr (q, expected, remaining)
      left_inv := by rintro (_ | ⟨_, _, _⟩) <;> rfl
      right_inv := by intro state; cases state <;> rfl }

/-- Forget the scan protocol and recover the represented original control state. -/
public def BinaryBranchState.original : BinaryBranchState Γ Λ → Λ
  | .ready q => q
  | .scan q _ _ => q

/-- Canonically select the head of a finite set's list representation. -/
public noncomputable def pickMove [DecidableEq Γ] [DecidableEq Λ]
    (remaining : Finset (Move Γ Λ)) : Option (Move Γ Λ) :=
  remaining.toList.head?

private theorem pickMove_eq_none_iff
    [DecidableEq Γ] [DecidableEq Λ]
    {remaining : Finset (Move Γ Λ)} :
    pickMove remaining = none ↔ remaining = ∅ := by
  rw [pickMove, List.head?_eq_none_iff, Finset.toList_eq_nil]

private theorem mem_of_pickMove_eq_some
    [DecidableEq Γ] [DecidableEq Λ]
    {remaining : Finset (Move Γ Λ)} {move : Move Γ Λ}
    (hpick : pickMove remaining = some move) :
    move ∈ remaining := by
  rw [pickMove, List.head?_eq_some_iff] at hpick
  obtain ⟨tail, hlist⟩ := hpick
  rw [← Finset.mem_toList, hlist]
  simp

/-- Serialize every original transition table into binary choices. -/
public noncomputable def Machine.binaryBranch
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    Machine Γ (BinaryBranchState Γ Λ) where
  transition state symbol :=
    match state with
    | .ready q =>
        {(.scan q symbol Finset.univ, symbol, .stay)}
    | .scan q expected remaining =>
        if symbol = expected then
          match LBA.pickMove remaining with
          | none => ∅
          | some move =>
              {(BinaryBranchState.scan q expected (remaining.erase move),
                  symbol, DLBA.Dir.stay)} ∪
                if move ∈ M.transition q expected then
                  {(BinaryBranchState.ready move.1, move.2.1, move.2.2)}
                else ∅
        else ∅
  accept
    | .ready q => M.accept q
    | .scan _ _ _ => false
  initial := .ready M.initial

/-- An LBA has binary local branching when every state/symbol transition set has cardinality
at most two. -/
public def Machine.BinaryBranching (M : Machine Γ Λ) : Prop :=
  ∀ q a, Set.encard (M.transition q a) ≤ 2

/-- The serialized machine has local branching degree at most two. -/
public theorem Machine.binaryBranch_binaryBranching
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    M.binaryBranch.BinaryBranching := by
  intro state symbol
  cases state with
  | ready q =>
      simp [Machine.binaryBranch]
  | scan q expected remaining =>
      simp only [Machine.binaryBranch]
      split
      · split
        · simp
        · next move hpick =>
            split
            · calc
                Set.encard
                    ({(BinaryBranchState.scan q expected (remaining.erase move),
                        symbol, DLBA.Dir.stay)} ∪
                      {(BinaryBranchState.ready move.1, move.2.1, move.2.2)}) ≤
                    Set.encard
                        ({(BinaryBranchState.scan q expected (remaining.erase move),
                            symbol, DLBA.Dir.stay)} :
                          Set (BinaryBranchState Γ Λ × Γ × DLBA.Dir)) +
                      Set.encard
                        ({(BinaryBranchState.ready move.1, move.2.1, move.2.2)} :
                          Set (BinaryBranchState Γ Λ × Γ × DLBA.Dir)) :=
                  Set.encard_union_le _ _
                _ = 2 := by
                  rw [Set.encard_singleton, Set.encard_singleton]
                  rfl
            · simp
      · simp

/-- Embed an original bounded configuration as a ready configuration of the serialized machine. -/
public def binaryLiftCfg {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Cfg Γ (BinaryBranchState Γ Λ) n :=
  ⟨.ready cfg.state, cfg.tape⟩

/-- Forget the scan protocol in an arbitrary serialized bounded configuration. -/
public def binaryProjectCfg {n : ℕ}
    (cfg : DLBA.Cfg Γ (BinaryBranchState Γ Λ) n) :
    DLBA.Cfg Γ Λ n :=
  ⟨cfg.state.original, cfg.tape⟩

@[simp]
public theorem binaryProjectCfg_lift {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    binaryProjectCfg (binaryLiftCfg cfg) = cfg := rfl

private theorem write_read_stay {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    (tape.write tape.read).moveHead .stay = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
    Function.update_eq_self]

/-- A ready configuration deterministically enters the full move scan without changing tape. -/
private theorem Machine.step_ready_scan
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    Step M.binaryBranch (binaryLiftCfg cfg)
      ⟨.scan cfg.state cfg.tape.read Finset.univ, cfg.tape⟩ := by
  refine ⟨.scan cfg.state cfg.tape.read Finset.univ, cfg.tape.read, .stay, ?_, ?_⟩
  · simp [Machine.binaryBranch, binaryLiftCfg]
  · simpa only [binaryLiftCfg] using
      congrArg
        (fun tape =>
          (⟨.scan cfg.state cfg.tape.read Finset.univ, tape⟩ :
            DLBA.Cfg Γ (BinaryBranchState Γ Λ) n))
        (write_read_stay cfg.tape).symm

/-- A scan can discard its selected move while preserving the represented configuration. -/
private theorem Machine.step_scan_skip
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (q : Λ) (tape : DLBA.BoundedTape Γ n)
    (remaining : Finset (Move Γ Λ)) (move : Move Γ Λ)
    (hpick : pickMove remaining = some move) :
    Step M.binaryBranch
      ⟨.scan q tape.read remaining, tape⟩
      ⟨.scan q tape.read (remaining.erase move), tape⟩ := by
  refine ⟨.scan q tape.read (remaining.erase move), tape.read, .stay, ?_, ?_⟩
  · simp [Machine.binaryBranch, hpick]
  · rw [write_read_stay]

/-- If the selected move is enabled, the scan can apply exactly that original transition and
return to a ready state. -/
private theorem Machine.step_scan_apply
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (q : Λ) (tape : DLBA.BoundedTape Γ n)
    (remaining : Finset (Move Γ Λ)) (move : Move Γ Λ)
    (hpick : pickMove remaining = some move)
    (henabled : move ∈ M.transition q tape.read) :
    Step M.binaryBranch
      ⟨.scan q tape.read remaining, tape⟩
      (binaryLiftCfg
        (⟨move.1, (tape.write move.2.1).moveHead move.2.2⟩ :
          DLBA.Cfg Γ Λ n)) := by
  refine ⟨.ready move.1, move.2.1, move.2.2, ?_, rfl⟩
  have henabled' : move ∈ M.transition q (tape.contents tape.head) := by
    simpa only [DLBA.BoundedTape.read] using henabled
  simp [Machine.binaryBranch, hpick, henabled']

/-- Starting from a scan set containing an enabled move, repeated binary skips can expose and
apply that move. -/
private theorem Machine.reaches_scan_apply_of_mem
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (q : Λ) (tape : DLBA.BoundedTape Γ n)
    (remaining : Finset (Move Γ Λ)) (move : Move Γ Λ)
    (hremaining : move ∈ remaining)
    (henabled : move ∈ M.transition q tape.read) :
    Reaches M.binaryBranch
      ⟨.scan q tape.read remaining, tape⟩
      (binaryLiftCfg
        (⟨move.1, (tape.write move.2.1).moveHead move.2.2⟩ :
          DLBA.Cfg Γ Λ n)) := by
  induction hcard : remaining.card using Nat.strong_induction_on generalizing remaining with
  | h card ih =>
      have hnonempty : remaining ≠ ∅ := by
        intro hempty
        subst remaining
        simp at hremaining
      have hpickNe : pickMove remaining ≠ none := by
        intro hpickNone
        exact hnonempty (pickMove_eq_none_iff.mp hpickNone)
      obtain ⟨selected, hselectedRev⟩ :=
        Option.ne_none_iff_exists.mp hpickNe
      have hpick : pickMove remaining = some selected := hselectedRev.symm
      have hselectedMem : selected ∈ remaining :=
        mem_of_pickMove_eq_some hpick
      by_cases hsame : selected = move
      · subst selected
        exact Relation.ReflTransGen.single
          (M.step_scan_apply q tape remaining move hpick henabled)
      · have hmoveRest : move ∈ remaining.erase selected := by
          rw [Finset.mem_erase]
          exact ⟨Ne.symm hsame, hremaining⟩
        have hsmaller : (remaining.erase selected).card < card := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hselectedMem
        have hrest :=
          ih (remaining.erase selected).card hsmaller
            (remaining.erase selected) hmoveRest rfl
        exact (Relation.ReflTransGen.single
          (M.step_scan_skip q tape remaining selected hpick)).trans
            hrest

/-- One original step is simulated by a finite ready-to-ready path of binary choices. -/
public theorem Machine.reaches_binaryLift_of_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ Λ n} (hstep : Step M cfg cfg') :
    Reaches M.binaryBranch (binaryLiftCfg cfg) (binaryLiftCfg cfg') := by
  rcases hstep with ⟨q', a, d, hmem, rfl⟩
  let move : Move Γ Λ := (q', a, d)
  have hmoveUniv : move ∈ (Finset.univ : Finset (Move Γ Λ)) := by simp
  exact Relation.ReflTransGen.head
    (M.step_ready_scan cfg)
    (M.reaches_scan_apply_of_mem cfg.state cfg.tape Finset.univ move
      hmoveUniv hmem)

/-- Every original run lifts to a run of the binary-branching simulator. -/
public theorem Machine.reaches_binaryLift_of_reaches
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ Λ n} (hreach : Reaches M cfg cfg') :
    Reaches M.binaryBranch (binaryLiftCfg cfg) (binaryLiftCfg cfg') := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.trans (M.reaches_binaryLift_of_step hstep)

private theorem Machine.mem_binaryBranch_ready_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (q : Λ) (symbol : Γ)
    (out : BinaryBranchState Γ Λ × Γ × DLBA.Dir) :
    out ∈ M.binaryBranch.transition (.ready q) symbol ↔
      out = (.scan q symbol Finset.univ, symbol, .stay) := by
  simp [Machine.binaryBranch]

private theorem Machine.mem_binaryBranch_scan_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (q : Λ) (expected symbol : Γ)
    (remaining : Finset (Move Γ Λ))
    (out : BinaryBranchState Γ Λ × Γ × DLBA.Dir) :
    out ∈ M.binaryBranch.transition (.scan q expected remaining) symbol ↔
      symbol = expected ∧
        ∃ move, pickMove remaining = some move ∧
          (out =
              (.scan q expected (remaining.erase move), symbol, .stay) ∨
            (move ∈ M.transition q expected ∧
              out = (.ready move.1, move.2.1, move.2.2))) := by
  by_cases hsymbol : symbol = expected
  · subst expected
    cases hpick : pickMove remaining with
    | none =>
        simp [Machine.binaryBranch, hpick]
    | some move =>
        by_cases henabled : move ∈ M.transition q symbol
        · simp [Machine.binaryBranch, hpick, henabled]
        · simp [Machine.binaryBranch, hpick, henabled]
  · simp [Machine.binaryBranch, hsymbol]

/-- Projecting one simulator step either stutters or produces one genuine original step. -/
private theorem Machine.binaryProjectCfg_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ (BinaryBranchState Γ Λ) n}
    (hstep : Step M.binaryBranch cfg cfg') :
    binaryProjectCfg cfg = binaryProjectCfg cfg' ∨
      Step M (binaryProjectCfg cfg) (binaryProjectCfg cfg') := by
  rcases cfg with ⟨state, tape⟩
  rcases hstep with ⟨next, written, dir, hmem, rfl⟩
  cases state with
  | ready q =>
      have hout :=
        (M.mem_binaryBranch_ready_iff q tape.read (next, written, dir)).1 hmem
      simp only [Prod.mk.injEq] at hout
      rcases hout with ⟨rfl, rfl, rfl⟩
      left
      change
        (⟨q, tape⟩ : DLBA.Cfg Γ Λ n) =
          ⟨q, (tape.write tape.read).moveHead .stay⟩
      exact congrArg (fun nextTape => (⟨q, nextTape⟩ : DLBA.Cfg Γ Λ n))
        (write_read_stay tape).symm
  | scan q expected remaining =>
      obtain ⟨hsymbol, selected, hpick, hskip | ⟨henabled, happly⟩⟩ :=
        (M.mem_binaryBranch_scan_iff q expected tape.read remaining
          (next, written, dir)).1 hmem
      · simp only [Prod.mk.injEq] at hskip
        rcases hskip with ⟨rfl, rfl, rfl⟩
        left
        change
          (⟨q, tape⟩ : DLBA.Cfg Γ Λ n) =
            ⟨q, (tape.write tape.read).moveHead .stay⟩
        exact congrArg (fun nextTape => (⟨q, nextTape⟩ : DLBA.Cfg Γ Λ n))
          (write_read_stay tape).symm
      · simp only [Prod.mk.injEq] at happly
        rcases happly with ⟨rfl, rfl, rfl⟩
        right
        rw [← hsymbol] at henabled
        exact ⟨selected.1, selected.2.1, selected.2.2, henabled, rfl⟩

/-- Projecting an arbitrary simulator run yields an original run; scan steps disappear as
stuttering. -/
public theorem Machine.reaches_binaryProjectCfg
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ (BinaryBranchState Γ Λ) n}
    (hreach : Reaches M.binaryBranch cfg cfg') :
    Reaches M (binaryProjectCfg cfg) (binaryProjectCfg cfg') := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      rcases M.binaryProjectCfg_step hstep with hsame | horiginal
      · simpa [hsame] using ih
      · exact ih.tail horiginal

/-- The original machine and its binary-branching serialization accept exactly the same bounded
configurations, when the simulator starts in the corresponding ready state. -/
public theorem Machine.accepts_binaryBranch_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    Accepts M.binaryBranch (binaryLiftCfg cfg) ↔ Accepts M cfg := by
  constructor
  · rintro ⟨target, hreach, haccept⟩
    have hprojected :
        Reaches M cfg (binaryProjectCfg target) := by
      simpa using M.reaches_binaryProjectCfg hreach
    cases hstate : target.state with
    | ready q =>
        refine ⟨binaryProjectCfg target, hprojected, ?_⟩
        simpa [Machine.binaryBranch, hstate, binaryProjectCfg,
          BinaryBranchState.original] using haccept
    | scan q expected remaining =>
        simp [Machine.binaryBranch, hstate] at haccept
  · rintro ⟨target, hreach, haccept⟩
    refine ⟨binaryLiftCfg target, M.reaches_binaryLift_of_reaches hreach, ?_⟩
    simpa [Machine.binaryBranch, binaryLiftCfg] using haccept

/-- Serialization preserves the language on nonempty inputs embedded into the same tape
alphabet. -/
public theorem Machine.languageViaEmbed_binaryBranch_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} (M : Machine Γ Λ) (embed : T → Γ) :
    LanguageViaEmbed M.binaryBranch embed = LanguageViaEmbed M embed := by
  funext w
  apply propext
  simp only [LanguageViaEmbed]
  constructor
  · rintro ⟨hne, haccept⟩
    refine ⟨hne, ?_⟩
    change Accepts M.binaryBranch
      (binaryLiftCfg (initCfgList M (w.map embed) hne)) at haccept
    exact (M.accepts_binaryBranch_iff _).mp haccept
  · rintro ⟨hne, haccept⟩
    refine ⟨hne, ?_⟩
    change Accepts M.binaryBranch
      (binaryLiftCfg (initCfgList M (w.map embed) hne))
    exact (M.accepts_binaryBranch_iff _).mpr haccept

/-- Serialization preserves `LanguageRecognized`, including the same explicit empty-word bit. -/
public theorem Machine.languageRecognized_binaryBranch_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} (M : Machine Γ Λ) (embed : T → Γ) (acceptEmpty : Bool) :
    LanguageRecognized M.binaryBranch embed acceptEmpty =
      LanguageRecognized M embed acceptEmpty := by
  funext w
  apply propext
  simp only [LanguageRecognized]
  rw [M.languageViaEmbed_binaryBranch_eq embed]

/-- Serialization preserves the canonical endmarker language, including the empty input. -/
public theorem Machine.languageEnd_binaryBranch_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} [Fintype T] [DecidableEq T]
    (M : Machine (EndAlpha T Γ) Λ) :
    LanguageEnd M.binaryBranch = LanguageEnd M := by
  funext w
  apply propext
  change
    Accepts M.binaryBranch (binaryLiftCfg (initCfgEnd M w)) ↔
      Accepts M (initCfgEnd M w)
  exact M.accepts_binaryBranch_iff _

end LBA

/-- Languages presented by canonical endmarker LBAs with local branching degree at most two. -/
public def is_BinaryBranchingLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.BinaryBranching ∧ LBA.LanguageEnd M = L

/-- The language class recognized by binary-branching canonical endmarker LBAs. -/
public def BinaryBranchingLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    Set (Language T) :=
  setOf is_BinaryBranchingLBA

/-- Every finite LBA language has a presentation with the same tape alphabet and local branching
degree at most two.  The reverse implication simply forgets the branching restriction. -/
public theorem is_LBA_iff_is_BinaryBranchingLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_LBA L ↔ is_BinaryBranchingLBA L := by
  constructor
  · rintro ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩
    letI := hΓ
    letI := hΛ
    letI := hdecΓ
    letI := hdecΛ
    refine ⟨Γ, LBA.BinaryBranchState (LBA.EndAlpha T Γ) Λ,
      hΓ, inferInstance, hdecΓ, inferInstance, M.binaryBranch,
      M.binaryBranch_binaryBranching, ?_⟩
    exact M.languageEnd_binaryBranch_eq.trans hM
  · rintro ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, _hbinary, hM⟩
    exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩

/-- Binary local branching recognizes exactly the full LBA language class. -/
public theorem BinaryBranchingLBA_eq_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (BinaryBranchingLBA : Set (Language T)) = LBA := by
  ext L
  exact (is_LBA_iff_is_BinaryBranchingLBA L).symm

/-- The first LBA problem is unchanged when restricted to LBAs of local branching degree at most
two. -/
public theorem lba_subset_dlba_iff_binaryBranchingLBA_subset
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) ⊆ DLBA) ↔
      ((BinaryBranchingLBA : Set (Language T)) ⊆ DLBA) := by
  rw [BinaryBranchingLBA_eq_LBA]

/-- The equality question is equivalently whether every binary-branching LBA language is
deterministic-LBA recognizable. -/
public theorem lba_eq_dlba_iff_binaryBranchingLBA_subset
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((BinaryBranchingLBA : Set (Language T)) ⊆ DLBA) := by
  rw [Set.Subset.antisymm_iff]
  simp only [DLBA_subset_LBA, and_true]
  exact lba_subset_dlba_iff_binaryBranchingLBA_subset

end
