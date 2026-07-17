module

public import Langlib.Automata.LinearBounded.BinaryBranching
public import Langlib.Automata.DeterministicLinearBounded.Inclusion.LinearBounded
public import Mathlib.Data.Set.Card
import Mathlib.Tactic

@[expose]
public section

/-!
# Simultaneously bounding both configuration-graph degrees

The binary-branching construction bounds the number of outgoing local moves.  This file adds a
second, independent serialization on the incoming side.  An original transition is split into:

1. a write, entering a state tagged by the complete source-side transition data;
2. the head movement, entering a private arrival state;
3. a finite merge chain that forgets the tag two incoming edges at a time.

The source symbol is retained in the tag, so overwriting does not merge distinct predecessors.
Clamped movement can have two predecessors at an endpoint, but never more: they are the target
tape itself and the target tape with its head moved once in the opposite direction.  Consequently
the transformed configuration graph has both indegree and outdegree at most two, for every tape
width.  The tape alphabet and the number of tape cells are unchanged.
-/

namespace LBA

open Classical

variable {Γ Λ : Type*}

/-- The information that must survive an overwritten transition until its incoming edge has
entered the target's private merge gadget. -/
public structure IncomingTag (Γ Λ : Type*) where
  source : Λ
  old : Γ
  written : Γ
  direction : DLBA.Dir
  deriving DecidableEq, Fintype

/-- Control states for incoming-edge serialization.

`written` is the state just after the source cell has been overwritten, while `arrived` is the
state just after the tagged head movement.  The `merge` chain canonically forgets the incoming
tag before returning to a `base` state. -/
public inductive IncomingState (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] where
  | base (state : Λ)
  | written (target : Λ) (tag : IncomingTag Γ Λ)
  | arrived (target : Λ) (tag : IncomingTag Γ Λ)
  | merge (target : Λ) (index : Fin (Fintype.card (IncomingTag Γ Λ)))
  deriving DecidableEq, Fintype

/-- The canonical index of an incoming transition tag. -/
public noncomputable def incomingIndex
    [Fintype Γ] [Fintype Λ] (tag : IncomingTag Γ Λ) :
    Fin (Fintype.card (IncomingTag Γ Λ)) :=
  (Fintype.equivFin (IncomingTag Γ Λ)) tag

/-- Recover the incoming tag at a canonical merge-chain index. -/
public noncomputable def incomingTagAt
    [Fintype Γ] [Fintype Λ]
    (index : Fin (Fintype.card (IncomingTag Γ Λ))) :
    IncomingTag Γ Λ :=
  (Fintype.equivFin (IncomingTag Γ Λ)).symm index

@[simp]
public theorem incomingTagAt_incomingIndex
    [Fintype Γ] [Fintype Λ] (tag : IncomingTag Γ Λ) :
    incomingTagAt (incomingIndex tag) = tag :=
  (Fintype.equivFin (IncomingTag Γ Λ)).symm_apply_apply tag

@[simp]
public theorem incomingIndex_incomingTagAt
    [Fintype Γ] [Fintype Λ]
    (index : Fin (Fintype.card (IncomingTag Γ Λ))) :
    incomingIndex (incomingTagAt index) = index :=
  (Fintype.equivFin (IncomingTag Γ Λ)).apply_symm_apply index

/-- Serialize all incoming edges of a machine.  The transition out of a `base` state first writes
the new symbol but deliberately stays on the source cell.  The separately tagged `written` state
then performs the original head movement. -/
public noncomputable def Machine.serializeIncoming
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    Machine Γ (IncomingState Γ Λ) where
  transition state symbol :=
    match state with
    | .base q =>
        (fun move =>
          (IncomingState.written move.1
              { source := q
                old := symbol
                written := move.2.1
                direction := move.2.2 },
            move.2.1, DLBA.Dir.stay)) '' M.transition q symbol
    | .written target tag =>
        if symbol = tag.written ∧
            (target, tag.written, tag.direction) ∈ M.transition tag.source tag.old then
          {(IncomingState.arrived target tag, symbol, tag.direction)}
        else ∅
    | .arrived target tag =>
        {(IncomingState.merge target (incomingIndex tag), symbol, DLBA.Dir.stay)}
    | .merge target index =>
        if hnext : index.val + 1 < Fintype.card (IncomingTag Γ Λ) then
          {(IncomingState.merge target ⟨index.val + 1, hnext⟩,
              symbol, DLBA.Dir.stay)}
        else
          {(IncomingState.base target, symbol, DLBA.Dir.stay)}
  accept
    | .base q => M.accept q
    | .written _ _ => false
    | .arrived _ _ => false
    | .merge _ _ => false
  initial := .base M.initial

/-- Embed an original configuration into the base phase of incoming-edge serialization. -/
public def incomingLiftCfg [Fintype Γ] [Fintype Λ]
    {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Cfg Γ (IncomingState Γ Λ) n :=
  ⟨.base cfg.state, cfg.tape⟩

/-- Project a serialized configuration to the original machine.

In the `written` phase the old source symbol is restored, because the original transition is
projected only when the separate movement step is taken. -/
public def incomingProjectCfg
    [Fintype Γ] [Fintype Λ] {n : ℕ}
    (cfg : DLBA.Cfg Γ (IncomingState Γ Λ) n) :
    DLBA.Cfg Γ Λ n :=
  match cfg.state with
  | .base q => ⟨q, cfg.tape⟩
  | .written _ tag => ⟨tag.source, cfg.tape.write tag.old⟩
  | .arrived target _ => ⟨target, cfg.tape⟩
  | .merge target _ => ⟨target, cfg.tape⟩

@[simp]
public theorem incomingProjectCfg_lift
    [Fintype Γ] [Fintype Λ] {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    incomingProjectCfg (incomingLiftCfg cfg) = cfg := rfl

private theorem write_read {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    tape.write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

private theorem write_write_read {n : ℕ} (tape : DLBA.BoundedTape Γ n)
    (written : Γ) :
    (tape.write written).write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

private theorem moveHead_write_read {n : ℕ} (tape : DLBA.BoundedTape Γ n)
    (direction : DLBA.Dir) :
    (tape.write tape.read).moveHead direction = tape.moveHead direction := by
  rw [write_read]

private theorem restore_then_write
    [DecidableEq Γ] {n : ℕ} (tape : DLBA.BoundedTape Γ n)
    (old written : Γ) (hread : tape.read = written) :
    (tape.write old).write written = tape := by
  subst written
  rw [write_write_read]

/-- The write half of an original transition enters its private tagged state. -/
private theorem Machine.step_base_written
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) (target : Λ) (written : Γ)
    (direction : DLBA.Dir)
    (henabled : (target, written, direction) ∈
      M.transition cfg.state cfg.tape.read) :
    Step M.serializeIncoming
      (incomingLiftCfg cfg)
      ⟨.written target
          { source := cfg.state
            old := cfg.tape.read
            written := written
            direction := direction },
        cfg.tape.write written⟩ := by
  refine ⟨.written target
      { source := cfg.state
        old := cfg.tape.read
        written := written
        direction := direction },
    written, .stay, ?_, ?_⟩
  · exact ⟨(target, written, direction), henabled, rfl⟩
  · simp [incomingLiftCfg, DLBA.BoundedTape.moveHead]

/-- The movement half of a tagged transition enters its private arrival state. -/
private theorem Machine.step_written_arrived
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) (target : Λ) (written : Γ)
    (direction : DLBA.Dir)
    (henabled : (target, written, direction) ∈
      M.transition cfg.state cfg.tape.read) :
    let tag : IncomingTag Γ Λ :=
      { source := cfg.state
        old := cfg.tape.read
        written := written
        direction := direction }
    Step M.serializeIncoming
      ⟨.written target tag, cfg.tape.write written⟩
      ⟨.arrived target tag, (cfg.tape.write written).moveHead direction⟩ := by
  let tag : IncomingTag Γ Λ :=
    { source := cfg.state
      old := cfg.tape.read
      written := written
      direction := direction }
  refine ⟨.arrived target tag, written, direction, ?_, ?_⟩
  · simp only [Machine.serializeIncoming]
    have henabled' :
        (target, written, direction) ∈
          M.transition cfg.state (cfg.tape.contents cfg.tape.head) := by
      simpa only [DLBA.BoundedTape.read] using henabled
    simpa [tag, DLBA.BoundedTape.write] using henabled'
  · simp [tag, DLBA.BoundedTape.write]

/-- A private arrival enters the merge chain at the canonical index of its tag. -/
private theorem Machine.step_arrived_merge
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (target : Λ) (tag : IncomingTag Γ Λ) (tape : DLBA.BoundedTape Γ n) :
    Step M.serializeIncoming
      ⟨.arrived target tag, tape⟩
      ⟨.merge target (incomingIndex tag), tape⟩ := by
  refine ⟨.merge target (incomingIndex tag), tape.read, .stay, ?_, ?_⟩
  · simp [Machine.serializeIncoming]
  · rw [write_read]
    rfl

/-- Every point of a merge chain reaches its target base state. -/
private theorem Machine.reaches_merge_base
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    (target : Λ)
    (index : Fin (Fintype.card (IncomingTag Γ Λ)))
    (tape : DLBA.BoundedTape Γ n) :
    Reaches M.serializeIncoming
      ⟨.merge target index, tape⟩
      ⟨.base target, tape⟩ := by
  induction hremaining :
      Fintype.card (IncomingTag Γ Λ) - 1 - index.val
      using Nat.strong_induction_on generalizing index with
  | h remaining ih =>
      by_cases hnext :
          index.val + 1 < Fintype.card (IncomingTag Γ Λ)
      · let next : Fin (Fintype.card (IncomingTag Γ Λ)) :=
          ⟨index.val + 1, hnext⟩
        have hsmaller :
            Fintype.card (IncomingTag Γ Λ) - 1 - next.val < remaining := by
          dsimp [next]
          omega
        have htail :=
          ih
            (Fintype.card (IncomingTag Γ Λ) - 1 - next.val)
            hsmaller next rfl
        apply Relation.ReflTransGen.head _ htail
        refine ⟨.merge target next, tape.read, .stay, ?_, ?_⟩
        · simp [Machine.serializeIncoming, hnext, next]
        · rw [write_read]
          rfl
      · exact Relation.ReflTransGen.single
          ⟨.base target, tape.read, .stay,
            by simp [Machine.serializeIncoming, hnext],
            by rw [write_read]; rfl⟩

/-- One original transition is simulated by a path through its private incoming-edge gadget. -/
public theorem Machine.reaches_incomingLift_of_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ Λ n} (hstep : Step M cfg cfg') :
    Reaches M.serializeIncoming
      (incomingLiftCfg cfg) (incomingLiftCfg cfg') := by
  rcases hstep with ⟨target, written, direction, henabled, rfl⟩
  let tag : IncomingTag Γ Λ :=
    { source := cfg.state
      old := cfg.tape.read
      written := written
      direction := direction }
  let writtenCfg : DLBA.Cfg Γ (IncomingState Γ Λ) n :=
    ⟨.written target tag, cfg.tape.write written⟩
  let arrivedCfg : DLBA.Cfg Γ (IncomingState Γ Λ) n :=
    ⟨.arrived target tag, (cfg.tape.write written).moveHead direction⟩
  let mergeCfg : DLBA.Cfg Γ (IncomingState Γ Λ) n :=
    ⟨.merge target (incomingIndex tag),
      (cfg.tape.write written).moveHead direction⟩
  exact Relation.ReflTransGen.head
    (M.step_base_written cfg target written direction henabled)
    (Relation.ReflTransGen.head
      (M.step_written_arrived cfg target written direction henabled)
      (Relation.ReflTransGen.head
        (M.step_arrived_merge target tag
          ((cfg.tape.write written).moveHead direction))
        (M.reaches_merge_base target (incomingIndex tag)
          ((cfg.tape.write written).moveHead direction))))

/-- Every original run lifts to a run of the incoming-edge serializer. -/
public theorem Machine.reaches_incomingLift_of_reaches
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ Λ n} (hreach : Reaches M cfg cfg') :
    Reaches M.serializeIncoming
      (incomingLiftCfg cfg) (incomingLiftCfg cfg') := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.trans (M.reaches_incomingLift_of_step hstep)

/-- Projecting one incoming-serializer step either stutters or performs one genuine original
transition.  This statement is global: it also covers unreachable, malformed intermediate
configurations. -/
private theorem Machine.incomingProjectCfg_step
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ (IncomingState Γ Λ) n}
    (hstep : Step M.serializeIncoming cfg cfg') :
    incomingProjectCfg cfg = incomingProjectCfg cfg' ∨
      Step M (incomingProjectCfg cfg) (incomingProjectCfg cfg') := by
  rcases cfg with ⟨state, tape⟩
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  cases state with
  | base q =>
      simp only [Machine.serializeIncoming] at hmem
      rcases hmem with ⟨move, henabled, hmove⟩
      simp only [Prod.mk.injEq] at hmove
      rcases hmove with ⟨rfl, rfl, rfl⟩
      left
      change
        (⟨q, tape⟩ : DLBA.Cfg Γ Λ n) =
          ⟨q, ((tape.write move.2.1).moveHead .stay).write tape.read⟩
      simp only [DLBA.BoundedTape.moveHead]
      exact congrArg
        (fun nextTape => (⟨q, nextTape⟩ : DLBA.Cfg Γ Λ n))
        (write_write_read tape move.2.1).symm
  | written target tag =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · next henabled =>
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          right
          change
            Step M
              ⟨tag.source, tape.write tag.old⟩
              ⟨target, (tape.write tape.read).moveHead tag.direction⟩
          refine ⟨target, tag.written, tag.direction, ?_, ?_⟩
          · simpa [DLBA.BoundedTape.write] using henabled.2
          · have hrestore :
                (tape.write tag.old).write tag.written = tape :=
              restore_then_write tape tag.old tag.written henabled.1
            have hcopy : tape.write tape.read = tape := write_read tape
            rw [hrestore, hcopy]
      · simp at hmem
  | arrived target tag =>
      simp only [Machine.serializeIncoming, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      left
      change
        (⟨target, tape⟩ : DLBA.Cfg Γ Λ n) =
          ⟨target, (tape.write tape.read).moveHead .stay⟩
      rw [write_read]
      rfl
  | merge target index =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        left
        change
          (⟨target, tape⟩ : DLBA.Cfg Γ Λ n) =
            ⟨target, (tape.write tape.read).moveHead .stay⟩
        rw [write_read]
        rfl
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        left
        change
          (⟨target, tape⟩ : DLBA.Cfg Γ Λ n) =
            ⟨target, (tape.write tape.read).moveHead .stay⟩
        rw [write_read]
        rfl

/-- Projecting an arbitrary serialized run yields an original run; all gadget phases except the
tagged movement disappear as stuttering. -/
public theorem Machine.reaches_incomingProjectCfg
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg cfg' : DLBA.Cfg Γ (IncomingState Γ Λ) n}
    (hreach : Reaches M.serializeIncoming cfg cfg') :
    Reaches M (incomingProjectCfg cfg) (incomingProjectCfg cfg') := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      rcases M.incomingProjectCfg_step hstep with hsame | horiginal
      · simpa [hsame] using ih
      · exact ih.tail horiginal

/-- Incoming-edge serialization preserves acceptance from every embedded original
configuration. -/
public theorem Machine.accepts_serializeIncoming_iff
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    Accepts M.serializeIncoming (incomingLiftCfg cfg) ↔ Accepts M cfg := by
  constructor
  · rintro ⟨target, hreach, haccept⟩
    have hprojected :
        Reaches M cfg (incomingProjectCfg target) := by
      simpa using M.reaches_incomingProjectCfg hreach
    cases hstate : target.state with
    | base q =>
        refine ⟨incomingProjectCfg target, hprojected, ?_⟩
        simpa [Machine.serializeIncoming, hstate, incomingProjectCfg] using haccept
    | written target tag =>
        simp [Machine.serializeIncoming, hstate] at haccept
    | arrived target tag =>
        simp [Machine.serializeIncoming, hstate] at haccept
    | merge target index =>
        simp [Machine.serializeIncoming, hstate] at haccept
  · rintro ⟨target, hreach, haccept⟩
    refine ⟨incomingLiftCfg target,
      M.reaches_incomingLift_of_reaches hreach, ?_⟩
    simpa [Machine.serializeIncoming, incomingLiftCfg] using haccept

/-- Incoming-edge serialization preserves languages loaded through an arbitrary alphabet
embedding. -/
public theorem Machine.languageViaEmbed_serializeIncoming_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} (M : Machine Γ Λ) (embed : T → Γ) :
    LanguageViaEmbed M.serializeIncoming embed = LanguageViaEmbed M embed := by
  funext w
  apply propext
  simp only [LanguageViaEmbed]
  constructor
  · rintro ⟨hne, haccept⟩
    refine ⟨hne, ?_⟩
    change Accepts M.serializeIncoming
      (incomingLiftCfg (initCfgList M (w.map embed) hne)) at haccept
    exact (M.accepts_serializeIncoming_iff _).mp haccept
  · rintro ⟨hne, haccept⟩
    refine ⟨hne, ?_⟩
    change Accepts M.serializeIncoming
      (incomingLiftCfg (initCfgList M (w.map embed) hne))
    exact (M.accepts_serializeIncoming_iff _).mpr haccept

/-- Incoming-edge serialization preserves `LanguageRecognized`, including its explicit empty
word bit. -/
public theorem Machine.languageRecognized_serializeIncoming_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} (M : Machine Γ Λ) (embed : T → Γ) (acceptEmpty : Bool) :
    LanguageRecognized M.serializeIncoming embed acceptEmpty =
      LanguageRecognized M embed acceptEmpty := by
  funext w
  apply propext
  simp only [LanguageRecognized]
  rw [M.languageViaEmbed_serializeIncoming_eq embed]

/-- Incoming-edge serialization preserves the canonical endmarker language, including the empty
input. -/
public theorem Machine.languageEnd_serializeIncoming_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} [Fintype T] [DecidableEq T]
    (M : Machine (EndAlpha T Γ) Λ) :
    LanguageEnd M.serializeIncoming = LanguageEnd M := by
  funext w
  apply propext
  change
    Accepts M.serializeIncoming (incomingLiftCfg (initCfgEnd M w)) ↔
      Accepts M (initCfgEnd M w)
  exact M.accepts_serializeIncoming_iff _

/-- Every configuration has at most two distinct immediate successors. -/
public def Machine.ConfigurationOutdegreeAtMostTwo (M : Machine Γ Λ) : Prop :=
  ∀ (n : ℕ) (cfg : DLBA.Cfg Γ Λ n),
    Set.encard {cfg' | Step M cfg cfg'} ≤ 2

/-- Every configuration has at most two distinct immediate predecessors. -/
public def Machine.ConfigurationIndegreeAtMostTwo (M : Machine Γ Λ) : Prop :=
  ∀ (n : ℕ) (cfg : DLBA.Cfg Γ Λ n),
    Set.encard {cfg' | Step M cfg' cfg} ≤ 2

/-- Both directed degrees of every configuration graph are at most two, uniformly over all tape
widths. -/
public def Machine.ConfigurationDegreeAtMostTwo (M : Machine Γ Λ) : Prop :=
  M.ConfigurationOutdegreeAtMostTwo ∧ M.ConfigurationIndegreeAtMostTwo

/-- The successor configurations are the image of the enabled local transition triples. -/
private theorem Machine.successors_eq_image
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    {cfg' | Step M cfg cfg'} =
      (fun move =>
        (⟨move.1, (cfg.tape.write move.2.1).moveHead move.2.2⟩ :
          DLBA.Cfg Γ Λ n)) '' M.transition cfg.state cfg.tape.read := by
  ext cfg'
  constructor
  · rintro ⟨target, written, direction, henabled, rfl⟩
    exact ⟨(target, written, direction), henabled, rfl⟩
  · rintro ⟨⟨target, written, direction⟩, henabled, rfl⟩
    exact ⟨target, written, direction, henabled, rfl⟩

/-- Configuration outdegree is bounded by the cardinality of the local transition set. -/
public theorem Machine.configurationOutdegree_le_transition
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    Set.encard {cfg' | Step M cfg cfg'} ≤
      Set.encard (M.transition cfg.state cfg.tape.read) := by
  rw [M.successors_eq_image cfg]
  apply Set.encard_image_le

/-- Incoming-edge serialization does not increase the local branching bound. -/
public theorem Machine.serializeIncoming_binaryBranching
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) (hbinary : M.BinaryBranching) :
    M.serializeIncoming.BinaryBranching := by
  intro state symbol
  cases state with
  | base q =>
      calc
        Set.encard
            (M.serializeIncoming.transition (.base q) symbol) ≤
            Set.encard (M.transition q symbol) := by
          simp only [Machine.serializeIncoming]
          apply Set.encard_image_le
        _ ≤ 2 := hbinary q symbol
  | written target tag =>
      simp only [Machine.serializeIncoming]
      split <;> simp
  | arrived target tag =>
      simp [Machine.serializeIncoming]
  | merge target index =>
      simp only [Machine.serializeIncoming]
      split <;> simp

/-- A binary local transition table gives configuration outdegree at most two. -/
public theorem Machine.configurationOutdegreeAtMostTwo_of_binaryBranching
    (M : Machine Γ Λ) (hbinary : M.BinaryBranching) :
    M.ConfigurationOutdegreeAtMostTwo := by
  intro n cfg
  exact (M.configurationOutdegree_le_transition cfg).trans
    (hbinary cfg.state cfg.tape.read)

/-- Reverse a head direction for the purpose of listing the at-most-two inverse clamped moves. -/
private def oppositeDir : DLBA.Dir → DLBA.Dir
  | .left => .right
  | .right => .left
  | .stay => .stay

/-- A clamped head movement has at most the two obvious inverse tapes: the target tape itself and
the target tape moved once in the opposite direction.  At a boundary both can genuinely occur;
away from a boundary one of them is merely an unused over-approximation. -/
private theorem moveHead_eq_implies_eq_or_opposite
    {n : ℕ} (source target : DLBA.BoundedTape Γ n) (direction : DLBA.Dir)
    (hmove : source.moveHead direction = target) :
    source = target ∨ source = target.moveHead (oppositeDir direction) := by
  subst target
  cases direction with
  | stay =>
      left
      rfl
  | left =>
      by_cases hpos : 0 < source.head.val
      · right
        cases source with
        | mk contents head =>
            have hpos' : 0 < head.val := by
              simpa using hpos
            have hlt : head.val - 1 < n := by
              have := head.isLt
              omega
            simp only [DLBA.BoundedTape.moveHead, hpos, oppositeDir, hlt,
              dite_true]
            apply congrArg
              (fun newHead =>
                (⟨contents, newHead⟩ : DLBA.BoundedTape Γ n))
            apply Fin.ext
            simp
            exact (Nat.sub_add_cancel hpos').symm
      · left
        simp [DLBA.BoundedTape.moveHead, hpos]
  | right =>
      by_cases hlt : source.head.val < n
      · right
        cases source with
        | mk contents head =>
            have hpos : 0 < head.val + 1 := by omega
            simp [DLBA.BoundedTape.moveHead, hlt, oppositeDir, hpos]
      · left
        simp [DLBA.BoundedTape.moveHead, hlt]

/-- On a one-cell tape (`n = 0`) every direction is clamped to the unique head position.  Thus
the two inverse candidates in `moveHead_eq_implies_eq_or_opposite` collapse to one. -/
public theorem moveHead_oneCell
    (tape : DLBA.BoundedTape Γ 0) (direction : DLBA.Dir) :
    tape.moveHead direction = tape := by
  cases tape with
  | mk contents head =>
      cases direction <;>
        simp [DLBA.BoundedTape.moveHead, Fin.eq_zero head]

/-- With at least two cells, left clamping genuinely creates two distinct inverse head positions:
the boundary cell and its immediate neighbour. -/
public theorem moveHead_leftBoundary_twoPreimages
    {n : ℕ} (contents : Fin ((n + 1) + 1) → Γ) :
    let boundary : DLBA.BoundedTape Γ (n + 1) :=
      ⟨contents, ⟨0, by omega⟩⟩
    let neighbor : DLBA.BoundedTape Γ (n + 1) :=
      ⟨contents, ⟨1, by omega⟩⟩
    boundary.moveHead .left = boundary ∧
      neighbor.moveHead .left = boundary ∧ neighbor ≠ boundary := by
  dsimp
  constructor
  · simp [DLBA.BoundedTape.moveHead]
  constructor
  · simp [DLBA.BoundedTape.moveHead]
  · intro heq
    have hhead := congrArg DLBA.BoundedTape.head heq
    simp at hhead

/-- With at least two cells, right clamping likewise creates the last cell and its immediate
neighbour as two distinct inverse head positions. -/
public theorem moveHead_rightBoundary_twoPreimages
    {n : ℕ} (contents : Fin ((n + 1) + 1) → Γ) :
    let boundary : DLBA.BoundedTape Γ (n + 1) :=
      ⟨contents, ⟨n + 1, by omega⟩⟩
    let neighbor : DLBA.BoundedTape Γ (n + 1) :=
      ⟨contents, ⟨n, by omega⟩⟩
    boundary.moveHead .right = boundary ∧
      neighbor.moveHead .right = boundary ∧ neighbor ≠ boundary := by
  dsimp
  constructor
  · simp [DLBA.BoundedTape.moveHead]
  constructor
  · simp [DLBA.BoundedTape.moveHead]
  · intro heq
    have hhead := congrArg DLBA.BoundedTape.head heq
    simp at hhead

/-- A tagged post-write configuration has at most one predecessor, obtained by restoring the
overwritten source symbol. -/
private theorem Machine.predecessor_written_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg : DLBA.Cfg Γ (IncomingState Γ Λ) n}
    {target : Λ} {tag : IncomingTag Γ Λ} {tape : DLBA.BoundedTape Γ n}
    (hstep : Step M.serializeIncoming cfg ⟨.written target tag, tape⟩) :
    cfg = ⟨.base tag.source, tape.write tag.old⟩ := by
  rcases cfg with ⟨state, sourceTape⟩
  rcases hstep with ⟨next, written, direction, hmem, heq⟩
  cases state with
  | base q =>
      simp only [Machine.serializeIncoming] at hmem
      rcases hmem with ⟨move, henabled, hmove⟩
      simp only [Prod.mk.injEq] at hmove
      rcases hmove with ⟨rfl, rfl, rfl⟩
      simp only [IncomingState.written.injEq, DLBA.Cfg.mk.injEq] at heq
      rcases heq with ⟨hstate, htape⟩
      rcases hstate with ⟨rfl, htag⟩
      cases htag
      apply congrArg
        (fun nextTape =>
          (⟨.base q, nextTape⟩ :
            DLBA.Cfg Γ (IncomingState Γ Λ) n))
      rw [htape]
      simp only [DLBA.BoundedTape.moveHead]
      exact (write_write_read sourceTape move.2.1).symm
  | written sourceTarget sourceTag =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        simp at heq
      · simp at hmem
  | arrived sourceTarget sourceTag =>
      simp only [Machine.serializeIncoming, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      simp at heq
  | merge sourceTarget sourceIndex =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        simp at heq
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        simp at heq

/-- A private arrival configuration has at most the two predecessors created by inverse clamped
movement.  This is the only phase where two predecessors may arise from one tagged edge. -/
private theorem Machine.predecessor_arrived_eq_or_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg : DLBA.Cfg Γ (IncomingState Γ Λ) n}
    {target : Λ} {tag : IncomingTag Γ Λ} {tape : DLBA.BoundedTape Γ n}
    (hstep : Step M.serializeIncoming cfg ⟨.arrived target tag, tape⟩) :
    cfg = ⟨.written target tag, tape⟩ ∨
      cfg = ⟨.written target tag, tape.moveHead (oppositeDir tag.direction)⟩ := by
  rcases cfg with ⟨state, sourceTape⟩
  rcases hstep with ⟨next, written, direction, hmem, heq⟩
  cases state with
  | base q =>
      simp only [Machine.serializeIncoming] at hmem
      rcases hmem with ⟨move, henabled, hmove⟩
      simp only [Prod.mk.injEq] at hmove
      rcases hmove with ⟨rfl, rfl, rfl⟩
      simp at heq
  | written sourceTarget sourceTag =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · next henabled =>
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          simp only [IncomingState.arrived.injEq, DLBA.Cfg.mk.injEq] at heq
          rcases heq with ⟨hstate, htape⟩
          rcases hstate with ⟨rfl, rfl⟩
          have htape' :
              sourceTape.moveHead tag.direction = tape := by
            rw [htape, write_read]
          rcases moveHead_eq_implies_eq_or_opposite
              sourceTape tape tag.direction htape' with hsame | hopposite
          · left
            exact congrArg
              (fun nextTape =>
                (⟨.written target tag, nextTape⟩ :
                  DLBA.Cfg Γ (IncomingState Γ Λ) n))
              hsame
          · right
            exact congrArg
              (fun nextTape =>
                (⟨.written target tag, nextTape⟩ :
                  DLBA.Cfg Γ (IncomingState Γ Λ) n))
              hopposite
      · simp at hmem
  | arrived sourceTarget sourceTag =>
      simp only [Machine.serializeIncoming, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      simp at heq
  | merge sourceTarget sourceIndex =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        simp at heq
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        simp at heq

/-- A canonical predecessor index.  At index zero the value is an unused fallback; no merge edge
can enter the zero node. -/
private def previousIncomingIndex
    [Fintype Γ] [Fintype Λ]
    (index : Fin (Fintype.card (IncomingTag Γ Λ))) :
    Fin (Fintype.card (IncomingTag Γ Λ)) :=
  if hpos : 0 < index.val then
    ⟨index.val - 1, by
      have := index.isLt
      omega⟩
  else index

/-- A merge node has at most two predecessors: its uniquely indexed arrival leaf and the previous
merge node. -/
private theorem Machine.predecessor_merge_eq_or_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg : DLBA.Cfg Γ (IncomingState Γ Λ) n}
    {target : Λ}
    {index : Fin (Fintype.card (IncomingTag Γ Λ))}
    {tape : DLBA.BoundedTape Γ n}
    (hstep : Step M.serializeIncoming cfg ⟨.merge target index, tape⟩) :
    cfg = ⟨.arrived target (incomingTagAt index), tape⟩ ∨
      cfg = ⟨.merge target (previousIncomingIndex index), tape⟩ := by
  rcases cfg with ⟨state, sourceTape⟩
  rcases hstep with ⟨next, written, direction, hmem, heq⟩
  cases state with
  | base q =>
      simp only [Machine.serializeIncoming] at hmem
      rcases hmem with ⟨move, henabled, hmove⟩
      simp only [Prod.mk.injEq] at hmove
      rcases hmove with ⟨rfl, rfl, rfl⟩
      simp at heq
  | written sourceTarget sourceTag =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        simp at heq
      · simp at hmem
  | arrived sourceTarget sourceTag =>
      simp only [Machine.serializeIncoming, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      simp only [IncomingState.merge.injEq, DLBA.Cfg.mk.injEq] at heq
      rcases heq with ⟨hstate, htape⟩
      rcases hstate with ⟨rfl, hindex⟩
      left
      have htag : sourceTag = incomingTagAt index := by
        apply (Fintype.equivFin (IncomingTag Γ Λ)).injective
        simpa only [incomingIndex, incomingTagAt,
          Equiv.apply_symm_apply] using hindex.symm
      subst sourceTag
      apply congrArg
        (fun nextTape =>
          (⟨.arrived target (incomingTagAt index), nextTape⟩ :
            DLBA.Cfg Γ (IncomingState Γ Λ) n))
      rw [htape, write_read]
      rfl
  | merge sourceTarget sourceIndex =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · next hnext =>
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          simp only [IncomingState.merge.injEq, DLBA.Cfg.mk.injEq] at heq
          rcases heq with ⟨hstate, htape⟩
          rcases hstate with ⟨rfl, hindex⟩
          right
          have hpos : 0 < index.val := by
            have hval := congrArg Fin.val hindex
            simp only at hval
            omega
          have hsource :
              sourceIndex = previousIncomingIndex index := by
            rw [previousIncomingIndex, dif_pos hpos]
            apply Fin.ext
            have hval := congrArg Fin.val hindex
            simp only at hval
            simp only
            omega
          subst sourceIndex
          apply congrArg
            (fun nextTape =>
              (⟨.merge target (previousIncomingIndex index), nextTape⟩ :
                DLBA.Cfg Γ (IncomingState Γ Λ) n))
          rw [htape, write_read]
          rfl
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        simp at heq

/-- The last merge index, with explicit alphabet/state witnesses so this definition remains usable
without global `Nonempty` instances. -/
private def lastIncomingIndex
    [Fintype Γ] [Fintype Λ] (symbol : Γ) (state : Λ) :
    Fin (Fintype.card (IncomingTag Γ Λ)) :=
  ⟨Fintype.card (IncomingTag Γ Λ) - 1, by
    have hnonempty : Nonempty (IncomingTag Γ Λ) :=
      ⟨{ source := state,
          old := symbol,
          written := symbol,
          direction := .stay }⟩
    have hpositive : 0 < Fintype.card (IncomingTag Γ Λ) :=
      Fintype.card_pos_iff.mpr hnonempty
    omega⟩

/-- A base configuration has at most one predecessor: the last node of its merge chain. -/
private theorem Machine.predecessor_base_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ}
    {cfg : DLBA.Cfg Γ (IncomingState Γ Λ) n}
    {target : Λ} {tape : DLBA.BoundedTape Γ n}
    (hstep : Step M.serializeIncoming cfg ⟨.base target, tape⟩) :
    cfg = ⟨.merge target (lastIncomingIndex tape.read target), tape⟩ := by
  rcases cfg with ⟨state, sourceTape⟩
  rcases hstep with ⟨next, written, direction, hmem, heq⟩
  cases state with
  | base q =>
      simp only [Machine.serializeIncoming] at hmem
      rcases hmem with ⟨move, henabled, hmove⟩
      simp only [Prod.mk.injEq] at hmove
      rcases hmove with ⟨rfl, rfl, rfl⟩
      simp at heq
  | written sourceTarget sourceTag =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        simp at heq
      · simp at hmem
  | arrived sourceTarget sourceTag =>
      simp only [Machine.serializeIncoming, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩
      simp at heq
  | merge sourceTarget sourceIndex =>
      simp only [Machine.serializeIncoming] at hmem
      split at hmem
      · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩
        simp at heq
      · next hlast =>
          simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          simp only [IncomingState.base.injEq, DLBA.Cfg.mk.injEq] at heq
          rcases heq with ⟨rfl, htape⟩
          have hindex :
              sourceIndex = lastIncomingIndex tape.read target := by
            apply Fin.ext
            simp only [lastIncomingIndex]
            have hupper := sourceIndex.isLt
            have hpositive :
                0 < Fintype.card (IncomingTag Γ Λ) := by
              exact Fintype.card_pos_iff.mpr
                ⟨{ source := target,
                    old := tape.read,
                    written := tape.read,
                    direction := .stay }⟩
            have hlastEq :
                sourceIndex.val + 1 =
                  Fintype.card (IncomingTag Γ Λ) := by
              omega
            exact Nat.eq_sub_of_add_eq hlastEq
          subst sourceIndex
          apply congrArg
            (fun nextTape =>
              (⟨.merge target (lastIncomingIndex tape.read target), nextTape⟩ :
                DLBA.Cfg Γ (IncomingState Γ Λ) n))
          rw [htape, write_read]
          rfl

/-- Every base-phase configuration of the incoming-edge serializer has at most one immediate
predecessor.  This sharper phase-specific bound leaves one spare predecessor slot at the
canonical initial configuration when the certified-row presentation adds its raw-input
initialization edge. -/
public theorem Machine.serializeIncoming_configurationIndegreeBaseAtMostOne
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) {n : ℕ} (target : Λ) (tape : DLBA.BoundedTape Γ n) :
    Set.encard
        {cfg' | Step M.serializeIncoming cfg'
          ⟨.base target, tape⟩} ≤ 1 := by
  let candidate :
      DLBA.Cfg Γ (IncomingState Γ Λ) n :=
    ⟨.merge target (lastIncomingIndex tape.read target), tape⟩
  calc
    Set.encard
        {cfg' | Step M.serializeIncoming cfg'
          ⟨.base target, tape⟩} ≤
        Set.encard ({candidate} :
          Set (DLBA.Cfg Γ (IncomingState Γ Λ) n)) := by
      apply Set.encard_le_encard
      intro predecessor hpredecessor
      simp only [Set.mem_singleton_iff]
      exact M.predecessor_base_eq hpredecessor
    _ = 1 := Set.encard_singleton candidate

/-- Incoming-edge serialization bounds the number of distinct predecessor configurations by two
at every tape width. -/
public theorem Machine.serializeIncoming_configurationIndegreeAtMostTwo
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    M.serializeIncoming.ConfigurationIndegreeAtMostTwo := by
  intro n cfg
  rcases cfg with ⟨state, tape⟩
  cases state with
  | base target =>
      let candidate :
          DLBA.Cfg Γ (IncomingState Γ Λ) n :=
        ⟨.merge target (lastIncomingIndex tape.read target), tape⟩
      calc
        Set.encard
            {cfg' | Step M.serializeIncoming cfg'
              ⟨.base target, tape⟩} ≤
            Set.encard ({candidate} :
              Set (DLBA.Cfg Γ (IncomingState Γ Λ) n)) := by
          apply Set.encard_le_encard
          intro predecessor hpredecessor
          simp only [Set.mem_singleton_iff]
          exact M.predecessor_base_eq hpredecessor
        _ ≤ 2 := by simp
  | written target tag =>
      let candidate :
          DLBA.Cfg Γ (IncomingState Γ Λ) n :=
        ⟨.base tag.source, tape.write tag.old⟩
      calc
        Set.encard
            {cfg' | Step M.serializeIncoming cfg'
              ⟨.written target tag, tape⟩} ≤
            Set.encard ({candidate} :
              Set (DLBA.Cfg Γ (IncomingState Γ Λ) n)) := by
          apply Set.encard_le_encard
          intro predecessor hpredecessor
          simp only [Set.mem_singleton_iff]
          exact M.predecessor_written_eq hpredecessor
        _ ≤ 2 := by simp
  | arrived target tag =>
      let first :
          DLBA.Cfg Γ (IncomingState Γ Λ) n :=
        ⟨.written target tag, tape⟩
      let second :
          DLBA.Cfg Γ (IncomingState Γ Λ) n :=
        ⟨.written target tag, tape.moveHead (oppositeDir tag.direction)⟩
      calc
        Set.encard
            {cfg' | Step M.serializeIncoming cfg'
              ⟨.arrived target tag, tape⟩} ≤
            Set.encard ({first, second} :
              Set (DLBA.Cfg Γ (IncomingState Γ Λ) n)) := by
          apply Set.encard_le_encard
          intro predecessor hpredecessor
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact M.predecessor_arrived_eq_or_eq hpredecessor
        _ ≤ 2 := by
          calc
            Set.encard ({first, second} :
                Set (DLBA.Cfg Γ (IncomingState Γ Λ) n)) ≤
                Set.encard ({second} :
                  Set (DLBA.Cfg Γ (IncomingState Γ Λ) n)) + 1 :=
              Set.encard_insert_le _ _
            _ = 2 := by
              rw [Set.encard_singleton]
              rfl
  | merge target index =>
      let first :
          DLBA.Cfg Γ (IncomingState Γ Λ) n :=
        ⟨.arrived target (incomingTagAt index), tape⟩
      let second :
          DLBA.Cfg Γ (IncomingState Γ Λ) n :=
        ⟨.merge target (previousIncomingIndex index), tape⟩
      calc
        Set.encard
            {cfg' | Step M.serializeIncoming cfg'
              ⟨.merge target index, tape⟩} ≤
            Set.encard ({first, second} :
              Set (DLBA.Cfg Γ (IncomingState Γ Λ) n)) := by
          apply Set.encard_le_encard
          intro predecessor hpredecessor
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact M.predecessor_merge_eq_or_eq hpredecessor
        _ ≤ 2 := by
          calc
            Set.encard ({first, second} :
                Set (DLBA.Cfg Γ (IncomingState Γ Λ) n)) ≤
                Set.encard ({second} :
                  Set (DLBA.Cfg Γ (IncomingState Γ Λ) n)) + 1 :=
              Set.encard_insert_le _ _
            _ = 2 := by
              rw [Set.encard_singleton]
              rfl

/-- Simultaneously serialize outgoing and incoming edges.  The binary outgoing serializer is
applied first, then incoming edges are split and merged. -/
public noncomputable def Machine.boundedDegree
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    Machine Γ (IncomingState Γ (BinaryBranchState Γ Λ)) :=
  M.binaryBranch.serializeIncoming

/-- The simultaneous serializer has both configuration-graph degrees at most two at every tape
width. -/
public theorem Machine.boundedDegree_configurationDegreeAtMostTwo
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    (M : Machine Γ Λ) :
    M.boundedDegree.ConfigurationDegreeAtMostTwo := by
  constructor
  · exact
      (M.binaryBranch.serializeIncoming).configurationOutdegreeAtMostTwo_of_binaryBranching
        (M.binaryBranch.serializeIncoming_binaryBranching
          M.binaryBranch_binaryBranching)
  · exact M.binaryBranch.serializeIncoming_configurationIndegreeAtMostTwo

/-- The simultaneous degree serializer preserves canonical endmarker languages. -/
public theorem Machine.languageEnd_boundedDegree_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} [Fintype T] [DecidableEq T]
    (M : Machine (EndAlpha T Γ) Λ) :
    LanguageEnd M.boundedDegree = LanguageEnd M := by
  exact
    M.binaryBranch.languageEnd_serializeIncoming_eq.trans
      M.languageEnd_binaryBranch_eq

/-- The simultaneous degree serializer preserves every marker-free embedded-input language. -/
public theorem Machine.languageViaEmbed_boundedDegree_eq
    [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]
    {T : Type*} (M : Machine Γ Λ) (embed : T → Γ) :
    LanguageViaEmbed M.boundedDegree embed = LanguageViaEmbed M embed := by
  exact
    (M.binaryBranch.languageViaEmbed_serializeIncoming_eq embed).trans
      (M.languageViaEmbed_binaryBranch_eq embed)

end LBA

/-- Languages recognized by canonical endmarker LBAs whose configuration graphs have both
indegree and outdegree at most two at every tape width. -/
public def is_BoundedDegreeLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (M : LBA.Machine (LBA.EndAlpha T Γ) Λ),
    M.ConfigurationDegreeAtMostTwo ∧ LBA.LanguageEnd M = L

/-- The class of languages recognized by uniformly degree-two LBAs. -/
public def BoundedDegreeLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    Set (Language T) :=
  setOf is_BoundedDegreeLBA

/-- Every finite LBA has an equivalent presentation, over the same tape alphabet and tape width,
whose configuration graph has both directed degrees at most two. -/
public theorem is_LBA_iff_is_BoundedDegreeLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) :
    is_LBA L ↔ is_BoundedDegreeLBA L := by
  constructor
  · rintro ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩
    letI := hΓ
    letI := hΛ
    letI := hdecΓ
    letI := hdecΛ
    refine ⟨Γ,
      LBA.IncomingState (LBA.EndAlpha T Γ)
        (LBA.BinaryBranchState (LBA.EndAlpha T Γ) Λ),
      hΓ, inferInstance, hdecΓ, inferInstance, M.boundedDegree,
      M.boundedDegree_configurationDegreeAtMostTwo, ?_⟩
    exact M.languageEnd_boundedDegree_eq.trans hM
  · rintro ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, _hdegree, hM⟩
    exact ⟨Γ, Λ, hΓ, hΛ, hdecΓ, hdecΛ, M, hM⟩

/-- Degree-two configuration graphs recognize exactly the full LBA language class. -/
public theorem BoundedDegreeLBA_eq_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (BoundedDegreeLBA : Set (Language T)) = LBA := by
  ext L
  exact (is_LBA_iff_is_BoundedDegreeLBA L).symm

/-- The first LBA problem is exactly the question whether all degree-two LBA languages are
deterministic. -/
public theorem lba_eq_dlba_iff_boundedDegreeLBA_subset
    {T : Type} [Fintype T] [DecidableEq T] :
    ((LBA : Set (Language T)) = DLBA) ↔
      ((BoundedDegreeLBA : Set (Language T)) ⊆ DLBA) := by
  rw [BoundedDegreeLBA_eq_LBA]
  constructor
  · intro heq
    rw [heq]
  · intro hsubset
    exact Set.Subset.antisymm hsubset DLBA_subset_LBA

end
