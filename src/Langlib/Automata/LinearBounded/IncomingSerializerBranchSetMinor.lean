module

public import Langlib.Automata.LinearBounded.BoundedDegree
public import Langlib.Automata.LinearBounded.BranchSetMinor
import Mathlib.Tactic

@[expose]
public section

/-!
# Branch-set minors through incoming-edge serialization

The incoming-degree serializer replaces each source edge by a write edge, a tagged movement,
and a target-side merge corridor.  This file contracts those concrete corridors.  The write
vertex belongs to the source branch set; the arrival vertex and its entire merge chain belong to
the target branch set.  Consequently the tagged movement is the one edge left between branch
sets.

The construction is global at every tape width, including clamped boundary moves and malformed
arrival or merge states.  A branch set contains only write states actually adjacent to its base
representative, while every arrival and merge state lies in the fiber selected by
`incomingProjectCfg`.  Thus malformed write states are simply unused and distinct source
configurations remain disjoint even when clamped moves share an arrival configuration.
-/

open Classical Relation

namespace LBA.IncomingSerializer

variable {Γ Λ : Type*}
variable [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

/-- The branch set representing an original configuration inside its incoming-edge serializer.

The projection equation makes the ownership of every included vertex explicit.  A written
configuration is included only when it is directly reached from the represented base
configuration; arrival and merge configurations need no validity condition because their raw
suffix always reaches that base configuration. -/
@[expose]
public def branchSet (M : Machine Γ Λ) {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) :
    Set (DLBA.Cfg Γ (IncomingState Γ Λ) n) :=
  {raw | incomingProjectCfg raw = cfg ∧
    match raw.state with
    | .base _ => True
    | .written _ _ => Step M.serializeIncoming (incomingLiftCfg cfg) raw
    | .arrived _ _ => True
    | .merge _ _ => True}

@[simp]
public theorem incomingLiftCfg_mem_branchSet
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    incomingLiftCfg cfg ∈ branchSet M cfg := by
  simp [branchSet, incomingLiftCfg, incomingProjectCfg]

omit [Fintype Γ] [DecidableEq Γ] in
private theorem write_read {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    tape.write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

omit [Fintype Γ] [DecidableEq Γ] in
private theorem write_write_read {n : ℕ} (tape : DLBA.BoundedTape Γ n)
    (written : Γ) :
    (tape.write written).write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

/-- Every arrival enters its canonical merge leaf. -/
private theorem step_arrived_merge
    (M : Machine Γ Λ) {n : ℕ} (target : Λ)
    (tag : IncomingTag Γ Λ) (tape : DLBA.BoundedTape Γ n) :
    Step M.serializeIncoming
      ⟨.arrived target tag, tape⟩
      ⟨.merge target (incomingIndex tag), tape⟩ := by
  refine ⟨.merge target (incomingIndex tag), tape.read, .stay, ?_, ?_⟩
  · simp [Machine.serializeIncoming]
  · rw [write_read]
    rfl

/-- A merge chain is connected to its target base configuration while staying inside the
target's branch set. -/
private theorem merge_connected_to_base
    (M : Machine Γ Λ) {n : ℕ} (target : Λ)
    (index : Fin (Fintype.card (IncomingTag Γ Λ)))
    (tape : DLBA.BoundedTape Γ n) :
    ReflTransGen
      (Restricted (branchSet M (⟨target, tape⟩ : DLBA.Cfg Γ Λ n))
        (SymmetricClosure (Step M.serializeIncoming)))
      ⟨.merge target index, tape⟩
      (incomingLiftCfg (⟨target, tape⟩ : DLBA.Cfg Γ Λ n)) := by
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
        have htail := ih
          (Fintype.card (IncomingTag Γ Λ) - 1 - next.val)
          hsmaller next rfl
        apply ReflTransGen.head _ htail
        refine ⟨?_, Or.inl ?_, ?_⟩
        · simp [branchSet, incomingProjectCfg]
        · refine ⟨.merge target next, tape.read, .stay, ?_, ?_⟩
          · simp [Machine.serializeIncoming, hnext, next]
          · rw [write_read]
            rfl
        · simp [branchSet, incomingProjectCfg]
      · apply ReflTransGen.single
        refine ⟨?_, Or.inl ?_, ?_⟩
        · simp [branchSet, incomingProjectCfg]
        · refine ⟨.base target, tape.read, .stay, ?_, ?_⟩
          · simp [Machine.serializeIncoming, hnext]
          · rw [write_read]
            rfl
        · simp [branchSet, incomingLiftCfg, incomingProjectCfg]

/-- Every branch-set representative is connected to the embedded original configuration. -/
private theorem connected_to_lift
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    {raw : DLBA.Cfg Γ (IncomingState Γ Λ) n}
    (hraw : raw ∈ branchSet M cfg) :
    ReflTransGen
      (Restricted (branchSet M cfg)
        (SymmetricClosure (Step M.serializeIncoming)))
      raw (incomingLiftCfg cfg) := by
  rcases raw with ⟨state, tape⟩
  rcases hraw with ⟨hproject, hphase⟩
  cases state with
  | base state =>
      have hrawEq :
          (⟨.base state, tape⟩ : DLBA.Cfg Γ (IncomingState Γ Λ) n) =
            incomingLiftCfg cfg := by
        rcases cfg with ⟨cfgState, cfgTape⟩
        simp [incomingProjectCfg, incomingLiftCfg] at hproject ⊢
        exact hproject
      rw [hrawEq]
  | written target tag =>
      apply ReflTransGen.single
      exact ⟨⟨hproject, hphase⟩, Or.inr hphase,
        incomingLiftCfg_mem_branchSet M cfg⟩
  | arrived target tag =>
      have hcfg : cfg = (⟨target, tape⟩ : DLBA.Cfg Γ Λ n) := by
        simpa [incomingProjectCfg] using hproject.symm
      subst cfg
      apply ReflTransGen.head
      · refine ⟨?_, Or.inl (step_arrived_merge M target tag tape), ?_⟩
        · simp [branchSet, incomingProjectCfg]
        · simp [branchSet, incomingProjectCfg]
      · exact merge_connected_to_base M target (incomingIndex tag) tape
  | merge target index =>
      have hcfg : cfg = (⟨target, tape⟩ : DLBA.Cfg Γ Λ n) := by
        simpa [incomingProjectCfg] using hproject.symm
      subst cfg
      exact merge_connected_to_base M target index tape

/-- Distinct original configurations have disjoint incoming-serializer branch sets. -/
public theorem branchSet_disjoint
    (M : Machine Γ Λ) {n : ℕ}
    {left right : DLBA.Cfg Γ Λ n} (hne : left ≠ right) :
    Disjoint (branchSet M left) (branchSet M right) := by
  rw [Set.disjoint_left]
  intro raw hleft hright
  exact hne (hleft.1.symm.trans hright.1)

/-- Each incoming-serializer branch set is connected in the underlying undirected raw
configuration graph. -/
public theorem branchSet_connected
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n)
    {source target : DLBA.Cfg Γ (IncomingState Γ Λ) n}
    (hsource : source ∈ branchSet M cfg)
    (htarget : target ∈ branchSet M cfg) :
    ReflTransGen
      (Restricted (branchSet M cfg)
        (SymmetricClosure (Step M.serializeIncoming)))
      source target := by
  have hsourcePath := connected_to_lift M cfg hsource
  have htargetPath := connected_to_lift M cfg htarget
  have hsymm : Symmetric
      (Restricted (branchSet M cfg)
        (SymmetricClosure (Step M.serializeIncoming))) := by
    intro left right hstep
    exact ⟨hstep.2.2, hstep.2.1.elim Or.inr Or.inl, hstep.1⟩
  exact hsourcePath.trans (htargetPath.symmetric hsymm)

/-- One original transition leaves a canonical tagged movement edge between its source and
target branch sets. -/
private theorem edge_witness_of_step
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg Γ Λ n} (hstep : Step M source target) :
    ∃ sourceRep ∈ branchSet M source,
      ∃ targetRep ∈ branchSet M target,
        Step M.serializeIncoming sourceRep targetRep := by
  rcases hstep with ⟨targetState, written, direction, henabled, rfl⟩
  let tag : IncomingTag Γ Λ :=
    { source := source.state
      old := source.tape.read
      written := written
      direction := direction }
  let sourceRep : DLBA.Cfg Γ (IncomingState Γ Λ) n :=
    ⟨.written targetState tag, source.tape.write written⟩
  let targetRep : DLBA.Cfg Γ (IncomingState Γ Λ) n :=
    ⟨.arrived targetState tag,
      (source.tape.write written).moveHead direction⟩
  have hbaseWritten :
      Step M.serializeIncoming (incomingLiftCfg source) sourceRep := by
    refine ⟨.written targetState tag, written, .stay, ?_, ?_⟩
    · exact ⟨(targetState, written, direction), henabled, rfl⟩
    · simp [sourceRep, tag, incomingLiftCfg, DLBA.BoundedTape.moveHead]
  have hwrittenArrived : Step M.serializeIncoming sourceRep targetRep := by
    refine ⟨.arrived targetState tag, written, direction, ?_, ?_⟩
    · simp only [Machine.serializeIncoming]
      have henabled' :
          (targetState, written, direction) ∈
            M.transition source.state
              (source.tape.contents source.tape.head) := by
        simpa only [DLBA.BoundedTape.read] using henabled
      simpa [sourceRep, tag, DLBA.BoundedTape.write] using henabled'
    · simp [sourceRep, targetRep, tag, DLBA.BoundedTape.write]
  refine ⟨sourceRep, ?_, targetRep, ?_, hwrittenArrived⟩
  · exact ⟨by
      change
        (⟨source.state,
          (source.tape.write written).write source.tape.read⟩ :
            DLBA.Cfg Γ Λ n) = source
      exact congrArg (fun tape => (⟨source.state, tape⟩ : DLBA.Cfg Γ Λ n))
        (write_write_read source.tape written),
      hbaseWritten⟩
  · simp [branchSet, targetRep, incomingProjectCfg]

/-- **Incoming-serializer corridor theorem.**  At every tape width, the symmetrized original
configuration relation is a branch-set minor of the raw configuration graph of the concrete
incoming-degree serializer. -/
public def branchSetMinorModel
    (M : Machine Γ Λ) {n : ℕ} :
    BranchSetMinorModel
      (SymmetricClosure (Step (n := n) M))
      (Step (n := n) M.serializeIncoming) where
  branchSet := branchSet M
  nonempty cfg := ⟨incomingLiftCfg cfg, incomingLiftCfg_mem_branchSet M cfg⟩
  disjoint hne := branchSet_disjoint M hne
  connected cfg {source target} hsource htarget :=
    branchSet_connected M cfg hsource htarget
  map_edge {source target} hedge := by
    rcases hedge with hforward | hbackward
    · rcases edge_witness_of_step M hforward with
        ⟨sourceRep, hsource, targetRep, htarget, hraw⟩
      exact ⟨sourceRep, hsource, targetRep, htarget, Or.inl hraw⟩
    · rcases edge_witness_of_step M hbackward with
        ⟨targetRep, htarget, sourceRep, hsource, hraw⟩
      exact ⟨sourceRep, hsource, targetRep, htarget, Or.inr hraw⟩

end LBA.IncomingSerializer

end
