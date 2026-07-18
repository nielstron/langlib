module

public import Langlib.Automata.LinearBounded.AcyclicClock.CrossingMacro
public import Langlib.Automata.LinearBounded.BoundedDegreeTrace
public import Langlib.Automata.LinearBounded.AcyclicClock.AcyclicityReduction
public import Langlib.Automata.LinearBounded.AcyclicBoundedDegree
import Mathlib.Tactic

@[expose]
public section

/-!
# A fixed clock run from a deterministic source with exponentially many boundary crossings

Every self-loop of a source machine can be repeated through all exact semantic clock layers.
When the source head is at cell zero, each operational clock macro crosses every physical tape
boundary.  Concatenating the macros therefore gives one concrete bottom-to-top run with one
crossing per boundary for each successive layer advance.  The first section proves this uniformly
for arbitrary finite input/work alphabets, state types, machines over the canonical source
alphabet, and tape widths.

The second section instantiates the result with a one-state deterministic identity machine over
`AcyclicClock.SourceAlpha Unit Bool`.  Its width-`n` configuration space has exactly
`6 ^ (n + 1) * (n + 1)` elements.  The same single clocked-and-degree-serialized machine thus has
an actual width-`n` run crossing every boundary at least that many times, while its complete raw
configuration graph is globally acyclic, has both directed degrees at most two, and has the
serializer's width-uniform two-partial-bijection partition.

This is a structural witness run from a deliberately self-looping deterministic source.  It is
not a claim that acceptance or rejection forces an arbitrary computation to make these
crossings, and hence is not a language lower bound or a determinization theorem.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ] [Nonempty Λ]

/-! ## Iterating an arbitrary self-loop through the complete semantic clock -/

/-- Repeat a source self-loop through the first `k` exact semantic layers and retain one
concrete operational trace.  Each macro crosses every physical boundary because the represented
source head remains at cell zero.

The incoming Ready trails are arbitrary and the outgoing trails are existential.  In
particular, the statement is valid at `n = 0`: it still supplies a genuine operational trace,
while its boundary-indexed numerical conclusion is vacuous because `Fin 0` is empty. -/
public theorem exists_selfLoop_stepTrace_to_semanticLayer_crosses
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (hself : LBA.Step M cfg cfg)
    (hhead : cfg.tape.head.val = 0)
    (k : ℕ)
    (hk : k ≤ Fintype.card (DLBA.Cfg (SourceAlpha T Γ) Λ n))
    (trails : ReadyTrails n) :
    ∃ (trails' : ReadyTrails n)
      (trace : LBA.StepTrace (machine M)
        (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ) n
          (LBA.StrictClockLayering.bottom cfg) trails)
        (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ) n
          (LBA.StrictClockLayering.atLayer cfg k hk) trails')),
      ∀ b : Fin n, k ≤ LBA.StepTrace.crossingCount b trace := by
  induction k generalizing trails with
  | zero =>
      refine ⟨trails, ?_, ?_⟩
      · simpa [LBA.StrictClockLayering.bottom,
          LBA.StrictClockLayering.atLayer, LayeredReachability.bottom,
          LayeredReachability.atLayer] using
          (LBA.StepTrace.refl
            (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ) n
              (LBA.StrictClockLayering.bottom cfg) trails) :
            LBA.StepTrace (machine M) _ _)
      · intro b
        exact Nat.zero_le _
  | succ k ih =>
      have hk' : k ≤ Fintype.card (DLBA.Cfg (SourceAlpha T Γ) Λ n) := by
        omega
      obtain ⟨middleTrails, first, hfirst⟩ := ih hk' trails
      let old := LBA.StrictClockLayering.atLayer cfg k hk'
      let new := LBA.StrictClockLayering.atLayer cfg (k + 1) hk
      have hclock : LBA.StrictClockLayering.ClockedStep M old new := by
        refine ⟨?_, ?_⟩
        · rfl
        · exact hself
      obtain ⟨finalTrails, last, hlast⟩ :=
        exists_semanticCheckpoint_stepTrace_crosses_every_boundary
          M hclock middleTrails hhead
      refine ⟨finalTrails, LBA.StepTrace.append first last, ?_⟩
      intro b
      rw [LBA.StepTrace.crossingCount_append]
      have hfirst' := hfirst b
      have hlast' := hlast b
      omega

/-- Full-clock specialization of `exists_selfLoop_stepTrace_to_semanticLayer_crosses`.
There are exactly as many operational macros as source configurations: the trace starts at
semantic layer zero and ends at layer `|Cfg|`. -/
public theorem exists_selfLoop_fullClock_stepTrace_crosses
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (hself : LBA.Step M cfg cfg)
    (hhead : cfg.tape.head.val = 0)
    (trails : ReadyTrails n) :
    ∃ (trails' : ReadyTrails n)
      (trace : LBA.StepTrace (machine M)
        (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ) n
          (LBA.StrictClockLayering.bottom cfg) trails)
        (semanticCheckpointCfg (T := T) (Γ := Γ) (Λ := Λ) n
          (LBA.StrictClockLayering.atLayer cfg
            (Fintype.card (DLBA.Cfg (SourceAlpha T Γ) Λ n))
            (Nat.le_refl _)) trails')),
      ∀ b : Fin n,
        Fintype.card (DLBA.Cfg (SourceAlpha T Γ) Λ n) ≤
          LBA.StepTrace.crossingCount b trace := by
  exact exists_selfLoop_stepTrace_to_semanticLayer_crosses
    M cfg hself hhead _ (Nat.le_refl _) trails

/-! ## The fixed one-state identity witness -/

namespace IdentityCrossing

/-- A one-state source machine that writes back the symbol it reads and stays in place.
Its complete step relation is the identity relation, so this is a deterministic source in the
strongest possible sense. -/
public def identitySource :
    LBA.Machine (SourceAlpha Unit Bool) Unit where
  transition _ symbol := {((), symbol, .stay)}
  accept _ := false
  initial := ()

/-- The identity source takes a self-step at every complete fixed-width configuration. -/
public theorem identitySource_step_self {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha Unit Bool) Unit n) :
    LBA.Step identitySource cfg cfg := by
  refine ⟨(), cfg.tape.read, .stay, ?_, ?_⟩
  · simp [identitySource]
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

/-- Conversely, the identity source has no step other than the self-step. -/
public theorem identitySource_step_iff {n : ℕ}
    {source target : DLBA.Cfg (SourceAlpha Unit Bool) Unit n} :
    LBA.Step identitySource source target ↔ target = source := by
  constructor
  · rintro ⟨next, written, direction, henabled, rfl⟩
    simp only [identitySource, Set.mem_singleton_iff] at henabled
    rcases henabled with ⟨rfl, rfl, rfl⟩
    simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
  · rintro rfl
    exact identitySource_step_self _

/-- The complete fixed-width step relation of the source is right-unique. -/
public theorem identitySource_step_rightUnique (n : ℕ) :
    Relator.RightUnique
      (LBA.Step (n := n) identitySource) := by
  intro source left right hleft hright
  rw [identitySource_step_iff] at hleft hright
  exact hleft.trans hright.symm

/-- A canonical width-`n` source tape filled with the left-endmarker symbol and with its head at
physical cell zero.  The contents are immaterial to the identity transition; choosing a fixed
row makes the witness explicit at every width, including `n = 0`. -/
public def identityTape (n : ℕ) :
    DLBA.BoundedTape (SourceAlpha Unit Bool) n :=
  ⟨fun _ ↦ LBA.leftMark, ⟨0, Nat.zero_lt_succ n⟩⟩

/-- The canonical fixed-width source configuration used by the crossing witness. -/
public def identityCfg (n : ℕ) :
    DLBA.Cfg (SourceAlpha Unit Bool) Unit n :=
  ⟨(), identityTape n⟩

@[simp]
public theorem identityCfg_head (n : ℕ) :
    (identityCfg n).tape.head.val = 0 := rfl

/-- The canonical identity configuration has the required source self-loop. -/
public theorem identityCfg_step_self (n : ℕ) :
    LBA.Step identitySource (identityCfg n) (identityCfg n) :=
  identitySource_step_self _

/-- The canonical source alphabet has exactly six symbols: blank, one input symbol, two work
symbols, and two endmarkers. -/
public theorem card_sourceAlpha_unit_bool :
    Fintype.card (SourceAlpha Unit Bool) = 6 := by
  simp [SourceAlpha, LBA.EndAlpha]

/-- Exact number of width-`n` configurations of the one-state identity source. -/
public theorem card_identityCfgSpace (n : ℕ) :
    Fintype.card (DLBA.Cfg (SourceAlpha Unit Bool) Unit n) =
      6 ^ (n + 1) * (n + 1) := by
  rw [DLBA.card_cfg, card_sourceAlpha_unit_bool]
  simp

/-- The one fixed target machine used in every width: first compile the deterministic identity
source with the concrete acyclic clock, then apply both directed-degree serializers. -/
public noncomputable def finalMachine :=
  (machine identitySource).boundedDegree

/-- A complete bottom-to-top trace of the operational clock before degree serialization.  It
performs exactly `|Cfg|` macros, advancing through the `|Cfg| + 1` semantic layers, and crosses
each physical boundary at least once per macro. -/
public theorem exists_identity_fullClock_stepTrace_crosses (n : ℕ) :
    ∃ (trails : ReadyTrails n)
      (trace : LBA.StepTrace (machine identitySource)
        (canonicalCfg identitySource (identityCfg n))
        (semanticCheckpointCfg (T := Unit) (Γ := Bool) (Λ := Unit) n
          (LBA.StrictClockLayering.atLayer (identityCfg n)
            (Fintype.card
              (DLBA.Cfg (SourceAlpha Unit Bool) Unit n))
            (Nat.le_refl _)) trails)),
      ∀ b : Fin n,
        Fintype.card (DLBA.Cfg (SourceAlpha Unit Bool) Unit n) ≤
          LBA.StepTrace.crossingCount b trace := by
  have h :=
    exists_selfLoop_fullClock_stepTrace_crosses
      identitySource (identityCfg n) (identityCfg_step_self n)
        (identityCfg_head n) (ReadyTrails.clear n)
  rw [semanticCheckpointCfg_bottom_clear identitySource (identityCfg n)] at h
  exact h

/-- Lift the complete clock trace through both actual degree serializers.  The endpoints are the
canonical serializer lifts of the exact same operational checkpoints, and no source crossing is
lost. -/
public theorem exists_finalMachine_stepTrace_crosses_card (n : ℕ) :
    ∃ (trails : ReadyTrails n)
      (trace : LBA.StepTrace finalMachine
        (LBA.boundedDegreeLiftCfg
          (canonicalCfg identitySource (identityCfg n)))
        (LBA.boundedDegreeLiftCfg
          (semanticCheckpointCfg (T := Unit) (Γ := Bool) (Λ := Unit) n
            (LBA.StrictClockLayering.atLayer (identityCfg n)
              (Fintype.card
                (DLBA.Cfg (SourceAlpha Unit Bool) Unit n))
              (Nat.le_refl _)) trails))),
      ∀ b : Fin n,
        Fintype.card (DLBA.Cfg (SourceAlpha Unit Bool) Unit n) ≤
          LBA.StepTrace.crossingCount b trace := by
  obtain ⟨trails, sourceTrace, hsource⟩ :=
    exists_identity_fullClock_stepTrace_crosses n
  let trace := (machine identitySource).boundedDegreeLiftTrace sourceTrace
  refine ⟨trails, trace, ?_⟩
  intro b
  exact (hsource b).trans
    ((machine identitySource).crossingCount_le_boundedDegreeLiftTrace b sourceTrace)

/-- Exact closed-form crossing lower bound for the fixed final machine. -/
public theorem exists_finalMachine_stepTrace_crosses_exact (n : ℕ) :
    ∃ (trails : ReadyTrails n)
      (trace : LBA.StepTrace finalMachine
        (LBA.boundedDegreeLiftCfg
          (canonicalCfg identitySource (identityCfg n)))
        (LBA.boundedDegreeLiftCfg
          (semanticCheckpointCfg (T := Unit) (Γ := Bool) (Λ := Unit) n
            (LBA.StrictClockLayering.atLayer (identityCfg n)
              (Fintype.card
                (DLBA.Cfg (SourceAlpha Unit Bool) Unit n))
              (Nat.le_refl _)) trails))),
      ∀ b : Fin n,
        6 ^ (n + 1) * (n + 1) ≤
          LBA.StepTrace.crossingCount b trace := by
  simpa only [card_identityCfgSpace] using
    exists_finalMachine_stepTrace_crosses_card n

/-- In particular, the fixed final machine has a width-`n` run crossing every boundary at least
`2 ^ (n + 1)` times.  The statement is uniform at `n = 0`; the trace still exists there and the
quantification over physical boundaries is vacuous. -/
public theorem exists_finalMachine_stepTrace_crosses_twoPow (n : ℕ) :
    ∃ (trails : ReadyTrails n)
      (trace : LBA.StepTrace finalMachine
        (LBA.boundedDegreeLiftCfg
          (canonicalCfg identitySource (identityCfg n)))
        (LBA.boundedDegreeLiftCfg
          (semanticCheckpointCfg (T := Unit) (Γ := Bool) (Λ := Unit) n
            (LBA.StrictClockLayering.atLayer (identityCfg n)
              (Fintype.card
                (DLBA.Cfg (SourceAlpha Unit Bool) Unit n))
              (Nat.le_refl _)) trails))),
      ∀ b : Fin n,
        2 ^ (n + 1) ≤ LBA.StepTrace.crossingCount b trace := by
  obtain ⟨trails, trace, hcross⟩ :=
    exists_finalMachine_stepTrace_crosses_exact n
  refine ⟨trails, trace, ?_⟩
  intro b
  apply le_trans ?_ (hcross b)
  calc
    2 ^ (n + 1) ≤ 6 ^ (n + 1) :=
      Nat.pow_le_pow_left (by omega) (n + 1)
    _ ≤ 6 ^ (n + 1) * (n + 1) := by
      nth_rewrite 1 [← Nat.mul_one (6 ^ (n + 1))]
      exact Nat.mul_le_mul_left _ (by omega)

/-! ## Global promises of the exact same final machine -/

/-- The complete raw configuration graph of `finalMachine` is acyclic at every tape width,
including malformed clock and serializer configurations unrelated to the displayed run. -/
public theorem finalMachine_configurationAcyclic :
    finalMachine.ConfigurationAcyclic := by
  apply LBA.AcyclicBoundedDegree.configurationAcyclic_boundedDegree
  exact machine_configurationAcyclic identitySource

/-- Every complete raw fixed-width configuration graph of `finalMachine` has both directed
degrees at most two. -/
public theorem finalMachine_configurationDegreeAtMostTwo :
    finalMachine.ConfigurationDegreeAtMostTwo :=
  LBA.Machine.boundedDegree_configurationDegreeAtMostTwo
    (machine identitySource)

/-- One syntactically defined family of two partial-bijection edge layers partitions the raw
step relation of `finalMachine`, uniformly over all tape widths. -/
public theorem finalMachine_hasTwoBiUniqueStepPartition :
    finalMachine.HasTwoBiUniqueStepPartition :=
  LBA.Machine.boundedDegree_hasTwoBiUniqueStepPartition
    (machine identitySource)

/-- Package the three global graph promises enjoyed by the very same fixed machine whose
bottom-to-top trace has the exponential crossing lower bound. -/
public theorem finalMachine_globalProperties :
    finalMachine.ConfigurationAcyclic ∧
      finalMachine.ConfigurationDegreeAtMostTwo ∧
      finalMachine.HasTwoBiUniqueStepPartition :=
  ⟨finalMachine_configurationAcyclic,
    finalMachine_configurationDegreeAtMostTwo,
    finalMachine_hasTwoBiUniqueStepPartition⟩

end IdentityCrossing

end LBA.AcyclicClock

end
