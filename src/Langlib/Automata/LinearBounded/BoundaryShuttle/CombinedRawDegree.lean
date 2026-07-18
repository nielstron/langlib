module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.CombinedCanonical
public import Langlib.Automata.LinearBounded.BoundaryShuttle.RawDegree
import Mathlib.Tactic

@[expose]
public section

/-!
# Raw predecessor bounds for the combined shuttle

The three moving protocol landings have the two unavoidable clamped inverse-head candidates.
The stationary pending landing has a unique predecessor.  A shared normal landing has a unique
predecessor only after three explicit hypotheses:

* `DirectionalTargetInjective` for two directional finishes;
* `StationaryTargetWrittenInjective` for two stationary finishes;
* `ShuttleTargetKindDisjoint` for a directional/stationary pair.

The last condition cannot be replaced by written-symbol separation on malformed tapes: the final
directional edge restores an arbitrary neighbour symbol.  All results quantify over every tape
width, including zero and one.
-/

namespace LBA

open Classical

variable {Γ Λ : Type*}

private theorem combined_write_write_read {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (written : A) :
    (tape.write written).write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

/-! ## Directional tagged phases -/

public theorem Machine.predecessor_combinedShuttle_directionalAtNeighbour_eq_or_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ}
    {tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n}
    (hstep : Step M.combinedBoundaryShuttle predecessor
      ⟨.directionalAtNeighbour move, tape⟩) :
    predecessor = ⟨.normal move.source, tape.write (.plain move.old)⟩ ∨
      predecessor = ⟨.normal move.source,
        (tape.moveHead (reverseDirection move.direction)).write (.plain move.old)⟩ := by
  rw [M.step_combinedBoundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩
  · simp only [DLBA.Cfg.mk.injEq,
      CombinedShuttleState.directionalAtNeighbour.injEq] at htarget
    rcases htarget with ⟨hmove, htape⟩
    subst sourceMove
    have hcandidates := tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (.plain move.old) (.directionalDeparture move) move.direction
      hread htape.symm
    rcases hcandidates with htapeSource | htapeSource
    · left
      rw [hsource, htapeSource]
    · right
      rw [hsource, htapeSource]
  all_goals simp at htarget

public theorem Machine.predecessor_combinedShuttle_directionalAtDeparture_eq_or_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ} {neighbour : Γ}
    {tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n}
    (hstep : Step M.combinedBoundaryShuttle predecessor
      ⟨.directionalAtDeparture move neighbour, tape⟩) :
    predecessor = ⟨.directionalAtNeighbour move, tape.write (.plain neighbour)⟩ ∨
      predecessor = ⟨.directionalAtNeighbour move,
        (tape.moveHead move.direction).write (.plain neighbour)⟩ := by
  rw [M.step_combinedBoundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩
  · simp at htarget
  · simp only [DLBA.Cfg.mk.injEq,
      CombinedShuttleState.directionalAtDeparture.injEq] at htarget
    rcases htarget with ⟨hstate, htape⟩
    rcases hstate with ⟨hmove, hneighbour⟩
    subst sourceMove
    subst sourceNeighbour
    have hcandidates := tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (.plain neighbour) (.directionalNeighbour move neighbour)
        (reverseDirection move.direction) hread htape.symm
    rw [reverseDirection_reverseDirection] at hcandidates
    rcases hcandidates with htapeSource | htapeSource
    · left
      rw [hsource, htapeSource]
    · right
      rw [hsource, htapeSource]
  all_goals simp at htarget

public theorem Machine.predecessor_combinedShuttle_directionalRestoreNeighbour_eq_or_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ} {neighbour : Γ}
    {tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n}
    (hstep : Step M.combinedBoundaryShuttle predecessor
      ⟨.directionalRestoreNeighbour move neighbour, tape⟩) :
    predecessor = ⟨.directionalAtDeparture move neighbour,
        tape.write (.directionalDeparture move)⟩ ∨
      predecessor = ⟨.directionalAtDeparture move neighbour,
        (tape.moveHead (reverseDirection move.direction)).write
          (.directionalDeparture move)⟩ := by
  rw [M.step_combinedBoundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩
  · simp at htarget
  · simp at htarget
  · simp only [DLBA.Cfg.mk.injEq,
      CombinedShuttleState.directionalRestoreNeighbour.injEq] at htarget
    rcases htarget with ⟨hstate, htape⟩
    rcases hstate with ⟨hmove, hneighbour⟩
    subst sourceMove
    subst sourceNeighbour
    have hcandidates := tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (.directionalDeparture move) (.plain move.written)
        move.direction hread htape.symm
    rcases hcandidates with htapeSource | htapeSource
    · left
      rw [hsource, htapeSource]
    · right
      rw [hsource, htapeSource]
  all_goals simp at htarget

/-! ## Stationary pending phase -/

public theorem Machine.predecessor_combinedShuttle_stationaryPending_eq
    (M : Machine Γ Λ) {n : ℕ}
    {left right :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ}
    {tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n}
    (hleft : Step M.combinedBoundaryShuttle left ⟨.stationaryPending move, tape⟩)
    (hright : Step M.combinedBoundaryShuttle right ⟨.stationaryPending move, tape⟩) :
    left = right := by
  rw [M.step_combinedBoundaryShuttle_iff] at hleft hright
  rcases hleft with
      ⟨leftMove, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftNeighbour, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftNeighbour, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftNeighbour, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩
  all_goals try simp at hleftTarget
  rcases hright with
      ⟨rightMove, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightNeighbour, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightNeighbour, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightNeighbour, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩
  all_goals try simp at hrightTarget
  rcases hleftTarget with ⟨hleftMove, hleftTape⟩
  rcases hrightTarget with ⟨hrightMove, hrightTape⟩
  subst leftMove
  subst rightMove
  have hleftRestore : leftTape = tape.write (.plain move.old) := by
    rw [hleftTape]
    rw [← hleftRead]
    exact (combined_write_write_read leftTape (.stationarySaved move)).symm
  have hrightRestore : rightTape = tape.write (.plain move.old) := by
    rw [hrightTape]
    rw [← hrightRead]
    exact (combined_write_write_read rightTape (.stationarySaved move)).symm
  rw [hleftSource, hrightSource, hleftRestore, hrightRestore]

/-! ## Shared normal phase and explicit cross-kind inversion -/

/-- A raw edge into a shared normal configuration is exactly a directional finish or a
stationary finish. -/
public theorem Machine.step_combinedBoundaryShuttle_to_normal_iff
    (M : Machine Γ Λ) {n : ℕ}
    (source : DLBA.Cfg
      (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n)
    (target : Λ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n) :
    Step M.combinedBoundaryShuttle source ⟨.normal target, tape⟩ ↔
      (∃ (move : ShuttleMove Γ Λ) (neighbour : Γ)
          (sourceTape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n),
        M.ShuttleDirectionalEnabled move ∧
        sourceTape.read = .directionalNeighbour move neighbour ∧
        source = ⟨.directionalRestoreNeighbour move neighbour, sourceTape⟩ ∧
        move.target = target ∧ sourceTape.write (.plain neighbour) = tape) ∨
      (∃ (move : ShuttleMove Γ Λ)
          (sourceTape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n),
        M.ShuttleStationaryEnabled move ∧
        sourceTape.read = .stationarySaved move ∧
        source = ⟨.stationaryPending move, sourceTape⟩ ∧
        move.target = target ∧ sourceTape.write (.plain move.written) = tape) := by
  rw [M.step_combinedBoundaryShuttle_iff]
  constructor
  · rintro (⟨move, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨move, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨move, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨move, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨move, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨move, sourceTape, henabled, hread, hsource, htarget⟩)
    all_goals try simp at htarget
    · rcases htarget with ⟨hstate, htape⟩
      exact Or.inl ⟨move, neighbour, sourceTape, henabled, hread, hsource,
        hstate.symm, htape.symm⟩
    · rcases htarget with ⟨hstate, htape⟩
      exact Or.inr ⟨move, sourceTape, henabled, hread, hsource,
        hstate.symm, htape.symm⟩
  · rintro (⟨move, neighbour, sourceTape, henabled, hread, rfl, htarget, htape⟩ |
      ⟨move, sourceTape, henabled, hread, rfl, htarget, htape⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨move, neighbour, sourceTape, henabled, hread, rfl,
          by simp [htarget, htape]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨move, sourceTape, henabled, hread, rfl,
          by simp [htarget, htape]⟩))))

/-- Under the three kind-specific hypotheses, a shared normal landing has exactly one raw
predecessor.  The proof exposes all four same/cross-kind combinations. -/
public theorem Machine.predecessor_combinedShuttle_normal_eq
    (M : Machine Γ Λ)
    (hdirectional : M.DirectionalTargetInjective)
    (hstationary : M.StationaryTargetWrittenInjective)
    (hkind : M.ShuttleTargetKindDisjoint)
    {n : ℕ}
    {left right :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    {target : Λ}
    {tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n}
    (hleft : Step M.combinedBoundaryShuttle left ⟨.normal target, tape⟩)
    (hright : Step M.combinedBoundaryShuttle right ⟨.normal target, tape⟩) :
    left = right := by
  rw [M.step_combinedBoundaryShuttle_to_normal_iff left target tape] at hleft
  rw [M.step_combinedBoundaryShuttle_to_normal_iff right target tape] at hright
  rcases hleft with
      ⟨leftMove, leftNeighbour, leftTape, hleftEnabled, hleftRead,
        hleftSource, hleftTarget, hleftTape⟩ |
      ⟨leftMove, leftTape, hleftEnabled, hleftRead,
        hleftSource, hleftTarget, hleftTape⟩
  · rcases hright with
      ⟨rightMove, rightNeighbour, rightTape, hrightEnabled, hrightRead,
        hrightSource, hrightTarget, hrightTape⟩ |
      ⟨rightMove, rightTape, hrightEnabled, hrightRead,
        hrightSource, hrightTarget, hrightTape⟩
    · have hmove : leftMove = rightMove :=
        hdirectional leftMove rightMove hleftEnabled hrightEnabled
          (hleftTarget.trans hrightTarget.symm)
      subst rightMove
      have hneighbour : leftNeighbour = rightNeighbour := by
        have hleftVisible : tape.read = .plain leftNeighbour := by
          rw [← hleftTape]
          simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
        have hrightVisible : tape.read = .plain rightNeighbour := by
          rw [← hrightTape]
          simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
        rw [hleftVisible] at hrightVisible
        exact CombinedShuttleAlphabet.plain.inj hrightVisible
      subst rightNeighbour
      have hleftRestore :
          leftTape = tape.write (.directionalNeighbour leftMove leftNeighbour) := by
        rw [← hleftTape]
        rw [← hleftRead]
        exact (combined_write_write_read leftTape (.plain leftNeighbour)).symm
      have hrightRestore :
          rightTape = tape.write (.directionalNeighbour leftMove leftNeighbour) := by
        rw [← hrightTape]
        rw [← hrightRead]
        exact (combined_write_write_read rightTape (.plain leftNeighbour)).symm
      rw [hleftSource, hrightSource, hleftRestore, hrightRestore]
    · exact False.elim
        (hkind leftMove rightMove hleftEnabled hrightEnabled
          (hleftTarget.trans hrightTarget.symm))
  · rcases hright with
      ⟨rightMove, rightNeighbour, rightTape, hrightEnabled, hrightRead,
        hrightSource, hrightTarget, hrightTape⟩ |
      ⟨rightMove, rightTape, hrightEnabled, hrightRead,
        hrightSource, hrightTarget, hrightTape⟩
    · exact False.elim
        (hkind rightMove leftMove hrightEnabled hleftEnabled
          (hrightTarget.trans hleftTarget.symm))
    · have hleftVisible : tape.read = .plain leftMove.written := by
        rw [← hleftTape]
        simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
      have hrightVisible : tape.read = .plain rightMove.written := by
        rw [← hrightTape]
        simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
      have hwritten : leftMove.written = rightMove.written := by
        rw [hleftVisible] at hrightVisible
        exact CombinedShuttleAlphabet.plain.inj hrightVisible
      have hmove : leftMove = rightMove :=
        hstationary leftMove rightMove hleftEnabled hrightEnabled
          (hleftTarget.trans hrightTarget.symm) hwritten
      subst rightMove
      have hleftRestore : leftTape = tape.write (.stationarySaved leftMove) := by
        rw [← hleftTape]
        rw [← hleftRead]
        exact (combined_write_write_read leftTape (.plain leftMove.written)).symm
      have hrightRestore : rightTape = tape.write (.stationarySaved leftMove) := by
        rw [← hrightTape]
        rw [← hrightRead]
        exact (combined_write_write_read rightTape (.plain leftMove.written)).symm
      rw [hleftSource, hrightSource, hleftRestore, hrightRestore]

/-! ## Uniform cardinal bounds -/

public theorem Machine.combinedBoundaryShuttle_configurationIndegreeAtMostTwo
    (M : Machine Γ Λ)
    (hdirectional : M.DirectionalTargetInjective)
    (hstationary : M.StationaryTargetWrittenInjective)
    (hkind : M.ShuttleTargetKindDisjoint) :
    M.combinedBoundaryShuttle.ConfigurationIndegreeAtMostTwo := by
  intro n target
  rcases target with ⟨state, tape⟩
  cases state with
  | normal target =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      exact M.predecessor_combinedShuttle_normal_eq
        hdirectional hstationary hkind hleft hright
  | directionalAtNeighbour move =>
      let first : DLBA.Cfg
          (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
        ⟨.normal move.source, tape.write (.plain move.old)⟩
      let second : DLBA.Cfg
          (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
        ⟨.normal move.source,
          (tape.moveHead (reverseDirection move.direction)).write (.plain move.old)⟩
      calc
        Set.encard {cfg | Step M.combinedBoundaryShuttle cfg
            ⟨.directionalAtNeighbour move, tape⟩} ≤
            Set.encard ({first, second} : Set _) := by
          apply Set.encard_le_encard
          intro cfg hcfg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact M.predecessor_combinedShuttle_directionalAtNeighbour_eq_or_eq hcfg
        _ ≤ 2 := by
          calc
            Set.encard ({first, second} : Set _) ≤
                Set.encard ({second} : Set _) + 1 := Set.encard_insert_le _ _
            _ = 2 := by rw [Set.encard_singleton]; rfl
  | directionalAtDeparture move neighbour =>
      let first : DLBA.Cfg
          (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
        ⟨.directionalAtNeighbour move, tape.write (.plain neighbour)⟩
      let second : DLBA.Cfg
          (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
        ⟨.directionalAtNeighbour move,
          (tape.moveHead move.direction).write (.plain neighbour)⟩
      calc
        Set.encard {cfg | Step M.combinedBoundaryShuttle cfg
            ⟨.directionalAtDeparture move neighbour, tape⟩} ≤
            Set.encard ({first, second} : Set _) := by
          apply Set.encard_le_encard
          intro cfg hcfg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact M.predecessor_combinedShuttle_directionalAtDeparture_eq_or_eq hcfg
        _ ≤ 2 := by
          calc
            Set.encard ({first, second} : Set _) ≤
                Set.encard ({second} : Set _) + 1 := Set.encard_insert_le _ _
            _ = 2 := by rw [Set.encard_singleton]; rfl
  | directionalRestoreNeighbour move neighbour =>
      let first : DLBA.Cfg
          (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
        ⟨.directionalAtDeparture move neighbour,
          tape.write (.directionalDeparture move)⟩
      let second : DLBA.Cfg
          (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
        ⟨.directionalAtDeparture move neighbour,
          (tape.moveHead (reverseDirection move.direction)).write
            (.directionalDeparture move)⟩
      calc
        Set.encard {cfg | Step M.combinedBoundaryShuttle cfg
            ⟨.directionalRestoreNeighbour move neighbour, tape⟩} ≤
            Set.encard ({first, second} : Set _) := by
          apply Set.encard_le_encard
          intro cfg hcfg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact M.predecessor_combinedShuttle_directionalRestoreNeighbour_eq_or_eq hcfg
        _ ≤ 2 := by
          calc
            Set.encard ({first, second} : Set _) ≤
                Set.encard ({second} : Set _) + 1 := Set.encard_insert_le _ _
            _ = 2 := by rw [Set.encard_singleton]; rfl
  | stationaryPending move =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      exact M.predecessor_combinedShuttle_stationaryPending_eq hleft hright

public theorem Machine.combinedBoundaryShuttle_configurationOutdegreeAtMostOne
    (M : Machine Γ Λ) (hfunctional : M.Functional) :
    ∀ (n : ℕ)
      (source : DLBA.Cfg
        (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n),
      Set.encard {target | Step M.combinedBoundaryShuttle source target} ≤ 1 := by
  intro n source
  apply Set.encard_le_one_iff.mpr
  intro left right hleft hright
  rcases hleft with
    ⟨leftTarget, leftWritten, leftDirection, hleftEnabled, rfl⟩
  rcases hright with
    ⟨rightTarget, rightWritten, rightDirection, hrightEnabled, rfl⟩
  have hmove := M.combinedBoundaryShuttle_functional hfunctional
    source.state source.tape.read hleftEnabled hrightEnabled
  simp only [Prod.mk.injEq] at hmove
  rcases hmove with ⟨rfl, rfl, rfl⟩
  rfl

public theorem Machine.combinedBoundaryShuttle_configurationOutdegreeAtMostTwo
    (M : Machine Γ Λ) (hfunctional : M.Functional) :
    M.combinedBoundaryShuttle.ConfigurationOutdegreeAtMostTwo := by
  intro n source
  exact (M.combinedBoundaryShuttle_configurationOutdegreeAtMostOne
    hfunctional n source).trans (by norm_num)

public theorem Machine.combinedBoundaryShuttle_configurationDegreeAtMostTwo
    (M : Machine Γ Λ) (hfunctional : M.Functional)
    (hdirectional : M.DirectionalTargetInjective)
    (hstationary : M.StationaryTargetWrittenInjective)
    (hkind : M.ShuttleTargetKindDisjoint) :
    M.combinedBoundaryShuttle.ConfigurationDegreeAtMostTwo :=
  ⟨M.combinedBoundaryShuttle_configurationOutdegreeAtMostTwo hfunctional,
    M.combinedBoundaryShuttle_configurationIndegreeAtMostTwo
      hdirectional hstationary hkind⟩

end LBA
