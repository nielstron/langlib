module

public import Langlib.Automata.LinearBounded.AcyclicClock.ReadySkeleton
public import Langlib.Automata.LinearBounded.BranchSetMinor
import Mathlib.Tactic

@[expose]
public section

/-!
# Branch-set minors through the concrete acyclic-clock compiler

This file contracts the actual one-tape protocol corridors of `AcyclicClock.machine`, rather
than only its semantic checkpoint skeleton.  We work at the all-zero physical clock.  The
normalization prefix of every simulated source step converges to a clean `carry` entry depending
only on the source-step target.  Its corridor is stopped before `ready`, so deterministic
non-Ready predecessor cones of distinct clean carry entries are disjoint.

The resulting theorem is deliberately generic over source machines on the endmarker alphabet.
It requires an explicit self-loop at every fixed-width source configuration in order to connect
the checkpoint representative to its own carry cone.  It does not assert that a machine over an
unrelated tape alphabet has already been transported into the compiler's source alphabet.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- The canonical bottom-clock checkpoint representing a source configuration. -/
@[expose]
public def bottomCheckpoint
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n :=
  canonicalCfg M cfg

/-- The clean carry-entry configuration reached before the physical increment begins. -/
@[expose]
public def cleanCarry
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n :=
  ⟨.carry cfg.state,
    leftHeadReadyTape cfg.tape (fun _ => clockZero M)⟩

@[simp]
public theorem bottomCheckpoint_state
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    (bottomCheckpoint M cfg).state = .ready cfg.state := rfl

@[simp]
public theorem cleanCarry_state
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    (cleanCarry M cfg).state = .carry cfg.state := rfl

@[simp]
public theorem cleanCarry_head
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    (cleanCarry M cfg).tape.head = ⟨0, by omega⟩ := rfl

@[simp]
public theorem clockValue_cleanCarry
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    clockValue M (cleanCarry M cfg).tape = 0 := by
  letI : Nonempty Λ := ⟨M.initial⟩
  change
    (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value
      (List.ofFn fun _ : Fin (n + 1) =>
        (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).zero) = 0
  have hrow :
      (List.ofFn fun _ : Fin (n + 1) =>
          (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).zero) =
        (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).zeroRow (n + 1) := by
    simp only [List.ofFn_const, RowNumeral.DigitCodec.zeroRow]
  rw [hrow]
  exact (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value_zeroRow (n + 1)

@[simp]
public theorem effectiveClock_cleanCarry
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    effectiveClock M (cleanCarry M cfg) = 1 := by
  unfold effectiveClock pendingCarryWeight
  rw [clockValue_cleanCarry]
  simp [cleanCarry, leftHeadReadyTape]

/-- A nonempty path from Ready to a target outside the pre-carry phases must cross a carry-entry
edge, and therefore strictly raises the effective clock. -/
public theorem effectiveClock_lt_of_ready_transGen_to_not_preCarry
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hold : old.state.IsReady) (hnew : ¬ new.state.PreCarry)
    (hpath : TransGen (LBA.Step (machine M)) old new) :
    effectiveClock M old < effectiveClock M new := by
  rcases TransGen.head'_iff.mp hpath with ⟨first, hfirst, hrest⟩
  have hpre := ready_step_preCarry M hold hfirst
  rcases reflTransGen_preCarry_or_contains_entry M hpre hrest with
    hstill | ⟨before, after, hprefix, hentry, hsuffix⟩
  · exact (hnew hstill).elim
  · exact
      ((step_effectiveClock_le M hfirst).trans
        (reflTransGen_effectiveClock_le M hprefix)).trans_lt
          ((carryEntry_effectiveClock_lt M hentry).trans_le
            (reflTransGen_effectiveClock_le M hsuffix))

@[simp]
public theorem clockValue_bottomCheckpoint
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    clockValue M (bottomCheckpoint M cfg).tape = 0 := by
  simpa [bottomCheckpoint] using clockValue_canonicalTape M cfg.tape

private theorem beforeReadyTail_of_bottom_to_cleanCarry
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (source target : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    {current : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hprefix :
      TransGen (LBA.Step (machine M)) (bottomCheckpoint M source) current)
    (htail :
      ReflTransGen (LBA.Step (machine M)) current (cleanCarry M target)) :
    ReflTransGen (BeforeReadyStep M) current (cleanCarry M target) := by
  induction htail using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head old middle hstep hrest ih =>
      have hold : ¬ old.state.IsReady := by
        intro hready
        have hpositive : 0 < effectiveClock M old := by
          have hgrowth :=
            ready_transGen_clockValue_lt M (by
              simp [bottomCheckpoint, State.IsReady]) hready hprefix
          rw [effectiveClock_eq_clockValue_of_isReady M old hready]
          simpa using hgrowth
        have hsuffix :
            TransGen (LBA.Step (machine M)) old (cleanCarry M target) :=
          TransGen.head' hstep hrest
        have hsmall :=
          effectiveClock_lt_of_ready_transGen_to_not_preCarry M hready
            (by simp [cleanCarry, State.PreCarry]) hsuffix
        rw [effectiveClock_cleanCarry] at hsmall
        omega
      exact ReflTransGen.head ⟨hstep, hold⟩ (ih (hprefix.tail hstep))

/-- The concrete normalization prefix of a bottom-clock source step can be stopped at its clean
carry entry.  After the first (possibly nondeterministic) Ready edge, every source of the remaining
path is non-Ready. -/
public theorem bottomCheckpoint_to_cleanCarry_beforeReady_of_step
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    {source target : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (hsource : LBA.Step M source target) :
    ∃ after,
      LBA.Step (machine M) (bottomCheckpoint M source) after ∧
        ReflTransGen (BeforeReadyStep M) after (cleanCarry M target) := by
  have hraw :
      LBA.Reaches (machine M) (bottomCheckpoint M source) (cleanCarry M target) := by
    simpa [bottomCheckpoint, cleanCarry] using
      (reaches_carry_checkpoint_of_step M
        (fun _ => clockZero M) (ReadyTrails.clear n) hsource)
  rcases ReflTransGen.cases_head hraw with heq | ⟨after, hfirst, htail⟩
  · have hstate := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.state) heq
    simp [bottomCheckpoint, cleanCarry] at hstate
  · exact ⟨after, hfirst,
      beforeReadyTail_of_bottom_to_cleanCarry M source target
        (.single hfirst) htail⟩

/-! ## Separation of clean carry cones -/

/-- Moving the physical head to the least-significant cell does not lose the source tape head:
the unique simulated-head mark still records it in the tape contents. -/
public theorem leftHeadReadyTape_pair_injective {n : ℕ} :
    Function.Injective
      (fun data :
          DLBA.BoundedTape (SourceAlpha T Γ) n ×
            (Fin (n + 1) → ClockDigit T Γ Λ) =>
        leftHeadReadyTape data.1 data.2) := by
  rintro ⟨leftTape, leftDigits⟩ ⟨rightTape, rightDigits⟩ heq
  have hcells : ∀ index,
      readyCell leftTape leftDigits index =
        readyCell rightTape rightDigits index := by
    intro index
    have hsymbol :=
      congrFun (congrArg DLBA.BoundedTape.contents heq) index
    change
      workSymbol (readyCell leftTape leftDigits index) =
        workSymbol (readyCell rightTape rightDigits index) at hsymbol
    simpa [workSymbol] using hsymbol
  have hcontents : leftTape.contents = rightTape.contents := by
    funext index
    exact congrArg WorkCell.src (hcells index)
  have hdigits : leftDigits = rightDigits := by
    funext index
    exact congrArg WorkCell.digit (hcells index)
  have hhead : leftTape.head = rightTape.head := by
    have hmark := congrArg WorkCell.mark (hcells leftTape.head)
    simpa [readyCell] using hmark
  have htapes : leftTape = rightTape := by
    cases leftTape
    cases rightTape
    simp_all
  simp_all

/-- A clean carry entry preserves the complete represented source configuration. -/
public theorem cleanCarry_injective
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ} :
    Function.Injective
      (cleanCarry M :
        DLBA.Cfg (SourceAlpha T Γ) Λ n →
          DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) := by
  intro left right heq
  have hstate : left.state = right.state := by
    have := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.state) heq
    simpa [cleanCarry] using this
  have htapes : left.tape = right.tape := by
    have htapeEq := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.tape) heq
    have hpairs :
        (left.tape, fun _ : Fin (n + 1) => clockZero M) =
          (right.tape, fun _ : Fin (n + 1) => clockZero M) :=
      leftHeadReadyTape_pair_injective (T := T) (Γ := Γ) (Λ := Λ)
      (show
        leftHeadReadyTape left.tape (fun _ => clockZero M) =
          leftHeadReadyTape right.tape (fun _ => clockZero M) by
        simpa [cleanCarry] using htapeEq)
    exact congrArg Prod.fst hpairs
  cases left
  cases right
  simp_all

@[simp]
public theorem phasePotential_cleanCarry
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    phasePotential (cleanCarry M cfg) = 7 * phaseStride n + 1 := by
  simp [phasePotential, phaseIndex, localRank, cleanCarry,
    carryCount, workCellCount, symbolCount, leftHeadReadyTape,
    readyTape, readyCell]

/-- A nonempty stopped non-Ready path whose endpoint is non-Ready strictly raises the phase
potential. -/
public theorem beforeReadyTransGen_phasePotential_lt_of_target_not_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hpath : TransGen (BeforeReadyStep M) old new)
    (hnew : ¬ new.state.IsReady) :
    phasePotential old < phasePotential new := by
  induction hpath with
  | single hstep =>
      exact nonready_step_phasePotential_lt M hstep.1 hstep.2 hnew
  | @tail middle target hpath hstep ih =>
      exact (ih hstep.2).trans
        (nonready_step_phasePotential_lt M hstep.1 hstep.2 hnew)

/-- Equal phase potential forces a stopped path ending outside Ready to be reflexive. -/
public theorem eq_of_beforeReady_reaches_of_phasePotential_eq
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    {old new : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hpath : ReflTransGen (BeforeReadyStep M) old new)
    (hnew : ¬ new.state.IsReady)
    (hpotential : phasePotential old = phasePotential new) :
    old = new := by
  rcases reflTransGen_iff_eq_or_transGen.mp hpath with heq | hstrict
  · exact heq.symm
  · have := beforeReadyTransGen_phasePotential_lt_of_target_not_ready M hstrict hnew
    omega

/-! ## The branch-set certificate -/

/-- The stopped deterministic predecessor cone of one clean carry entry. -/
@[expose]
public def cleanCarryCone
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    Set (DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) :=
  {raw | ReflTransGen (BeforeReadyStep M) raw (cleanCarry M cfg)}

/-- A source vertex is represented by its bottom checkpoint together with the stopped
predecessor cone of its clean carry entry. -/
@[expose]
public def concreteClockBranchSet
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    Set (DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) :=
  {bottomCheckpoint M cfg} ∪ cleanCarryCone M cfg

private theorem cleanCarry_eq_of_common_cone
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    {left right : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    {raw : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hleft : raw ∈ cleanCarryCone M left)
    (hright : raw ∈ cleanCarryCone M right) :
    cleanCarry M left = cleanCarry M right := by
  rcases ReflTransGen.total_of_right_unique
      (beforeReadyStep_rightUnique M) hleft hright with
    hleftRight | hrightLeft
  · exact eq_of_beforeReady_reaches_of_phasePotential_eq M hleftRight
      (by simp [cleanCarry, State.IsReady]) (by simp)
  · exact (eq_of_beforeReady_reaches_of_phasePotential_eq M hrightLeft
      (by simp [cleanCarry, State.IsReady]) (by simp)).symm

/-- Branch sets of distinct source configurations are disjoint as raw target-configuration
sets.  The proof uses stopped-corridor right-uniqueness, not a quotient of checkpoints. -/
public theorem concreteClockBranchSet_disjoint
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    {left right : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (hne : left ≠ right) :
    Disjoint (concreteClockBranchSet M left)
      (concreteClockBranchSet M right) := by
  rw [Set.disjoint_left]
  intro raw hleft hright
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright
  · have heq : bottomCheckpoint M left = bottomCheckpoint M right := by
      simpa [concreteClockBranchSet] using hleft.symm.trans hright
    exact hne (canonicalCfg_injective M heq)
  · have hready : (bottomCheckpoint M left).state.IsReady := by
      simp [bottomCheckpoint, State.IsReady]
    have heq := beforeReady_reaches_eq_of_ready M hready
      (show ReflTransGen (BeforeReadyStep M)
          (bottomCheckpoint M left) (cleanCarry M right) by
        simpa [concreteClockBranchSet, cleanCarryCone] using hleft.symm ▸ hright)
    have hstate := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.state) heq
    simp [bottomCheckpoint, cleanCarry] at hstate
  · have hready : (bottomCheckpoint M right).state.IsReady := by
      simp [bottomCheckpoint, State.IsReady]
    have heq := beforeReady_reaches_eq_of_ready M hready
      (show ReflTransGen (BeforeReadyStep M)
          (bottomCheckpoint M right) (cleanCarry M left) by
        simpa [concreteClockBranchSet, cleanCarryCone] using hright.symm ▸ hleft)
    have hstate := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.state) heq
    simp [bottomCheckpoint, cleanCarry] at hstate
  · have hcarry := cleanCarry_eq_of_common_cone M
      (show raw ∈ cleanCarryCone M left by
        simpa [concreteClockBranchSet] using hleft)
      (show raw ∈ cleanCarryCone M right by
        simpa [concreteClockBranchSet] using hright)
    exact hne (cleanCarry_injective M hcarry)

private theorem cleanCarryCone_connected_to_carry
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    {raw : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hraw : raw ∈ cleanCarryCone M cfg) :
    ReflTransGen
      (Restricted (concreteClockBranchSet M cfg)
        (SymmetricClosure (LBA.Step (machine M))))
      raw (cleanCarry M cfg) := by
  change ReflTransGen (BeforeReadyStep M) raw (cleanCarry M cfg) at hraw
  induction hraw using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head old middle hstep hrest ih =>
      apply ReflTransGen.head
      · refine ⟨?_, Or.inl hstep.1, ?_⟩
        · exact Or.inr (ReflTransGen.head hstep hrest)
        · exact Or.inr hrest
      · exact ih

private theorem concreteClockBranchSet_connected_to_carry
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (selfLoop : ∀ cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n,
      LBA.Step M cfg cfg)
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    {raw : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hraw : raw ∈ concreteClockBranchSet M cfg) :
    ReflTransGen
      (Restricted (concreteClockBranchSet M cfg)
        (SymmetricClosure (LBA.Step (machine M))))
      raw (cleanCarry M cfg) := by
  rcases hraw with hcheckpoint | hcone
  · have hrawEq : raw = bottomCheckpoint M cfg := by
      simpa [concreteClockBranchSet] using hcheckpoint
    subst raw
    obtain ⟨after, hfirst, htail⟩ :=
      bottomCheckpoint_to_cleanCarry_beforeReady_of_step M (selfLoop cfg)
    exact ReflTransGen.head
      ⟨Or.inl rfl, Or.inl hfirst, Or.inr htail⟩
      (cleanCarryCone_connected_to_carry M cfg htail)
  · exact cleanCarryCone_connected_to_carry M cfg hcone

/-- The checkpoint-plus-cone branch set is connected whenever the represented source vertex has
an explicit self-loop. -/
public theorem concreteClockBranchSet_connected
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (selfLoop : ∀ cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n,
      LBA.Step M cfg cfg)
    (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hsource : source ∈ concreteClockBranchSet M cfg)
    (htarget : target ∈ concreteClockBranchSet M cfg) :
    ReflTransGen
      (Restricted (concreteClockBranchSet M cfg)
        (SymmetricClosure (LBA.Step (machine M))))
      source target := by
  have toCarrySource :=
    concreteClockBranchSet_connected_to_carry M selfLoop cfg hsource
  have toCarryTarget :=
    concreteClockBranchSet_connected_to_carry M selfLoop cfg htarget
  have hsymm : Symmetric
      (Restricted (concreteClockBranchSet M cfg)
        (SymmetricClosure (LBA.Step (machine M)))) := by
    intro left right hstep
    refine ⟨hstep.2.2, ?_, hstep.1⟩
    exact hstep.2.1.elim Or.inr Or.inl
  exact toCarrySource.trans (toCarryTarget.symmetric hsymm)

/-- **Concrete compiler corridor theorem.**  At every fixed width, a reflexive source
configuration relation is an underlying undirected branch-set minor of the raw configuration
graph of the actual one-tape acyclic-clock machine. -/
public def concreteClockBranchSetMinorModel
    (M : LBA.Machine (SourceAlpha T Γ) Λ) {n : ℕ}
    (selfLoop : ∀ cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n,
      LBA.Step M cfg cfg) :
    BranchSetMinorModel
      (SymmetricClosure (LBA.Step (n := n) M))
      (LBA.Step (n := n) (machine M)) where
  branchSet := concreteClockBranchSet M
  nonempty cfg := ⟨bottomCheckpoint M cfg, Or.inl rfl⟩
  disjoint hne := concreteClockBranchSet_disjoint M hne
  connected cfg {source target} hsource htarget :=
    concreteClockBranchSet_connected M selfLoop cfg hsource htarget
  map_edge {source target} hsourceTarget := by
    rcases hsourceTarget with hforward | hbackward
    · obtain ⟨after, hfirst, htail⟩ :=
        bottomCheckpoint_to_cleanCarry_beforeReady_of_step M hforward
      exact ⟨bottomCheckpoint M source, Or.inl rfl,
        after, Or.inr htail, Or.inl hfirst⟩
    · obtain ⟨after, hfirst, htail⟩ :=
        bottomCheckpoint_to_cleanCarry_beforeReady_of_step M hbackward
      exact ⟨after, Or.inr htail,
        bottomCheckpoint M target, Or.inl rfl, Or.inr hfirst⟩

end LBA.AcyclicClock

end
