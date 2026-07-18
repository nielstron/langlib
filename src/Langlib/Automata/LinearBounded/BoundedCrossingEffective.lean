module

public import Langlib.Automata.LinearBounded.BoundedCrossingProfiles
public import Langlib.Automata.LinearBounded.FiniteReachabilityCounting
public import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic

@[expose]
public section

/-!
# Effective checking of bounded crossing profiles

`CellRun` is a semantic, type-valued description of a one-cell history.  This file gives it an
explicit finite-graph decision procedure.  The only extra information requested alongside the
source LBA presentation is a finite table of its *local* moves: the table is indexed by one control
state and one tape symbol, and its correctness field says exactly that it enumerates the
corresponding transition set.  In particular, the table is never given the input word or a
whole-language membership question.

For fixed left and right profiles, graph vertices retain a local phase and a suffix of each
profile.  Edges are precisely the stationary, exit, and entry constructors of `CellRun`.
`FiniteReachabilityCounting.reached` saturates this finite graph after its number of vertices.
This yields Boolean checkers for `CellRun`, `CellCompatible`, and the start/step/accept predicates
of `profileNFA`.
-/

namespace LBA.Machine

universe u v

variable {Gamma : Type u} {State : Type v}
variable [DecidableEq Gamma] [DecidableEq State]

/-- Executable local transition data for an LBA whose transition field is represented
semantically as a `Set`.  The table sees only one state and one scanned symbol at a time. -/
public structure TransitionTable (M : LBA.Machine Gamma State) where
  next : State → Gamma → Finset (State × Gamma × DLBA.Dir)
  mem_next_iff : ∀ {state symbol move},
    move ∈ next state symbol ↔ move ∈ M.transition state symbol

end LBA.Machine

namespace LBA.BoundedCrossing.Effective

open Relation

universe u v

variable {Gamma : Type u} {State : Type v}

/-- A suffix of one fixed chronological crossing profile.  There are exactly finitely many such
suffixes, even when the state type itself is empty. -/
abbrev ProfileSuffix (profile : List State) :=
  {remaining : List State // remaining ∈ profile.tails}

/-- Finite encoding of `Phase`; the left summand is active and the right summand is outside. -/
abbrev EncodedPhase (Gamma : Type u) (State : Type v) :=
  (State × Gamma) ⊕ (Side × Gamma)

/-- Encode a semantic local phase as a finite sum. -/
def encodePhase : Phase Gamma State → EncodedPhase Gamma State
  | .active state symbol => .inl (state, symbol)
  | .outside side symbol => .inr (side, symbol)

/-- Decode the finite phase representation. -/
def decodePhase : EncodedPhase Gamma State → Phase Gamma State
  | .inl (state, symbol) => .active state symbol
  | .inr (side, symbol) => .outside side symbol

@[simp] theorem decodePhase_encodePhase (phase : Phase Gamma State) :
    decodePhase (encodePhase phase) = phase := by
  cases phase <;> rfl

@[simp] theorem encodePhase_decodePhase (phase : EncodedPhase Gamma State) :
    encodePhase (decodePhase phase) = phase := by
  rcases phase with ⟨state, symbol⟩ | ⟨side, symbol⟩ <;> rfl

/-- A vertex of the finite local-history graph for two fixed profiles. -/
structure LocalVertex (Gamma : Type u) (State : Type v)
    (leftProfile rightProfile : List State) where
  phase : EncodedPhase Gamma State
  left : ProfileSuffix leftProfile
  right : ProfileSuffix rightProfile
deriving DecidableEq

/-- Product presentation used to enumerate all local vertices. -/
def localVertexEquiv {leftProfile rightProfile : List State} :
    LocalVertex Gamma State leftProfile rightProfile ≃
      EncodedPhase Gamma State × ProfileSuffix leftProfile × ProfileSuffix rightProfile where
  toFun vertex := (vertex.phase, vertex.left, vertex.right)
  invFun vertex := ⟨vertex.1, vertex.2.1, vertex.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype Gamma] [Fintype State] [DecidableEq State]
    {leftProfile rightProfile : List State} :
    Fintype (LocalVertex Gamma State leftProfile rightProfile) :=
  Fintype.ofEquiv
    (EncodedPhase Gamma State × ProfileSuffix leftProfile × ProfileSuffix rightProfile)
    localVertexEquiv.symm

namespace LocalVertex

variable {leftProfile rightProfile : List State}

/-- Vertex at the beginning of both supplied profiles. -/
def initial (phase : Phase Gamma State) :
    LocalVertex Gamma State leftProfile rightProfile :=
  ⟨encodePhase phase, ⟨leftProfile, by simp⟩, ⟨rightProfile, by simp⟩⟩

end LocalVertex

/-- The decidable local graph extracted from an explicit transition table.

An edge consumes no profile entry for a stationary move and exactly one entry for an exit or
entry.  Physical endpoint clamping is delegated to the same direction predicates as `CellRun`. -/
def LocalStep [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    (atLeft atRight : Bool) {leftProfile rightProfile : List State}
    (source target : LocalVertex Gamma State leftProfile rightProfile) : Prop :=
  match source.phase, target.phase with
  | .inl (state, symbol), .inl (nextState, written) =>
      source.left = target.left ∧ source.right = target.right ∧
        ∃ direction : DLBA.Dir,
          (nextState, written, direction) ∈ table.next state symbol ∧
          DirectionStaysLocal atLeft atRight direction
  | .inl (state, symbol), .inr (.left, written) =>
      source.right = target.right ∧
        ∃ nextState direction,
          source.left.1 = nextState :: target.left.1 ∧
          (nextState, written, direction) ∈ table.next state symbol ∧
          DirectionExitsLeft atLeft direction
  | .inl (state, symbol), .inr (.right, written) =>
      source.left = target.left ∧
        ∃ nextState direction,
          source.right.1 = nextState :: target.right.1 ∧
          (nextState, written, direction) ∈ table.next state symbol ∧
          DirectionExitsRight atRight direction
  | .inr (.left, symbol), .inl (state, activeSymbol) =>
      symbol = activeSymbol ∧ source.right = target.right ∧
        source.left.1 = state :: target.left.1
  | .inr (.right, symbol), .inl (state, activeSymbol) =>
      symbol = activeSymbol ∧ source.left = target.left ∧
        source.right.1 = state :: target.right.1
  | _, _ => False

instance (atLeft atRight : Bool) : DecidablePred (DirectionStaysLocal atLeft atRight) :=
  fun direction => by
    cases direction <;> simp [DirectionStaysLocal] <;> infer_instance

instance (atLeft : Bool) : DecidablePred (DirectionExitsLeft atLeft) :=
  fun direction => by
    cases direction <;> simp [DirectionExitsLeft] <;> infer_instance

instance (atRight : Bool) : DecidablePred (DirectionExitsRight atRight) :=
  fun direction => by
    cases direction <;> simp [DirectionExitsRight] <;> infer_instance

instance [Fintype State] [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    (atLeft atRight : Bool) {leftProfile rightProfile : List State} :
    DecidableRel (@LocalStep Gamma State _ _ M table atLeft atRight leftProfile rightProfile) :=
  fun source target => by
    unfold LocalStep
    split <;> infer_instance

/-- A graph vertex is one of the three base constructors of `CellRun`. -/
def LocalFinal (M : LBA.Machine Gamma State) {leftProfile rightProfile : List State}
    (terminal : Bool) (vertex : LocalVertex Gamma State leftProfile rightProfile) : Prop :=
  vertex.left.1 = [] ∧ vertex.right.1 = [] ∧
    match terminal, vertex.phase with
    | true, .inl (state, _) => M.accept state = true
    | false, .inr _ => True
    | _, _ => False

instance [DecidableEq State] (M : LBA.Machine Gamma State)
    {leftProfile rightProfile : List State} (terminal : Bool) :
    DecidablePred (@LocalFinal Gamma State M leftProfile rightProfile terminal) :=
  fun vertex => by
    unfold LocalFinal
    split <;> infer_instance

/-- Saturated finite local reachability ending in the requested base constructor. -/
def HasCheckedRun [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    (atLeft atRight : Bool) (phase : Phase Gamma State)
    (leftProfile rightProfile : List State) (terminal : Bool) : Prop :=
  let source : LocalVertex Gamma State leftProfile rightProfile := .initial phase
  (FiniteReachabilityCounting.reached
      (LocalStep table atLeft atRight) source
      (Fintype.card (LocalVertex Gamma State leftProfile rightProfile))).filter
      (LocalFinal M terminal) |>.Nonempty

instance [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    (atLeft atRight : Bool) (phase : Phase Gamma State)
    (leftProfile rightProfile : List State) (terminal : Bool) :
    Decidable (HasCheckedRun table atLeft atRight phase leftProfile rightProfile terminal) := by
  unfold HasCheckedRun
  dsimp only
  infer_instance

/-- Boolean decision procedure for `Nonempty (CellRun ...)`, relative only to an explicit local
transition table. -/
def cellRunBool [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    (atLeft atRight : Bool) (phase : Phase Gamma State)
    (leftProfile rightProfile : List State) (terminal : Bool) : Bool :=
  decide (HasCheckedRun table atLeft atRight phase leftProfile rightProfile terminal)

/-- Boolean decision procedure for `CellCompatible`. -/
def cellCompatibleBool [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine Gamma State) (table : M.TransitionTable)
    (atLeft atRight : Bool) (initialSymbol : Gamma)
    (left right : List State) (terminal : Bool) : Bool :=
  cellRunBool table atLeft atRight
    (if atLeft then .active M.initial initialSymbol else .outside .left initialSymbol)
    left right terminal

private theorem tail_mem_tails_of_cons_mem_tails
    {state : State} {remaining profile : List State}
    (h : state :: remaining ∈ profile.tails) : remaining ∈ profile.tails := by
  rw [List.mem_tails] at h ⊢
  exact (List.suffix_cons state remaining).trans h

private theorem reaches_final_of_cellRun
    [Fintype State] [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    {atLeft atRight : Bool} {phase : Phase Gamma State}
    {left right : List State} {terminal : Bool}
    (run : CellRun M atLeft atRight phase left right terminal)
    {leftProfile rightProfile : List State}
    (hleft : left ∈ leftProfile.tails) (hright : right ∈ rightProfile.tails) :
    ∃ target : LocalVertex Gamma State leftProfile rightProfile,
      ReflTransGen (LocalStep table atLeft atRight)
        ⟨encodePhase phase, ⟨left, hleft⟩, ⟨right, hright⟩⟩ target ∧
      LocalFinal M terminal target := by
  induction run with
  | terminal haccept =>
      exact ⟨_, .refl, by simp [LocalFinal, encodePhase, haccept]⟩
  | idleLeft symbol =>
      exact ⟨_, .refl, by simp [LocalFinal, encodePhase]⟩
  | idleRight symbol =>
      exact ⟨_, .refl, by simp [LocalFinal, encodePhase]⟩
  | @stationary state symbol nextState written direction left right terminal
      henabled hstays rest ih =>
      obtain ⟨target, hreach, hfinal⟩ := ih hleft hright
      refine ⟨target, ReflTransGen.head ?_ hreach, hfinal⟩
      simp only [LocalStep, encodePhase]
      exact ⟨trivial, trivial, direction, table.mem_next_iff.mpr henabled, hstays⟩
  | @exitLeft state symbol nextState written direction left right terminal
      henabled hexits rest ih =>
      have hleft' : left ∈ leftProfile.tails :=
        tail_mem_tails_of_cons_mem_tails hleft
      obtain ⟨target, hreach, hfinal⟩ := ih hleft' hright
      refine ⟨target, ReflTransGen.head ?_ hreach, hfinal⟩
      simp only [LocalStep, encodePhase]
      exact ⟨trivial, nextState, direction, rfl,
        table.mem_next_iff.mpr henabled, hexits⟩
  | @exitRight state symbol nextState written direction left right terminal
      henabled hexits rest ih =>
      have hright' : right ∈ rightProfile.tails :=
        tail_mem_tails_of_cons_mem_tails hright
      obtain ⟨target, hreach, hfinal⟩ := ih hleft hright'
      refine ⟨target, ReflTransGen.head ?_ hreach, hfinal⟩
      simp only [LocalStep, encodePhase]
      exact ⟨trivial, nextState, direction, rfl,
        table.mem_next_iff.mpr henabled, hexits⟩
  | @enterLeft state symbol left right terminal rest ih =>
      have hleft' : left ∈ leftProfile.tails :=
        tail_mem_tails_of_cons_mem_tails hleft
      obtain ⟨target, hreach, hfinal⟩ := ih hleft' hright
      refine ⟨target, ReflTransGen.head ?_ hreach, hfinal⟩
      simp [LocalStep, encodePhase]
  | @enterRight state symbol left right terminal rest ih =>
      have hright' : right ∈ rightProfile.tails :=
        tail_mem_tails_of_cons_mem_tails hright
      obtain ⟨target, hreach, hfinal⟩ := ih hleft hright'
      refine ⟨target, ReflTransGen.head ?_ hreach, hfinal⟩
      simp [LocalStep, encodePhase]

private theorem cellRun_of_localFinal
    {M : LBA.Machine Gamma State} {atLeft atRight : Bool}
    {leftProfile rightProfile : List State} {terminal : Bool}
    (vertex : LocalVertex Gamma State leftProfile rightProfile)
    (hfinal : LocalFinal M terminal vertex) :
    Nonempty <| CellRun M atLeft atRight (decodePhase vertex.phase)
      vertex.left.1 vertex.right.1 terminal := by
  rcases vertex with ⟨phase, left, right⟩
  rcases terminal with _ | _ <;>
    rcases phase with ⟨state, symbol⟩ | ⟨side, symbol⟩
  · simp [LocalFinal] at hfinal
  · rcases hfinal with ⟨hleft, hright, _⟩
    cases side with
    | left =>
        rw [hleft, hright]
        exact ⟨CellRun.idleLeft symbol⟩
    | right =>
        rw [hleft, hright]
        exact ⟨CellRun.idleRight symbol⟩
  · rcases hfinal with ⟨hleft, hright, haccept⟩
    rw [hleft, hright]
    exact ⟨CellRun.terminal haccept⟩
  · simp [LocalFinal] at hfinal

private theorem cellRun_of_localStep
    [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    {atLeft atRight : Bool} {leftProfile rightProfile : List State}
    {source target : LocalVertex Gamma State leftProfile rightProfile}
    {terminal : Bool} (hstep : LocalStep table atLeft atRight source target)
    (hrest : Nonempty <| CellRun M atLeft atRight (decodePhase target.phase)
      target.left.1 target.right.1 terminal) :
    Nonempty <| CellRun M atLeft atRight (decodePhase source.phase)
      source.left.1 source.right.1 terminal := by
  rcases hrest with ⟨rest⟩
  rcases source with ⟨sourcePhase, sourceLeft, sourceRight⟩
  rcases target with ⟨targetPhase, targetLeft, targetRight⟩
  rcases sourcePhase with ⟨state, symbol⟩ | ⟨sourceSide, symbol⟩
  · rcases targetPhase with ⟨nextState, written⟩ | ⟨targetSide, written⟩
    · rcases hstep with ⟨hleft, hright, direction, henabled, hstays⟩
      cases hleft
      cases hright
      exact ⟨CellRun.stationary (table.mem_next_iff.mp henabled) hstays rest⟩
    · cases targetSide with
      | left =>
          rcases hstep with ⟨hright, nextState, direction, hleft,
            henabled, hexits⟩
          cases hright
          rw [hleft]
          exact ⟨CellRun.exitLeft (table.mem_next_iff.mp henabled) hexits rest⟩
      | right =>
          rcases hstep with ⟨hleft, nextState, direction, hright,
            henabled, hexits⟩
          cases hleft
          rw [hright]
          exact ⟨CellRun.exitRight (table.mem_next_iff.mp henabled) hexits rest⟩
  · rcases targetPhase with ⟨state, activeSymbol⟩ | ⟨targetSide, targetSymbol⟩
    · cases sourceSide with
      | left =>
          rcases hstep with ⟨hsymbol, hright, hleft⟩
          cases hsymbol
          cases hright
          rw [hleft]
          exact ⟨CellRun.enterLeft rest⟩
      | right =>
          rcases hstep with ⟨hsymbol, hleft, hright⟩
          cases hsymbol
          cases hleft
          rw [hright]
          exact ⟨CellRun.enterRight rest⟩
    · cases sourceSide <;> cases targetSide <;> simp [LocalStep] at hstep

private theorem cellRun_of_reaches_final
    [Fintype State] [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    {atLeft atRight : Bool} {leftProfile rightProfile : List State}
    {source target : LocalVertex Gamma State leftProfile rightProfile}
    {terminal : Bool}
    (hreach : ReflTransGen (LocalStep table atLeft atRight) source target)
    (hfinal : LocalFinal M terminal target) :
    Nonempty <| CellRun M atLeft atRight (decodePhase source.phase)
      source.left.1 source.right.1 terminal := by
  induction hreach using ReflTransGen.head_induction_on with
  | refl => exact cellRun_of_localFinal target hfinal
  | @head source middle hstep hreach ih =>
      exact cellRun_of_localStep table hstep ih

/-- The saturated local graph is exact for the semantic `CellRun` type. -/
public theorem hasCheckedRun_iff_nonempty_cellRun
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    (atLeft atRight : Bool) (phase : Phase Gamma State)
    (left right : List State) (terminal : Bool) :
    HasCheckedRun table atLeft atRight phase left right terminal ↔
      Nonempty (CellRun M atLeft atRight phase left right terminal) := by
  let source : LocalVertex Gamma State left right := .initial phase
  constructor
  · rintro ⟨target, htarget⟩
    rw [Finset.mem_filter] at htarget
    have hreach : ReflTransGen (LocalStep table atLeft atRight) source target :=
      (FiniteReachabilityCounting.mem_reached_card_iff
        (edge := LocalStep table atLeft atRight) (source := source)).mp htarget.1
    simpa [source, LocalVertex.initial] using
      cellRun_of_reaches_final table hreach htarget.2
  · rintro ⟨run⟩
    obtain ⟨target, hreach, hfinal⟩ :=
      reaches_final_of_cellRun table run
        (leftProfile := left) (rightProfile := right) (by simp) (by simp)
    refine ⟨target, Finset.mem_filter.mpr ⟨?_, hfinal⟩⟩
    apply (FiniteReachabilityCounting.mem_reached_card_iff
      (edge := LocalStep table atLeft atRight) (source := source)).mpr
    simpa [source, LocalVertex.initial] using hreach

/-- Correctness of the explicit Boolean one-cell-history checker. -/
public theorem cellRunBool_eq_true_iff
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    {M : LBA.Machine Gamma State} (table : M.TransitionTable)
    (atLeft atRight : Bool) (phase : Phase Gamma State)
    (left right : List State) (terminal : Bool) :
    cellRunBool table atLeft atRight phase left right terminal = true ↔
      Nonempty (CellRun M atLeft atRight phase left right terminal) := by
  rw [cellRunBool, decide_eq_true_eq]
  exact hasCheckedRun_iff_nonempty_cellRun table atLeft atRight phase left right terminal

/-- Correctness of the explicit Boolean `CellCompatible` checker. -/
public theorem cellCompatibleBool_eq_true_iff
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine Gamma State) (table : M.TransitionTable)
    (atLeft atRight : Bool) (initialSymbol : Gamma)
    (left right : List State) (terminal : Bool) :
    cellCompatibleBool M table atLeft atRight initialSymbol left right terminal = true ↔
      CellCompatible M atLeft atRight initialSymbol left right terminal := by
  simp only [cellCompatibleBool, cellRunBool_eq_true_iff, CellCompatible]

/-- A constructive `Decidable` instance assembled from the explicit local checker.  It is kept as
an explicit argument-taking definition so importing this file does not silently make arbitrary
semantic transition sets executable. -/
def cellCompatibleDecidable
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine Gamma State) (table : M.TransitionTable)
    (atLeft atRight : Bool) (initialSymbol : Gamma)
    (left right : List State) (terminal : Bool) :
    Decidable (CellCompatible M atLeft atRight initialSymbol left right terminal) :=
  decidable_of_iff
    (cellCompatibleBool M table atLeft atRight initialSymbol left right terminal = true)
    (cellCompatibleBool_eq_true_iff M table atLeft atRight initialSymbol left right terminal)

/-- Existential search over an explicitly finite type. -/
def finiteAnyBool {A : Type*} [Fintype A] [DecidableEq A] (predicate : A → Bool) : Bool :=
  decide ((Finset.univ.filter fun value => predicate value = true).Nonempty)

@[simp] theorem finiteAnyBool_eq_true_iff {A : Type*} [Fintype A] [DecidableEq A]
    (predicate : A → Bool) :
    finiteAnyBool predicate = true ↔ ∃ value, predicate value = true := by
  simp only [finiteAnyBool, decide_eq_true_eq, Finset.filter_nonempty_iff,
    Finset.mem_univ, true_and]

/-- Boolean membership in the start set of the bounded-profile NFA. -/
def profileStartBool
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    {bound : Nat} (state : ScanState Gamma State bound) : Bool :=
  decide (state = .before)

/-- Boolean membership in one transition set of the bounded-profile NFA.  All existential
profile guesses are enumerated from their finite types; every local compatibility test is handled
by `cellCompatibleBool`. -/
def profileStepBool
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine Gamma State) (table : M.TransitionTable) (bound : Nat)
    (source : ScanState Gamma State bound) (symbol : Gamma)
    (target : ScanState Gamma State bound) : Bool :=
  match source with
  | .before => decide (target = .first symbol)
  | .first old =>
      finiteAnyBool fun guess : Profile State bound × Bool =>
        cellCompatibleBool M table true false old [] guess.1.list guess.2 &&
          decide (target = .pending symbol guess.1 guess.2)
  | .pending old left seen =>
      finiteAnyBool fun guess : Profile State bound × Bool =>
        cellCompatibleBool M table false false old left.list guess.1.list guess.2 &&
          decide (¬ (seen = true ∧ guess.2 = true)) &&
          decide (target = .pending symbol guess.1 (seen || guess.2))

/-- Boolean membership in the accepting set of the bounded-profile NFA. -/
def profileAcceptBool
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine Gamma State) (table : M.TransitionTable) (bound : Nat)
    (state : ScanState Gamma State bound) : Bool :=
  match state with
  | .before => false
  | .first symbol => cellCompatibleBool M table true true symbol [] [] true
  | .pending symbol left seen =>
      finiteAnyBool fun terminal : Bool =>
        cellCompatibleBool M table false true symbol left.list [] terminal &&
          decide (¬ (seen = true ∧ terminal = true)) &&
          decide ((seen || terminal) = true)

/-- Correctness of Boolean start-set membership. -/
public theorem profileStartBool_eq_true_iff
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine Gamma State) (bound : Nat)
    (state : ScanState Gamma State bound) :
    profileStartBool state = true ↔
      state ∈ (profileNFA M bound).start := by
  cases state <;> simp [profileStartBool, profileNFA]

/-- Correctness of Boolean transition-set membership. -/
public theorem profileStepBool_eq_true_iff
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine Gamma State) (table : M.TransitionTable) (bound : Nat)
    (source : ScanState Gamma State bound) (symbol : Gamma)
    (target : ScanState Gamma State bound) :
    profileStepBool M table bound source symbol target = true ↔
      target ∈ (profileNFA M bound).step source symbol := by
  cases source <;>
    simp [profileStepBool, profileNFA, cellCompatibleBool_eq_true_iff]
  aesop

/-- Correctness of Boolean accepting-set membership. -/
public theorem profileAcceptBool_eq_true_iff
    [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine Gamma State) (table : M.TransitionTable) (bound : Nat)
    (state : ScanState Gamma State bound) :
    profileAcceptBool M table bound state = true ↔
      state ∈ (profileNFA M bound).accept := by
  cases state <;>
    simp [profileAcceptBool, profileNFA, cellCompatibleBool_eq_true_iff]

end LBA.BoundedCrossing.Effective

end
