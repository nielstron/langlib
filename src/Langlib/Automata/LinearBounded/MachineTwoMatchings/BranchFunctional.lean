module

public import Langlib.Automata.LinearBounded.AcyclicBoundedDegree
public import Langlib.Automata.LinearBounded.FiniteAcyclicRank
public import Langlib.Automata.LinearBounded.Functional
public import Langlib.Automata.LinearBounded.TwoMatchingChoiceBound

@[expose]
public section

/-!
# Pinning the sole branch of a two-matching LBA

For a machine whose complete configuration relation is the exact union of two directed
matchings, every run is configuration-functional after its first edge.  This module pins one
finite transition triple at a fresh boot state and thereafter chooses an arbitrary enabled
transition locally.  Although several transition triples may describe the same clamped
configuration edge, the two-matching theorem guarantees that every such choice reaches the same
successor along a run with an incoming edge.

The pinned machine is genuinely `Machine.Functional`.  Every accepting run of the source is
accepted by at least one pinned machine, and every pinned run projects to a source run.  Thus the
source language is a finite union, indexed by the fixed finite move alphabet, of functional
languages.  Global configuration acyclicity is preserved.

Combining that finite union into one marker-free `DLBA.Machine` is a separate operational step;
it is not claimed in this file.
-/

namespace LBA

open Classical Relation

variable {Γ Λ : Type*}

/-- The finite-control states of a machine with one pinned first move. -/
public inductive FirstMoveState (Λ : Type*) where
  | boot
  | run (state : Λ)
deriving Fintype, DecidableEq

/-- Forget the fresh boot marker. -/
@[expose]
public def FirstMoveState.project (M : Machine Γ Λ) : FirstMoveState Λ → Λ
  | .boot => M.initial
  | .run state => state

/-- Choose one enabled transition triple, if one exists. -/
@[expose]
public noncomputable def Machine.selectedMove
    (M : Machine Γ Λ) (state : Λ) (symbol : Γ) :
    Option (Λ × Γ × DLBA.Dir) := by
  exact if h : ∃ move, move ∈ M.transition state symbol
    then some (Classical.choose h)
    else none

/-- A selected move is enabled in the source transition table. -/
public theorem Machine.selectedMove_mem
    (M : Machine Γ Λ) {state : Λ} {symbol : Γ} {move : Λ × Γ × DLBA.Dir}
    (hmove : M.selectedMove state symbol = some move) :
    move ∈ M.transition state symbol := by
  simp only [Machine.selectedMove] at hmove
  split at hmove
  · next h =>
      have heq : Classical.choose h = move := Option.some.inj hmove
      rw [← heq]
      exact Classical.choose_spec h
  · simp at hmove

/-- If some move is enabled, the selector returns an enabled move. -/
public theorem Machine.exists_selectedMove_of_mem
    (M : Machine Γ Λ) {state : Λ} {symbol : Γ} {move : Λ × Γ × DLBA.Dir}
    (hmem : move ∈ M.transition state symbol) :
    ∃ selected, M.selectedMove state symbol = some selected := by
  simp only [Machine.selectedMove]
  split
  · exact ⟨_, rfl⟩
  · next h => exact False.elim (h ⟨move, hmem⟩)

/-- Pin one transition triple at a fresh boot state and use an arbitrary enabled move after it.
The selector is local to the finite transition table; no configuration or acceptance predicate
is used to make the choice. -/
@[expose]
public noncomputable def Machine.pinFirst
    (M : Machine Γ Λ) (first : Λ × Γ × DLBA.Dir) :
    Machine Γ (FirstMoveState Λ) where
  transition
    | .boot, symbol =>
        if first ∈ M.transition M.initial symbol then
          {(.run first.1, first.2.1, first.2.2)}
        else ∅
    | .run state, symbol =>
        match M.selectedMove state symbol with
        | none => ∅
        | some move => {(.run move.1, move.2.1, move.2.2)}
  accept
    | .boot => M.accept M.initial
    | .run state => M.accept state
  initial := .boot

/-- Project a pinned configuration to the source configuration with the same tape. -/
@[expose]
public def Machine.pinFirstProjectCfg
    (M : Machine Γ Λ) {n : ℕ}
    (cfg : DLBA.Cfg Γ (FirstMoveState Λ) n) : DLBA.Cfg Γ Λ n :=
  ⟨cfg.state.project M, cfg.tape⟩

/-- Embed a source configuration in the running phase. -/
@[expose]
public def Machine.pinFirstRunCfg
    (_M : Machine Γ Λ) {n : ℕ}
    (cfg : DLBA.Cfg Γ Λ n) : DLBA.Cfg Γ (FirstMoveState Λ) n :=
  ⟨.run cfg.state, cfg.tape⟩

/-- Put a tape at the pinned machine's fresh boot state. -/
@[expose]
public def Machine.pinFirstBootCfg
    (_M : Machine Γ Λ) {n : ℕ}
    (tape : DLBA.BoundedTape Γ n) : DLBA.Cfg Γ (FirstMoveState Λ) n :=
  ⟨.boot, tape⟩

@[simp]
public theorem Machine.pinFirstProjectCfg_run
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    M.pinFirstProjectCfg (M.pinFirstRunCfg cfg) = cfg := rfl

@[simp]
public theorem Machine.pinFirstProjectCfg_boot
    (M : Machine Γ Λ) {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    M.pinFirstProjectCfg (M.pinFirstBootCfg tape) = ⟨M.initial, tape⟩ := rfl

/-- Every pinned machine has a single transition triple at each state/symbol pair. -/
public theorem Machine.pinFirst_functional
    (M : Machine Γ Λ) (first : Λ × Γ × DLBA.Dir) :
    (M.pinFirst first).Functional := by
  intro state symbol left hleft right hright
  cases state with
  | boot =>
      simp only [Machine.pinFirst] at hleft hright
      split at hleft <;> simp_all
  | run state =>
      simp only [Machine.pinFirst] at hleft hright
      cases hselected : M.selectedMove state symbol <;> simp_all

/-- Every pinned step projects to a genuine source-machine step, on all raw configurations. -/
public theorem Machine.step_of_step_pinFirst
    (M : Machine Γ Λ) (first : Λ × Γ × DLBA.Dir) {n : ℕ}
    {source target : DLBA.Cfg Γ (FirstMoveState Λ) n}
    (hstep : Step (M.pinFirst first) source target) :
    Step M (M.pinFirstProjectCfg source) (M.pinFirstProjectCfg target) := by
  rcases source with ⟨sourceState, tape⟩
  rcases hstep with ⟨nextState, write, direction, hmem, rfl⟩
  cases sourceState with
  | boot =>
      simp only [Machine.pinFirst] at hmem
      split at hmem
      · next henabled =>
          simp only [Set.mem_singleton_iff] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          exact ⟨first.1, first.2.1, first.2.2, henabled, rfl⟩
      · simp at hmem
  | run state =>
      simp only [Machine.pinFirst] at hmem
      change (nextState, write, direction) ∈
        (match M.selectedMove state tape.read with
        | none => ∅
        | some move => {(FirstMoveState.run move.1, move.2.1, move.2.2)}) at hmem
      cases hselected : M.selectedMove state tape.read with
      | none =>
          rw [hselected] at hmem
          simp at hmem
      | some selected =>
          rw [hselected] at hmem
          simp only [Set.mem_singleton_iff] at hmem
          rcases hmem with ⟨rfl, rfl, rfl⟩
          exact ⟨selected.1, selected.2.1, selected.2.2,
            M.selectedMove_mem hselected, rfl⟩

/-- Projecting a pinned run gives a source-machine run. -/
public theorem Machine.reaches_pinFirst_project
    (M : Machine Γ Λ) (first : Λ × Γ × DLBA.Dir) {n : ℕ}
    {source target : DLBA.Cfg Γ (FirstMoveState Λ) n}
    (hreach : Reaches (M.pinFirst first) source target) :
    Reaches M (M.pinFirstProjectCfg source) (M.pinFirstProjectCfg target) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.tail (M.step_of_step_pinFirst first hstep)

/-- Positive pinned paths also project edge-for-edge to positive source paths. -/
public theorem Machine.transGen_pinFirst_project
    (M : Machine Γ Λ) (first : Λ × Γ × DLBA.Dir) {n : ℕ}
    {source target : DLBA.Cfg Γ (FirstMoveState Λ) n}
    (hreach : TransGen (Step (M.pinFirst first)) source target) :
    TransGen (Step M) (M.pinFirstProjectCfg source) (M.pinFirstProjectCfg target) := by
  induction hreach with
  | single hstep => exact .single (M.step_of_step_pinFirst first hstep)
  | tail _ hstep ih =>
      exact ih.tail (M.step_of_step_pinFirst first hstep)

/-- The pinned boot step executes exactly the supplied enabled source move. -/
public theorem Machine.step_pinFirst_boot
    (M : Machine Γ Λ) {n : ℕ}
    (tape : DLBA.BoundedTape Γ n) (first : Λ × Γ × DLBA.Dir)
    (henabled : first ∈ M.transition M.initial tape.read) :
    Step (M.pinFirst first) (M.pinFirstBootCfg tape)
      (M.pinFirstRunCfg
        (⟨first.1, (tape.write first.2.1).moveHead first.2.2⟩ :
          DLBA.Cfg Γ Λ n)) := by
  exact ⟨.run first.1, first.2.1, first.2.2, by
    simp only [Machine.pinFirstBootCfg, Machine.pinFirst]
    rw [if_pos henabled]
    rfl, rfl⟩

/-- Once a run has an incoming source edge, the locally selected move reaches the same successor
as every supplied source edge. -/
public theorem Machine.step_pinFirst_run_of_incoming
    (M : Machine Γ Λ) (first : Λ × Γ × DLBA.Dir) {n : ℕ}
    {layer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (cover : ∀ source target, Step M source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {predecessor source target : DLBA.Cfg Γ Λ n}
    (hincoming : Step M predecessor source)
    (hstep : Step M source target) :
    Step (M.pinFirst first) (M.pinFirstRunCfg source)
      (M.pinFirstRunCfg target) := by
  have hstepOld := hstep
  rcases hstep with ⟨nextState, write, direction, henabled, htarget⟩
  obtain ⟨selected, hselected⟩ :=
    M.exists_selectedMove_of_mem henabled
  let chosenTarget : DLBA.Cfg Γ Λ n :=
    ⟨selected.1, (source.tape.write selected.2.1).moveHead selected.2.2⟩
  have hchosen : Step M source chosenTarget :=
    ⟨selected.1, selected.2.1, selected.2.2,
      M.selectedMove_mem hselected, rfl⟩
  have heq : chosenTarget = target :=
    ThreeMatchingReachability.successor_eq_of_incoming
      cover biUnique short hincoming hchosen hstepOld
  rw [← heq]
  refine ⟨.run selected.1, selected.2.1, selected.2.2, ?_, ?_⟩
  · change (FirstMoveState.run selected.1, selected.2.1, selected.2.2) ∈
      (match M.selectedMove source.state source.tape.read with
      | none => ∅
      | some move => {(FirstMoveState.run move.1, move.2.1, move.2.2)})
    rw [hselected]
    rfl
  · rfl

/-- Every tail after a genuine first edge lifts to the functional running phase. -/
public theorem Machine.reaches_pinFirst_run_of_reaches_of_incoming
    (M : Machine Γ Λ) (first : Λ × Γ × DLBA.Dir) {n : ℕ}
    {layer : Fin 2 → DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop}
    (cover : ∀ source target, Step M source target ↔
      ∃! color, layer color source target)
    (biUnique : ∀ color, Relator.BiUnique (layer color))
    (short : ∀ color,
      LinearTwoDiforestReachability.PathLengthAtMostOne (layer color))
    {predecessor source target : DLBA.Cfg Γ Λ n}
    (hincoming : Step M predecessor source)
    (hreach : Reaches M source target) :
    Reaches (M.pinFirst first) (M.pinFirstRunCfg source)
      (M.pinFirstRunCfg target) := by
  induction hreach using Relation.ReflTransGen.head_induction_on generalizing predecessor with
  | refl => exact .refl
  | @head source middle hstep _ ih =>
      exact ReflTransGen.head
        (M.step_pinFirst_run_of_incoming first cover biUnique short hincoming hstep)
        (ih hstep)

/-- A pinned accepting run is always sound for the source machine. -/
public theorem Machine.accepts_of_accepts_pinFirst
    (M : Machine Γ Λ) (first : Λ × Γ × DLBA.Dir) {n : ℕ}
    (tape : DLBA.BoundedTape Γ n)
    (haccept : Accepts (M.pinFirst first) (M.pinFirstBootCfg tape)) :
    Accepts M ⟨M.initial, tape⟩ := by
  obtain ⟨target, hreach, hfinal⟩ := haccept
  refine ⟨M.pinFirstProjectCfg target,
    M.reaches_pinFirst_project first hreach, ?_⟩
  rcases target with ⟨state, targetTape⟩
  cases state <;> exact hfinal

/-- Source acceptance is exactly acceptance by one of the finitely many pinned-first-move
functional machines. -/
public theorem Machine.accepts_iff_exists_accepts_pinFirst
    (M : Machine Γ Λ) (hlayers : M.HasTwoMatchingStepPartition)
    {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    Accepts M ⟨M.initial, tape⟩ ↔
      ∃ first : Λ × Γ × DLBA.Dir,
        Accepts (M.pinFirst first) (M.pinFirstBootCfg tape) := by
  rcases hlayers with ⟨layer, cover, _sub, biUnique, short⟩
  constructor
  · rintro ⟨target, hreach, hfinal⟩
    by_cases hinitial : M.accept M.initial = true
    · let first : Λ × Γ × DLBA.Dir := (M.initial, tape.read, .stay)
      exact ⟨first, M.pinFirstBootCfg tape, .refl, hinitial⟩
    · rcases ReflTransGen.cases_head hreach with heq | ⟨middle, hfirst, htail⟩
      · subst target
        exact False.elim (hinitial hfinal)
      · rcases hfirst with ⟨nextState, write, direction, henabled, hmiddle⟩
        have hfirstOld : Step M ⟨M.initial, tape⟩ middle :=
          ⟨nextState, write, direction, henabled, hmiddle⟩
        let first : Λ × Γ × DLBA.Dir := (nextState, write, direction)
        have hboot : Step (M.pinFirst first) (M.pinFirstBootCfg tape)
            (M.pinFirstRunCfg middle) := by
          subst middle
          exact M.step_pinFirst_boot tape first henabled
        have hrun : Reaches (M.pinFirst first) (M.pinFirstRunCfg middle)
            (M.pinFirstRunCfg target) :=
          M.reaches_pinFirst_run_of_reaches_of_incoming first
            (cover n) (biUnique n) (short n) hfirstOld htail
        refine ⟨first, M.pinFirstRunCfg target,
          ReflTransGen.head hboot hrun, ?_⟩
        exact hfinal
  · rintro ⟨first, haccept⟩
    exact M.accepts_of_accepts_pinFirst first tape haccept

/-- Canonical endmarker language membership is the finite union of the pinned functional
presentations. -/
public theorem Machine.languageEnd_pinFirst_iff
    {T : Type*} (M : Machine (EndAlpha T Γ) Λ)
    (hlayers : M.HasTwoMatchingStepPartition) (input : List T) :
    LanguageEnd M input ↔
      ∃ first : Λ × EndAlpha T Γ × DLBA.Dir,
        LanguageEnd (M.pinFirst first) input := by
  exact M.accepts_iff_exists_accepts_pinFirst hlayers (loadEnd input)

/-- Pinning preserves global configuration acyclicity because every positive pinned path
projects edge-for-edge to a positive source path. -/
public theorem Machine.configurationAcyclic_pinFirst
    (M : Machine Γ Λ) (hacyclic : M.ConfigurationAcyclic)
    (first : Λ × Γ × DLBA.Dir) :
    (M.pinFirst first).ConfigurationAcyclic := by
  intro n cfg hcycle
  exact hacyclic n (M.pinFirstProjectCfg cfg)
    (M.transGen_pinFirst_project first hcycle)

/-- From every pinned configuration, global acyclicity and finiteness provide a reachable
configuration with no outgoing step. -/
public theorem Machine.exists_reachable_sink_pinFirst
    (M : Machine Γ Λ) [Fintype Γ] [Fintype Λ]
    (hacyclic : M.ConfigurationAcyclic)
    (first : Λ × Γ × DLBA.Dir) {n : ℕ}
    (source : DLBA.Cfg Γ (FirstMoveState Λ) n) :
    ∃ target, Reaches (M.pinFirst first) source target ∧
      ∀ next, ¬ Step (M.pinFirst first) target next := by
  exact FiniteAcyclicRank.exists_reachable_sink
    ((M.configurationAcyclic_pinFirst hacyclic first) n) source

/-- If a pinned acyclic computation cannot accept, it reaches a rejecting dead end. -/
public theorem Machine.exists_reachable_rejecting_sink_pinFirst
    (M : Machine Γ Λ) [Fintype Γ] [Fintype Λ]
    (hacyclic : M.ConfigurationAcyclic)
    (first : Λ × Γ × DLBA.Dir) {n : ℕ}
    (source : DLBA.Cfg Γ (FirstMoveState Λ) n)
    (hreject : ¬ Accepts (M.pinFirst first) source) :
    ∃ target, Reaches (M.pinFirst first) source target ∧
      (M.pinFirst first).accept target.state = false ∧
      ∀ next, ¬ Step (M.pinFirst first) target next := by
  obtain ⟨target, hreach, hsink⟩ :=
    M.exists_reachable_sink_pinFirst hacyclic first source
  have hnot : (M.pinFirst first).accept target.state ≠ true := by
    intro hfinal
    exact hreject ⟨target, hreach, hfinal⟩
  exact ⟨target, hreach, Bool.eq_false_of_not_eq_true hnot, hsink⟩

end LBA

end
