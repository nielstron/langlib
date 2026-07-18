module

public import Langlib.Automata.LinearBounded.ScheduleCapacity
public import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

@[expose]
public section

/-!
# Capacity barriers for literal Savitch simulation

The standard deterministic reachability recursion retains a stack of continuation frames.  If
each frame can independently name one of `|Frame|` values, a depth-`depth` stack has
`|Frame| ^ depth` values.  An injective materialization of every such stack in one width-`width`
row therefore requires at least that many rows.  In particular, a depth-`n` stack of width-`n`
configurations over a fixed source alphabet has `|SourceCell| ^ (n * n)` possible values.

Discarding the stack and literally recomputing the resulting traversal has a separate finite-
state obstruction.  Along an orbit of a deterministic transition function, all states through
the first visit to a target are distinct.  Thus a first hit after `steps` transitions requires
strictly more than `steps` states.  A deterministic machine whose complete configurations fit
in one fixed-width row can consequently make fewer than `|Cell| ^ width` transitions before a
first target hit.

These are barriers only to **literal materialization or execution** of that recursive traversal.
They are not deterministic-space lower bounds: an algorithm may avoid representing arbitrary
independent stacks or reorganize the search so that it does not execute the full traversal.
No graph-degree assumption is used.
-/

namespace SavitchRecomputationBarrier

/-! ## Literal continuation-stack capacity -/

/-- An injective encoding of every depth-`depth` stack over an arbitrary finite frame type in a
single fixed-width row forces the exact cardinal-capacity inequality.

The statement permits empty frame and row alphabets as well as zero depth and zero width. -/
public theorem frameStacks_le_rowCapacity_of_injective
    {Frame Cell : Type*} [Fintype Frame] [Fintype Cell]
    {depth width : ℕ}
    (encode : (Fin depth → Frame) → Fin width → Cell)
    (hinjective : Function.Injective encode) :
    Fintype.card Frame ^ depth ≤ Fintype.card Cell ^ width := by
  exact ScheduleCapacity.finChoiceVectors_le_rowCapacity_of_injective
    encode hinjective

/-- Below the exact capacity threshold, no single row injectively materializes every stack of
independently chosen frames. -/
public theorem not_injective_frameStacks_of_capacity_lt
    {Frame Cell : Type*} [Fintype Frame] [Fintype Cell]
    {depth width : ℕ}
    (hcapacity : Fintype.card Cell ^ width < Fintype.card Frame ^ depth)
    (encode : (Fin depth → Frame) → Fin width → Cell) :
    ¬ Function.Injective encode := by
  intro hinjective
  exact (Nat.not_lt_of_ge
    (frameStacks_le_rowCapacity_of_injective encode hinjective)) hcapacity

/-- If one continuation frame retains an arbitrary width-`configWidth` source configuration,
then a literal depth-`depth` stack has
`(|SourceCell| ^ configWidth) ^ depth` independently selectable values. -/
public theorem configurationStacks_le_rowCapacity_of_injective
    {SourceCell WorkCell : Type*} [Fintype SourceCell] [Fintype WorkCell]
    {configWidth depth workWidth : ℕ}
    (encode :
      (Fin depth → (Fin configWidth → SourceCell)) →
        Fin workWidth → WorkCell)
    (hinjective : Function.Injective encode) :
    (Fintype.card SourceCell ^ configWidth) ^ depth ≤
      Fintype.card WorkCell ^ workWidth := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    frameStacks_le_rowCapacity_of_injective encode hinjective

/-- At recursion depth equal to the source configuration width, literal stack capacity has the
quadratic exponent `configWidth * configWidth`.  This is the cardinal form of the usual
`Theta(log² N)` Savitch-stack accounting when `N` configurations have `Theta(log N)`-cell
names. -/
public theorem squareConfigurationStacks_le_rowCapacity_of_injective
    {SourceCell WorkCell : Type*} [Fintype SourceCell] [Fintype WorkCell]
    {configWidth workWidth : ℕ}
    (encode :
      (Fin configWidth → (Fin configWidth → SourceCell)) →
        Fin workWidth → WorkCell)
    (hinjective : Function.Injective encode) :
    Fintype.card SourceCell ^ (configWidth * configWidth) ≤
      Fintype.card WorkCell ^ workWidth := by
  simpa only [pow_mul] using
    configurationStacks_le_rowCapacity_of_injective encode hinjective

/-- If the work row has less capacity than the quadratic family of source-configuration stacks,
no literal injective same-row representation exists.  This is an encoding obstruction, not a
simulation lower bound. -/
public theorem not_injective_squareConfigurationStacks_of_capacity_lt
    {SourceCell WorkCell : Type*} [Fintype SourceCell] [Fintype WorkCell]
    {configWidth workWidth : ℕ}
    (hcapacity :
      Fintype.card WorkCell ^ workWidth <
        Fintype.card SourceCell ^ (configWidth * configWidth))
    (encode :
      (Fin configWidth → (Fin configWidth → SourceCell)) →
        Fin workWidth → WorkCell) :
    ¬ Function.Injective encode := by
  intro hinjective
  exact (Nat.not_lt_of_ge
    (squareConfigurationStacks_le_rowCapacity_of_injective encode hinjective))
    hcapacity

/-- For every fixed work alphabet and linear cell factor, there is an explicit width at which
the family of depth-`n` stacks of `n`-bit configurations exceeds all work rows of width
`factor * n`.

The witness `n = |WorkCell| * factor + 1` is deliberately elementary rather than asymptotically
optimized.  No nonemptiness or lower-cardinality premise is imposed on `WorkCell`. -/
public theorem binarySquare_exceeds_fixedLinearRowCapacity
    (WorkCell : Type*) [Fintype WorkCell] (factor : ℕ) :
    let n := Fintype.card WorkCell * factor + 1
    Fintype.card WorkCell ^ (factor * n) < 2 ^ (n * n) := by
  let n := Fintype.card WorkCell * factor + 1
  have hbase : Fintype.card WorkCell ≤ 2 ^ Fintype.card WorkCell :=
    Nat.le_of_lt (Fintype.card WorkCell).lt_two_pow_self
  have hn : Fintype.card WorkCell * factor < n := by
    simp [n]
  have hexponent :
      Fintype.card WorkCell * (factor * n) < n * n := by
    calc
      Fintype.card WorkCell * (factor * n) =
          (Fintype.card WorkCell * factor) * n :=
        (Nat.mul_assoc _ _ _).symm
      _ < n * n := Nat.mul_lt_mul_of_pos_right hn (by simp [n])
  calc
    Fintype.card WorkCell ^ (factor * n) ≤
        (2 ^ Fintype.card WorkCell) ^ (factor * n) :=
      Nat.pow_le_pow_left hbase _
    _ = 2 ^ (Fintype.card WorkCell * (factor * n)) := by
      exact (pow_mul 2 (Fintype.card WorkCell) (factor * n)).symm
    _ < 2 ^ (n * n) :=
      Nat.pow_lt_pow_right (by omega) hexponent

/-- Hence no fixed target alphabet and fixed linear width factor can literally inject every
depth-`n` stack of `n`-bit configurations into its work row uniformly at every width: the theorem
supplies one explicit failing width.  This is the precise capacity mismatch `2^(n²)` versus
`|WorkCell|^(factor*n)`. -/
public theorem exists_no_injective_binarySquareStacks_fixedLinear
    (WorkCell : Type*) [Fintype WorkCell] (factor : ℕ) :
    ∃ n : ℕ,
      ∀ encode :
        (Fin n → (Fin n → Bool)) → Fin (factor * n) → WorkCell,
        ¬ Function.Injective encode := by
  let n := Fintype.card WorkCell * factor + 1
  refine ⟨n, ?_⟩
  intro encode
  apply not_injective_squareConfigurationStacks_of_capacity_lt
    (encode := encode)
  simpa only [Fintype.card_bool] using
    binarySquare_exceeds_fixedLinearRowCapacity WorkCell factor

/-! ## First target hits in finite deterministic state spaces -/

/-- The state reached after exactly `steps` iterations of a deterministic transition
function. -/
@[expose]
public def orbit {State : Type*} (step : State → State) (source : State)
    (steps : ℕ) : State :=
  step^[steps] source

@[simp]
public theorem orbit_zero {State : Type*} (step : State → State)
    (source : State) :
    orbit step source 0 = source := by
  simp [orbit]

/-- Iterating from a state already reached after `right` steps agrees with iterating for the
sum of the two step counts. -/
public theorem orbit_add {State : Type*} (step : State → State)
    (source : State) (left right : ℕ) :
    orbit step source (left + right) =
      step^[left] (orbit step source right) := by
  exact Function.iterate_add_apply step left right source

/-- Every state up to and including the first point satisfying an arbitrary predicate is
distinct.

This is the automaton-facing form of the finite-orbit argument: `accepting` may describe an
entire set of accepting configurations, and its members need not be fixed points or terminal. -/
public theorem orbitPrefix_injective_of_firstSatisfying
    {State : Type*} (step : State → State) (source : State)
    (accepting : State → Prop) {steps : ℕ}
    (haccept : accepting (orbit step source steps))
    (hfirst : ∀ k < steps, ¬ accepting (orbit step source k)) :
    Function.Injective
      (fun time : Fin (steps + 1) ↦ orbit step source time.val) := by
  have noCollision {early late : ℕ} (hlt : early < late)
      (hlate : late ≤ steps) :
      orbit step source early ≠ orbit step source late := by
    intro heq
    let remaining := steps - late
    have hlateRemaining : late + remaining = steps := by
      dsimp only [remaining]
      omega
    have hearlyRemaining : early + remaining < steps := by
      omega
    apply hfirst (early + remaining) hearlyRemaining
    rw [show orbit step source (early + remaining) =
        orbit step source steps by
      calc
        orbit step source (early + remaining) =
            step^[remaining] (orbit step source early) := by
          rw [Nat.add_comm]
          exact orbit_add step source remaining early
        _ = step^[remaining] (orbit step source late) :=
          congrArg (step^[remaining]) heq
        _ = orbit step source (late + remaining) := by
          rw [Nat.add_comm]
          exact (orbit_add step source remaining late).symm
        _ = orbit step source steps := by rw [hlateRemaining]]
    exact haccept
  intro left right heq
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact noCollision hlt (Nat.le_of_lt_succ right.isLt) heq
  · exact noCollision hgt (Nat.le_of_lt_succ left.isLt) heq.symm

/-- A first visit to any state satisfying a predicate occurs strictly before the cardinality of
the finite deterministic state space. -/
public theorem firstSatisfying_steps_lt_card
    {State : Type*} [Fintype State]
    (step : State → State) (source : State) (accepting : State → Prop)
    {steps : ℕ}
    (haccept : accepting (orbit step source steps))
    (hfirst : ∀ k < steps, ¬ accepting (orbit step source k)) :
    steps < Fintype.card State := by
  have hcard :
      Fintype.card (Fin (steps + 1)) ≤ Fintype.card State :=
    Fintype.card_le_of_injective _
      (orbitPrefix_injective_of_firstSatisfying
        step source accepting haccept hfirst)
  simpa only [Fintype.card_fin] using hcard

/-- If complete deterministic states inject into fixed-width rows, the first visit to an
arbitrary accepting set occurs before the row capacity.  The state type may include finite
control, head data, or any other information retained by the supplied injection. -/
public theorem firstSatisfying_steps_lt_rowCapacity_of_injective
    {State Cell : Type*} [Fintype State] [Fintype Cell]
    {width steps : ℕ}
    (encode : State → Fin width → Cell)
    (hinjective : Function.Injective encode)
    (step : State → State) (source : State) (accepting : State → Prop)
    (haccept : accepting (orbit step source steps))
    (hfirst : ∀ k < steps, ¬ accepting (orbit step source k)) :
    steps < Fintype.card Cell ^ width := by
  exact (firstSatisfying_steps_lt_card
    step source accepting haccept hfirst).trans_le
      (ScheduleCapacity.card_le_rowCapacity_of_injective encode hinjective)

/-- Every state up to and including the first visit to a designated target is distinct.

This is a first-*target* theorem, not a halting assertion: `target` need not be a fixed point or
have no outgoing transition.  The only premise is that its occurrence at `steps` is the first
one on this particular orbit. -/
public theorem orbitPrefix_injective_of_firstHit
    {State : Type*} (step : State → State) (source target : State)
    {steps : ℕ}
    (hhit : orbit step source steps = target)
    (hfirst : ∀ k < steps, orbit step source k ≠ target) :
    Function.Injective
      (fun time : Fin (steps + 1) ↦ orbit step source time.val) := by
  exact orbitPrefix_injective_of_firstSatisfying
    step source (fun state ↦ state = target) hhit hfirst

/-- A first visit to a target in a finite deterministic state space occurs strictly before the
number of available states. -/
public theorem firstHit_steps_lt_card
    {State : Type*} [Fintype State]
    (step : State → State) (source target : State) {steps : ℕ}
    (hhit : orbit step source steps = target)
    (hfirst : ∀ k < steps, orbit step source k ≠ target) :
    steps < Fintype.card State := by
  exact firstSatisfying_steps_lt_card
    step source (fun state ↦ state = target) hhit hfirst

/-- If the complete states of a deterministic computation inject into fixed-width rows, a first
target hit occurs before the row capacity.  Unlike the following specialization, this theorem
allows the state type to carry arbitrary finite control as long as the supplied row encoding is
injective. -/
public theorem firstHit_steps_lt_rowCapacity_of_injective
    {State Cell : Type*} [Fintype State] [Fintype Cell]
    {width steps : ℕ}
    (encode : State → Fin width → Cell)
    (hinjective : Function.Injective encode)
    (step : State → State) (source target : State)
    (hhit : orbit step source steps = target)
    (hfirst : ∀ k < steps, orbit step source k ≠ target) :
    steps < Fintype.card Cell ^ width := by
  exact (firstHit_steps_lt_card step source target hhit hfirst).trans_le
    (ScheduleCapacity.card_le_rowCapacity_of_injective encode hinjective)

/-- Specializing the finite state space to width-`width` rows gives the exact first-hit time
capacity.  The cell alphabet and width are arbitrary, including the empty and zero cases whenever
a source row exists. -/
public theorem firstHit_rowOrbit_steps_lt_capacity
    {Cell : Type*} [Fintype Cell] {width steps : ℕ}
    (step : (Fin width → Cell) → (Fin width → Cell))
    (source target : Fin width → Cell)
    (hhit : orbit step source steps = target)
    (hfirst : ∀ k < steps, orbit step source k ≠ target) :
    steps < Fintype.card Cell ^ width := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    firstHit_steps_lt_card step source target hhit hfirst

/-- If a proposed literal deterministic row traversal has at least as many transitions before
its first target as there are row states, its specification is impossible. -/
public theorem no_firstHit_rowOrbit_of_capacity_le
    {Cell : Type*} [Fintype Cell] {width steps : ℕ}
    (hcapacity : Fintype.card Cell ^ width ≤ steps)
    (step : (Fin width → Cell) → (Fin width → Cell))
    (source target : Fin width → Cell) :
    ¬ (orbit step source steps = target ∧
      ∀ k < steps, orbit step source k ≠ target) := by
  rintro ⟨hhit, hfirst⟩
  exact (Nat.not_lt_of_ge hcapacity)
    (firstHit_rowOrbit_steps_lt_capacity step source target hhit hfirst)

/-- At the same explicit width used by the stack-capacity theorem, no deterministic work-row
orbit can first hit a target only after all `2^(n²)` putative traversal indices have elapsed.

This excludes executing that literal full traversal.  It says nothing about a reorganized
algorithm that reaches its answer without visiting one state per traversal index. -/
public theorem exists_no_binarySquare_firstHit_fixedLinear
    (WorkCell : Type*) [Fintype WorkCell] (factor : ℕ) :
    ∃ n : ℕ,
      ∀ (step :
          (Fin (factor * n) → WorkCell) →
            Fin (factor * n) → WorkCell)
        (source target : Fin (factor * n) → WorkCell),
        ¬ (orbit step source (2 ^ (n * n)) = target ∧
          ∀ k < 2 ^ (n * n), orbit step source k ≠ target) := by
  let n := Fintype.card WorkCell * factor + 1
  refine ⟨n, ?_⟩
  intro step source target
  apply no_firstHit_rowOrbit_of_capacity_le
  exact Nat.le_of_lt
    (binarySquare_exceeds_fixedLinearRowCapacity WorkCell factor)

end SavitchRecomputationBarrier

end
