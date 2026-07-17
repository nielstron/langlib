module

public import Langlib.Automata.LinearBounded.Definition
public import Langlib.Automata.LinearBounded.FiniteReachabilityCounting
import Mathlib.Tactic

@[expose]
public section

/-!
# Cofunctional linearly bounded automata

This file proves an abstract finite-graph characterization for a restricted class of LBAs.
A machine is `Cofunctional` when every bounded configuration has at most one predecessor,
uniformly over all tape lengths.  Semantically, reachability can then be characterized backwards:
start at a proposed target configuration and repeatedly follow its unique predecessor.

On a finite configuration space, at most `Fintype.card (DLBA.Cfg Γ Λ n)` predecessor
steps are needed.  Consequently, LBA acceptance is equivalent to a finite enumeration of
accepting target configurations followed by bounded, single-valued backtracking.

The `predecessor` and `backtrack` functions below are noncomputable definitions because the
machine transition relation is represented by a `Set`.  The final theorem packages the resulting
finite exhaustive search as a Boolean decision procedure: enumerate accepting targets, and for
each one follow its unique predecessor for at most the number of bounded configurations.

At the resource level this search uses linear space: a constant number of configurations and a
counter up to the configuration-space cardinality all have `O(n)`-bit encodings.  This file does
**not** yet construct that search as a concrete `DLBA.Machine`; the low-level same-tape compiler
and its simulation proof remain to be mechanized.

## Main results

* `LBA.Machine.Cofunctional` — every configuration has at most one predecessor.
* `LBA.Machine.predecessor` — the unique predecessor, when one exists.
* `LBA.Machine.backtrack` — repeated predecessor traversal.
* `LBA.Machine.reaches_iff_exists_backtrack_le_card` — reachability is abstractly characterized
  by bounded backtracking.
* `LBA.Machine.accepts_iff_exists_backtrack_le_card` — acceptance is finite target
  enumeration plus bounded backtracking.
* `LBA.Machine.acceptsByExhaustiveBacktracking` — the corresponding finite Boolean search.
* `LBA.Machine.acceptsByExhaustiveBacktracking_eq_true_iff` — correctness of that search.
-/

namespace LBA

open FiniteReachabilityCounting

variable {Γ Λ : Type*}

/-- An LBA is cofunctional when every bounded target configuration has at most one
predecessor, uniformly over all tape lengths.  Multiple transition witnesses from the same
source configuration to the same target configuration are allowed. -/
public def Machine.Cofunctional (M : Machine Γ Λ) : Prop :=
  ∀ {n : ℕ} {cfg₁ cfg₂ cfg' : DLBA.Cfg Γ Λ n},
    Step M cfg₁ cfg' → Step M cfg₂ cfg' → cfg₁ = cfg₂

/-- Choose the predecessor of `cfg`, when one exists.

Under `Machine.Cofunctional` the chosen configuration is the unique predecessor.  The
definition is noncomputable because `Machine.transition` is represented by a `Set`; with
finite tape and state alphabets, predecessor search can instead scan the finite configuration
space exhaustively. -/
public noncomputable def Machine.predecessor
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    Option (DLBA.Cfg Γ Λ n) := by
  classical
  exact if h : ∃ previous, Step M previous cfg then some (Classical.choose h) else none

/-- A configuration returned by `predecessor` really takes one machine step to the target. -/
public theorem Machine.step_of_predecessor_eq_some
    (M : Machine Γ Λ) {n : ℕ} {cfg cfg' : DLBA.Cfg Γ Λ n}
    (hpred : M.predecessor cfg' = some cfg) :
    Step M cfg cfg' := by
  simp only [Machine.predecessor] at hpred
  split at hpred
  · next h =>
      have hchosen : Classical.choose h = cfg := Option.some.inj hpred
      rw [← hchosen]
      exact Classical.choose_spec h
  · simp at hpred

/-- For a cofunctional machine, every genuine step identifies the chosen predecessor. -/
public theorem Machine.predecessor_eq_some_of_step
    (M : Machine Γ Λ) (hco : M.Cofunctional)
    {n : ℕ} {cfg cfg' : DLBA.Cfg Γ Λ n}
    (hstep : Step M cfg cfg') :
    M.predecessor cfg' = some cfg := by
  simp only [Machine.predecessor]
  split
  · next h =>
      apply congrArg some
      exact hco (Classical.choose_spec h) hstep
  · next h =>
      exact False.elim (h ⟨cfg, hstep⟩)

/-- On a cofunctional machine, predecessor lookup is exactly the one-step relation. -/
public theorem Machine.predecessor_eq_some_iff
    (M : Machine Γ Λ) (hco : M.Cofunctional)
    {n : ℕ} {cfg cfg' : DLBA.Cfg Γ Λ n} :
    M.predecessor cfg' = some cfg ↔ Step M cfg cfg' :=
  ⟨M.step_of_predecessor_eq_some, M.predecessor_eq_some_of_step hco⟩

/-- Follow `steps` predecessors backwards from `cfg`, failing if a predecessor is absent. -/
public noncomputable def Machine.backtrack
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    ℕ → Option (DLBA.Cfg Γ Λ n)
  | 0 => some cfg
  | steps + 1 => (M.predecessor cfg).bind fun previous => M.backtrack previous steps

@[simp]
public theorem Machine.backtrack_zero
    (M : Machine Γ Λ) {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    M.backtrack cfg 0 = some cfg := rfl

public theorem Machine.backtrack_succ
    (M : Machine Γ Λ) {n steps : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    M.backtrack cfg (steps + 1) =
      (M.predecessor cfg).bind fun previous => M.backtrack previous steps := rfl

/-- Every successful backward traversal reverses to a genuine forward machine run. -/
public theorem Machine.reaches_of_backtrack_eq_some
    (M : Machine Γ Λ) {n steps : ℕ}
    {source target : DLBA.Cfg Γ Λ n}
    (hback : M.backtrack target steps = some source) :
    Reaches M source target := by
  induction steps generalizing source target with
  | zero =>
      simp only [Machine.backtrack] at hback
      cases hback
      exact .refl
  | succ steps ih =>
      rw [M.backtrack_succ] at hback
      obtain ⟨previous, hpred, hrest⟩ := Option.bind_eq_some_iff.mp hback
      exact (ih hrest).tail (M.step_of_predecessor_eq_some hpred)

/-- A padded forward path through a cofunctional machine can be retraced backwards in no
more steps than its fuel bound. -/
public theorem Machine.exists_backtrack_of_paddedPath
    (M : Machine Γ Λ) (hco : M.Cofunctional)
    {n fuel : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (hpath : PaddedPath (Step M) source fuel target) :
    ∃ steps ≤ fuel, M.backtrack target steps = some source := by
  induction hpath with
  | zero =>
      exact ⟨0, Nat.zero_le 0, rfl⟩
  | @succ fuel old new hpath hmove ih =>
      obtain ⟨steps, hsteps, hback⟩ := ih
      rcases hmove with rfl | hstep
      · exact ⟨steps, hsteps.trans (Nat.le_succ fuel), hback⟩
      · refine ⟨steps + 1, Nat.succ_le_succ hsteps, ?_⟩
        rw [M.backtrack_succ, M.predecessor_eq_some_of_step hco hstep]
        exact hback

variable [Fintype Γ] [Fintype Λ] [DecidableEq Γ] [DecidableEq Λ]

/-- For a finite cofunctional LBA, forward reachability is equivalent to following
predecessors for at most the number of bounded configurations. -/
public theorem Machine.reaches_iff_exists_backtrack_le_card
    (M : Machine Γ Λ) (hco : M.Cofunctional)
    {n : ℕ} (source target : DLBA.Cfg Γ Λ n) :
    Reaches M source target ↔
      ∃ steps ≤ Fintype.card (DLBA.Cfg Γ Λ n),
        M.backtrack target steps = some source := by
  classical
  letI : DecidableRel (Step M : DLBA.Cfg Γ Λ n → DLBA.Cfg Γ Λ n → Prop) :=
    Classical.decRel _
  constructor
  · intro hreach
    have hmem :
        target ∈ reached (Step M) source (Fintype.card (DLBA.Cfg Γ Λ n)) :=
      (mem_reached_card_iff (edge := Step M) (source := source)).2 hreach
    have hpath :
        PaddedPath (Step M) source (Fintype.card (DLBA.Cfg Γ Λ n)) target :=
      (mem_reached_iff_paddedPath (edge := Step M) (source := source)).1 hmem
    exact M.exists_backtrack_of_paddedPath hco hpath
  · rintro ⟨steps, _, hback⟩
    exact M.reaches_of_backtrack_eq_some hback

/-- Acceptance by a finite cofunctional LBA is exactly the following finite enumeration
criterion: choose an accepting target configuration, then backtrack from it to the source
within the cardinality of the bounded configuration space. -/
public theorem Machine.accepts_iff_exists_backtrack_le_card
    (M : Machine Γ Λ) (hco : M.Cofunctional)
    {n : ℕ} (source : DLBA.Cfg Γ Λ n) :
    Accepts M source ↔
      ∃ target : DLBA.Cfg Γ Λ n,
        M.accept target.state = true ∧
          ∃ steps ≤ Fintype.card (DLBA.Cfg Γ Λ n),
            M.backtrack target steps = some source := by
  constructor
  · rintro ⟨target, hreach, haccept⟩
    exact ⟨target, haccept,
      (M.reaches_iff_exists_backtrack_le_card hco source target).1 hreach⟩
  · rintro ⟨target, haccept, hback⟩
    exact ⟨target,
      (M.reaches_iff_exists_backtrack_le_card hco source target).2 hback,
      haccept⟩

/-- Decide acceptance by exhaustive target enumeration and bounded predecessor traversal.

This is a deterministic finite search.  Its mathematical definition is noncomputable only because
`Machine.transition` is an arbitrary `Set`; for a concrete finite transition table, the same search
enumerates that table. -/
public noncomputable def Machine.acceptsByExhaustiveBacktracking
    (M : Machine Γ Λ) {n : ℕ} (source : DLBA.Cfg Γ Λ n) : Bool := by
  classical
  exact Finset.univ.toList.any fun target =>
    M.accept target.state &&
      (List.range (Fintype.card (DLBA.Cfg Γ Λ n) + 1)).any fun steps =>
        decide (M.backtrack target steps = some source)

/-- Exhaustive bounded backtracking decides acceptance for every finite cofunctional LBA. -/
public theorem Machine.acceptsByExhaustiveBacktracking_eq_true_iff
    (M : Machine Γ Λ) (hco : M.Cofunctional)
    {n : ℕ} (source : DLBA.Cfg Γ Λ n) :
    M.acceptsByExhaustiveBacktracking source = true ↔ Accepts M source := by
  classical
  rw [M.accepts_iff_exists_backtrack_le_card hco source]
  simp only [Machine.acceptsByExhaustiveBacktracking, List.any_eq_true,
    Finset.mem_toList, Finset.mem_univ, Bool.and_eq_true, List.mem_range,
    decide_eq_true_eq, true_and, Nat.lt_add_one_iff]

end LBA
