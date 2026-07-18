module

public import Langlib.Automata.LinearBounded.BoundedNondeterminism
public import Langlib.Automata.LinearBounded.ThreeMatchingDiamondBranches
import Mathlib.Tactic

@[expose]
public section

/-!
# Exact branch-choice cost of the split diamond chain

The split `k`-diamond graph is presented as a `FiniteChoiceGraph` by using its three matching
colors as choice names.  Its generated edge relation is exactly the existing split-diamond edge
relation, so this is the same finite acyclic exact-three-matching witness rather than a new graph.

A natural-valued progress invariant then counts genuine branch events.  Deterministic stretches
preserve progress, while taking an edge from a genuine branch raises progress by exactly one.
Consequently every branch trace, and every bounded replay trace, from the designated source to
the designated target contains exactly `k` choices.  For the predicate accepting only that
target, bounded-choice acceptance is therefore equivalent to `k ≤ budget`, including when
either number is zero.

This is a lower bound for this particular finite-choice presentation.  It is not a language
lower bound and does not exclude a different presentation or an algorithm which recomputes
choices instead of recording this path's branch schedule.
-/

open Classical Relation

namespace FiniteChoiceGraph

variable {V Choice : Type*} (G : FiniteChoiceGraph V Choice)

private theorem progress_eq_of_deterministicPath
    (progress : V → ℕ)
    (hstep : ∀ {old new}, G.DeterministicStep old new →
      progress old = progress new)
    {source target : V}
    (path : ReflTransGen G.DeterministicStep source target) :
    progress source = progress target := by
  induction path with
  | refl => rfl
  | tail _ hlast ih => exact ih.trans (hstep hlast)

/-- A progress measure which is unchanged by deterministic steps and rises once at each genuine
branch computes the exact number of choices in every branch trace. -/
public theorem BranchTrace.length_add_progress_eq
    (progress : V → ℕ)
    (hdeterministic : ∀ {old new}, G.DeterministicStep old new →
      progress old = progress new)
    (hbranch : ∀ {old new : V} {choice : Choice},
      G.Branching old → G.next old choice = some new →
        progress new = progress old + 1)
    {choices : List Choice} {source target : V}
    (trace : G.BranchTrace choices source target) :
    choices.length + progress source = progress target := by
  induction trace with
  | finish path =>
      simpa using progress_eq_of_deterministicPath G progress hdeterministic path
  | @branch source junction next target choice choices path isBranch take rest ih =>
      have hprefix : progress source = progress junction :=
        progress_eq_of_deterministicPath G progress hdeterministic path
      have htaken : progress next = progress junction + 1 :=
        hbranch isBranch take
      simp only [List.length_cons]
      omega

/-- The same progress invariant computes the exact choice count of a bounded replay trace. -/
public theorem ReplayTrace.length_add_progress_eq
    [Fintype V]
    (progress : V → ℕ)
    (hdeterministic : ∀ {old new}, G.DeterministicStep old new →
      progress old = progress new)
    (hbranch : ∀ {old new : V} {choice : Choice},
      G.Branching old → G.next old choice = some new →
        progress new = progress old + 1)
    {choices : List Choice} {source target : V}
    (trace : G.ReplayTrace choices source target) :
    choices.length + progress source = progress target :=
  BranchTrace.length_add_progress_eq G progress hdeterministic hbranch
    (G.branchTrace_of_replayTrace trace)

end FiniteChoiceGraph

namespace ThreeMatchingDiamondChoiceLowerBound

open ThreeMatchingDiamondBranches

/-! ## The three-layer finite-choice presentation -/

/-- Use each of the three matching colors as a local choice name.  Since a matching layer is
functional, a color and source determine at most one target. -/
public noncomputable def choiceGraph (k : ℕ) :
    FiniteChoiceGraph (Vertex k) (Fin 3) where
  next source color :=
    if h : ∃ target, Layer k color source target
      then some (Classical.choose h)
      else none

/-- Looking up one matching color succeeds exactly on the corresponding layer edge. -/
public theorem choiceGraph_next_eq_some_iff
    {k : ℕ} {source target : Vertex k} {color : Fin 3} :
    (choiceGraph k).next source color = some target ↔
      Layer k color source target := by
  classical
  simp only [choiceGraph]
  split
  case isTrue h =>
    constructor
    · intro heq
      have hchosen : Classical.choose h = target := Option.some.inj heq
      rw [← hchosen]
      exact Classical.choose_spec h
    · intro hlayer
      apply congrArg some
      exact (layer_biUnique k color).2 (Classical.choose_spec h) hlayer
  case isFalse h =>
    constructor
    · simp
    · intro hlayer
      exact False.elim (h ⟨target, hlayer⟩)

/-- The choices generate exactly the pre-existing split-diamond edge relation. -/
public theorem choiceGraph_edge_iff
    (k : ℕ) (source target : Vertex k) :
    (choiceGraph k).Edge source target ↔ Edge k source target := by
  constructor
  · rintro ⟨color, hnext⟩
    exact layer_sub_edge k color source target
      (choiceGraph_next_eq_some_iff.mp hnext)
  · intro hedge
    obtain ⟨color, hlayer, _⟩ :=
      (edge_iff_existsUnique_layer k source target).mp hedge
    exact ⟨color, choiceGraph_next_eq_some_iff.mpr hlayer⟩

/-- Genuine branches in the choice presentation are exactly the named junction-output copies. -/
public theorem choiceGraph_branching_iff_exists_branchJunction
    {k : ℕ} {vertex : Vertex k} :
    (choiceGraph k).Branching vertex ↔
      ∃ i : Fin k, vertex = branchJunction i := by
  simpa only [FiniteChoiceGraph.Branching, choiceGraph_edge_iff,
    ThreeMatchingReachability.Branches] using
    (branches_iff_exists_branchJunction (k := k) (vertex := vertex))

/-! ## Exact progress of branch traces -/

/-- Number of already-passed diamonds at an unsplit vertex. -/
@[expose]
public def oldProgress {k : ℕ} : DiamondPaths.Vertex k → ℕ
  | .inl junction => junction.val
  | .inr (diamond, _) => diamond.val + 1

/-- Splitting a vertex does not change how many diamonds have been passed. -/
@[expose]
public def progress {k : ℕ} : Vertex k → ℕ
  | .input vertex => oldProgress vertex
  | .output vertex => oldProgress vertex

@[simp]
public theorem progress_source (k : ℕ) : progress (source k) = 0 := by
  rfl

@[simp]
public theorem progress_target (k : ℕ) : progress (target k) = k := by
  simp [target, DiamondPaths.target, DiamondPaths.junction, progress, oldProgress]

@[simp]
public theorem progress_branchJunction {k : ℕ} (i : Fin k) :
    progress (branchJunction i) = i.val := by
  rfl

@[simp]
public theorem progress_branchChild {k : ℕ} (i : Fin k) (bit : Bool) :
    progress (branchChild i bit) = i.val + 1 := by
  rfl

/-- Every edge out of a nonbranching vertex preserves diamond progress. -/
public theorem progress_eq_of_edge_of_not_branching
    {k : ℕ} {old new : Vertex k}
    (hedge : (choiceGraph k).Edge old new)
    (hnot : ¬ (choiceGraph k).Branching old) :
    progress old = progress new := by
  have hsplit : Edge k old new := (choiceGraph_edge_iff k old new).mp hedge
  rcases old with old | old
  · rcases new with new | new
    · exact False.elim hsplit
    · change old = new at hsplit
      subst new
      rfl
  · rcases new with new | new
    · change DiamondPaths.Edge k old new at hsplit
      rcases old with oldJunction | ⟨oldDiamond, oldBit⟩
      · rcases new with newJunction | ⟨newDiamond, newBit⟩
        · exact False.elim hsplit
        · apply False.elim
          apply hnot
          apply choiceGraph_branching_iff_exists_branchJunction.mpr
          refine ⟨newDiamond, ?_⟩
          simp only [branchJunction, DiamondPaths.junction]
          exact congrArg ThreeMatchingReachability.Vertex.output
            (congrArg Sum.inl hsplit)
      · rcases new with newJunction | ⟨newDiamond, newBit⟩
        · change newJunction = oldDiamond.succ at hsplit
          subst newJunction
          simp [progress, oldProgress]
        · exact False.elim hsplit
    · exact False.elim hsplit

/-- Every edge chosen at a genuine branch raises diamond progress by exactly one. -/
public theorem progress_eq_succ_of_next_of_branching
    {k : ℕ} {old new : Vertex k} {color : Fin 3}
    (hbranch : (choiceGraph k).Branching old)
    (hnext : (choiceGraph k).next old color = some new) :
    progress new = progress old + 1 := by
  obtain ⟨i, rfl⟩ :=
    choiceGraph_branching_iff_exists_branchJunction.mp hbranch
  have hedge : Edge k (branchJunction i) new :=
    (choiceGraph_edge_iff k (branchJunction i) new).mp ⟨color, hnext⟩
  rcases new with new | new
  · change DiamondPaths.Edge k (DiamondPaths.junction i.castSucc) new at hedge
    rcases new with newJunction | ⟨newDiamond, newBit⟩
    · exact False.elim hedge
    · change i.castSucc = newDiamond.castSucc at hedge
      have hindex : i = newDiamond := Fin.castSucc_inj.mp hedge
      subst newDiamond
      simp [progress, oldProgress, branchJunction, DiamondPaths.junction]
  · exact False.elim hedge

/-- Every deterministic step of the choice graph preserves diamond progress. -/
public theorem progress_eq_of_deterministicStep
    {k : ℕ} {old new : Vertex k}
    (hstep : (choiceGraph k).DeterministicStep old new) :
    progress old = progress new :=
  progress_eq_of_edge_of_not_branching hstep.1 hstep.2

/-- Every branch trace from the designated source to the target contains exactly one choice per
diamond. -/
public theorem branchTrace_length_eq
    {k : ℕ} {choices : List (Fin 3)}
    (trace : (choiceGraph k).BranchTrace choices (source k) (target k)) :
    choices.length = k := by
  have hprogress := FiniteChoiceGraph.BranchTrace.length_add_progress_eq
    (choiceGraph k) progress progress_eq_of_deterministicStep
      progress_eq_succ_of_next_of_branching trace
  simpa using hprogress

/-- Every bounded replay trace from the designated source to the target also contains exactly
one choice per diamond. -/
public theorem replayTrace_length_eq
    {k : ℕ} {choices : List (Fin 3)}
    (trace : (choiceGraph k).ReplayTrace choices (source k) (target k)) :
    choices.length = k := by
  have hprogress := FiniteChoiceGraph.ReplayTrace.length_add_progress_eq
    (choiceGraph k) progress progress_eq_of_deterministicStep
      progress_eq_succ_of_next_of_branching trace
  simpa using hprogress

/-! ## Exact bounded-choice threshold and retained matching structure -/

/-- Accept only the designated target. -/
@[expose]
public def acceptTarget (k : ℕ) (vertex : Vertex k) : Bool :=
  decide (vertex = target k)

@[simp]
public theorem acceptTarget_eq_true_iff {k : ℕ} {vertex : Vertex k} :
    acceptTarget k vertex = true ↔ vertex = target k := by
  simp [acceptTarget]

/-- Reaching the target with a bounded replay schedule is possible exactly when the budget can
hold all `k` genuine branch events. -/
public theorem acceptsWithChoices_acceptTarget_iff
    (k budget : ℕ) :
    (choiceGraph k).AcceptsWithChoices (acceptTarget k) (source k) budget ↔
      k ≤ budget := by
  constructor
  · rintro ⟨schedule, final, trace, hfinal⟩
    have htarget : final = target k := acceptTarget_eq_true_iff.mp hfinal
    subst final
    have hlength : schedule.toList.length = k := replayTrace_length_eq trace
    rw [← hlength, schedule.length_toList]
    exact Nat.le_of_lt_succ schedule.1.isLt
  · intro hbudget
    have hreach : ReflTransGen (choiceGraph k).Edge (source k) (target k) :=
      ReflTransGen.mono
        (fun old new hedge ↦ (choiceGraph_edge_iff k old new).mpr hedge)
        (source_reaches_target k)
    obtain ⟨choices, trace⟩ :=
      ((choiceGraph k).reaches_iff_exists_replayTrace (source k) (target k)).mp hreach
    have hlength : choices.length = k := replayTrace_length_eq trace
    have hchoices : choices.length ≤ budget := by omega
    let schedule : FiniteChoiceGraph.Schedule (Fin 3) budget :=
      FiniteChoiceGraph.Schedule.ofList choices hchoices
    refine ⟨schedule, target k, ?_, by simp⟩
    simpa [schedule] using trace

/-- The finite-choice presentation retains the existing acyclic exact-three-matching witness,
including the same three layers and designated source-to-target reachability. -/
public theorem choiceGraph_exactThreeMatching_structure (k : ℕ) :
    (∀ vertex, ¬ TransGen (choiceGraph k).Edge vertex vertex) ∧
      (∀ old new, (choiceGraph k).Edge old new ↔
        ∃! color, Layer k color old new) ∧
      (∀ color old new, Layer k color old new →
        (choiceGraph k).Edge old new) ∧
      (∀ color, Relator.BiUnique (Layer k color)) ∧
      (∀ color,
        LinearTwoDiforestReachability.PathLengthAtMostOne (Layer k color)) ∧
      ReflTransGen (choiceGraph k).Edge (source k) (target k) := by
  refine ⟨?_, ?_, ?_, layer_biUnique k, layer_pathLengthAtMostOne k, ?_⟩
  · intro vertex hcycle
    apply acyclic k vertex
    exact hcycle.mono fun old new hedge ↦
      (choiceGraph_edge_iff k old new).mp hedge
  · intro old new
    rw [choiceGraph_edge_iff]
    exact edge_iff_existsUnique_layer k old new
  · intro color old new hlayer
    exact (choiceGraph_edge_iff k old new).mpr
      (layer_sub_edge k color old new hlayer)
  · exact ReflTransGen.mono
      (fun old new hedge ↦ (choiceGraph_edge_iff k old new).mpr hedge)
      (source_reaches_target k)

end ThreeMatchingDiamondChoiceLowerBound

end
