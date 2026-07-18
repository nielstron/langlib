module

public import Langlib.Automata.LinearBounded.HistoryUnfolding
public import Langlib.Automata.LinearBounded.ScheduleCapacity
public import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

@[expose]
public section

/-!
# Diamond paths occupy exponentially many rooted histories

The finite rooted-history unfolding retains complete path information.  On the chain of `k`
diamonds, every explicit source-to-target path therefore determines a distinct history.  Hence
the history type has at least `2 ^ k` elements, and literally encoding every history as one
fixed-width row is subject to the same elementary capacity bound.

These statements concern injective materialization of every history vertex.  They are not a
lower bound for deterministic LBA simulation: a simulation can carry additional finite control,
recompute information, or avoid representing all unfolded histories as simultaneous row values.
-/

namespace HistoryDiamondCapacity

open HistoryUnfolding

/-! ## Retaining an explicit diamond path -/

/-- The two noninitial vertices visited in one diamond: the selected branch, followed by the
next junction. -/
@[expose]
public def visitBlocks {k : ℕ} (path : DiamondPaths.STPath k) : List (List (DiamondPaths.Vertex k)) :=
  List.ofFn fun i : Fin k => [path.branchAt i, path.junctionAt i.succ]

/-- The noninitial vertices of an explicit diamond path, in chronological order. -/
@[expose]
public def visits {k : ℕ} (path : DiamondPaths.STPath k) : List (DiamondPaths.Vertex k) :=
  (visitBlocks path).flatten

private def flattenPairs {X : Type*} (pairs : List (X × X)) : List X :=
  pairs.flatMap fun pair => [pair.1, pair.2]

private theorem flattenPairs_injective {X : Type*} :
    Function.Injective (flattenPairs : List (X × X) → List X) := by
  intro left
  induction left with
  | nil =>
      intro right heq
      cases right with
      | nil => rfl
      | cons pair rest => simp [flattenPairs] at heq
  | cons pair rest ih =>
      intro right heq
      cases right with
      | nil => simp [flattenPairs] at heq
      | cons other others =>
          simp only [flattenPairs, List.flatMap_cons, List.cons_append,
            List.nil_append, List.cons.injEq] at heq
          obtain ⟨hfirst, hsecond, hrest⟩ := heq
          have hpair : pair = other := Prod.ext hfirst hsecond
          subst other
          rw [ih hrest]

private def visitPairs {k : ℕ} (path : DiamondPaths.STPath k) :
    List (DiamondPaths.Vertex k × DiamondPaths.Vertex k) :=
  List.ofFn fun i : Fin k => (path.branchAt i, path.junctionAt i.succ)

private theorem visits_eq_flattenPairs {k : ℕ} (path : DiamondPaths.STPath k) :
    visits path = flattenPairs (visitPairs path) := by
  simp only [visits, visitBlocks, visitPairs, flattenPairs, List.flatMap,
    List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rfl

private theorem visitBlocks_nonempty {k : ℕ} (path : DiamondPaths.STPath k) :
    [] ∉ visitBlocks path := by
  simp [visitBlocks]

/-- The retained chronological vertex list follows diamond edges from the source. -/
public theorem visits_isChain {k : ℕ} (path : DiamondPaths.STPath k) :
    List.IsChain (DiamondPaths.Edge k) (DiamondPaths.source k :: visits path) := by
  have hflatten : List.IsChain (DiamondPaths.Edge k) (visits path) := by
    rw [visits, List.isChain_flatten (visitBlocks_nonempty path)]
    constructor
    · intro block hblock
      simp only [visitBlocks, List.mem_ofFn] at hblock
      obtain ⟨i, rfl⟩ := hblock
      simpa using path.leave i
    · rw [visitBlocks, List.isChain_ofFn]
      intro i hi
      let next : Fin k := ⟨i + 1, hi⟩
      simpa [next] using path.enter next
  rw [List.isChain_cons]
  refine ⟨?_, hflatten⟩
  cases k with
  | zero => simp [visits, visitBlocks]
  | succ k =>
      intro first hfirst
      have henter := path.enter (0 : Fin (k + 1))
      have hsource :
          path.junctionAt (Fin.castSucc (0 : Fin (k + 1))) =
            DiamondPaths.source (k + 1) := by
        simpa using path.source_eq
      rw [hsource] at henter
      have hhead :
          (visits path).head? = some (path.branchAt (0 : Fin (k + 1))) := by
        simp [visits, visitBlocks, List.ofFn_succ]
      rw [hhead] at hfirst
      simp only [Option.mem_some_iff] at hfirst
      subst first
      exact henter

/-- Regard an explicit source-to-target diamond path as ordinary list-based path data. -/
@[expose]
public def pathData {k : ℕ} (path : DiamondPaths.STPath k) :
    RelationalRun.PathData (DiamondPaths.Edge k) (DiamondPaths.source k) where
  visits := visits path
  isChain := visits_isChain path

/-- Retain the complete explicit diamond path as a duplicate-free rooted history. -/
@[expose]
public def historyOfPath {k : ℕ} (path : DiamondPaths.STPath k) :
    History (DiamondPaths.Edge k) (DiamondPaths.source k) :=
  History.ofPath (DiamondPaths.acyclic k) (pathData path)

@[simp]
public theorem historyOfPath_visits {k : ℕ} (path : DiamondPaths.STPath k) :
    (historyOfPath path).visits = visits path := rfl

/-- Retaining an explicit path as a rooted history is faithful: histories ending at the same
target remain distinct when their branch choices differ. -/
public theorem historyOfPath_injective (k : ℕ) :
    Function.Injective (@historyOfPath k) := by
  intro left right heq
  have hvisits : visits left = visits right :=
    congrArg History.visits heq
  rw [visits_eq_flattenPairs left, visits_eq_flattenPairs right] at hvisits
  have hpairs : visitPairs left = visitPairs right :=
    flattenPairs_injective hvisits
  have hfields :
      (fun i : Fin k => (left.branchAt i, left.junctionAt i.succ)) =
        fun i : Fin k => (right.branchAt i, right.junctionAt i.succ) := by
    exact List.ofFn_injective hpairs
  apply DiamondPaths.STPath.ext_fields
  · funext i
    exact (left.junctionAt_eq i).trans (right.junctionAt_eq i).symm
  · funext i
    exact congrArg Prod.fst (congrFun hfields i)

/-! ## Cardinal and row-capacity consequences -/

/-- The rooted-history unfolding of a `k`-diamond chain contains at least the `2 ^ k`
distinct histories obtained from its complete source-to-target paths. -/
public theorem twoPow_le_card_history (k : ℕ) :
    2 ^ k ≤ Fintype.card
      (History (DiamondPaths.Edge k) (DiamondPaths.source k)) := by
  calc
    2 ^ k = Nat.card (DiamondPaths.STPath k) :=
      (DiamondPaths.card_stPaths k).symm
    _ ≤ Nat.card (History (DiamondPaths.Edge k) (DiamondPaths.source k)) :=
      Nat.card_le_card_of_injective historyOfPath (historyOfPath_injective k)
    _ = Fintype.card (History (DiamondPaths.Edge k) (DiamondPaths.source k)) :=
      Nat.card_eq_fintype_card

/-- A literal injective encoding of every diamond-chain history as one width-`width` row
requires room for at least `2 ^ k` rows.  The alphabet and both natural parameters are fully
arbitrary, so the statement includes empty alphabets and zero widths. -/
public theorem histories_le_rowCapacity_of_injective
    {A : Type*} [Fintype A] {k width : ℕ}
    (encode : History (DiamondPaths.Edge k) (DiamondPaths.source k) → Fin width → A)
    (hinjective : Function.Injective encode) :
    2 ^ k ≤ Fintype.card A ^ width := by
  apply ScheduleCapacity.diamondPaths_le_rowCapacity_of_injective
    (encode := encode ∘ historyOfPath)
  exact hinjective.comp (historyOfPath_injective k)

/-- Below the `2 ^ k` threshold, no single row can injectively materialize every rooted
history of the diamond chain. -/
public theorem not_injective_histories_of_capacity_lt
    {A : Type*} [Fintype A] {k width : ℕ}
    (hcapacity : Fintype.card A ^ width < 2 ^ k)
    (encode : History (DiamondPaths.Edge k) (DiamondPaths.source k) → Fin width → A) :
    ¬ Function.Injective encode := by
  intro hinjective
  exact (Nat.not_lt_of_ge
    (histories_le_rowCapacity_of_injective encode hinjective)) hcapacity

end HistoryDiamondCapacity

end
