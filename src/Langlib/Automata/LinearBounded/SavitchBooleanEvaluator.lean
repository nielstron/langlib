module

public import Langlib.Automata.LinearBounded.SavitchReachability
public import Mathlib.Data.FinEnum
import Mathlib.Tactic

@[expose]
public section

/-!
# An executable and instrumented Savitch midpoint search

`savitchEval` is a Boolean implementation of the midpoint recurrence.  Its
second component counts invocations of the depth-recursive evaluator; calls
skipped by conjunction or midpoint short-circuiting are not counted.  The
count therefore describes the control flow of this implementation rather
than a syntactic expansion of the recurrence.

The empty relation on two distinct vertices is an order-independent worst
case for the relevant lower bound.  Every midpoint is scanned.  A midpoint
different from the source makes the left recursive call false; the source
midpoint makes the left call true and forces the same false pair on the right.
Thus a false query at depth `d` makes at least `|V| ^ d` recursive calls.  On
`|V| = 2 ^ n` vertices and depth `n = log₂ |V|`, this lower bound is
`2 ^ (n * n)` calls.  It is a lower bound for this evaluator, not for directed
reachability in general.
-/

namespace SavitchBooleanEvaluator

open Relation
open SavitchReachability

variable {V : Type*}

/-- Scan an explicitly ordered midpoint list.  The Boolean component is the
short-circuiting disjunction of short-circuiting pairs of recursive queries.
The natural-number component counts the recursive evaluator calls that were
actually demanded.  Scanning overhead itself is not counted. -/
public def midpointScan (recur : V → V → Bool × ℕ) :
    List V → V → V → Bool × ℕ
  | [], _, _ => (false, 0)
  | middle :: rest, source, target =>
      let left := recur source middle
      match left.1 with
      | false =>
          let tail := midpointScan recur rest source target
          (tail.1, left.2 + tail.2)
      | true =>
          let right := recur middle target
          match right.1 with
          | true => (true, left.2 + right.2)
          | false =>
              let tail := midpointScan recur rest source target
              (tail.1, left.2 + right.2 + tail.2)

/-- The instrumented Boolean midpoint evaluator.  Depth zero tests equality
or one edge.  At positive depth it scans `vertices` in the supplied order. -/
public def savitchEval [DecidableEq V] (edge : V → V → Bool)
    (vertices : List V) : ℕ → V → V → Bool × ℕ
  | 0, source, target =>
      (decide (source = target) || edge source target, 1)
  | depth + 1, source, target =>
      let result := midpointScan (savitchEval edge vertices depth)
        vertices source target
      (result.1, result.2 + 1)

/-- The executable Boolean answer returned by `savitchEval`. -/
public def savitchBool [DecidableEq V] (edge : V → V → Bool)
    (vertices : List V) (depth : ℕ) (source target : V) : Bool :=
  (savitchEval edge vertices depth source target).1

/-- The exact Boolean semantics of the explicit midpoint scan. -/
public theorem midpointScan_value_eq_any (recur : V → V → Bool × ℕ)
    (vertices : List V) (source target : V) :
    (midpointScan recur vertices source target).1 =
      vertices.any fun middle =>
        (recur source middle).1 && (recur middle target).1 := by
  induction vertices with
  | nil => rfl
  | cons middle rest ih =>
      simp only [List.any_cons]
      cases hleft : (recur source middle).1 <;>
        cases hright : (recur middle target).1 <;>
        simp [midpointScan, hleft, hright, ih]

/-- The scan succeeds exactly when one listed midpoint makes both recursive
queries succeed. -/
public theorem midpointScan_value_eq_true_iff
    (recur : V → V → Bool × ℕ) (vertices : List V)
    (source target : V) :
    (midpointScan recur vertices source target).1 = true ↔
      ∃ middle ∈ vertices,
        (recur source middle).1 = true ∧
        (recur middle target).1 = true := by
  rw [midpointScan_value_eq_any, List.any_eq_true]
  simp only [Bool.and_eq_true]

/-- Correctness of the executable evaluator for every explicit midpoint list
that contains every vertex. -/
public theorem savitchBool_eq_true_iff [DecidableEq V]
    (edge : V → V → Bool) (vertices : List V)
    (hcover : ∀ vertex : V, vertex ∈ vertices)
    (depth : ℕ) (source target : V) :
    savitchBool edge vertices depth source target = true ↔
      SavitchReach (fun old new => edge old new = true)
        depth source target := by
  induction depth generalizing source target with
  | zero =>
      simp [savitchBool, savitchEval, Bool.or_eq_true]
  | succ depth ih =>
      rw [savitchReach_succ]
      simp only [savitchBool, savitchEval]
      rw [midpointScan_value_eq_true_iff]
      constructor
      · rintro ⟨middle, _, hleft, hright⟩
        exact ⟨middle,
          (ih (source := source) (target := middle)).1 hleft,
          (ih (source := middle) (target := target)).1 hright⟩
      · rintro ⟨middle, hleft, hright⟩
        exact ⟨middle, hcover middle,
          (ih (source := source) (target := middle)).2 hleft,
          (ih (source := middle) (target := target)).2 hright⟩

/-- Canonical executable midpoint order supplied by `FinEnum`. -/
public def finiteSavitchEval [FinEnum V]
    (edge : V → V → Bool) (depth : ℕ) (source target : V) : Bool × ℕ :=
  savitchEval edge (FinEnum.toList V) depth source target

/-- Boolean projection of the canonical finite evaluator. -/
public def finiteSavitchBool [FinEnum V]
    (edge : V → V → Bool) (depth : ℕ) (source target : V) : Bool :=
  (finiteSavitchEval edge depth source target).1

/-- The finite Boolean enumerator decides the propositional midpoint
recurrence. -/
public theorem finiteSavitchBool_eq_true_iff [FinEnum V]
    (edge : V → V → Bool) (depth : ℕ) (source target : V) :
    finiteSavitchBool edge depth source target = true ↔
      SavitchReach (fun old new => edge old new = true)
        depth source target := by
  apply savitchBool_eq_true_iff
  simp

/-- At saturated depth, the finite Boolean enumerator decides ordinary
directed reachability. -/
public theorem finiteSavitchBool_clog_eq_true_iff
    [FinEnum V]
    (edge : V → V → Bool) (source target : V) :
    finiteSavitchBool edge (Nat.clog 2 (Fintype.card V)) source target = true ↔
      ReflTransGen (fun old new => edge old new = true) source target := by
  rw [finiteSavitchBool_eq_true_iff]
  exact (reaches_iff_savitchReach_clog
    (fun old new => edge old new = true) source target).symm

public def emptyEdge : V → V → Bool := fun _ _ => false

/-- With no edges, the evaluator returns true exactly on equal endpoints.
This theorem includes positive depths and therefore records that the supplied
midpoint list covers the vertex type. -/
public theorem savitchEval_empty_value_eq_decide [DecidableEq V]
    (vertices : List V) (hcover : ∀ vertex : V, vertex ∈ vertices)
    (depth : ℕ) (source target : V) :
    (savitchEval (emptyEdge (V := V)) vertices depth source target).1 =
      decide (source = target) := by
  change savitchBool (emptyEdge (V := V)) vertices depth source target =
    decide (source = target)
  apply Bool.eq_iff_iff.mpr
  rw [savitchBool_eq_true_iff
    (edge := emptyEdge (V := V)) (vertices := vertices) hcover]
  simp only [emptyEdge, Bool.false_eq_true, SavitchReachability.savitchReach_iff_paddedPath]
  have emptyPath_eq :
      ∀ {steps : ℕ} {old new : V},
        FiniteReachabilityCounting.PaddedPath
          (fun _ _ : V => False) old steps new → old = new := by
    intro steps old new hpath
    induction hpath with
    | zero => rfl
    | @succ _ middle new _ hstep ih =>
        rcases hstep with h | h
        · exact ih.trans h
        · contradiction
  constructor
  · intro hpath
    simpa using emptyPath_eq hpath
  · intro heq
    have : source = target := of_decide_eq_true heq
    subst target
    exact SavitchReachability.PaddedPath.mono
      FiniteReachabilityCounting.PaddedPath.zero (Nat.zero_le _)

/-- On a false empty-edge query, scanning any sublist incurs at least one
depth-`d` false recursive query per listed midpoint.  At the source midpoint
that query occurs on the right; at every other midpoint it occurs on the
left.  This is the step that accounts for conjunction short-circuiting. -/
private theorem midpointScan_empty_false_calls_ge [DecidableEq V]
    (vertices rest : List V) (hcover : ∀ vertex : V, vertex ∈ vertices)
    (depth lower : ℕ)
    (hlower : ∀ old new : V, old ≠ new →
      lower ≤ (savitchEval (emptyEdge (V := V)) vertices depth old new).2)
    (source target : V) (hne : source ≠ target) :
    rest.length * lower ≤
      (midpointScan
        (savitchEval (emptyEdge (V := V)) vertices depth)
        rest source target).2 := by
  induction rest with
  | nil => simp [midpointScan]
  | cons middle rest ih =>
      by_cases hm : source = middle
      · subst middle
        have hleft :
            (savitchEval (emptyEdge (V := V)) vertices depth source source).1 = true := by
          rw [savitchEval_empty_value_eq_decide vertices hcover]
          simp
        have hright :
            (savitchEval (emptyEdge (V := V)) vertices depth source target).1 = false := by
          rw [savitchEval_empty_value_eq_decide vertices hcover]
          simp [hne]
        have hcall := hlower source target hne
        calc
          (source :: rest).length * lower =
              lower + rest.length * lower := by
            rw [List.length_cons, Nat.add_mul, one_mul, Nat.add_comm]
          _ ≤ (savitchEval (emptyEdge (V := V)) vertices depth source target).2 +
                (midpointScan
                  (savitchEval (emptyEdge (V := V)) vertices depth)
                  rest source target).2 :=
            Nat.add_le_add hcall ih
          _ ≤ (savitchEval (emptyEdge (V := V)) vertices depth source source).2 +
                (savitchEval (emptyEdge (V := V)) vertices depth source target).2 +
                (midpointScan
                  (savitchEval (emptyEdge (V := V)) vertices depth)
                  rest source target).2 := by omega
          _ = (midpointScan
                (savitchEval (emptyEdge (V := V)) vertices depth)
                (source :: rest) source target).2 := by
            simp [midpointScan, hleft, hright]
      · have hleft :
            (savitchEval (emptyEdge (V := V)) vertices depth source middle).1 = false := by
          rw [savitchEval_empty_value_eq_decide vertices hcover]
          simp [hm]
        have hcall := hlower source middle hm
        calc
          (middle :: rest).length * lower =
              lower + rest.length * lower := by
            rw [List.length_cons, Nat.add_mul, one_mul, Nat.add_comm]
          _ ≤ (savitchEval (emptyEdge (V := V)) vertices depth source middle).2 +
                (midpointScan
                  (savitchEval (emptyEdge (V := V)) vertices depth)
                  rest source target).2 :=
            Nat.add_le_add hcall ih
          _ = (midpointScan
                (savitchEval (emptyEdge (V := V)) vertices depth)
                (middle :: rest) source target).2 := by
            simp [midpointScan, hleft]

/-- For the explicit short-circuiting evaluator, the empty relation and a
false query force at least `vertices.length ^ depth` recursive calls,
independently of the enumeration order. -/
public theorem savitchEval_empty_false_calls_ge_pow [DecidableEq V]
    (vertices : List V) (hcover : ∀ vertex : V, vertex ∈ vertices)
    (depth : ℕ) (source target : V) (hne : source ≠ target) :
    vertices.length ^ depth ≤
      (savitchEval (emptyEdge (V := V)) vertices depth source target).2 := by
  induction depth generalizing source target with
  | zero => simp [savitchEval]
  | succ depth ih =>
      have hscan := midpointScan_empty_false_calls_ge
        vertices vertices hcover depth (vertices.length ^ depth)
        (fun old new hne' => ih old new hne') source target hne
      change vertices.length ^ (depth + 1) ≤
        (midpointScan
          (savitchEval (emptyEdge (V := V)) vertices depth)
          vertices source target).2 + 1
      calc
        vertices.length ^ (depth + 1) =
            vertices.length * vertices.length ^ depth := by
          rw [Nat.pow_succ, Nat.mul_comm]
        _ ≤ (midpointScan
              (savitchEval (emptyEdge (V := V)) vertices depth)
              vertices source target).2 := hscan
        _ ≤ _ := Nat.le_add_right _ _

/-- Canonical finite specialization of the order-independent empty-relation
lower bound. -/
public theorem finiteSavitchEval_empty_false_calls_ge_card_pow
    [FinEnum V]
    (depth : ℕ) (source target : V) (hne : source ≠ target) :
    FinEnum.card V ^ depth ≤
      (finiteSavitchEval (emptyEdge (V := V)) depth source target).2 := by
  simpa [finiteSavitchEval, FinEnum.toList] using
    savitchEval_empty_false_calls_ge_pow
      (V := V) (FinEnum.toList V) FinEnum.mem_toList
        depth source target hne

/-- On exactly `2 ^ n` numbered vertices, logarithmic recursion depth `n`
forces at least `2 ^ (n * n)` calls for every false empty-edge query. -/
public theorem finPow_empty_false_calls_ge_square
    (n : ℕ) (source target : Fin (2 ^ n)) (hne : source ≠ target) :
    2 ^ (n * n) ≤
      (finiteSavitchEval (emptyEdge (V := Fin (2 ^ n)))
        n source target).2 := by
  simpa [Nat.pow_mul] using
    finiteSavitchEval_empty_false_calls_ge_card_pow n source target hne

/-- The same concrete family eventually exceeds every fixed polynomial
degree in `N = 2 ^ n`.  The hypothesis `degree < n` is exactly what is needed
to compare `N ^ degree` with the checked `N ^ n` call lower bound. -/
public theorem finPow_empty_false_calls_superpolynomial
    (n degree : ℕ) (hn : n ≠ 0) (hdegree : degree < n)
    (source target : Fin (2 ^ n)) (hne : source ≠ target) :
    (2 ^ n) ^ degree <
      (finiteSavitchEval (emptyEdge (V := Fin (2 ^ n)))
        n source target).2 := by
  have hstrict : (2 ^ n) ^ degree < (2 ^ n) ^ n :=
    Nat.pow_lt_pow_right (Nat.one_lt_two_pow hn) hdegree
  have hwork := finPow_empty_false_calls_ge_square n source target hne
  rw [Nat.pow_mul] at hwork
  omega

/-- The first endpoint in the fully concrete worst-case family. -/
public def finPowSource (n : ℕ) : Fin (2 ^ n) :=
  ⟨0, Nat.two_pow_pos n⟩

/-- The distinct second endpoint, available for every positive logarithmic
depth. -/
public def finPowTarget (n : ℕ) (hn : n ≠ 0) : Fin (2 ^ n) :=
  ⟨1, Nat.one_lt_two_pow hn⟩

public theorem finPowSource_ne_finPowTarget (n : ℕ) (hn : n ≠ 0) :
    finPowSource n ≠ finPowTarget n hn := by
  intro h
  have hval := congrArg Fin.val h
  simp [finPowSource, finPowTarget] at hval

/-- A completely specified order-independent witness: the empty Boolean
edge relation, `FinEnum`'s numbered order on `Fin (2 ^ n)`, and endpoints
zero and one.  For every fixed degree below the logarithmic depth, its actual
instrumented evaluation uses more than `N ^ degree` recursive calls. -/
public theorem concrete_empty_evaluation_superpolynomial
    (n degree : ℕ) (hn : n ≠ 0) (hdegree : degree < n) :
    (2 ^ n) ^ degree <
      (finiteSavitchEval (emptyEdge (V := Fin (2 ^ n)))
        n (finPowSource n) (finPowTarget n hn)).2 :=
  finPow_empty_false_calls_superpolynomial n degree hn hdegree
    (finPowSource n) (finPowTarget n hn)
    (finPowSource_ne_finPowTarget n hn)

end SavitchBooleanEvaluator
