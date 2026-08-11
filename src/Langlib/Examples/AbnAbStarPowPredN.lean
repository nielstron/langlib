module

public import Langlib.Examples.AbnPowM

@[expose]
public section

/-!
# The language `{a b^n (a b*)^(n-1) | n >= 1}`

Words use the binary alphabet with `false = a` and `true = b`.
Language-class membership facts live in the corresponding files under
`Langlib.Classes`.
-/

open List

/-- A sequence of `a b*` blocks whose individual `b`-run lengths are listed in `ns`. -/
public def varyingBlocks : List Nat → List Bool
  | [] => []
  | n :: ns => abBlock n ++ varyingBlocks ns

/-- The language `{a b^n (a b*)^(n-1) | n >= 1}`. -/
public def abnAbStarPowPredN : Language Bool := fun w =>
  ∃ n : Nat, ∃ ns : List Nat,
    0 < n ∧ ns.length + 1 = n ∧ w = abBlock n ++ varyingBlocks ns

@[simp] lemma varyingBlocks_append (xs ys : List Nat) :
    varyingBlocks (xs ++ ys) = varyingBlocks xs ++ varyingBlocks ys := by
  induction xs with
  | nil => simp [varyingBlocks]
  | cons x xs ih => simp [varyingBlocks, ih, List.append_assoc]

@[simp] lemma count_false_varyingBlocks (ns : List Nat) :
    (varyingBlocks ns).count false = ns.length := by
  induction ns with
  | nil => simp [varyingBlocks]
  | cons n ns ih => simp [varyingBlocks, ih, Nat.add_comm]

@[simp] lemma varyingBlocks_replicate (n m : Nat) :
    varyingBlocks (replicate m n) = blockPower n m := by
  induction m with
  | zero => simp [varyingBlocks, blockPower]
  | succ m ih => simp [replicate_succ, varyingBlocks, blockPower, ih]

