module

public import Mathlib.Computability.Language

@[expose]
public section

/-!
# The language `{(a b^n)^m | n,m >= 1}`

Words use the binary alphabet with `false = a` and `true = b`.
Language-class membership facts live in the corresponding files under
`Langlib.Classes`.
-/

open List

/-- The binary block `a b^n`, with `false = a` and `true = b`. -/
public def abBlock (n : Nat) : List Bool :=
  false :: replicate n true

/-- `m` copies of the same block `a b^n`. -/
public def blockPower (n : Nat) : Nat → List Bool
  | 0 => []
  | m + 1 => abBlock n ++ blockPower n m

/-- The language `{(a b^n)^m | n,m >= 1}`. -/
public def abnPowM : Language Bool := fun w =>
  ∃ n m : Nat, 0 < n ∧ 0 < m ∧ w = blockPower n m

@[simp] lemma blockPower_zero (n : Nat) : blockPower n 0 = [] := rfl

@[simp] lemma blockPower_succ (n m : Nat) :
    blockPower n (m + 1) = abBlock n ++ blockPower n m := rfl

lemma blockPower_add (n m k : Nat) :
    blockPower n (m + k) = blockPower n m ++ blockPower n k := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_add, blockPower, ih, List.append_assoc]

@[simp] lemma count_false_abBlock (n : Nat) : (abBlock n).count false = 1 := by
  have hrep : (replicate n true).count false = 0 := by
    induction n with
    | zero => simp
    | succ n ih => simp [replicate_succ, ih]
  simp [abBlock, hrep]

@[simp] lemma count_false_blockPower (n m : Nat) :
    (blockPower n m).count false = m := by
  induction m with
  | zero => simp
  | succ m ih => simp [blockPower, ih, Nat.add_comm]

