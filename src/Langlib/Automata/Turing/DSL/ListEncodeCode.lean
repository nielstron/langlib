module

public import Mathlib.Computability.TMConfig
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-! # `ToPartrec.Code` for list encoding

This file isolates the Code-level part of an alternate `Code → is_TM` bridge.
Instead of asking a TM0 preprocessing machine to compute `Encodable.encode w`
from the input tape, we can compose the user code with a `ToPartrec.Code` that
computes list encoding from a variable-length `List ℕ` input.

The remaining tape-level bridge then only has to translate each finite input
symbol to a fixed chain fragment.

## Key results

- `pairCode_eval`: the `Nat.pair` helper code is correct.
- `listEncodeCode_eval`: `listEncodeCode` computes `Encodable.encode` for
  lists of natural numbers.
- `composedCode_halts_iff`: composing a user code with `listEncodeCode`
  recognizes shifted list encodings.
-/

open Turing ToPartrec

namespace Langlib.TMCodeListEncode

/-! ### Code for `Nat.pair` -/

/-- A `ToPartrec.Code` computing `Nat.pair` on two-element inputs. -/
noncomputable def pairCode : Code :=
  (Code.exists_code (n := 2) (Nat.Partrec'.prim (Nat.Primrec'.of_prim
    (Primrec₂.natPair.comp
      (Primrec.vector_get.comp .id (.const 0))
      (Primrec.vector_get.comp .id (.const 1)))))).choose

theorem pairCode_eval (a b : ℕ) :
    pairCode.eval [a, b] = Part.some [Nat.pair a b] := by
  have hExists :=
    Code.exists_code (n := 2)
      (f := fun v => pure (Nat.pair v[0]! v[1]!))
      (Nat.Partrec'.prim (Nat.Primrec'.of_prim
        (Primrec₂.natPair.comp
          (Primrec.vector_get.comp .id (.const 0))
          (Primrec.vector_get.comp .id (.const 1)))))
  convert hExists.choose_spec (List.Vector.ofFn fun i => if i = 0 then a else b)

/-! ### Code for the right-fold list encoder -/

/-- Swap the first two elements of a list. -/
noncomputable def swap12 : Code :=
  Code.cons (Code.comp Code.head Code.tail)
    (Code.cons Code.head (Code.comp Code.tail Code.tail))

theorem swap12_eval (a b : ℕ) (rest : List ℕ) :
    swap12.eval (a :: b :: rest) = Part.some (b :: a :: rest) := by
  unfold swap12
  simp [Code.head]

/-- Extract the first two elements of a list. -/
noncomputable def extract2 : Code :=
  Code.cons Code.head (Code.comp Code.head Code.tail)

theorem extract2_eval (a b : ℕ) (rest : List ℕ) :
    extract2.eval (a :: b :: rest) = Part.some [a, b] := by
  unfold extract2
  simp +decide [ToPartrec.Code.eval]

/-- One fold step: process an element and update the accumulator. -/
noncomputable def foldStep : Code :=
  Code.cons
    (Code.comp Code.succ Code.zero')
    (Code.cons
      (Code.comp Code.succ (Code.comp pairCode extract2))
      (Code.comp Code.tail Code.tail))

theorem foldStep_eval (e acc : ℕ) (rest : List ℕ) :
    foldStep.eval (e :: acc :: rest) =
    Part.some (1 :: Nat.succ (Nat.pair e acc) :: rest) := by
  unfold foldStep
  have hpair := pairCode_eval e acc
  have hextract := extract2_eval e acc rest
  simp_all +decide [Code.eval]

/-- Done case: return `[0, acc]`, so `Code.fix` terminates with `[acc]`. -/
noncomputable def foldDone : Code :=
  Code.cons Code.zero' Code.head

theorem foldDone_eval (acc : ℕ) (rest : List ℕ) :
    foldDone.eval (acc :: rest) = Part.some [0, acc] := by
  unfold foldDone
  simp +decide [ToPartrec.Code.eval]

/-- Fold body. It swaps the accumulator and next shifted input element before
case-splitting on the shifted element. -/
noncomputable def foldBody : Code :=
  Code.comp (Code.case foldDone foldStep) swap12

/-- The Code computing the list-encoding fold on shifted, reversed input. -/
noncomputable def listEncodeCode : Code :=
  Code.fix foldBody

/-- Helper fold function matching Lean's `Encodable` list encoding. -/
def foldAcc : List ℕ → ℕ → ℕ
  | [], acc => acc
  | e :: es, acc => foldAcc es (Nat.succ (Nat.pair e acc))

theorem foldAcc_append (es₁ es₂ : List ℕ) (acc : ℕ) :
    foldAcc (es₁ ++ es₂) acc = foldAcc es₂ (foldAcc es₁ acc) := by
  induction es₁ generalizing acc with
  | nil => simp [foldAcc]
  | cons e es₁ ih => simp [foldAcc, ih]

theorem foldBody_eval_zero (acc : ℕ) :
    foldBody.eval [acc, 0] = Part.some [0, acc] := by
  unfold foldBody foldDone swap12
  simp_all +decide [Code.eval]

theorem foldBody_eval_succ (e acc : ℕ) (rest : List ℕ) :
    foldBody.eval (acc :: (e + 1) :: rest) =
    Part.some (1 :: Nat.succ (Nat.pair e acc) :: rest) := by
  unfold foldBody
  simp +decide
  erw [swap12_eval]
  norm_num [foldDone_eval, foldStep_eval]

/-- `listEncodeCode` computes `foldAcc` on reversed, `+1`-shifted lists
terminated by zero. -/
theorem listEncodeCode_aux (rs : List ℕ) (acc : ℕ) :
    listEncodeCode.eval (acc :: rs.map (· + 1) ++ [0]) =
    Part.some [foldAcc rs acc] := by
  convert Part.eq_some_iff.mpr _ using 1
  induction rs generalizing acc with
  | nil =>
      simp_all +decide [listEncodeCode]
      rw [PFun.mem_fix_iff]
      rw [foldBody_eval_zero]
      norm_num [Part.map]
      exact Or.inl rfl
  | cons k l ih =>
      simp_all +decide [listEncodeCode]
      have hbody :
          foldBody.eval (acc :: (k + 1) :: (l.map (· + 1) ++ [0])) =
          Part.some (1 :: Nat.succ (Nat.pair k acc) :: (l.map (· + 1) ++ [0])) := by
        exact foldBody_eval_succ k acc (l.map (· + 1) ++ [0])
      rw [PFun.mem_fix_iff]
      rw [hbody]
      simp_all +decide [foldAcc]

/-- Folding over the reverse of a natural-number list gives Lean's list
encoding for that list. -/
theorem foldAcc_reverse_eq_encode (es : List ℕ) :
    foldAcc es.reverse 0 = Encodable.encode es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp +decide [Nat.pair]
      rw [foldAcc_append]
      aesop

theorem listEncodeCode_eval (es : List ℕ) :
    listEncodeCode.eval (0 :: es.reverse.map (· + 1) ++ [0]) =
    Part.some [Encodable.encode es] := by
  rw [← foldAcc_reverse_eq_encode]
  exact listEncodeCode_aux es.reverse 0

/-! ### Composing user code with the list encoder -/

/-- Precompose a user Code with list encoding. -/
noncomputable def composedCode (c : Code) : Code :=
  Code.comp c listEncodeCode

theorem composedCode_eval (c : Code) (w : List ℕ) :
    (composedCode c).eval (0 :: w.reverse.map (· + 1) ++ [0]) =
    c.eval [Encodable.encode w] := by
  simp only [composedCode, Code.comp_eval]
  rw [listEncodeCode_eval]
  simp [Part.bind_some]

/-- The finite-symbol-friendly input expected by `composedCode`. -/
def shiftedEncoding {T : Type} [Encodable T] (w : List T) : List ℕ :=
  0 :: (w.map Encodable.encode).reverse.map (· + 1) ++ [0]

/-- The encoding of `w : List T` equals the encoding of the list of
element-wise encodings because natural numbers encode as themselves. -/
theorem list_encode_eq {T : Type} [Encodable T] (w : List T) :
    Encodable.encode w = Encodable.encode (w.map Encodable.encode : List ℕ) := by
  induction w <;> simp_all +decide

theorem composedCode_halts_iff (c : Code) {T : Type} [Encodable T] (w : List T) :
    ((composedCode c).eval (shiftedEncoding w)).Dom ↔
    (c.eval [Encodable.encode w]).Dom := by
  unfold shiftedEncoding
  have heq := list_encode_eq w
  have h := composedCode_eval c (w.map Encodable.encode)
  rw [h, heq]

end Langlib.TMCodeListEncode
