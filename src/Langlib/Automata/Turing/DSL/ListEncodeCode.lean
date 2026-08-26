module

public import Mathlib.Computability.TuringMachine.Config
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
@[expose]
public section



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
@[expose]
public noncomputable def pairCode : Code :=
  (Code.exists_code (n := 2)
    (f := fun v => pure (Nat.pair v[0]! v[1]!))
    (Nat.Partrec'.prim (Nat.Primrec'.of_prim
    (Primrec₂.natPair.comp
      (Primrec.vector_get.comp .id (.const 0))
      (Primrec.vector_get.comp .id (.const 1)))))).choose

public theorem pairCode_eval (a b : ℕ) :
    pairCode.eval [a, b] = Part.some [Nat.pair a b] := by
  let hex :=
    Code.exists_code (n := 2)
      (f := fun v => pure (Nat.pair v[0]! v[1]!))
      (Nat.Partrec'.prim (Nat.Primrec'.of_prim
        (Primrec₂.natPair.comp
          (Primrec.vector_get.comp .id (.const 0))
          (Primrec.vector_get.comp .id (.const 1)))))
  have hcode : pairCode = hex.choose := by
    unfold pairCode hex
    congr
  rw [hcode]
  let v : List.Vector ℕ 2 := ⟨[a, b], by simp⟩
  have hv := hex.choose_spec v
  have hv_val : v.1 = [a, b] := rfl
  have hv_zero : v[0]! = a := rfl
  have hv_one : v[1]! = b := rfl
  have hpure : (pure (Nat.pair a b) : List ℕ) = [Nat.pair a b] := rfl
  simpa only [hv_val, hv_zero, hv_one, Part.map_eq_map, Part.pure_eq_some,
    Part.map_some, PFun.coe_val, hpure] using hv

/-! ### Code for the right-fold list encoder -/

/-- Swap the first two elements of a list. -/
@[expose]
public noncomputable def swap12 : Code :=
  Code.cons (Code.comp Code.head Code.tail)
    (Code.cons Code.head (Code.comp Code.tail Code.tail))

public theorem swap12_eval (a b : ℕ) (rest : List ℕ) :
    swap12.eval (a :: b :: rest) = Part.some (b :: a :: rest) := by
  unfold swap12
  simp [Code.head]

/-- Extract the first two elements of a list. -/
@[expose]
public noncomputable def extract2 : Code :=
  Code.cons Code.head (Code.comp Code.head Code.tail)

public theorem extract2_eval (a b : ℕ) (rest : List ℕ) :
    extract2.eval (a :: b :: rest) = Part.some [a, b] := by
  unfold extract2
  unfold Code.head Code.id Code.nil Code.eval
  simp

private theorem bind_eval_some (c : Code) (v : List ℕ) :
    Part.some v >>= c.eval = c.eval v := by
  exact Part.bind_some v (show List ℕ → Part (List ℕ) from c.eval)

/-- One fold step: process an element and update the accumulator. -/
@[expose]
public noncomputable def foldStep : Code :=
  Code.cons
    (Code.comp Code.succ Code.zero')
    (Code.cons
      (Code.comp Code.succ (Code.comp pairCode extract2))
      (Code.comp Code.tail Code.tail))

public theorem foldStep_eval (e acc : ℕ) (rest : List ℕ) :
    foldStep.eval (e :: acc :: rest) =
    Part.some (1 :: Nat.succ (Nat.pair e acc) :: rest) := by
  unfold foldStep
  have hpair := pairCode_eval e acc
  have hextract := extract2_eval e acc rest
  simp_all +decide [Code.eval, Part.bind_eq_bind]
  rw [bind_eval_some pairCode [e, acc], hpair]
  simp

/-- Done case: return `[0, acc]`, so `Code.fix` terminates with `[acc]`. -/
@[expose]
public noncomputable def foldDone : Code :=
  Code.cons Code.zero' Code.head

public theorem foldDone_eval (acc : ℕ) (rest : List ℕ) :
    foldDone.eval (acc :: rest) = Part.some [0, acc] := by
  unfold foldDone
  simp +decide [ToPartrec.Code.eval]

/-- Fold body. It swaps the accumulator and next shifted input element before
case-splitting on the shifted element. -/
@[expose]
public noncomputable def foldBody : Code :=
  Code.comp (Code.case foldDone foldStep) swap12

/-- The Code computing the list-encoding fold on shifted, reversed input. -/
@[expose]
public noncomputable def listEncodeCode : Code :=
  Code.fix foldBody

/-- Helper fold function matching Lean's `Encodable` list encoding. -/
@[expose]
public def foldAcc : List ℕ → ℕ → ℕ
  | [], acc => acc
  | e :: es, acc => foldAcc es (Nat.succ (Nat.pair e acc))

public theorem foldAcc_append (es₁ es₂ : List ℕ) (acc : ℕ) :
    foldAcc (es₁ ++ es₂) acc = foldAcc es₂ (foldAcc es₁ acc) := by
  induction es₁ generalizing acc with
  | nil => simp [foldAcc]
  | cons e es₁ ih => simp [foldAcc, ih]

public theorem foldBody_eval_zero (acc : ℕ) :
    foldBody.eval [acc, 0] = Part.some [0, acc] := by
  unfold foldBody foldDone swap12
  simp_all +decide [Code.head, Code.id, Code.nil, Code.eval, Part.bind_eq_bind]

public theorem foldBody_eval_succ (e acc : ℕ) (rest : List ℕ) :
    foldBody.eval (acc :: (e + 1) :: rest) =
    Part.some (1 :: Nat.succ (Nat.pair e acc) :: rest) := by
  unfold foldBody
  simp +decide
  erw [swap12_eval]
  norm_num [foldDone_eval, foldStep_eval]

private theorem mem_fix_eval_iff {f : Code} {input output : List ℕ} :
    output ∈ (Code.fix f).eval input ↔
      Sum.inl output ∈ (f.eval input).map
        (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) ∨
      ∃ next,
        Sum.inr next ∈ (f.eval input).map
          (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) ∧
        output ∈ (Code.fix f).eval next := by
  simpa only [Code.fix_eval] using
    (@PFun.mem_fix_iff (List ℕ) (List ℕ)
      (f := fun v => (f.eval v).map
        (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail))
      (a := input) (b := output))

/-- `listEncodeCode` computes `foldAcc` on reversed, `+1`-shifted lists
terminated by zero. -/
public theorem listEncodeCode_aux (rs : List ℕ) (acc : ℕ) :
    listEncodeCode.eval (acc :: rs.map (· + 1) ++ [0]) =
    Part.some [foldAcc rs acc] := by
  apply Part.eq_some_iff.mpr
  induction rs generalizing acc with
  | nil =>
      change [acc] ∈ (Code.fix foldBody).eval [acc, 0]
      rw [mem_fix_eval_iff]
      rw [foldBody_eval_zero]
      simp
  | cons k l ih =>
      change [foldAcc l (Nat.succ (Nat.pair k acc))] ∈
        (Code.fix foldBody).eval
          (acc :: (k + 1) :: (l.map (· + 1) ++ [0]))
      rw [mem_fix_eval_iff]
      rw [foldBody_eval_succ]
      refine Or.inr ⟨Nat.succ (Nat.pair k acc) :: (l.map (· + 1) ++ [0]), ?_, ?_⟩
      · simp
      · exact ih (Nat.succ (Nat.pair k acc))

/-- Folding over the reverse of a natural-number list gives Lean's list
encoding for that list. -/
public theorem foldAcc_reverse_eq_encode (es : List ℕ) :
    foldAcc es.reverse 0 = Encodable.encode es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp +decide [Nat.pair]
      rw [foldAcc_append]
      aesop

public theorem listEncodeCode_eval (es : List ℕ) :
    listEncodeCode.eval (0 :: es.reverse.map (· + 1) ++ [0]) =
    Part.some [Encodable.encode es] := by
  rw [← foldAcc_reverse_eq_encode]
  exact listEncodeCode_aux es.reverse 0

/-! ### Composing user code with the list encoder -/

/-- Precompose a user Code with list encoding. -/
@[expose]
public noncomputable def composedCode (c : Code) : Code :=
  Code.comp c listEncodeCode

private theorem comp_eval_at (f g : Code) (v : List ℕ) :
    (Code.comp f g).eval v = g.eval v >>= f.eval := by
  exact congrArg (fun p : List ℕ → Part (List ℕ) => p v) (Code.comp_eval f g)

public theorem composedCode_eval (c : Code) (w : List ℕ) :
    (composedCode c).eval (0 :: w.reverse.map (· + 1) ++ [0]) =
    c.eval [Encodable.encode w] := by
  unfold composedCode
  calc
    (Code.comp c listEncodeCode).eval (0 :: w.reverse.map (· + 1) ++ [0]) =
        listEncodeCode.eval (0 :: w.reverse.map (· + 1) ++ [0]) >>= c.eval :=
      comp_eval_at c listEncodeCode _
    _ = Part.some [Encodable.encode w] >>= c.eval := by
      exact congrArg
        (fun p : Part (List ℕ) => p >>= (show List ℕ → Part (List ℕ) from c.eval))
        (listEncodeCode_eval w)
    _ = c.eval [Encodable.encode w] := bind_eval_some c _

/-- The finite-symbol-friendly input expected by `composedCode`. -/
@[expose]
public def shiftedEncoding {T : Type} [Encodable T] (w : List T) : List ℕ :=
  0 :: (w.map Encodable.encode).reverse.map (· + 1) ++ [0]

/-- The encoding of `w : List T` equals the encoding of the list of
element-wise encodings because natural numbers encode as themselves. -/
public theorem list_encode_eq {T : Type} [Encodable T] (w : List T) :
    Encodable.encode w = Encodable.encode (w.map Encodable.encode : List ℕ) := by
  induction w <;> simp_all +decide

public theorem composedCode_halts_iff (c : Code) {T : Type} [Encodable T] (w : List T) :
    ((composedCode c).eval (shiftedEncoding w)).Dom ↔
    (c.eval [Encodable.encode w]).Dom := by
  unfold shiftedEncoding
  have heq := list_encode_eq w
  have h := composedCode_eval c (w.map Encodable.encode)
  rw [h, heq]

end Langlib.TMCodeListEncode
