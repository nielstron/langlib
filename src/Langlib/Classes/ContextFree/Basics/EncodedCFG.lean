module

public import Langlib.Grammars.ContextFree.Definition
public import Mathlib.Computability.Primrec.List
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-! # Encoded Context-Free Grammars and Uniform Computability of Emptiness

This file introduces a concrete encoded representation of context-free grammars
(`EncodedCFG`) that is `Primcodable`, enabling a genuine uniform computability
theorem for CFG emptiness where the grammar itself is the argument.

## Encoding

An `EncodedCFG T` is a triple `(numNT, initial, rules)` where:
- `numNT : ℕ` — the number of nonterminals minus one (the actual nonterminal type
  is `Fin (numNT + 1)`, ensuring it is always nonempty)
- `initial : ℕ` — index of the initial nonterminal (taken mod `numNT + 1`)
- `rules : List (ℕ × List (ℕ ⊕ T))` — production rules, where `Sum.inl k` represents
  nonterminal `k % (numNT + 1)` and `Sum.inr t` represents terminal `t`

The underlying type is `ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))`, which inherits `Primcodable`
from the standard Mathlib instances for products, sums, lists, and `ℕ` (plus
`Primcodable T`). It is `Primcodable` because each component is: `ℕ` has
`Primcodable.nat`, `⊕` has `Primcodable.sum`, `List` has `Primcodable.list`,
and `×` has `Primcodable.prod`.

## Main results

- `EncodedCFG` — the encoded grammar type
- `EncodedCFG.toCFGrammar` — translation to the project's `CF_grammar T`
-/

/-! ## The Encoded Grammar Type -/

/-- An encoded context-free grammar over terminal alphabet `T`. -/
def EncodedCFG (T : Type) := ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))

namespace EncodedCFG

variable {T : Type}

instance [Primcodable T] : Primcodable (EncodedCFG T) :=
  inferInstanceAs (Primcodable (ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))))

instance [DecidableEq T] : DecidableEq (EncodedCFG T) :=
  @instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance inferInstance)

def numNT (G : EncodedCFG T) : ℕ := G.1
def initialIdx (G : EncodedCFG T) : ℕ := G.2.1
def rawRules (G : EncodedCFG T) : List (ℕ × List (ℕ ⊕ T)) := G.2.2
def ntCount (G : EncodedCFG T) : ℕ := G.numNT + 1

lemma ntCount_pos (G : EncodedCFG T) : 0 < G.ntCount := by
  unfold ntCount numNT; omega

def toNT (G : EncodedCFG T) (k : ℕ) : Fin G.ntCount :=
  ⟨k % G.ntCount, Nat.mod_lt k G.ntCount_pos⟩

def toSymbol (G : EncodedCFG T) : ℕ ⊕ T → symbol T (Fin G.ntCount)
  | .inl k => symbol.nonterminal (G.toNT k)
  | .inr t => symbol.terminal t

def toCFGrammar (G : EncodedCFG T) : CF_grammar T :=
  { nt := Fin G.ntCount
    initial := G.toNT G.initialIdx
    rules := G.rawRules.map fun (lhs, rhs) =>
      (G.toNT lhs, rhs.map G.toSymbol) }

instance (G : EncodedCFG T) : Fintype (G.toCFGrammar).nt :=
  inferInstanceAs (Fintype (Fin G.ntCount))

instance (G : EncodedCFG T) : DecidableEq (G.toCFGrammar).nt :=
  inferInstanceAs (DecidableEq (Fin G.ntCount))

end EncodedCFG
