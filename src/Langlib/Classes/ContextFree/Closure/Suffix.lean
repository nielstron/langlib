module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Utilities.LanguageOperations
public import Mathlib.Computability.ContextFreeGrammar
import Langlib.Classes.ContextFree.Closure.Prefix
import Langlib.Classes.ContextFree.Closure.Reverse
import Langlib.Grammars.ContextFree.EquivMathlibCFG
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

/-! # Context-Free Closure Under Suffix
This file proves that context-free languages are closed under the suffix operation,
via the decomposition `suffixLang L = reverse(prefixLang(reverse L))`.
## Strategy
We use the identity `suffixLang L = (prefixLang L.reverse).reverse`
(proved in `LanguageOperations.lean` as `suffixLang_eq_reverse_prefixLang_reverse`),
together with the already-established closure of context-free languages under:
- reversal (`CF_of_reverse_CF`, `CF_of_reverse_CF_rev`), and
- prefix (`is_CF_prefixLang`).
## Main declarations
- `is_CF_suffixLang`
- `Language.IsContextFree.suffixLang`
-/

variable {T : Type} [Fintype T]
/-- Context-free languages are closed under the suffix operation
(project-level `is_CF` formulation).
The proof decomposes suffix as `reverse ∘ prefix ∘ reverse`:
  `suffixLang L = (prefixLang L.reverse).reverse`
and applies the known closure of CFLs under reversal and prefix. -/
theorem is_CF_suffixLang {L : Language T} (h : is_CF L) :
    is_CF (Language.suffixLang L) := by
  rw [Language.suffixLang_eq_reverse_prefixLang_reverse]
  exact CF_of_reverse_CF _ (is_CF_prefixLang (CF_of_reverse_CF L h))
/-- Context-free languages are closed under the suffix operation
(Mathlib-style `Language.IsContextFree` formulation). -/
theorem Language.IsContextFree.suffixLang {L : Language T}
    (h : L.IsContextFree) :
    (Language.suffixLang L).IsContextFree := by
  rw [← is_CF_iff_isContextFree] at h ⊢
  exact is_CF_suffixLang h
