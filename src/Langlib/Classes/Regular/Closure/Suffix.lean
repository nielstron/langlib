module

public import Langlib.Utilities.LanguageOperations
import Langlib.Classes.Regular.Examples.AnBn
import Langlib.Classes.Regular.Closure.Complement
import Langlib.Classes.Regular.Closure.Prefix
import Langlib.Classes.Regular.Examples.TopBot
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
import Mathlib.Computability.NFA
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.ENatToNat
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

/-! # Regular Closure Under Suffix

Proof idea: reduce suffix closure to prefix closure by reversing twice. A suffix
of a word in `L` reverses to a prefix of a word in `L.reverse`, and regular
languages are closed under both reverse and prefix.
-/

@[expose]
public section



/-! # Regular Closure Under Suffix

This file proves that regular languages are closed under the suffix operation,
via the decomposition `suffixLang L = reverse(prefixLang(reverse L))`, and
shows that the converse fails over any nontrivial alphabet.

## Strategy

We use the identity `suffixLang L = (prefixLang L.reverse).reverse`
(proved in `LanguageOperations.lean` as `suffixLang_eq_reverse_prefixLang_reverse`),
together with the already-established closure of regular languages under:
- reversal (`Language.isRegular_reverse_iff'`), and
- prefix (`Language.IsRegular.prefixLang`).

## Main declarations

- `Language.IsRegular.suffixLang`
- `Language.not_iff_regular_suffix`
-/

namespace Language

variable {α : Type*}

/-- Regular languages are closed under the suffix operation. -/
theorem IsRegular.suffixLang {L : Language α} (h : L.IsRegular) :
    (suffixLang L).IsRegular := by
  rw [suffixLang_eq_reverse_prefixLang_reverse]
  exact (h.reverse.prefixLang).reverse

private lemma map_anbn_compl_not_isRegular {T : Type*} {f : Bool → T}
    (hf : Function.Injective f) : ¬ (Language.map f anbn)ᶜ.IsRegular := by
  intro h
  exact map_anbn_not_isRegular hf (Language.isRegular_compl_iff.mp h)

/-- No word of the form `[f true] ++ w` belongs to the injective image of `anbn`. -/
private lemma true_image_prepend_not_mem_map_anbn {T : Type*} {f : Bool → T}
    (hf : Function.Injective f) (w : List T) :
    [f true] ++ w ∉ Language.map f anbn := by
  rintro ⟨u, ⟨n, rfl⟩, hmap⟩
  cases n with
  | zero =>
      simp at hmap
  | succ n =>
      have hhead := congr_arg List.head? hmap
      have hne : f false ≠ f true := by
        intro h
        have hft : false = true := hf h
        cases hft
      simp [List.map_append, List.replicate] at hhead
      exact hne hhead

/-- `suffixLang((map f anbn)ᶜ) = ⊤` for injective two-symbol codings. -/
private lemma suffixLang_map_anbn_compl_eq_top {T : Type*} {f : Bool → T}
    (hf : Function.Injective f) :
    suffixLang (Language.map f anbn)ᶜ = ⊤ := by
  ext w
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨[f true], true_image_prepend_not_mem_map_anbn hf w⟩

/-- The converse of suffix closure fails over any nontrivial alphabet. -/
theorem not_iff_regular_suffix [Nontrivial α] :
    ¬ (∀ (L : Language α), (suffixLang L).IsRegular ↔ L.IsRegular) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  let f : Bool → α := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  have hsuff : (suffixLang (Language.map f anbn)ᶜ).IsRegular := by
    rw [suffixLang_map_anbn_compl_eq_top hf]
    exact isRegular_top
  exact map_anbn_compl_not_isRegular hf ((h (Language.map f anbn)ᶜ).mp hsuff)

end Language
