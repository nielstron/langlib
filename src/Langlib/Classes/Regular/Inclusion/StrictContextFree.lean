module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Classes.Regular.Definition
public import Mathlib.Computability.DFA
import Langlib.Automata.FiniteState.Equivalence.Regular
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Classes.ContextFree.Examples.AnBn
import Langlib.Classes.Regular.Examples.AnBn
import Langlib.Classes.Regular.Closure.Bijection
import Langlib.Classes.Regular.Inclusion.ContextFree
import Langlib.Grammars.ContextFree.MathlibCFG
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
@[expose]
public section



/-! # RG ⊊ CF

This file uses the example language `{aⁿbⁿ}` to show that regular languages
form a strict subclass of context-free languages.

## Main results

- `exists_CF_not_regular` — There exists a CF language over `Bool` that is not regular.
- `exists_CF_not_regular_of_nontrivial` — There exists a CF nonregular language over any
  nontrivial alphabet.
- `RG_strict_subclass_CF` — Right-regular languages form a strict subclass of CF languages.
-/

open Language List

/-- There exists a context-free language that is not regular. -/
theorem exists_CF_not_regular : ∃ L : Language Bool, is_CF L ∧ ¬ L.IsRegular :=
  ⟨anbn, anbn_is_CF, anbn_not_isRegular⟩

private theorem map_anbn_is_CF {T : Type} (f : Bool → T) : is_CF (Language.map f anbn) := by
  have hsubst : is_CF (anbn.subst (fun x => ({[f x]} : Language T))) := by
    apply CF_of_subst_CF anbn
    · exact anbn_is_CF
    · intro x
      rw [is_CF_iff_isContextFree]
      exact isContextFree_singleton [f x]
  simpa [Language.subst_singletons_eq_map] using hsubst

/-- There exists a context-free nonregular language over any nontrivial alphabet. -/
theorem exists_CF_not_regular_of_nontrivial {T : Type} [Nontrivial T] :
    ∃ L : Language T, is_CF L ∧ ¬ L.IsRegular := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  let f : Bool → T := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  exact ⟨Language.map f anbn, map_anbn_is_CF f, map_anbn_not_isRegular hf⟩

/-- Right-regular languages form a strict subclass of context-free languages over any nontrivial alphabet. -/
theorem RG_strict_subclass_CF [Nontrivial T] :
  (RG : Set (Language T)) ⊂ (CF : Set (Language T)) := by
  refine ⟨RG_subclass_CF, ?_⟩
  · intro hCFsubsetRG
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    let f : Bool → T := fun x => if x then b else a
    have hf : Function.Injective f := by
      intro x y hxy
      cases x <;> cases y <;> try rfl
      · simp [f] at hxy
        exact False.elim (hab hxy)
      · simp [f] at hxy
        exact False.elim (hab hxy.symm)
    have hRG : Language.map f anbn ∈ (RG : Set (Language T)) :=
      hCFsubsetRG (a := Language.map f anbn) (map_anbn_is_CF f)
    have hreg : (Language.map f anbn).IsRegular := isRegular_of_is_RG hRG
    exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf hreg)
