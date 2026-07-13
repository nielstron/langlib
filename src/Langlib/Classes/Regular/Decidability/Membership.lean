module

public import Mathlib.Computability.DFA
public import Mathlib.Computability.Halting
public import Langlib.Classes.Regular.Decidability.Helper
public import Langlib.Classes.Regular.Decidability.Characterization
public import Langlib.Classes.ContextFree.Decidability.Membership
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
@[expose]
public section



/-! # Computability of Membership

This file proves that membership is computable for
regular languages, using `ComputablePred` rather than the weaker `Decidable`.

## Main results

- `dfa_membership_computablePred` – membership in a DFA's language is a computable predicate
- `regular_membership_computablePred` – membership in a regular language is a computable predicate
- `regular_computableMembership` – membership is *uniformly* computable for encoded
  right-regular grammars (`ComputableMembership`)
-/

open List Relation

/-! ## Part 1: Regular Languages -/

section Regular

variable {α σ : Type*}

/-- Membership in a DFA's accepted language is a computable predicate.

The proof constructs the computable decision function explicitly as the
composition of `M.eval` (which is `List.foldl M.step M.start`, primitive
recursive by `Primrec.list_foldl` since `M.step` is a function from a
finite domain) with the accept-state test (primitive recursive by
`Primrec.dom_finite`). -/
theorem dfa_membership_computablePred [Primcodable α] [Primcodable σ]
    [Finite σ] [Finite α]
    (M : DFA α σ) [DecidablePred (· ∈ M.accept)] :
    ComputablePred (· ∈ M.accepts) := by
  show ComputablePred (fun w => M.eval w ∈ M.accept)
  have h_eval_comp : Computable M.eval := by
    show Computable (fun w => List.foldl M.step M.start w)
    exact (Primrec.list_foldl Primrec.id (Primrec.const M.start)
      (((Primrec.dom_finite (fun (p : σ × α) => M.step p.1 p.2)).comp
        Primrec.snd).to₂)).to_comp
  have h_dec : Computable (fun s : σ => decide (s ∈ M.accept)) :=
    (Primrec.dom_finite _).to_comp
  exact ⟨inferInstance, h_dec.comp h_eval_comp⟩

/-- Membership in a regular language is a computable predicate. -/
noncomputable def regular_membership_computablePred
    [Primcodable α] [Finite α]
    (L : Language α) (hL : L.IsRegular) :
    ComputablePred (· ∈ L) := by
  classical
  obtain ⟨σ, hσ⟩ := hL
  obtain ⟨hfin, hσ'⟩ := hσ
  obtain ⟨M, hM⟩ := hσ'
  rw [← hM]
  letI : Primcodable σ :=
    Primcodable.ofEquiv (Fin (Fintype.card σ)) (Fintype.equivFin σ)
  exact dfa_membership_computablePred M

end Regular

/-! ## Part 2: Uniform computability over encoded right-regular grammars -/

namespace Regular.EncodedRG

/-- The raw uniform membership decider for encoded right-regular grammars, obtained by
composing the context-free membership decider with the primitive-recursive translation
`toCFG : EncodedRG T → EncodedCFG T`. -/
public theorem regular_membership_computablePred [Fintype T] [DecidableEq T] [Primcodable T] :
    ComputablePred (fun p : EncodedRG T × List T => p.2 ∈ regularLanguageOf p.1) := by
  obtain ⟨f, hf_comp, hf_eq⟩ :=
    ComputablePred.computable_iff.mp (contextFree_membership_computablePred (T := T))
  rw [ComputablePred.computable_iff]
  refine ⟨fun p => f (toCFG p.1, p.2), ?_, ?_⟩
  · exact hf_comp.comp
      (Primrec.to_comp (Primrec.pair (toCFG_primrec.comp Primrec.fst) Primrec.snd))
  · funext p
    have h := congrFun hf_eq (toCFG p.1, p.2)
    simpa [regularLanguageOf] using h

/-- **Membership is uniformly computable** for the regular languages: encoded
right-regular grammars are an adequate, effective presentation
(`regularLanguageOf_characterizes`) with uniformly decidable membership. -/
public theorem regular_computableMembership [Fintype T] [DecidableEq T] [Primcodable T] :
    ComputableMembership RG (regularLanguageOf : EncodedRG T → Language T) :=
  ⟨regularLanguageOf_characterizes.onTrue, regular_membership_computablePred.to_re,
    ComputablePredOnPromise.ofComputablePred regular_membership_computablePred⟩

end Regular.EncodedRG
