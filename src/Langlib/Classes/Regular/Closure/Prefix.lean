module

public import Langlib.Utilities.LanguageOperations
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Closure.Complement
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

/-! # Regular Closure Under Prefix

Proof idea: a word is a prefix of some word in `L` exactly when the DFA state
reached after reading it can still reach an accepting state. Mark those
co-reachable states as accepting in a new DFA.
-/

@[expose]
public section



/-! # Regular Closure Under Prefix

This file proves that regular languages are closed under the prefix operation
and shows that the converse fails over any nontrivial alphabet.

## Main declarations

- `DFA.reachableAccept`
- `DFA.prefixDFA`
- `Language.IsRegular.prefixLang`
- `Language.not_iff_regular_prefix`
-/

open List Set Computability

namespace DFA

variable {α : Type*} {σ : Type*}

/-- The set of states from which some accepting state is reachable. -/
@[expose]
public def reachableAccept (M : DFA α σ) : Set σ :=
  { s : σ | ∃ x : List α, M.evalFrom s x ∈ M.accept }

/-- A DFA accepting the prefix language of the original DFA's language. -/
@[expose]
public def prefixDFA (M : DFA α σ) : DFA α σ where
  step := M.step
  start := M.start
  accept := M.reachableAccept

public theorem evalFrom_prefixDFA (M : DFA α σ) (s : σ) (x : List α) :
    M.prefixDFA.evalFrom s x = M.evalFrom s x := by
  rfl

public theorem mem_prefixDFA_accept (M : DFA α σ) (s : σ) :
    s ∈ M.prefixDFA.accept ↔ ∃ x : List α, M.evalFrom s x ∈ M.accept := by
  rfl

/-- The prefix DFA accepts exactly the prefix language of the original DFA. -/
public theorem prefixDFA_accepts (M : DFA α σ) :
    M.prefixDFA.accepts = Language.prefixLang M.accepts := by
  ext w
  simp only [DFA.mem_accepts, Language.mem_prefixLang, evalFrom_prefixDFA,
    mem_prefixDFA_accept, DFA.eval]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rwa [DFA.evalFrom_of_append]⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rwa [← DFA.evalFrom_of_append]⟩

end DFA

namespace Language

variable {α : Type*}

/-- Regular languages are closed under the prefix operation. -/
public theorem IsRegular.prefixLang {L : Language α} (h : L.IsRegular) :
    (prefixLang L).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨σ, inferInstance, M.prefixDFA, M.prefixDFA_accepts⟩

private lemma map_anbn_compl_not_isRegular {T : Type*} {f : Bool → T}
    (hf : Function.Injective f) : ¬ (Language.map f anbn)ᶜ.IsRegular := by
  intro h
  exact map_anbn_not_isRegular hf (Language.isRegular_compl_iff.mp h)

/-- No word of the form `w ++ [f false]` belongs to the injective image of `anbn`. -/
private lemma append_false_image_not_mem_map_anbn {T : Type*} {f : Bool → T}
    (hf : Function.Injective f) (w : List T) :
    w ++ [f false] ∉ Language.map f anbn := by
  rintro ⟨u, ⟨n, rfl⟩, hmap⟩
  cases n with
  | zero =>
      simp at hmap
  | succ n =>
      have hrev := congr_arg List.reverse hmap
      have hhead := congr_arg List.head? hrev
      have hne : f true ≠ f false := by
        intro h
        have htf : true = false := hf h
        cases htf
      simp [List.map_append, List.reverse_append, List.replicate] at hhead
      have hrep : (List.replicate n (f true)).head?.getD (f true) = f true := by
        cases n <;> simp [List.replicate]
      exact hne (hrep.symm.trans hhead)

/-- `prefixLang((map f anbn)ᶜ) = ⊤` for injective two-symbol codings. -/
private lemma prefixLang_map_anbn_compl_eq_top {T : Type*} {f : Bool → T}
    (hf : Function.Injective f) :
    prefixLang (Language.map f anbn)ᶜ = ⊤ := by
  ext w
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨[f false], append_false_image_not_mem_map_anbn hf w⟩

/-- The converse of prefix closure fails over any nontrivial alphabet. -/
theorem not_iff_regular_prefix [Nontrivial α] :
    ¬ (∀ (L : Language α), (prefixLang L).IsRegular ↔ L.IsRegular) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  let f : Bool → α := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f]
  have hpref : (prefixLang (Language.map f anbn)ᶜ).IsRegular := by
    rw [prefixLang_map_anbn_compl_eq_top hf]
    exact isRegular_top
  exact map_anbn_compl_not_isRegular hf ((h (Language.map f anbn)ᶜ).mp hpref)

end Language
