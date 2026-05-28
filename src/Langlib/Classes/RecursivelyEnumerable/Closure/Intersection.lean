module

public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipTest
public import Langlib.Utilities.ClosurePredicates
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Computability.Partrec
import Langlib.Automata.Turing.DSL.CodeToTMDirect
import Langlib.Automata.Turing.DSL.SearchProcToTM0
import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipComputability
import Langlib.Automata.Turing.Equivalence.TMToGrammar
import Langlib.Classes.Regular.Inclusion.RecursivelyEnumerable
import Langlib.Grammars.Unrestricted.FiniteNonterminals
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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



/-! # RE Closure Under Intersection

This file proves the search-level closure theorem for recursively enumerable
languages under intersection.  The key result is `RE_of_RE_i_RE`: after replacing
both grammar witnesses by finite-nonterminal equivalents, a single computable
test checks both derivation witnesses and the existing search-to-TM compiler
turns that test back into an RE witness.

## Main declarations

- `reIntersectionTest`
- `reIntersectionTest_computable₂`
- `RE_of_RE_i_RE`
- `RE_closedUnderIntersection`
- `RE_closedUnderIntersectionWithRegular`
-/

open Turing

variable {T : Type} [DecidableEq T]

/-- Search test for membership in the intersection of two grammar languages. -/
@[expose]
public def reIntersectionTest (g₁ g₂ : grammar T) [DecidableEq g₁.nt] [DecidableEq g₂.nt]
    (p : List (ℕ × ℕ) × List (ℕ × ℕ)) (w : List T) : Bool :=
  grammarTest g₁ p.1 w && grammarTest g₂ p.2 w

/-- The two-witness intersection search test is computable. -/
public theorem reIntersectionTest_computable₂ (g₁ g₂ : grammar T)
    [DecidableEq g₁.nt] [DecidableEq g₂.nt]
    [Primcodable T] [Primcodable g₁.nt] [Primcodable g₂.nt] :
    Computable₂ (reIntersectionTest g₁ g₂) := by
  apply Computable₂.mk
  unfold reIntersectionTest
  have h₁ : Computable (fun p : (List (ℕ × ℕ) × List (ℕ × ℕ)) × List T =>
      grammarTest g₁ p.1.1 p.2) :=
    (grammarTest_computable₂ g₁).comp (Computable.fst.comp Computable.fst) Computable.snd
  have h₂ : Computable (fun p : (List (ℕ × ℕ) × List (ℕ × ℕ)) × List T =>
      grammarTest g₂ p.1.2 p.2) :=
    (grammarTest_computable₂ g₂).comp (Computable.snd.comp Computable.fst) Computable.snd
  exact (Primrec.and.to_comp).comp h₁ h₂

/-- Recursively enumerable languages over a finite alphabet are closed under intersection. -/
public theorem RE_of_RE_i_RE [Fintype T] (L₁ L₂ : Language T) :
    is_RE L₁ ∧ is_RE L₂ → is_RE (L₁ ⊓ L₂) := by
  rintro ⟨hL₁, hL₂⟩
  obtain ⟨g₁, hg₁⟩ := hL₁
  obtain ⟨g₂, hg₂⟩ := hL₂
  obtain ⟨g₁', _hfin₁, hlang₁⟩ := grammar_equivalent_finiteNT g₁
  obtain ⟨g₂', _hfin₂, hlang₂⟩ := grammar_equivalent_finiteNT g₂
  haveI : Fintype g₁'.nt := Fintype.ofFinite _
  haveI : Fintype g₂'.nt := Fintype.ofFinite _
  haveI : DecidableEq g₁'.nt := Classical.decEq _
  haveI : DecidableEq g₂'.nt := Classical.decEq _
  haveI : Primcodable T :=
    Primcodable.ofEquiv (Fin (Fintype.card T)) (Fintype.truncEquivFin T).out
  haveI : Primcodable g₁'.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g₁'.nt)) (Fintype.truncEquivFin g₁'.nt).out
  haveI : Primcodable g₂'.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g₂'.nt)) (Fintype.truncEquivFin g₂'.nt).out
  let test := reIntersectionTest g₁' g₂'
  have hcomp : Computable₂ test := reIntersectionTest_computable₂ g₁' g₂'
  obtain ⟨c, hc⟩ := search_is_partrec test hcomp
  have htm : is_TM (L₁ ⊓ L₂) :=
    code_implies_isTM_direct (L₁ ⊓ L₂) c (fun w => by
      constructor
      · intro hw
        rw [← hc]
        have hw₁ : w ∈ grammar_language g₁' := by
          rw [← hlang₁, hg₁]
          exact hw.1
        have hw₂ : w ∈ grammar_language g₂' := by
          rw [← hlang₂, hg₂]
          exact hw.2
        obtain ⟨seq₁, hseq₁⟩ := grammarTest_complete g₁' w hw₁
        obtain ⟨seq₂, hseq₂⟩ := grammarTest_complete g₂' w hw₂
        exact ⟨(seq₁, seq₂), by simp [test, reIntersectionTest, hseq₁, hseq₂]⟩
      · intro hdom
        rw [← hc] at hdom
        obtain ⟨seqs, hseqs⟩ := hdom
        have hboth : grammarTest g₁' seqs.1 w = true ∧ grammarTest g₂' seqs.2 w = true := by
          simpa [test, reIntersectionTest] using hseqs
        constructor
        · rw [← hg₁, hlang₁]
          exact grammarTest_sound g₁' seqs.1 w hboth.1
        · rw [← hg₂, hlang₂]
          exact grammarTest_sound g₂' seqs.2 w hboth.2)
  exact tm_recognizable_implies_re (L₁ ⊓ L₂) htm

/-- The class of recursively enumerable languages is closed under intersection. -/
theorem RE_closedUnderIntersection [Fintype T] :
    ClosedUnderIntersection (α := T) is_RE :=
  fun L₁ L₂ h₁ h₂ => RE_of_RE_i_RE L₁ L₂ ⟨h₁, h₂⟩

/-- RE languages are closed under intersection with a Mathlib-regular language. -/
theorem RE_of_RE_i_regular [Fintype T] (L R : Language T) :
    is_RE L → R.IsRegular → is_RE (L ⊓ R) := by
  intro hL hR
  exact RE_of_RE_i_RE L R ⟨hL, is_RE_of_isRegular hR⟩

/-- The class of RE languages is closed under intersection with regular languages. -/
theorem RE_closedUnderIntersectionWithRegular [Fintype T] :
    ClosedUnderIntersectionWithRegular (α := T) is_RE :=
  fun L hL R hR => RE_of_RE_i_regular L R hL hR
