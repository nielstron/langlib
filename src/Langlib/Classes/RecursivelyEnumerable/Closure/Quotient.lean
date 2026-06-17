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



/-! # RE Closure Under Right Quotient

This file proves that recursively enumerable languages over finite alphabets are
closed under right quotient, both by another RE language and by a regular
language.  The key result is `RE_of_RE_rightQuotient_RE`: a search witness
consists of a suffix `v`, a derivation sequence for `w ++ v` in the grammar for
`L`, and a derivation sequence for `v` in the grammar for `R`.

## Main declarations

- `reRightQuotientTest`
- `reRightQuotientTest_computable₂`
- `RE_of_RE_rightQuotient_RE`
- `RE_closedUnderRightQuotient`
- `reRightQuotientRegularTest`
- `reRightQuotientRegularTest_computable₂`
- `RE_of_RE_rightQuotient_regular`
- `RE_closedUnderRightQuotientWithRegular`
-/

open Turing

variable {T σ : Type}

/-- Search test for membership in the right quotient of two grammar languages. -/
def reRightQuotientTest [DecidableEq T]
    (g₁ g₂ : grammar T) [DecidableEq g₁.nt] [DecidableEq g₂.nt]
    (p : List T × List (ℕ × ℕ) × List (ℕ × ℕ)) (w : List T) : Bool :=
  grammarTest g₁ p.2.1 (w ++ p.1) && grammarTest g₂ p.2.2 p.1

/-- The suffix-and-two-derivations search test for right quotient is computable. -/
theorem reRightQuotientTest_computable₂ [DecidableEq T]
    [Primcodable T] (g₁ g₂ : grammar T)
    [DecidableEq g₁.nt] [DecidableEq g₂.nt]
    [Primcodable g₁.nt] [Primcodable g₂.nt] :
    Computable₂ (reRightQuotientTest g₁ g₂) := by
  apply Computable₂.mk
  unfold reRightQuotientTest
  have hword : Computable (fun p : (List T × List (ℕ × ℕ) × List (ℕ × ℕ)) × List T =>
      p.2 ++ p.1.1) :=
    (Primrec.list_append.to_comp).comp Computable.snd (Computable.fst.comp Computable.fst)
  have h₁ : Computable (fun p : (List T × List (ℕ × ℕ) × List (ℕ × ℕ)) × List T =>
      grammarTest g₁ p.1.2.1 (p.2 ++ p.1.1)) :=
    (grammarTest_computable₂ g₁).comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
      hword
  have h₂ : Computable (fun p : (List T × List (ℕ × ℕ) × List (ℕ × ℕ)) × List T =>
      grammarTest g₂ p.1.2.2 p.1.1) :=
    (grammarTest_computable₂ g₂).comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
      (Computable.fst.comp Computable.fst)
  exact (Primrec.and.to_comp).comp h₁ h₂

/-- RE languages are closed under right quotient with RE languages. -/
theorem RE_of_RE_rightQuotient_RE [DecidableEq T] [Fintype T]
    (L R : Language T) (hL : is_RE L) (hR : is_RE R) :
    is_RE (L / R) := by
  obtain ⟨gL, hgL⟩ := hL
  obtain ⟨gR, hgR⟩ := hR
  obtain ⟨gL', _hfinL, hlangL⟩ := grammar_equivalent_finiteNT gL
  obtain ⟨gR', _hfinR, hlangR⟩ := grammar_equivalent_finiteNT gR
  haveI : Fintype gL'.nt := Fintype.ofFinite _
  haveI : Fintype gR'.nt := Fintype.ofFinite _
  haveI : DecidableEq gL'.nt := Classical.decEq _
  haveI : DecidableEq gR'.nt := Classical.decEq _
  haveI : Primcodable T :=
    Primcodable.ofEquiv (Fin (Fintype.card T)) (Fintype.truncEquivFin T).out
  haveI : Primcodable gL'.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card gL'.nt)) (Fintype.truncEquivFin gL'.nt).out
  haveI : Primcodable gR'.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card gR'.nt)) (Fintype.truncEquivFin gR'.nt).out
  let test := reRightQuotientTest gL' gR'
  have hcomp : Computable₂ test := reRightQuotientTest_computable₂ gL' gR'
  obtain ⟨c, hc⟩ := search_is_partrec test hcomp
  have htm : is_TM (L / R) :=
    code_implies_isTM_direct (L / R) c (fun w => by
      constructor
      · intro hw
        rw [← hc]
        obtain ⟨v, hvR, hwvL⟩ := Language.mem_rightQuotient.mp hw
        have hwvG : w ++ v ∈ grammar_language gL' := by
          rw [← hlangL, hgL]
          exact hwvL
        have hvG : v ∈ grammar_language gR' := by
          rw [← hlangR, hgR]
          exact hvR
        obtain ⟨seqL, hseqL⟩ := grammarTest_complete gL' (w ++ v) hwvG
        obtain ⟨seqR, hseqR⟩ := grammarTest_complete gR' v hvG
        exact ⟨(v, seqL, seqR), by simp [test, reRightQuotientTest, hseqL, hseqR]⟩
      · intro hdom
        rw [← hc] at hdom
        obtain ⟨p, hp⟩ := hdom
        have hboth : grammarTest gL' p.2.1 (w ++ p.1) = true ∧
            grammarTest gR' p.2.2 p.1 = true := by
          simpa [test, reRightQuotientTest] using hp
        have hwvL : w ++ p.1 ∈ L := by
          rw [← hgL, hlangL]
          exact grammarTest_sound gL' p.2.1 (w ++ p.1) hboth.1
        have hvR : p.1 ∈ R := by
          rw [← hgR, hlangR]
          exact grammarTest_sound gR' p.2.2 p.1 hboth.2
        exact Language.mem_rightQuotient.mpr ⟨p.1, hvR, hwvL⟩)
  exact tm_recognizable_implies_re (L / R) htm

/-- The class of RE languages is closed under right quotient. -/
theorem RE_closedUnderRightQuotient [DecidableEq T] [Fintype T] :
    ClosedUnderRightQuotient (α := T) is_RE :=
  fun L R hL hR => RE_of_RE_rightQuotient_RE L R hL hR

/-- Search test for membership in the right quotient of a grammar language by a DFA language. -/
def reRightQuotientRegularTest [DecidableEq T]
    (g : grammar T) [DecidableEq g.nt] (M : DFA T σ) [DecidablePred (· ∈ M.accept)]
    (p : List T × List (ℕ × ℕ)) (w : List T) : Bool :=
  grammarTest g p.2 (w ++ p.1) && decide (M.eval p.1 ∈ M.accept)

/-- The suffix-and-derivation search test for right quotient by a DFA language is computable. -/
theorem reRightQuotientRegularTest_computable₂ [DecidableEq T]
    [Primcodable T] [Primcodable σ] [Finite T] [Finite σ]
    (g : grammar T) [DecidableEq g.nt] [Primcodable g.nt]
    (M : DFA T σ) [DecidablePred (· ∈ M.accept)] :
    Computable₂ (reRightQuotientRegularTest g M) := by
  apply Computable₂.mk
  unfold reRightQuotientRegularTest
  have hword : Computable (fun p : (List T × List (ℕ × ℕ)) × List T => p.2 ++ p.1.1) :=
    (Primrec.list_append.to_comp).comp Computable.snd (Computable.fst.comp Computable.fst)
  have hmem : Computable (fun p : (List T × List (ℕ × ℕ)) × List T =>
      grammarTest g p.1.2 (p.2 ++ p.1.1)) :=
    (grammarTest_computable₂ g).comp (Computable.snd.comp Computable.fst) hword
  have h_eval_comp : Computable M.eval := by
    show Computable (fun w => List.foldl M.step M.start w)
    exact (Primrec.list_foldl Primrec.id (Primrec.const M.start)
      (((Primrec.dom_finite (fun (p : σ × T) => M.step p.1 p.2)).comp
        Primrec.snd).to₂)).to_comp
  have haccWord : Computable (fun w : List T => decide (M.eval w ∈ M.accept)) :=
    (Primrec.dom_finite (fun s : σ => decide (s ∈ M.accept))).to_comp.comp h_eval_comp
  have hacc : Computable (fun p : (List T × List (ℕ × ℕ)) × List T =>
      decide (M.eval p.1.1 ∈ M.accept)) :=
    haccWord.comp (Computable.fst.comp Computable.fst)
  exact (Primrec.and.to_comp).comp hmem hacc

/-- RE languages are closed under right quotient with regular languages. -/
theorem RE_of_RE_rightQuotient_regular [DecidableEq T] [Fintype T]
    (L R : Language T) (hL : is_RE L) (hR : R.IsRegular) :
    is_RE (L / R) := by
  obtain ⟨g, hg⟩ := hL
  obtain ⟨g', _hfin, hlang⟩ := grammar_equivalent_finiteNT g
  obtain ⟨σ, _hσfin, M, hM⟩ := hR
  haveI : Fintype g'.nt := Fintype.ofFinite _
  haveI : DecidableEq g'.nt := Classical.decEq _
  haveI : DecidableEq σ := Classical.decEq _
  haveI : DecidablePred (· ∈ M.accept) := Classical.decPred _
  haveI : Primcodable T :=
    Primcodable.ofEquiv (Fin (Fintype.card T)) (Fintype.truncEquivFin T).out
  haveI : Primcodable σ :=
    Primcodable.ofEquiv (Fin (Fintype.card σ)) (Fintype.truncEquivFin σ).out
  haveI : Primcodable g'.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g'.nt)) (Fintype.truncEquivFin g'.nt).out
  let test := reRightQuotientRegularTest g' M
  have hcomp : Computable₂ test := reRightQuotientRegularTest_computable₂ g' M
  obtain ⟨c, hc⟩ := search_is_partrec test hcomp
  have htm : is_TM (L / R) :=
    code_implies_isTM_direct (L / R) c (fun w => by
      constructor
      · intro hw
        rw [← hc]
        obtain ⟨v, hvR, hwvL⟩ := Language.mem_rightQuotient.mp hw
        have hwvG : w ++ v ∈ grammar_language g' := by
          rw [← hlang, hg]
          exact hwvL
        have hvM : M.eval v ∈ M.accept := by
          change v ∈ M.accepts
          rw [hM]
          exact hvR
        obtain ⟨seq, hseq⟩ := grammarTest_complete g' (w ++ v) hwvG
        exact ⟨(v, seq), by simp [test, reRightQuotientRegularTest, hseq, hvM]⟩
      · intro hdom
        rw [← hc] at hdom
        obtain ⟨p, hp⟩ := hdom
        have hboth : grammarTest g' p.2 (w ++ p.1) = true ∧
            decide (M.eval p.1 ∈ M.accept) = true := by
          simpa [test, reRightQuotientRegularTest] using hp
        have hwvL : w ++ p.1 ∈ L := by
          rw [← hg, hlang]
          exact grammarTest_sound g' p.2 (w ++ p.1) hboth.1
        have hvM : M.eval p.1 ∈ M.accept :=
          of_decide_eq_true hboth.2
        have hvR : p.1 ∈ R := by
          rw [← hM]
          exact hvM
        exact Language.mem_rightQuotient.mpr ⟨p.1, hvR, hwvL⟩)
  exact tm_recognizable_implies_re (L / R) htm

/-- The class of RE languages is closed under right quotient with regular languages. -/
theorem RE_closedUnderRightQuotientWithRegular [DecidableEq T] [Fintype T] :
    ClosedUnderRightQuotientWithRegular (α := T) is_RE :=
  fun L hL R hR => RE_of_RE_rightQuotient_regular L R hL hR
