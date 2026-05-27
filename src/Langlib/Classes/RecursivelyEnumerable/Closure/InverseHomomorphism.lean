import Mathlib
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Grammars.Unrestricted.FiniteNonterminals
import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipComputability
import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipTest
import Langlib.Automata.Turing.DSL.SearchProcToTM0
import Langlib.Automata.Turing.DSL.CodeToTMDirect
import Langlib.Automata.Turing.Equivalence.TMToGrammar
import Langlib.Utilities.ClosurePredicates
import Langlib.Utilities.PrimrecHelpers

/-! # RE Closure Under Inverse Homomorphism

This file proves that recursively enumerable languages over finite alphabets are
closed under inverse string homomorphism.  The key result is
`RE_of_inverseHomomorphism_RE`: for a fixed finite-alphabet homomorphism
`h : α → List β`, the preprocessing map `w ↦ w.flatMap h` is primitive
recursive, so a grammar-membership search for `L` can be reused as a search for
the preimage `{w | w.flatMap h ∈ L}`.

## Main declarations

- `primrec_flatMap_finite`
- `reInverseHomomorphismTest`
- `reInverseHomomorphismTest_computable₂`
- `RE_of_inverseHomomorphism_RE`
- `RE_closedUnderInverseHomomorphism`
-/

open Turing

/-- Search test for the inverse homomorphic image of a grammar language. -/
def reInverseHomomorphismTest {α β : Type} [DecidableEq β]
    (g : grammar β) [DecidableEq g.nt] (h : α → List β)
    (seq : List (ℕ × ℕ)) (w : List α) : Bool :=
  grammarTest g seq (w.flatMap h)

/-- The inverse-homomorphism grammar search test is computable. -/
theorem reInverseHomomorphismTest_computable₂ {α β : Type}
    [DecidableEq β] [Primcodable α] [Primcodable β] [Finite α]
    (g : grammar β) [DecidableEq g.nt] [Primcodable g.nt] (h : α → List β) :
    Computable₂ (reInverseHomomorphismTest g h) := by
  apply Computable₂.mk
  unfold reInverseHomomorphismTest
  exact (grammarTest_computable₂ g).comp Computable.fst
    ((primrec_flatMap_finite h).to_comp.comp Computable.snd)

/-- RE languages over finite alphabets are closed under inverse string homomorphism. -/
theorem RE_of_inverseHomomorphism_RE {α β : Type}
    [Fintype α] [Fintype β] (L : Language β) (h : α → List β) :
    is_RE L → is_RE { w : List α | w.flatMap h ∈ L } := by
  intro hL
  haveI : DecidableEq α := Classical.decEq _
  haveI : DecidableEq β := Classical.decEq _
  obtain ⟨g, hg⟩ := hL
  obtain ⟨g', _hfin, hlang⟩ := grammar_equivalent_finiteNT g
  haveI : Fintype g'.nt := Fintype.ofFinite _
  haveI : DecidableEq g'.nt := Classical.decEq _
  haveI : Primcodable α :=
    Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.truncEquivFin α).out
  haveI : Primcodable β :=
    Primcodable.ofEquiv (Fin (Fintype.card β)) (Fintype.truncEquivFin β).out
  haveI : Primcodable g'.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g'.nt)) (Fintype.truncEquivFin g'.nt).out
  let test := reInverseHomomorphismTest g' h
  have hcomp : Computable₂ test := reInverseHomomorphismTest_computable₂ g' h
  obtain ⟨c, hc⟩ := search_is_partrec test hcomp
  have htm : is_TM ({ w : List α | w.flatMap h ∈ L } : Language α) :=
    code_implies_isTM_direct ({ w : List α | w.flatMap h ∈ L } : Language α) c (fun w => by
      constructor
      · intro hw
        rw [← hc]
        have hw' : w.flatMap h ∈ grammar_language g' := by
          rw [← hlang, hg]
          exact hw
        obtain ⟨seq, hseq⟩ := grammarTest_complete g' (w.flatMap h) hw'
        exact ⟨seq, by simpa [test, reInverseHomomorphismTest] using hseq⟩
      · intro hdom
        rw [← hc] at hdom
        obtain ⟨seq, hseq⟩ := hdom
        have hw' : w.flatMap h ∈ grammar_language g' :=
          grammarTest_sound g' seq (w.flatMap h) (by
            simpa [test, reInverseHomomorphismTest] using hseq)
        rw [← hg, hlang]
        exact hw')
  exact tm_recognizable_implies_re ({ w : List α | w.flatMap h ∈ L } : Language α) htm

/-- The class of RE languages is closed under inverse string homomorphism. -/
theorem RE_closedUnderInverseHomomorphism :
    ClosedUnderInverseHomomorphism is_RE := by
  intro α β _ _ L h hL
  exact RE_of_inverseHomomorphism_RE L h hL
