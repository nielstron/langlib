module

public import Langlib.Utilities.ClosurePredicates
public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Mathlib.Computability.Halting
import Langlib.Automata.Turing.DSL.CodeToTMDirect
import Langlib.Automata.Turing.DSL.SearchProcToTM0
import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipComputability
import Langlib.Automata.Turing.Equivalence.TMEqualsRE
import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
import Langlib.Classes.RecursivelyEnumerable.Closure.InverseHomomorphism
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

@[expose] public section

/-! # RE Non-Closure Under Complement

Key results: `haltingUnary_complement_not_RE` gives a concrete RE language whose complement
is not RE, and `RE_notClosedUnderComplement` packages this as failure of complement closure.

The proof encodes `Nat.Partrec.Code` as unary words.  The halting language is RE because
bounded evaluation is a computable search; if its complement were RE, grammar-membership search
after the unary encoding would make the halting complement an `REPred`, contradicting Mathlib's
`ComputablePred.halting_problem_not_re`.
-/

open Nat.Partrec

abbrev PartrecCode := Nat.Partrec.Code

/-- The unary word whose length is the code number of a partial-recursive code. -/
def codeUnaryWord (c : PartrecCode) : List Unit :=
  (List.range (Encodable.encode c)).map (fun _ => ())

@[simp] theorem codeUnaryWord_length (c : PartrecCode) :
    (codeUnaryWord c).length = Encodable.encode c := by
  simp [codeUnaryWord]

/-- Unary halting language: a word is accepted when its length decodes to a code that halts on 0. -/
def haltingUnaryLanguage : Language Unit :=
  fun w => ((Nat.Partrec.Code.ofNatCode w.length).eval 0).Dom

/-- Bounded halting test for the unary language. -/
def haltingUnaryTest (k : ℕ) (w : List Unit) : Bool :=
  (Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0).isSome

theorem haltingUnaryTest_computable₂ :
    Computable₂ haltingUnaryTest := by
  apply Computable₂.mk
  have hEval : Primrec (fun p : ℕ × List Unit =>
      Nat.Partrec.Code.evaln p.1 (Nat.Partrec.Code.ofNatCode p.2.length) 0) := by
    convert Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.fst.pair
        ((Primrec.ofNat PartrecCode).comp (Primrec.list_length.comp Primrec.snd))).pair
        (Primrec.const 0)) using 1
  exact (Primrec.option_isSome.comp hEval).to_comp.of_eq (by
    intro p
    rfl)

theorem haltingUnaryLanguage_search (w : List Unit) :
    w ∈ haltingUnaryLanguage ↔ ∃ k, haltingUnaryTest k w = true := by
  unfold haltingUnaryLanguage haltingUnaryTest
  constructor
  · intro h
    change ((Nat.Partrec.Code.ofNatCode w.length).eval 0).Dom at h
    rw [Part.dom_iff_mem] at h
    obtain ⟨x, hx⟩ := h
    rw [Nat.Partrec.Code.evaln_complete] at hx
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    cases hEval : Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0 with
    | none =>
        simp [hEval] at hk
    | some y =>
        rfl
  · rintro ⟨k, hk⟩
    cases hEval : Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0 with
    | none =>
        simp [hEval] at hk
    | some y =>
        change ((Nat.Partrec.Code.ofNatCode w.length).eval 0).Dom
        rw [Part.dom_iff_mem]
        exact ⟨y, Nat.Partrec.Code.evaln_sound (by simpa [hEval])⟩

/-- The unary halting language is recursively enumerable. -/
theorem haltingUnaryLanguage_RE : is_RE haltingUnaryLanguage := by
  obtain ⟨c, hc⟩ := search_is_partrec haltingUnaryTest haltingUnaryTest_computable₂
  have htm : is_TM haltingUnaryLanguage :=
    code_implies_isTM_direct haltingUnaryLanguage c (fun w => by
      rw [← hc w]
      exact haltingUnaryLanguage_search w)
  exact (is_TM_iff_is_RE haltingUnaryLanguage).1 htm

theorem codeUnaryWord_computable : Computable codeUnaryWord := by
  have h : Primrec codeUnaryWord := by
    unfold codeUnaryWord
    exact Primrec.list_map
      (Primrec.list_range.comp Primrec.encode)
      (Primrec.const ()).to₂
  exact h.to_comp

theorem codeUnaryWord_mem_haltingUnaryLanguage (c : PartrecCode) :
    codeUnaryWord c ∈ haltingUnaryLanguage ↔ (c.eval 0).Dom := by
  change ((Nat.Partrec.Code.ofNatCode (codeUnaryWord c).length).eval 0).Dom ↔
    (c.eval 0).Dom
  rw [codeUnaryWord_length]
  rw [← Nat.Partrec.Code.ofNatCode_eq]
  simp [Denumerable.ofNat_encode]

/-- Preimage of an RE unary language along `codeUnaryWord` is an `REPred`. -/
theorem REPred_codeUnaryWord_preimage {L : Language Unit} (hL : is_RE L) :
    REPred (fun c : PartrecCode => codeUnaryWord c ∈ L) := by
  obtain ⟨g, hg⟩ := hL
  obtain ⟨g', hfin, hlang⟩ := grammar_equivalent_finiteNT g
  haveI : Fintype g'.nt := Fintype.ofFinite _
  haveI : DecidableEq g'.nt := Classical.decEq _
  haveI : Primcodable g'.nt :=
    Primcodable.ofEquiv (Fin (Fintype.card g'.nt)) (Fintype.truncEquivFin g'.nt).out
  let test : List (ℕ × ℕ) → PartrecCode → Bool :=
    fun seq c => grammarTest g' seq (codeUnaryWord c)
  have htest : Computable₂ test := by
    apply Computable₂.mk
    exact (grammarTest_computable₂ g').comp
      (g := fun p : List (ℕ × ℕ) × PartrecCode => p.1)
      (h := fun p : List (ℕ × ℕ) × PartrecCode => codeUnaryWord p.2)
      Computable.fst
      (codeUnaryWord_computable.comp Computable.snd)
  have hpart : REPred (fun c : PartrecCode =>
      ∃ seq : List (ℕ × ℕ), test seq c = true) := by
    have hdom : Partrec (fun c : PartrecCode =>
        Nat.rfind (fun k =>
          Part.some (((Encodable.decode (α := List (ℕ × ℕ)) k).map
            (fun seq => test seq c)).getD false))) := by
      have hgEnc : Computable₂ (fun c k =>
          ((Encodable.decode (α := List (ℕ × ℕ)) k).map
            (fun seq => test seq c)).getD false) := by
        unfold test
        exact Computable.option_getD
          (Computable.option_map
            (Computable.decode.comp Computable.snd)
            (htest.comp
              (g := fun x : (PartrecCode × ℕ) × List (ℕ × ℕ) => x.2)
              (h := fun x : (PartrecCode × ℕ) × List (ℕ × ℕ) => x.1.1)
              Computable.snd
              (Computable.fst.comp Computable.fst)))
          (Computable.const false)
      exact Partrec.rfind hgEnc.partrec₂
    exact hdom.dom_re.of_eq fun c => by
      simp [Nat.rfind_dom]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨Denumerable.ofNat (List (ℕ × ℕ)) n, hn⟩
      · rintro ⟨seq, hseq⟩
        exact ⟨Encodable.encode seq, by simpa [Denumerable.ofNat_encode] using hseq⟩
  exact hpart.of_eq fun c => by
    constructor
    · rintro ⟨seq, hseq⟩
      have hmem : codeUnaryWord c ∈ grammar_language g' :=
        grammarTest_sound g' seq (codeUnaryWord c) hseq
      rw [← hlang] at hmem
      rw [hg] at hmem
      exact hmem
    · intro h
      have hmem : codeUnaryWord c ∈ grammar_language g' := by
        rw [← hg] at h
        rw [hlang] at h
        exact h
      obtain ⟨seq, hseq⟩ := grammarTest_complete g' (codeUnaryWord c) hmem
      exact ⟨seq, hseq⟩

/-- The complement of the unary halting language is not RE. -/
theorem haltingUnary_complement_not_RE : ¬ is_RE haltingUnaryLanguageᶜ := by
  intro hcomp
  have hpre := REPred_codeUnaryWord_preimage hcomp
  have hnot : REPred (fun c : PartrecCode => ¬(c.eval 0).Dom) :=
    hpre.of_eq fun c => by
      rw [Set.mem_compl_iff, codeUnaryWord_mem_haltingUnaryLanguage]
  exact ComputablePred.halting_problem_not_re 0 hnot

/-- Recursively enumerable languages over the unary alphabet are not closed under complement. -/
theorem RE_notClosedUnderComplement :
    ¬ ClosedUnderComplement (α := Unit) is_RE := by
  intro hclosed
  exact haltingUnary_complement_not_RE
    (hclosed haltingUnaryLanguage haltingUnaryLanguage_RE)

/-- RE languages over any nonempty finite alphabet are not closed under complement. -/
theorem RE_notClosedUnderComplement_of_nonempty {T : Type} [Fintype T] [Nonempty T] :
    ¬ ClosedUnderComplement (α := T) is_RE := by
  intro hclosed
  let a : T := Classical.choice inferInstance
  let f : Unit → T := fun _ => a
  have hf : Function.Injective f := by
    intro x y _
    cases x
    cases y
    rfl
  have hmap : is_RE (Language.map f haltingUnaryLanguage) :=
    RE_of_map_injective_RE hf haltingUnaryLanguage haltingUnaryLanguage_RE
  have hcomp : is_RE (Language.map f haltingUnaryLanguage)ᶜ :=
    hclosed _ hmap
  let h : Unit → List T := fun _ => [a]
  have hpre : is_RE ({w : List Unit | w.flatMap h ∈ (Language.map f haltingUnaryLanguage)ᶜ}) :=
    RE_of_inverseHomomorphism_RE (Language.map f haltingUnaryLanguage)ᶜ h hcomp
  have heq :
      ({w : List Unit | w.flatMap h ∈ (Language.map f haltingUnaryLanguage)ᶜ} :
        Language Unit) = haltingUnaryLanguageᶜ := by
    ext w
    change (w.flatMap h ∈ (Language.map f haltingUnaryLanguage)ᶜ) ↔
      w ∈ haltingUnaryLanguageᶜ
    rw [Set.mem_compl_iff, Set.mem_compl_iff]
    have hflat : w.flatMap h = w.map f := by
      simpa [h, f, Function.comp_def] using (List.flatMap_pure_eq_map f w)
    rw [hflat]
    constructor
    · intro hnot hw
      exact hnot ⟨w, hw, rfl⟩
    · rintro hnot ⟨u, hu, humap⟩
      have huw : u = w := by
        apply List.map_injective_iff.mpr hf
        simpa using humap
      exact hnot (by simpa [huw] using hu)
  exact haltingUnary_complement_not_RE (by simpa [heq] using hpre)
