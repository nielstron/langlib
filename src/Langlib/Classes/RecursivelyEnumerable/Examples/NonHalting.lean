module

public import Langlib.Examples.Halting
public import Langlib.Examples.NonHalting
public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Mathlib.Computability.Halting
import Langlib.Automata.Turing.Equivalence.GrammarToTM.MembershipComputability
import Langlib.Grammars.Unrestricted.FiniteNonterminals
@[expose]
public section

/-! # The non-halting language is not recursively enumerable

This file proves `nonHaltingUnaryLanguage_not_RE`: the language of all non-halting Turing
machines (`nonHaltingUnaryLanguage`, the complement of `haltingUnaryLanguage`) is *not*
recursively enumerable.

The argument encodes each partial-recursive code `c` as the unary word `codeUnaryWord c`.
If the non-halting language were RE, then grammar-membership search after this encoding
would make `fun c => ¬ (c.eval 0).Dom` an `REPred`, contradicting Mathlib's
`ComputablePred.halting_problem_not_re`.
-/

open Nat.Partrec

@[expose]
public abbrev PartrecCode := Nat.Partrec.Code

/-- The unary word whose length is the code number of a partial-recursive code. -/
@[expose]
public def codeUnaryWord (c : PartrecCode) : List Unit :=
  (List.range (Encodable.encode c)).map (fun _ => ())

@[simp] theorem codeUnaryWord_length (c : PartrecCode) :
    (codeUnaryWord c).length = Encodable.encode c := by
  simp [codeUnaryWord]

public theorem codeUnaryWord_computable : Computable codeUnaryWord := by
  have h : Primrec codeUnaryWord := by
    unfold codeUnaryWord
    exact Primrec.list_map
      (Primrec.list_range.comp Primrec.encode)
      (Primrec.const ()).to₂
  exact h.to_comp

public theorem codeUnaryWord_mem_haltingUnaryLanguage (c : PartrecCode) :
    codeUnaryWord c ∈ haltingUnaryLanguage ↔ (c.eval 0).Dom := by
  change ((Nat.Partrec.Code.ofNatCode (codeUnaryWord c).length).eval 0).Dom ↔
    (c.eval 0).Dom
  rw [codeUnaryWord_length]
  rw [← Nat.Partrec.Code.ofNatCode_eq]
  simp [Denumerable.ofNat_encode]

/-- Preimage of an RE unary language along `codeUnaryWord` is an `REPred`. -/
public theorem REPred_codeUnaryWord_preimage {L : Language Unit} (hL : is_RE L) :
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
public theorem haltingUnary_complement_not_RE : ¬ is_RE haltingUnaryLanguageᶜ := by
  intro hcomp
  have hpre := REPred_codeUnaryWord_preimage hcomp
  have hnot : REPred (fun c : PartrecCode => ¬(c.eval 0).Dom) :=
    hpre.of_eq fun c => by
      rw [Set.mem_compl_iff, codeUnaryWord_mem_haltingUnaryLanguage]
  exact ComputablePred.halting_problem_not_re 0 hnot

/-- The unary non-halting language is not recursively enumerable. -/
public theorem nonHaltingUnaryLanguage_not_RE : ¬ is_RE nonHaltingUnaryLanguage :=
  haltingUnary_complement_not_RE

end
