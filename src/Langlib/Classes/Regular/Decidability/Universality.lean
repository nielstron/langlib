module

public import Langlib.Classes.Regular.Decidability.Emptiness
public import Langlib.Utilities.WordEnumeration
import Langlib.Classes.ContextFree.Decidability.PrimrecSatStep
public import Langlib.Classes.ContextFree.Decidability.UniformMembership
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



/-! # Decidability of Universality

This file proves that universality is decidable for
regular languages.

## Main results

- `regular_universality_decidable` – universality of a regular language is decidable
- `regular_computableUniversality` – universality is *uniformly* computable for
  encoded right-regular grammars (`ComputableUniversality`)
-/

section Regular

variable {α : Type*}

/-- Universality of a regular language is decidable. -/
noncomputable def regular_universality_decidable
    [Fintype α] [DecidableEq α] (L : Language α) (hL : L.IsRegular) :
    Decidable (L = (⊤ : Set (List α))) := by
  change Decidable (L = (Set.univ : Set (List α)))
  rw [← Set.compl_empty_iff]
  exact regular_emptiness_decidable Lᶜ hL.compl

end Regular

namespace Regular.EncodedRG

open Classical

variable {T : Type}

/-- A coarse subset-DFA state bound for the encoded right-regular grammar. -/
public def regularSearchBound (c : EncodedRG T) : ℕ :=
  2 ^ (c.1 + 2)

public theorem subsetDFA_card_le_regularSearchBound (c : EncodedRG T) :
    Fintype.card (Set (Option (toRG c).FinNT)) ≤ regularSearchBound c := by
  classical
  have hsub : Fintype.card (toRG c).FinNT ≤ (toCFG c).ntCount := by
    change Fintype.card { x : Fin (toCFG c).ntCount // x ∈ (toRG c).nonterminalFinset } ≤
      (toCFG c).ntCount
    simpa using Fintype.card_subtype_le (p := fun x : Fin (toCFG c).ntCount =>
      x ∈ (toRG c).nonterminalFinset)
  have hopt : Fintype.card (Option (toRG c).FinNT) ≤ (toCFG c).ntCount + 1 := by
    rw [Fintype.card_option]
    exact Nat.succ_le_succ hsub
  calc
    Fintype.card (Set (Option (toRG c).FinNT))
        = 2 ^ Fintype.card (Option (toRG c).FinNT) := by
          rw [Fintype.card_set]
    _ ≤ 2 ^ ((toCFG c).ntCount + 1) :=
          Nat.pow_le_pow_right (by decide) hopt
    _ = regularSearchBound c := by
          simp [regularSearchBound, toCFG, EncodedCFG.ntCount, EncodedCFG.numNT]

private theorem exists_short_regular_counterexample [Fintype T]
    (c : EncodedRG T) {w : List T} (hw : w ∉ regularLanguageOf c) :
    ∃ u : List T, u.length ≤ regularSearchBound c ∧ u ∉ regularLanguageOf c := by
  classical
  let g := toRG c
  let M := (NFA_of_RG g).toDFA
  have hM : M.accepts = regularLanguageOf c := by
    simp [M, g, NFA.toDFA_correct, NFA_of_RG_accepts, rgLanguage_toRG]
  have hnotM : w ∉ M.accepts := by
    simpa [hM] using hw
  obtain ⟨u, huLen, huEval⟩ := M.short_word_of_reachable w
  refine ⟨u, huLen.trans (subsetDFA_card_le_regularSearchBound c), ?_⟩
  intro hu
  apply hnotM
  have huM : u ∈ M.accepts := by
    simpa [hM] using hu
  have huAcc : M.eval u ∈ M.accept := by
    simpa [DFA.mem_accepts] using huM
  have hwAcc : M.eval w ∈ M.accept := by
    change M.evalFrom M.start w ∈ M.accept
    change M.evalFrom M.start u ∈ M.accept at huAcc
    rwa [← huEval]
  simpa [DFA.mem_accepts] using hwAcc

public theorem regularSearchBound_primrec [Primcodable T] :
    Primrec (regularSearchBound : EncodedRG T → ℕ) := by
  have hpow : Primrec₂ (fun x y : ℕ => x ^ y) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact hpow.comp (Primrec.const 2) (Primrec.succ.comp (Primrec.succ.comp Primrec.fst))

private def regularCandidateWords (alphabet : List T) (c : EncodedRG T) : List (List T) :=
  wordsUpTo alphabet (regularSearchBound c)

private noncomputable def regularCounterexampleTest [DecidableEq T] [Fintype T]
    (c : EncodedRG T) (w : List T) : Bool :=
  !checkMembershipEncoded (toCFG c, w)

private noncomputable def regularUniversalityCheckWith [DecidableEq T] [Fintype T]
    (alphabet : List T) (c : EncodedRG T) : Bool :=
  !wordSearch (regularCandidateWords alphabet c) (regularCounterexampleTest c)

/-- Executable universality check for encoded right-regular grammars. -/
private noncomputable def regularUniversalityCheck [Fintype T] [DecidableEq T]
    (c : EncodedRG T) : Bool :=
  regularUniversalityCheckWith ((Finset.univ : Finset T).toList) c

private theorem regularCandidateWords_primrec [Primcodable T] (alphabet : List T) :
    Primrec (fun c : EncodedRG T => regularCandidateWords alphabet c) := by
  change Primrec (fun c : EncodedRG T => wordsUpTo alphabet (regularSearchBound c))
  exact wordsUpTo_primrec.comp (Primrec.pair (Primrec.const alphabet) regularSearchBound_primrec)

private theorem regularCounterexampleTest_computable [Fintype T] [DecidableEq T] [Primcodable T] :
    Computable₂ (regularCounterexampleTest : EncodedRG T → List T → Bool) := by
  apply Computable₂.mk
  have hcheck : Computable (fun q : EncodedRG T × List T =>
      checkMembershipEncoded (toCFG q.1, q.2)) :=
    checkMembershipEncoded_computable'.comp
      (Primrec.to_comp (Primrec.pair (toCFG_primrec.comp Primrec.fst) Primrec.snd))
  change Computable (fun q : EncodedRG T × List T =>
    !checkMembershipEncoded (toCFG q.1, q.2))
  exact Primrec.not.to_comp.comp hcheck

private theorem regularUniversalityCheckWith_computable [Fintype T] [DecidableEq T] [Primcodable T]
    (alphabet : List T) :
    Computable (regularUniversalityCheckWith alphabet : EncodedRG T → Bool) := by
  have hsearch : Computable (fun c : EncodedRG T =>
      wordSearch (regularCandidateWords alphabet c) (regularCounterexampleTest c)) :=
    wordSearch_computable (regularCandidateWords_primrec alphabet).to_comp
      regularCounterexampleTest_computable
  change Computable (fun c : EncodedRG T =>
    !wordSearch (regularCandidateWords alphabet c) (regularCounterexampleTest c))
  exact Primrec.not.to_comp.comp hsearch

private theorem checkMembershipEncoded_regular_iff [Fintype T] [DecidableEq T]
    (c : EncodedRG T) (w : List T) :
    checkMembershipEncoded (toCFG c, w) = true ↔ w ∈ regularLanguageOf c := by
  simpa [regularLanguageOf, contextFreeLanguageOf] using
    checkMembershipEncoded_correct (toCFG c) w

private theorem regularUniversalityCheck_correct [Fintype T] [DecidableEq T]
    (c : EncodedRG T) :
    regularUniversalityCheck c = true ↔ regularLanguageOf c = Set.univ := by
  unfold regularUniversalityCheck regularUniversalityCheckWith regularCandidateWords
    regularCounterexampleTest
  constructor
  · intro hcheck
    have hNoSearch :
        wordSearch (wordsUpTo ((Finset.univ : Finset T).toList) (regularSearchBound c))
          (fun w => !checkMembershipEncoded (toCFG c, w)) = false :=
      by
        cases hsearch :
            wordSearch (wordsUpTo ((Finset.univ : Finset T).toList) (regularSearchBound c))
              (fun w => !checkMembershipEncoded (toCFG c, w))
        · rfl
        · have hFalse :
              wordSearch (wordsUpTo ((Finset.univ : Finset T).toList) (regularSearchBound c))
                (fun w => !checkMembershipEncoded (toCFG c, w)) = false := by
            simpa using hcheck
          rwa [hsearch] at hFalse
    apply Set.eq_univ_of_forall
    intro w
    cases hwCheck : checkMembershipEncoded (toCFG c, w)
    · have hwNot : w ∉ regularLanguageOf c := by
        intro hwMem
        have hwTrue : checkMembershipEncoded (toCFG c, w) = true :=
          (checkMembershipEncoded_regular_iff c w).mpr hwMem
        rw [hwCheck] at hwTrue
        contradiction
      obtain ⟨u, huLen, huNot⟩ := exists_short_regular_counterexample c hwNot
      have hSearch :
          wordSearch (wordsUpTo ((Finset.univ : Finset T).toList) (regularSearchBound c))
            (fun w => !checkMembershipEncoded (toCFG c, w)) = true := by
        rw [wordSearch_true_iff_exists_mem]
        refine ⟨u, ?_, ?_⟩
        · rw [mem_wordsUpTo_univ]
          exact huLen
        · have huFalse : checkMembershipEncoded (toCFG c, u) = false := by
            exact Bool.eq_false_of_not_eq_true fun huTrue =>
              huNot ((checkMembershipEncoded_regular_iff c u).mp huTrue)
          simp [huFalse]
      rw [hNoSearch] at hSearch
      contradiction
    · exact (checkMembershipEncoded_regular_iff c w).mp hwCheck
  · intro hUniv
    have hNoSearch :
        wordSearch (wordsUpTo ((Finset.univ : Finset T).toList) (regularSearchBound c))
          (fun w => !checkMembershipEncoded (toCFG c, w)) = false := by
      cases hSearch :
          wordSearch (wordsUpTo ((Finset.univ : Finset T).toList) (regularSearchBound c))
            (fun w => !checkMembershipEncoded (toCFG c, w))
      · rfl
      · rw [wordSearch_true_iff_exists_mem] at hSearch
        rcases hSearch with ⟨w, _, hwBad⟩
        have hwMem : w ∈ regularLanguageOf c := by
          rw [hUniv]
          exact Set.mem_univ w
        have hwTrue : checkMembershipEncoded (toCFG c, w) = true :=
          (checkMembershipEncoded_regular_iff c w).mpr hwMem
        simp [hwTrue] at hwBad
    rw [hNoSearch]
    rfl

/-- The raw uniform universality decider for encoded right-regular grammars. -/
public theorem regular_universality_computablePred [Fintype T] [DecidableEq T] [Primcodable T] :
    ComputablePred (fun c : EncodedRG T => regularLanguageOf c = Set.univ) := by
  rw [ComputablePred.computable_iff]
  refine ⟨regularUniversalityCheck, ?_, ?_⟩
  · change Computable
      (regularUniversalityCheckWith ((Finset.univ : Finset T).toList) : EncodedRG T → Bool)
    exact regularUniversalityCheckWith_computable ((Finset.univ : Finset T).toList)
  funext c
  exact propext (regularUniversalityCheck_correct c).symm

/-- **Universality is uniformly computable** for the regular languages: encoded
right-regular grammars are an adequate, effective presentation
(`regularLanguageOf_characterizes`) with uniformly decidable universality. -/
public theorem regular_computableUniversality [Fintype T] [DecidableEq T] [Primcodable T] :
    ComputableUniversality RG (regularLanguageOf : EncodedRG T → Language T) :=
  ⟨regularLanguageOf_characterizes.onTrue, regular_membership_computablePred.to_re,
    ComputablePredOnPromise.ofComputablePred regular_universality_computablePred⟩

end Regular.EncodedRG
