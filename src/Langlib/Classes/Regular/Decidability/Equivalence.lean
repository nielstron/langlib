module

public import Langlib.Classes.Regular.Decidability.Universality
import Langlib.Classes.Regular.Closure.Intersection
import Langlib.Classes.Regular.Closure.Union
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
import Mathlib.Order.BourbakiWitt
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



/-! # Decidability of Equivalence for Regular Languages

This file proves that equivalence is decidable for regular languages.

The proof reduces equivalence to emptiness of the symmetric difference:
`L₁ = L₂ ↔ symmDiff L₁ L₂ = ∅`, and the symmetric difference is regular
(by closure under complement, intersection, and union).

## Main results

- `regular_equivalence_decidable` — equivalence of two regular languages is decidable.
- `regular_computableEquivalence` – equivalence is *uniformly* computable for
  encoded right-regular grammars (`ComputableEquivalence`)
-/

section Regular

variable {α : Type*}

lemma eq_iff_symmDiff_eq_bot (L₁ L₂ : Language α) :
    L₁ = L₂ ↔ symmDiff L₁ L₂ = ⊥ := by
  constructor <;> intro <;> rw [ symmDiff ] at * <;> aesop

lemma symmDiff_isRegular {L₁ L₂ : Language α}
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (symmDiff L₁ L₂).IsRegular := by
  convert Language.IsRegular.add' _ _ using 1;
  · convert Language.IsRegular.inf' h₁ ( Language.IsRegular.compl h₂ ) using 1;
  · convert Language.IsRegular.inf' h₂ ( Language.IsRegular.compl h₁ ) using 1

/-- Equivalence of two regular languages is decidable. -/
noncomputable def regular_equivalence_decidable
    [Fintype α] [DecidableEq α] (L₁ L₂ : Language α)
    (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    Decidable (L₁ = L₂) := by
  rw [eq_iff_symmDiff_eq_bot]
  exact regular_emptiness_decidable _ (symmDiff_isRegular h₁ h₂)

end Regular

/-! ## Uniform computability over encoded right-regular grammars -/

namespace Regular.EncodedRG

variable {T : Type}

private def productDFA (M₁ : DFA T σ₁) (M₂ : DFA T σ₂) : DFA T (σ₁ × σ₂) where
  step s a := (M₁.step s.1 a, M₂.step s.2 a)
  start := (M₁.start, M₂.start)
  accept := {s | (s.1 ∈ M₁.accept ∧ s.2 ∉ M₂.accept) ∨
    (s.1 ∉ M₁.accept ∧ s.2 ∈ M₂.accept)}

private lemma productDFA_evalFrom (M₁ : DFA T σ₁) (M₂ : DFA T σ₂)
    (s : σ₁ × σ₂) (w : List T) :
    (productDFA M₁ M₂).evalFrom s w =
      (M₁.evalFrom s.1 w, M₂.evalFrom s.2 w) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
      exact ih (M₁.step s.1 a, M₂.step s.2 a)

private lemma productDFA_eval (M₁ : DFA T σ₁) (M₂ : DFA T σ₂) (w : List T) :
    (productDFA M₁ M₂).eval w = (M₁.eval w, M₂.eval w) :=
  productDFA_evalFrom M₁ M₂ (M₁.start, M₂.start) w

/-- A coarse product subset-DFA state bound for comparing two encoded
right-regular grammars. -/
public def regularEquivalenceSearchBound (p : EncodedRG T × EncodedRG T) : ℕ :=
  regularSearchBound p.1 * regularSearchBound p.2

private theorem productDFA_card_le_regularEquivalenceSearchBound
    (c₁ c₂ : EncodedRG T) :
    Fintype.card
        (Set (Option (toRG c₁).FinNT) × Set (Option (toRG c₂).FinNT)) ≤
      regularEquivalenceSearchBound (c₁, c₂) := by
  rw [Fintype.card_prod, regularEquivalenceSearchBound]
  exact Nat.mul_le_mul (subsetDFA_card_le_regularSearchBound c₁)
    (subsetDFA_card_le_regularSearchBound c₂)

private theorem exists_short_regular_separator [Fintype T]
    (c₁ c₂ : EncodedRG T) {w : List T}
    (hw : (w ∈ regularLanguageOf c₁ ∧ w ∉ regularLanguageOf c₂) ∨
      (w ∉ regularLanguageOf c₁ ∧ w ∈ regularLanguageOf c₂)) :
    ∃ u : List T, u.length ≤ regularEquivalenceSearchBound (c₁, c₂) ∧
      ((u ∈ regularLanguageOf c₁ ∧ u ∉ regularLanguageOf c₂) ∨
        (u ∉ regularLanguageOf c₁ ∧ u ∈ regularLanguageOf c₂)) := by
  classical
  let g₁ := toRG c₁
  let g₂ := toRG c₂
  let M₁ := (NFA_of_RG g₁).toDFA
  let M₂ := (NFA_of_RG g₂).toDFA
  let P := productDFA M₁ M₂
  have hM₁ : M₁.accepts = regularLanguageOf c₁ := by
    simp [M₁, g₁, NFA.toDFA_correct, NFA_of_RG_accepts, rgLanguage_toRG]
  have hM₂ : M₂.accepts = regularLanguageOf c₂ := by
    simp [M₂, g₂, NFA.toDFA_correct, NFA_of_RG_accepts, rgLanguage_toRG]
  have hwAcc : P.eval w ∈ P.accept := by
    change ((P.eval w).1 ∈ M₁.accept ∧ (P.eval w).2 ∉ M₂.accept) ∨
      ((P.eval w).1 ∉ M₁.accept ∧ (P.eval w).2 ∈ M₂.accept)
    rw [show P.eval w = (M₁.eval w, M₂.eval w) by
      simpa [P] using productDFA_eval M₁ M₂ w]
    simpa [← hM₁, ← hM₂, DFA.mem_accepts] using hw
  obtain ⟨u, huLen, huEval⟩ := P.short_word_of_reachable w
  refine ⟨u, huLen.trans (productDFA_card_le_regularEquivalenceSearchBound c₁ c₂), ?_⟩
  have huAcc : P.eval u ∈ P.accept := by
    change P.evalFrom P.start u ∈ P.accept
    rwa [huEval]
  have huAcc' :
      (M₁.eval u ∈ M₁.accept ∧ M₂.eval u ∉ M₂.accept) ∨
        (M₁.eval u ∉ M₁.accept ∧ M₂.eval u ∈ M₂.accept) := by
    change ((P.eval u).1 ∈ M₁.accept ∧ (P.eval u).2 ∉ M₂.accept) ∨
      ((P.eval u).1 ∉ M₁.accept ∧ (P.eval u).2 ∈ M₂.accept) at huAcc
    rw [show P.eval u = (M₁.eval u, M₂.eval u) by
      simpa [P] using productDFA_eval M₁ M₂ u] at huAcc
    exact huAcc
  simpa [← hM₁, ← hM₂, DFA.mem_accepts] using huAcc'

private def boolNe (a b : Bool) : Bool :=
  !(decide (a = b))

private lemma boolNe_true_iff (a b : Bool) :
    boolNe a b = true ↔ a ≠ b := by
  cases a <;> cases b <;> simp [boolNe]

private theorem boolNe_primrec : Primrec (fun p : Bool × Bool => boolNe p.1 p.2) := by
  unfold boolNe
  exact Primrec.not.comp (Primrec.beq.comp Primrec.fst Primrec.snd)

private def regularEquivalenceBadWith (mem : EncodedRG T × List T → Bool)
    (p : EncodedRG T × EncodedRG T) (w : List T) : Bool :=
  boolNe (mem (p.1, w)) (mem (p.2, w))

private def regularEquivalenceCandidates (alphabet : List T)
    (p : EncodedRG T × EncodedRG T) : List (List T) :=
  wordsUpTo alphabet (regularEquivalenceSearchBound p)

private def regularEquivalenceCheckWithMem (mem : EncodedRG T × List T → Bool)
    (alphabet : List T) (p : EncodedRG T × EncodedRG T) : Bool :=
  !wordSearch (regularEquivalenceCandidates alphabet p) (regularEquivalenceBadWith mem p)

private theorem regularEquivalenceSearchBound_primrec [Primcodable T] :
    Primrec (regularEquivalenceSearchBound : EncodedRG T × EncodedRG T → ℕ) := by
  unfold regularEquivalenceSearchBound
  exact Primrec.nat_mul.comp
    (regularSearchBound_primrec.comp Primrec.fst)
    (regularSearchBound_primrec.comp Primrec.snd)

private theorem regularEquivalenceCandidates_primrec [Primcodable T] (alphabet : List T) :
    Primrec (fun p : EncodedRG T × EncodedRG T =>
      regularEquivalenceCandidates alphabet p) := by
  change Primrec (fun p : EncodedRG T × EncodedRG T =>
    wordsUpTo alphabet (regularEquivalenceSearchBound p))
  exact wordsUpTo_primrec.comp
    (Primrec.pair (Primrec.const alphabet) regularEquivalenceSearchBound_primrec)

private theorem regularEquivalenceBadWith_computable [Primcodable T]
    {mem : EncodedRG T × List T → Bool} (hmem : Computable mem) :
    Computable₂ (regularEquivalenceBadWith mem :
      EncodedRG T × EncodedRG T → List T → Bool) := by
  apply Computable₂.mk
  have h₁ : Computable (fun q : (EncodedRG T × EncodedRG T) × List T =>
      mem (q.1.1, q.2)) :=
    hmem.comp (Primrec.to_comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
  have h₂ : Computable (fun q : (EncodedRG T × EncodedRG T) × List T =>
      mem (q.1.2, q.2)) :=
    hmem.comp (Primrec.to_comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
  change Computable (fun q : (EncodedRG T × EncodedRG T) × List T =>
    boolNe (mem (q.1.1, q.2)) (mem (q.1.2, q.2)))
  exact boolNe_primrec.to_comp.comp (h₁.pair h₂)

private theorem regularEquivalenceCheckWithMem_computable [Primcodable T]
    (alphabet : List T) {mem : EncodedRG T × List T → Bool} (hmem : Computable mem) :
    Computable (regularEquivalenceCheckWithMem mem alphabet :
      EncodedRG T × EncodedRG T → Bool) := by
  have hsearch : Computable (fun p : EncodedRG T × EncodedRG T =>
      wordSearch (regularEquivalenceCandidates alphabet p) (regularEquivalenceBadWith mem p)) :=
    wordSearch_computable (regularEquivalenceCandidates_primrec alphabet).to_comp
      (regularEquivalenceBadWith_computable hmem)
  change Computable (fun p : EncodedRG T × EncodedRG T =>
    !wordSearch (regularEquivalenceCandidates alphabet p) (regularEquivalenceBadWith mem p))
  exact Primrec.not.to_comp.comp hsearch

private theorem regularEquivalenceBadWith_true_of_separator [Fintype T]
    {mem : EncodedRG T × List T → Bool}
    (hmem : ∀ c w, mem (c, w) = true ↔ w ∈ regularLanguageOf c)
    (p : EncodedRG T × EncodedRG T) {w : List T}
    (hw : (w ∈ regularLanguageOf p.1 ∧ w ∉ regularLanguageOf p.2) ∨
      (w ∉ regularLanguageOf p.1 ∧ w ∈ regularLanguageOf p.2)) :
    regularEquivalenceBadWith mem p w = true := by
  rcases hw with ⟨hw₁, hw₂⟩ | ⟨hw₁, hw₂⟩
  · have h₁ : mem (p.1, w) = true := (hmem p.1 w).mpr hw₁
    have h₂ : mem (p.2, w) = false :=
      Bool.eq_false_of_not_eq_true fun h => hw₂ ((hmem p.2 w).mp h)
    simp [regularEquivalenceBadWith, boolNe, h₁, h₂]
  · have h₁ : mem (p.1, w) = false :=
      Bool.eq_false_of_not_eq_true fun h => hw₁ ((hmem p.1 w).mp h)
    have h₂ : mem (p.2, w) = true := (hmem p.2 w).mpr hw₂
    simp [regularEquivalenceBadWith, boolNe, h₁, h₂]

private theorem regularEquivalenceCheckWithMem_correct [Fintype T] [DecidableEq T]
    (mem : EncodedRG T × List T → Bool)
    (hmem : ∀ c w, mem (c, w) = true ↔ w ∈ regularLanguageOf c)
    (p : EncodedRG T × EncodedRG T) :
    regularEquivalenceCheckWithMem mem ((Finset.univ : Finset T).toList) p = true ↔
      regularLanguageOf p.1 = regularLanguageOf p.2 := by
  unfold regularEquivalenceCheckWithMem regularEquivalenceCandidates
  constructor
  · intro hcheck
    have hNoSearch :
        wordSearch
          (wordsUpTo ((Finset.univ : Finset T).toList) (regularEquivalenceSearchBound p))
          (regularEquivalenceBadWith mem p) = false := by
      cases hsearch :
          wordSearch
            (wordsUpTo ((Finset.univ : Finset T).toList) (regularEquivalenceSearchBound p))
            (regularEquivalenceBadWith mem p)
      · rfl
      · have hFalse :
            wordSearch
              (wordsUpTo ((Finset.univ : Finset T).toList) (regularEquivalenceSearchBound p))
              (regularEquivalenceBadWith mem p) = false := by
          simpa using hcheck
        rwa [hsearch] at hFalse
    ext w
    have hCheckEq : mem (p.1, w) = mem (p.2, w) := by
      cases h₁ : mem (p.1, w) <;> cases h₂ : mem (p.2, w)
      · rfl
      · have hsep :
            (w ∈ regularLanguageOf p.1 ∧ w ∉ regularLanguageOf p.2) ∨
              (w ∉ regularLanguageOf p.1 ∧ w ∈ regularLanguageOf p.2) := by
          right
          constructor
          · intro hw
            have hwTrue : mem (p.1, w) = true := (hmem p.1 w).mpr hw
            rw [h₁] at hwTrue
            contradiction
          · exact (hmem p.2 w).mp h₂
        obtain ⟨u, huLen, huSep⟩ := exists_short_regular_separator p.1 p.2 hsep
        have hSearch :
            wordSearch
              (wordsUpTo ((Finset.univ : Finset T).toList) (regularEquivalenceSearchBound p))
              (regularEquivalenceBadWith mem p) = true := by
          rw [wordSearch_true_iff_exists_mem]
          refine ⟨u, ?_, regularEquivalenceBadWith_true_of_separator hmem p huSep⟩
          rw [mem_wordsUpTo_univ]
          exact huLen
        rw [hNoSearch] at hSearch
        contradiction
      · have hsep :
            (w ∈ regularLanguageOf p.1 ∧ w ∉ regularLanguageOf p.2) ∨
              (w ∉ regularLanguageOf p.1 ∧ w ∈ regularLanguageOf p.2) := by
          left
          constructor
          · exact (hmem p.1 w).mp h₁
          · intro hw
            have hwTrue : mem (p.2, w) = true := (hmem p.2 w).mpr hw
            rw [h₂] at hwTrue
            contradiction
        obtain ⟨u, huLen, huSep⟩ := exists_short_regular_separator p.1 p.2 hsep
        have hSearch :
            wordSearch
              (wordsUpTo ((Finset.univ : Finset T).toList) (regularEquivalenceSearchBound p))
              (regularEquivalenceBadWith mem p) = true := by
          rw [wordSearch_true_iff_exists_mem]
          refine ⟨u, ?_, regularEquivalenceBadWith_true_of_separator hmem p huSep⟩
          rw [mem_wordsUpTo_univ]
          exact huLen
        rw [hNoSearch] at hSearch
        contradiction
      · rfl
    constructor
    · intro hw
      have h₁ : mem (p.1, w) = true := (hmem p.1 w).mpr hw
      rw [hCheckEq] at h₁
      exact (hmem p.2 w).mp h₁
    · intro hw
      have h₂ : mem (p.2, w) = true := (hmem p.2 w).mpr hw
      rw [← hCheckEq] at h₂
      exact (hmem p.1 w).mp h₂
  · intro hEq
    have hNoSearch :
        wordSearch
          (wordsUpTo ((Finset.univ : Finset T).toList) (regularEquivalenceSearchBound p))
          (regularEquivalenceBadWith mem p) = false := by
      cases hSearch :
          wordSearch
            (wordsUpTo ((Finset.univ : Finset T).toList) (regularEquivalenceSearchBound p))
            (regularEquivalenceBadWith mem p)
      · rfl
      · rw [wordSearch_true_iff_exists_mem] at hSearch
        rcases hSearch with ⟨w, _, hwBad⟩
        have hne : mem (p.1, w) ≠ mem (p.2, w) := by
          simpa [regularEquivalenceBadWith] using (boolNe_true_iff _ _).mp hwBad
        have hEqCheck : mem (p.1, w) = mem (p.2, w) := by
          cases h₁ : mem (p.1, w) <;> cases h₂ : mem (p.2, w)
          · rfl
          · exfalso
            have hw₂ : w ∈ regularLanguageOf p.2 := (hmem p.2 w).mp h₂
            have hw₁ : w ∈ regularLanguageOf p.1 := by
              simpa [hEq] using hw₂
            have hw₁True : mem (p.1, w) = true := (hmem p.1 w).mpr hw₁
            rw [h₁] at hw₁True
            contradiction
          · exfalso
            have hw₁ : w ∈ regularLanguageOf p.1 := (hmem p.1 w).mp h₁
            have hw₂ : w ∈ regularLanguageOf p.2 := by
              simpa [hEq] using hw₁
            have hw₂True : mem (p.2, w) = true := (hmem p.2 w).mpr hw₂
            rw [h₂] at hw₂True
            contradiction
          · rfl
        exfalso
        exact hne hEqCheck
    rw [hNoSearch]
    rfl

/-- The raw uniform equivalence decider for encoded right-regular grammars. -/
public theorem regular_equivalence_computablePred [Fintype T] [DecidableEq T] [Primcodable T] :
    ComputablePred
      (fun p : EncodedRG T × EncodedRG T => regularLanguageOf p.1 = regularLanguageOf p.2) := by
  obtain ⟨mem, hmem_comp, hmem_eq⟩ :=
    ComputablePred.computable_iff.mp (regular_membership_computablePred (T := T))
  have hmem_correct : ∀ c w, mem (c, w) = true ↔ w ∈ regularLanguageOf c := by
    intro c w
    have hprop := congrFun hmem_eq (c, w)
    change (w ∈ regularLanguageOf c) = (mem (c, w) = true) at hprop
    rw [hprop]
  rw [ComputablePred.computable_iff]
  refine ⟨regularEquivalenceCheckWithMem mem ((Finset.univ : Finset T).toList), ?_, ?_⟩
  · exact regularEquivalenceCheckWithMem_computable ((Finset.univ : Finset T).toList) hmem_comp
  funext p
  exact propext (regularEquivalenceCheckWithMem_correct mem hmem_correct p).symm

/-- **Equivalence is uniformly computable** for the regular languages: encoded
right-regular grammars are an adequate, effective presentation
(`regularLanguageOf_characterizes`) with uniformly decidable equivalence. -/
public theorem regular_computableEquivalence [Fintype T] [DecidableEq T] [Primcodable T] :
    ComputableEquivalence RG (regularLanguageOf : EncodedRG T → Language T) :=
  ⟨regularLanguageOf_characterizes, regular_membership_computablePred.to_re,
    regular_equivalence_computablePred⟩

end Regular.EncodedRG
