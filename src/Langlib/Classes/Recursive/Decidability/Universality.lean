module

public import Langlib.Classes.Recursive.Decidability.Reduction
public import Langlib.Utilities.ComputabilityPredicates

@[expose]
public section

/-!
# Undecidability of universality for recursive languages

Recursive languages are presented by raw partial-recursive program codes under
the semantic promise `RecursiveDeciderCode.Valid` that the program halts on every
encoded word.  Universality is not uniformly decidable even under that promise.

The reduction compiles a source computation `c.eval n` into an always-halting
word decider.  On a word of length `k`, the compiled decider accepts exactly when
bounded evaluation has not found the source computation within budget `k`.  Over
a nonempty alphabet there are words of every length, so the compiled language is
universal exactly when `c.eval n` does not halt.

The nonempty-alphabet hypothesis is necessary: over the empty alphabet there is
only the empty word, so universality of a promised decider is just one membership
query.
-/

namespace RecursiveDeciderCode

open Nat.Partrec

variable {T : Type} [Primcodable T]

/-- The total bounded test used by the universality reduction. -/
private def boundedNonhaltingTest
    (p : Code × ℕ) (w : List T) : Bool :=
  !(Code.evaln w.length p.1 p.2).isSome

private theorem boundedNonhaltingTest_computable₂ :
    Computable₂ (boundedNonhaltingTest (T := T)) := by
  apply Computable₂.mk
  have hEval : Primrec (fun p : (Code × ℕ) × List T =>
      Code.evaln p.2.length p.1.1 p.1.2) := by
    convert Code.primrec_evaln.comp
      (((Primrec.list_length.comp Primrec.snd).pair
        (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst)) using 1
  exact (Primrec.not.comp (Primrec.option_isSome.comp hEval)).to_comp.of_eq fun _ => rfl

/-- The valid decider compiled from the bounded test is universal exactly when
the source computation does not halt.  Nonemptiness supplies a word of every
finite length. -/
private theorem compiledBoundedNonhalting_universal_iff
    [Nonempty T] (c : Code) (n : ℕ) :
    language (T := T)
        (compileBool (boundedNonhaltingTest (T := T))
          (boundedNonhaltingTest_computable₂ (T := T)) (c, n)) =
      Set.univ ↔ ¬(c.eval n).Dom := by
  constructor
  · intro hUniversal hDom
    rw [Part.dom_iff_mem] at hDom
    obtain ⟨x, hx⟩ := hDom
    rw [Code.evaln_complete] at hx
    obtain ⟨k, hk⟩ := hx
    let w : List T := List.replicate k (Classical.arbitrary T)
    have hw : w ∈ language (T := T)
        (compileBool (boundedNonhaltingTest (T := T))
          (boundedNonhaltingTest_computable₂ (T := T)) (c, n)) := by
      rw [hUniversal]
      trivial
    rw [mem_language_compileBool_iff] at hw
    change (!(Code.evaln w.length c n).isSome) = true at hw
    simp only [w, List.length_replicate] at hw
    cases hEval : Code.evaln k c n with
    | none => simp [hEval] at hk
    | some y => simp [hEval] at hw
  · intro hNotHalts
    ext w
    constructor
    · intro _
      trivial
    · intro _
      rw [mem_language_compileBool_iff]
      change (!(Code.evaln w.length c n).isSome) = true
      cases hEval : Code.evaln w.length c n with
      | none => rfl
      | some y =>
          exfalso
          apply hNotHalts
          rw [Part.dom_iff_mem]
          exact ⟨y, Code.evaln_sound (by simpa [hEval])⟩

/-- No promise algorithm can decide universality of valid always-halting decider
codes.  This holds over every nonempty computably encoded alphabet; the algorithm
is allowed to diverge on invalid raw codes. -/
public theorem universality_undecidable [Nonempty T] :
    ¬ ComputablePredOnPromise
      (Valid (T := T) : Code → Prop)
      (fun c : Code ↦ language (T := T) c = Set.univ) := by
  rintro ⟨evalUniversal, hEvalPartrec, hEvalSpec⟩
  let reduction : Code → Code := fun c =>
    compileBool (boundedNonhaltingTest (T := T))
      (boundedNonhaltingTest_computable₂ (T := T)) (c, 0)
  have hReduction : Computable reduction :=
    (compileBool_computable (boundedNonhaltingTest (T := T))
      (boundedNonhaltingTest_computable₂ (T := T))).comp
      (Computable.pair Computable.id (Computable.const 0))
  let run : Code →. Bool := fun c => evalUniversal (reduction c)
  have hRunPartrec : Partrec run := hEvalPartrec.comp hReduction
  have hReductionValid (c : Code) : Valid (T := T) (reduction c) :=
    compileBool_valid (boundedNonhaltingTest (T := T))
      (boundedNonhaltingTest_computable₂ (T := T)) (c, 0)
  have hRunDom (c : Code) : (run c).Dom :=
    (hEvalSpec (reduction c) (hReductionValid c)).1
  let decide : Code → Bool := fun c => (run c).get (hRunDom c)
  have hDecideComputable : Computable decide :=
    hRunPartrec.of_eq_tot fun c => Part.get_mem (hRunDom c)
  have hNonhalting : ComputablePred (fun c : Code => ¬(c.eval 0).Dom) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨decide, hDecideComputable, ?_⟩
    funext c
    apply propext
    rw [← compiledBoundedNonhalting_universal_iff (T := T) c 0]
    change language (T := T) (reduction c) = Set.univ ↔ decide c = true
    have hSpec : language (T := T) (reduction c) = Set.univ ↔ true ∈ run c := by
      simpa only [run] using (hEvalSpec (reduction c) (hReductionValid c)).2
    rw [hSpec]
    change true ∈ run c ↔ decide c = true
    constructor
    · intro hTrue
      exact Part.mem_unique (Part.get_mem (hRunDom c)) hTrue
    · intro hTrue
      rw [← hTrue]
      exact Part.get_mem (hRunDom c)
  apply ComputablePred.halting_problem 0
  exact hNonhalting.not.of_eq fun c => not_not

/-- **Universality cannot be decided uniformly for recursive languages.**

The result holds for the standard valid-decider presentation over every nonempty
computably encoded alphabet. -/
public theorem recursive_computableUniversality_undecidable [Nonempty T] :
    ¬ ComputableUniversality Recursive (language (T := T))
        (valid := Valid (T := T)) := by
  intro h
  exact universality_undecidable (T := T) h.2.2

end RecursiveDeciderCode
