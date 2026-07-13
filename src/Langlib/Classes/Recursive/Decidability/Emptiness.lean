module

public import Langlib.Classes.Recursive.Decidability.Reduction
public import Langlib.Utilities.ComputabilityPredicates

@[expose]
public section

/-!
# Undecidability of emptiness for promised recursive deciders

Recursive-language membership is uniformly decidable when a raw program code is
promised to halt on every word.  Emptiness is not.  The reduction below maps an
arbitrary source program `c` to an always-halting decider which, on a word of
length `k`, accepts exactly when `c` halts on input `0` within bounded-evaluation
budget `k`.

Every generated target code satisfies `RecursiveDeciderCode.Valid`, independently
of whether the source computation halts.  Over a nonempty alphabet there are words
of every length, so its language is empty exactly when the source does not halt.
This would turn a promise algorithm for emptiness into a decider for the halting
problem.

The nonempty-alphabet assumption is necessary: over an empty alphabet the only
word is `[]`, and emptiness of a valid decider is a single membership query.
-/

namespace RecursiveDeciderCode

open Nat.Partrec

variable {T : Type} [Primcodable T]

/-- The total bounded-halting test used in the emptiness reduction.  The word
length supplies the finite evaluation budget. -/
@[expose]
public def boundedHaltingTest (c : Code) (w : List T) : Bool :=
  (Code.evaln w.length c 0).isSome

/-- The bounded-halting test is computable jointly in the source code and word. -/
public theorem boundedHaltingTest_computable₂ :
    Computable₂ (boundedHaltingTest (T := T)) := by
  apply Computable₂.mk
  have hEval : Primrec (fun p : Code × List T =>
      Code.evaln p.2.length p.1 0) := by
    convert Code.primrec_evaln.comp
      (((Primrec.list_length.comp Primrec.snd).pair Primrec.fst).pair
        (Primrec.const 0)) using 1
  exact (Primrec.option_isSome.comp hEval).to_comp.of_eq fun _ => rfl

/-- Effectively compile the bounded-halting test into a raw recursive-language
decider code. -/
@[expose]
public noncomputable def boundedHaltingCode : Code → Code :=
  compileBool (boundedHaltingTest (T := T))
    (boundedHaltingTest_computable₂ (T := T))

/-- The reduction from source codes to bounded-halting deciders is computable. -/
public theorem boundedHaltingCode_computable :
    Computable (boundedHaltingCode (T := T)) :=
  compileBool_computable (boundedHaltingTest (T := T))
    (boundedHaltingTest_computable₂ (T := T))

/-- Every code produced by the reduction is valid, whether or not the source
program halts. -/
public theorem boundedHaltingCode_valid (c : Code) :
    Valid (T := T) (boundedHaltingCode (T := T) c) :=
  compileBool_valid (boundedHaltingTest (T := T))
    (boundedHaltingTest_computable₂ (T := T)) c

/-- Membership in the reduced language is precisely bounded halting. -/
public theorem mem_boundedHaltingCode_iff (c : Code) (w : List T) :
    w ∈ language (T := T) (boundedHaltingCode (T := T) c) ↔
      (Code.evaln w.length c 0).isSome = true := by
  exact mem_language_compileBool_iff (boundedHaltingTest (T := T))
    (boundedHaltingTest_computable₂ (T := T)) c w

/-- Over a nonempty alphabet, the reduced valid language is empty exactly when
the source program does not halt on input zero. -/
public theorem boundedHaltingCode_empty_iff [Nonempty T] (c : Code) :
    language (T := T) (boundedHaltingCode (T := T) c) =
        (∅ : Set (List T)) ↔
      ¬(c.eval 0).Dom := by
  constructor
  · intro hEmpty hDom
    rw [Part.dom_iff_mem] at hDom
    obtain ⟨x, hx⟩ := hDom
    rw [Code.evaln_complete] at hx
    obtain ⟨k, hk⟩ := hx
    let w : List T := List.replicate k (Classical.arbitrary T)
    have hwNot : w ∉ language (T := T) (boundedHaltingCode (T := T) c) := by
      rw [hEmpty]
      exact fun h => h
    apply hwNot
    rw [mem_boundedHaltingCode_iff]
    simp only [w, List.length_replicate]
    cases hEval : Code.evaln k c 0 with
    | none => simp [hEval] at hk
    | some y => rfl
  · intro hNotHalts
    ext w
    constructor
    · intro hw
      rw [mem_boundedHaltingCode_iff] at hw
      cases hEval : Code.evaln w.length c 0 with
      | none => simp [hEval] at hw
      | some y =>
          apply hNotHalts
          rw [Part.dom_iff_mem]
          exact ⟨y, Code.evaln_sound (by simpa [hEval])⟩
    · exact fun h => h.elim

/-- A valid raw code denoting the empty language exists over every computably
encoded alphabet. -/
public theorem exists_valid_empty :
    ∃ c : Code, Valid (T := T) c ∧
      language (T := T) c = (∅ : Set (List T)) := by
  let test : Unit → List T → Bool := fun _ _ => false
  have htest : Computable₂ test := (Computable.const false).to₂
  refine ⟨compileBool test htest (), compileBool_valid test htest (), ?_⟩
  rw [language_compileBool]
  ext w
  simp [test]

/-- Emptiness is not computable even under the semantic promise that the raw
program code is an always-halting word decider. -/
public theorem emptiness_undecidable [Nonempty T] :
    ¬ ComputablePredOnPromise
      (Valid (T := T) : Code → Prop)
      (fun c : Code ↦ language (T := T) c = (∅ : Set (List T))) := by
  rintro ⟨decideEmpty, hPartrec, hDecide⟩
  let run : Code →. Bool := fun c =>
    decideEmpty (boundedHaltingCode (T := T) c)
  have hRunPartrec : Partrec run :=
    hPartrec.comp (boundedHaltingCode_computable (T := T))
  have hRunDom (c : Code) : (run c).Dom :=
    (hDecide (boundedHaltingCode (T := T) c)
      (boundedHaltingCode_valid (T := T) c)).1
  let decide : Code → Bool := fun c => (run c).get (hRunDom c)
  have hDecideComputable : Computable decide :=
    hRunPartrec.of_eq_tot fun c => Part.get_mem (hRunDom c)
  have hNonhalting : ComputablePred (fun c : Code => ¬(c.eval 0).Dom) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨decide, hDecideComputable, ?_⟩
    funext c
    apply propext
    rw [← boundedHaltingCode_empty_iff (T := T) c]
    have hSpec :
        language (T := T) (boundedHaltingCode (T := T) c) =
            (∅ : Set (List T)) ↔ true ∈ run c :=
      (hDecide (boundedHaltingCode (T := T) c)
        (boundedHaltingCode_valid (T := T) c)).2
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

/-- There is no computable emptiness test for the promised raw-code presentation
of the class of recursive languages. -/
public theorem recursive_computableEmptiness_undecidable [Nonempty T] :
    ¬ ComputableEmptiness (Recursive : Set (Language T))
      (language (T := T)) (valid := Valid (T := T)) := by
  intro h
  exact emptiness_undecidable (T := T) h.2.2

end RecursiveDeciderCode
