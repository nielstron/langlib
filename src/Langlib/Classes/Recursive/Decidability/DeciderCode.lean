module

public import Langlib.Classes.Recursive.Decidability.Membership
public import Langlib.Utilities.PromiseComputability

@[expose]
public section

/-!
# Recursive languages presented by promised decider codes

The raw codes in this file are Mathlib's `Nat.Partrec.Code`.  Their universal
evaluator is partial on arbitrary codes.  A code is a `Valid` decider when that
evaluator halts on every encoded word; on such codes, `evalBool` uniformly decides
membership in `language`.

This is the promise-problem formulation of uniform membership for the class of
recursive languages.  It does not assert that the set of total program codes is
decidable (it is not), nor does it package those codes as a `Primcodable` subtype.

## Main results

* `RecursiveDeciderCode.eval_decidesMembership` gives the one universal membership
  procedure, total and correct under the validity promise.
* `RecursiveDeciderCode.exists_valid_iff_computablePred` characterizes computable
  membership predicates by valid codes.
* `RecursiveDeciderCode.exists_valid_iff_is_Recursive` specializes that
  characterization to the repository's `is_Recursive` language class.
-/

namespace RecursiveDeciderCode

open Encodable

variable {T : Type} [Primcodable T]

/-- Run a raw partial-recursive code on the encoding of a word and interpret an odd
natural-number result as `true` and an even result as `false`. -/
@[expose]
public def evalBool (c : Nat.Partrec.Code) (w : List T) : Part Bool :=
  (c.eval (encode w)).map Nat.bodd

/-- The semantic promise that a raw program code halts on every encoded word. -/
@[expose]
public def Valid (c : Nat.Partrec.Code) : Prop :=
  ∀ w : List T, (evalBool c w).Dom

/-- The language denoted by a raw decider code: precisely the words on which its
Boolean evaluation returns `true`.  This is meaningful for every raw code, although
only `Valid` codes are promised to decide it totally. -/
@[expose]
public def language (c : Nat.Partrec.Code) : Language T :=
  {w | true ∈ evalBool c w}

/-- The universal Boolean evaluator is partial recursive jointly in the raw code
and the input word. -/
public theorem evalBool_partrec₂ :
    Partrec₂ (evalBool : Nat.Partrec.Code → List T →. Bool) := by
  let natEval : Nat.Partrec.Code × List T →. ℕ := fun p =>
    p.1.eval (encode p.2)
  have hnat : Partrec natEval :=
    Nat.Partrec.Code.eval_part.comp Computable.fst
      (Computable.encode.comp Computable.snd)
  have hbool : Partrec (fun p : Nat.Partrec.Code × List T =>
      (natEval p).map Nat.bodd) :=
    hnat.map ((Computable.nat_bodd.comp Computable.snd).to₂)
  exact hbool.to₂

/-- `evalBool` is a uniform membership decider on the promise that its raw code is
valid. -/
public theorem eval_decidesMembership :
    DecidesOnPromise (Valid (T := T) : Nat.Partrec.Code → Prop)
      (evalBool : Nat.Partrec.Code → List T →. Bool)
      (fun c w => w ∈ language (T := T) c) := by
  exact ⟨⟨evalBool_partrec₂, fun c hc w => hc w⟩, fun _ _ _ => Iff.rfl⟩

/-- A language has a computable membership predicate exactly when it is denoted by
some valid raw partial-recursive decider code. -/
public theorem exists_valid_iff_computablePred (L : Language T) :
    (∃ c : Nat.Partrec.Code, Valid (T := T) c ∧ language (T := T) c = L) ↔
      ComputablePred (fun w : List T => w ∈ L) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    let decide : List T → Bool := fun w => (evalBool c w).get (hc w)
    have heval : Partrec (fun w : List T => evalBool c w) :=
      evalBool_partrec₂.comp (Computable.const c) Computable.id
    have hdecide : Computable decide :=
      heval.of_eq_tot fun w => Part.get_mem (hc w)
    apply ComputablePred.computable_iff.mpr
    refine ⟨decide, hdecide, ?_⟩
    funext w
    apply propext
    change true ∈ evalBool c w ↔ decide w = true
    constructor
    · intro htrue
      exact Part.mem_unique (Part.get_mem (hc w)) htrue
    · intro htrue
      rw [← htrue]
      exact Part.get_mem (hc w)
  · intro hL
    obtain ⟨f, hf, hspec⟩ := ComputablePred.computable_iff.mp hL
    have hnat : Nat.Partrec (fun n =>
        Part.bind (decode (α := List T) n) fun w =>
          (Part.some (f w)).map encode) := hf
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hnat
    have hc_word (w : List T) :
        c.eval (encode w) = Part.some (encode (f w)) := by
      rw [hc]
      simp
    refine ⟨c, ?_, ?_⟩
    · intro w
      simp only [evalBool, hc_word, Part.map_some, Part.some_dom]
    · ext w
      change true ∈ evalBool c w ↔ w ∈ L
      rw [evalBool, hc_word]
      simp only [Part.map_some, Part.mem_some_iff]
      rw [show Nat.bodd (encode (f w)) = f w by cases f w <;> rfl]
      have hw := congrFun hspec w
      simpa using (iff_of_eq hw).symm

/-- Over finite computably encoded alphabets, valid always-halting Boolean decider
codes denote exactly the recursive languages. -/
public theorem exists_valid_iff_is_Recursive
    [DecidableEq T] [Fintype T] (L : Language T) :
    (∃ c : Nat.Partrec.Code, Valid (T := T) c ∧ language (T := T) c = L) ↔
      is_Recursive L := by
  rw [exists_valid_iff_computablePred]
  constructor
  · intro hL
    obtain ⟨f, hf, hspec⟩ := ComputablePred.computable_iff.mp hL
    exact is_Recursive_of_computable_decide L f hf fun w => iff_of_eq (congrFun hspec w)
  · exact Recursive_membership_computable

end RecursiveDeciderCode
