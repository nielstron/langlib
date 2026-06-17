module

public import Langlib.Classes.Recursive.Decidability.Membership
public import Langlib.Classes.Recursive.Inclusion.StrictRecursivelyEnumerable
public import Langlib.Classes.Regular.Closure.Star
public import Langlib.Classes.Regular.Examples.SingletonWord
import Langlib.Utilities.PrimrecHelpers
import Mathlib.Tactic

@[expose]
public section

/-!
# Recursive Non-Closure Under Right Quotient By A Regular Language

Recursive languages are not closed under right quotient by a regular language.

The counterexample encodes the unary halting problem.  Over `Bool`, let the regular
suffix language be `false*`.  The recursive numerator consists of words
`false^n ++ [true] ++ false^k` such that the program encoded by `n` halts within
bounded time `k`.  Quotienting by `false*` removes the bounded-time certificate and
leaves exactly the unbounded unary halting language on prefixes `false^n ++ [true]`.
-/

open Nat.Partrec

private def falseStar : Language Bool :=
  KStar.kstar (singletonWordLanguage [false])

private lemma falseStar_regular : falseStar.IsRegular := by
  exact (singletonWordLanguage_isRegular [false]).kstar'

private lemma flatten_singleton_false_of_mem :
    ∀ blocks : List (List Bool),
      (∀ y ∈ blocks, y ∈ singletonWordLanguage [false]) →
        blocks.flatten = List.replicate blocks.length false
  | [], _ => by simp
  | b :: bs, hmem => by
      have hb : b = [false] := by simpa [singletonWordLanguage] using hmem b (by simp)
      have hbs : ∀ y ∈ bs, y ∈ singletonWordLanguage [false] := by
        intro y hy
        exact hmem y (by simp [hy])
      rw [List.flatten_cons, hb, flatten_singleton_false_of_mem bs hbs]
      rw [List.length_cons, List.replicate_succ]
      simp

private lemma falseStar_mem_iff_replicate {w : List Bool} :
    w ∈ falseStar ↔ ∃ k : ℕ, w = List.replicate k false := by
  constructor
  · intro hw
    rw [falseStar, Language.mem_kstar] at hw
    rcases hw with ⟨blocks, rfl, hmem⟩
    exact ⟨blocks.length, flatten_singleton_false_of_mem blocks hmem⟩
  · rintro ⟨k, rfl⟩
    rw [falseStar, Language.mem_kstar]
    refine ⟨List.replicate k [false], ?_, ?_⟩
    · have hmem : ∀ y ∈ List.replicate k [false], y ∈ singletonWordLanguage [false] := by
        intro y hy
        simpa [singletonWordLanguage] using List.eq_of_mem_replicate hy
      have hflat := flatten_singleton_false_of_mem (List.replicate k [false]) hmem
      rw [hflat]
      simp
    · intro y hy
      simpa [singletonWordLanguage] using List.eq_of_mem_replicate hy

private def allFalseBool (w : List Bool) : Bool :=
  !(w.any fun b => b)

private lemma allFalseBool_eq_true_iff (w : List Bool) :
    allFalseBool w = true ↔ ∀ b ∈ w, b = false := by
  unfold allFalseBool
  constructor
  · intro h b hb
    cases b
    · rfl
    · exfalso
      have hany : w.any (fun b => b) = true :=
        List.any_eq_true.mpr ⟨true, hb, rfl⟩
      simp [hany] at h
  · intro h
    have hany : w.any (fun b => b) = false := by
      rw [List.any_eq_false]
      intro b hb hbtrue
      rw [h b hb] at hbtrue
      simp at hbtrue
    simp [hany]

private lemma allFalseBool_map_false (w : List Unit) :
    allFalseBool (w.map fun _ => false) = true := by
  rw [allFalseBool_eq_true_iff]
  intro b hb
  rw [List.mem_map] at hb
  rcases hb with ⟨_, _, rfl⟩
  rfl

private lemma allFalseBool_replicate_false (k : ℕ) :
    allFalseBool (List.replicate k false) = true := by
  rw [allFalseBool_eq_true_iff]
  intro b hb
  exact List.eq_of_mem_replicate hb

private lemma allFalseBool_primrec : Primrec allFalseBool := by
  have hAny : Primrec (fun w : List Bool => w.any (fun b => b)) := by
    refine primrec_list_any (f := fun w : List Bool => w) (p := fun _ b => b)
      Primrec.id ?_
    exact Primrec₂.mk Primrec.snd
  simpa [allFalseBool] using Primrec.not.comp hAny

private def boundedHaltingDelimitedTest (w : List Bool) : Bool :=
  let n := w.findIdx id
  let tail := w.drop (n + 1)
  (((decide (n < w.length) && allFalseBool (w.take n)) && allFalseBool tail) &&
    (Nat.Partrec.Code.evaln tail.length (Nat.Partrec.Code.ofNatCode n) 0).isSome)

private def boundedHaltingDelimited : Language Bool :=
  fun w => boundedHaltingDelimitedTest w = true

private lemma boundedHaltingDelimitedTest_computable :
    Computable boundedHaltingDelimitedTest := by
  have hFind : Primrec (fun w : List Bool => w.findIdx id) := by
    refine Primrec.list_findIdx (f := fun w : List Bool => w) (p := fun _ b => b)
      Primrec.id ?_
    exact Primrec₂.mk Primrec.snd
  have hLen : Primrec (fun w : List Bool => w.length) :=
    Primrec.list_length
  have hLt : Primrec (fun w : List Bool => decide (w.findIdx id < w.length)) :=
    (PrimrecRel.decide Primrec.nat_lt).comp hFind hLen
  have hTake : Primrec (fun w : List Bool => w.take (w.findIdx id)) :=
    (primrec₂_list_take (α := Bool)).comp hFind Primrec.id
  have hDrop : Primrec (fun w : List Bool => w.drop (w.findIdx id + 1)) :=
    (primrec₂_list_drop (α := Bool)).comp (Primrec.succ.comp hFind) Primrec.id
  have hAllTake : Primrec (fun w : List Bool => allFalseBool (w.take (w.findIdx id))) :=
    allFalseBool_primrec.comp hTake
  have hAllTail : Primrec (fun w : List Bool => allFalseBool (w.drop (w.findIdx id + 1))) :=
    allFalseBool_primrec.comp hDrop
  have hEval : Primrec (fun w : List Bool =>
      Nat.Partrec.Code.evaln (w.drop (w.findIdx id + 1)).length
        (Nat.Partrec.Code.ofNatCode (w.findIdx id)) 0) := by
    convert Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.list_length.comp hDrop).pair
        ((Primrec.ofNat Nat.Partrec.Code).comp hFind)).pair (Primrec.const 0)) using 1
  have hSome : Primrec (fun w : List Bool =>
      (Nat.Partrec.Code.evaln (w.drop (w.findIdx id + 1)).length
        (Nat.Partrec.Code.ofNatCode (w.findIdx id)) 0).isSome) :=
    Primrec.option_isSome.comp hEval
  exact (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp hLt hAllTake) hAllTail)
    hSome).to_comp.of_eq (by
      intro w
      simp [boundedHaltingDelimitedTest])

private lemma boundedHaltingDelimited_recursive :
    is_Recursive boundedHaltingDelimited := by
  exact is_Recursive_of_computable_decide boundedHaltingDelimited boundedHaltingDelimitedTest
    boundedHaltingDelimitedTest_computable (fun _ => Iff.rfl)

private def encodeHaltingWord (w : List Unit) : List Bool :=
  w.map (fun _ => false) ++ [true]

private lemma encodeHaltingWord_computable :
    Computable encodeHaltingWord := by
  have hMap : Primrec (fun w : List Unit => w.map (fun _ => false)) := by
    refine Primrec.list_map (f := fun w : List Unit => w) (g := fun _ _ => false)
      Primrec.id ?_
    exact Primrec₂.const false
  exact (Primrec.list_append.to_comp).comp hMap.to_comp (Computable.const [true])

private lemma findIdx_encode_append_replicate (w : List Unit) (k : ℕ) :
    List.findIdx id (encodeHaltingWord w ++ List.replicate k false) = w.length := by
  have hleft₀ : List.findIdx id (List.replicate w.length false) =
      (List.replicate w.length false).length := by
    rw [List.findIdx_eq_length]
    intro x hx
    exact (List.mem_replicate.mp hx).2
  have hleft : List.findIdx id (List.replicate w.length false) = w.length := by
    simpa using hleft₀
  simp [encodeHaltingWord, List.findIdx_append, hleft, List.findIdx_cons]

private lemma take_encode_append_replicate (w : List Unit) (k : ℕ) :
    (encodeHaltingWord w ++ List.replicate k false).take w.length =
      w.map (fun _ => false) := by
  simp [encodeHaltingWord]

private lemma drop_encode_append_replicate (w : List Unit) (k : ℕ) :
    (encodeHaltingWord w ++ List.replicate k false).drop (w.length + 1) =
      List.replicate k false := by
  simp [encodeHaltingWord, List.drop_append]

private lemma length_lt_encode_append_replicate (w : List Unit) (k : ℕ) :
    w.length < (encodeHaltingWord w ++ List.replicate k false).length := by
  simp [encodeHaltingWord]

private lemma boundedHaltingDelimitedTest_encode_replicate (w : List Unit) (k : ℕ) :
    boundedHaltingDelimitedTest (encodeHaltingWord w ++ List.replicate k false) =
      (Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0).isSome := by
  have hlt : w.length < (encodeHaltingWord w).length + k := by
    simp [encodeHaltingWord]
    omega
  simp [boundedHaltingDelimitedTest, findIdx_encode_append_replicate,
    take_encode_append_replicate, drop_encode_append_replicate,
    hlt, allFalseBool_replicate_false]

private lemma encode_mem_quotient_iff_halting (w : List Unit) :
    encodeHaltingWord w ∈ Language.rightQuotient boundedHaltingDelimited falseStar ↔
      w ∈ haltingUnaryLanguage := by
  constructor
  · intro hw
    change ∃ v ∈ falseStar, encodeHaltingWord w ++ v ∈ boundedHaltingDelimited at hw
    rcases hw with ⟨v, hv, hvnum⟩
    rcases falseStar_mem_iff_replicate.mp hv with ⟨k, rfl⟩
    change boundedHaltingDelimitedTest
      (encodeHaltingWord w ++ List.replicate k false) = true at hvnum
    rw [boundedHaltingDelimitedTest_encode_replicate] at hvnum
    cases hEval : Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0 with
    | none =>
        simp [hEval] at hvnum
    | some y =>
        change ((Nat.Partrec.Code.ofNatCode w.length).eval 0).Dom
        rw [Part.dom_iff_mem]
        exact ⟨y, Nat.Partrec.Code.evaln_sound (by simpa [hEval])⟩
  · intro hw
    change ((Nat.Partrec.Code.ofNatCode w.length).eval 0).Dom at hw
    rw [Part.dom_iff_mem] at hw
    rcases hw with ⟨x, hx⟩
    rw [Nat.Partrec.Code.evaln_complete] at hx
    rcases hx with ⟨k, hk⟩
    change ∃ v ∈ falseStar, encodeHaltingWord w ++ v ∈ boundedHaltingDelimited
    refine ⟨List.replicate k false, falseStar_mem_iff_replicate.mpr ⟨k, rfl⟩, ?_⟩
    change boundedHaltingDelimitedTest
      (encodeHaltingWord w ++ List.replicate k false) = true
    rw [boundedHaltingDelimitedTest_encode_replicate]
    cases hEval : Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0 with
    | none =>
        simp [hEval] at hk
    | some y =>
        rfl

/-- Recursive languages are not closed under right quotient by regular languages. -/
public theorem Recursive_notClosedUnderRightQuotientWithRegular :
    ¬ ClosedUnderRightQuotientWithRegular (α := Bool) is_Recursive := by
  intro hclosed
  have hquot : is_Recursive (Language.rightQuotient boundedHaltingDelimited falseStar) :=
    hclosed boundedHaltingDelimited boundedHaltingDelimited_recursive falseStar falseStar_regular
  obtain ⟨f, hf, hs⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable hquot)
  have hrec : is_Recursive haltingUnaryLanguage := by
    refine is_Recursive_of_computable_decide haltingUnaryLanguage
      (fun w => f (encodeHaltingWord w)) (hf.comp encodeHaltingWord_computable) ?_
    intro w
    have hq : encodeHaltingWord w ∈ Language.rightQuotient boundedHaltingDelimited falseStar ↔
        f (encodeHaltingWord w) = true := by
      simpa using (iff_of_eq (congrFun hs (encodeHaltingWord w)))
    exact (encode_mem_quotient_iff_halting w).symm.trans hq
  exact haltingUnaryLanguage_not_Recursive hrec

end
