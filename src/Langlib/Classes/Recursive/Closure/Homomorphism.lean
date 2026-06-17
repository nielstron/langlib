module

public import Langlib.Classes.Recursive.Decidability.Membership
public import Langlib.Classes.Recursive.Inclusion.StrictRecursivelyEnumerable
import Langlib.Utilities.PrimrecHelpers
import Mathlib.Tactic

@[expose]
public section

/-!
# Recursive Non-Closure Under String Homomorphism

Recursive languages are not closed under arbitrary string homomorphisms.  The counterexample
uses an erasing homomorphism: a recursive source language stores a bounded halting witness in
symbols that are erased by the homomorphism.  After erasure, membership is exactly the unary
halting problem.
-/

open Nat.Partrec

private abbrev HomAlphabet := Bool ⊕ Unit

private abbrev progSym : HomAlphabet := Sum.inl false
private abbrev fuelSym : HomAlphabet := Sum.inl true
private abbrev delimSym : HomAlphabet := Sum.inr ()

private def isProg : HomAlphabet → Bool
  | Sum.inl false => true
  | _ => false

private def isFuel : HomAlphabet → Bool
  | Sum.inl true => true
  | _ => false

private def isDelim : HomAlphabet → Bool
  | Sum.inr _ => true
  | _ => false

private def allProgBool (w : List HomAlphabet) : Bool :=
  !(w.any fun a => !isProg a)

private def allFuelBool (w : List HomAlphabet) : Bool :=
  !(w.any fun a => !isFuel a)

private lemma isProg_eq_true_iff (a : HomAlphabet) : isProg a = true ↔ a = progSym := by
  cases a with
  | inl b => cases b <;> simp [isProg]
  | inr u => cases u; simp [isProg]

private lemma isFuel_eq_true_iff (a : HomAlphabet) : isFuel a = true ↔ a = fuelSym := by
  cases a with
  | inl b => cases b <;> simp [isFuel]
  | inr u => cases u; simp [isFuel]

private lemma isDelim_eq_true_iff (a : HomAlphabet) : isDelim a = true ↔ a = delimSym := by
  cases a with
  | inl b => cases b <;> simp [isDelim]
  | inr u => cases u; simp [isDelim]

private lemma allProgBool_eq_true_iff (w : List HomAlphabet) :
    allProgBool w = true ↔ ∀ a ∈ w, a = progSym := by
  constructor
  · intro h
    have hanyFalse : (w.any fun a => !isProg a) = false := by
      cases hAny : (w.any fun a => !isProg a) <;> simp [allProgBool, hAny] at h ⊢
    rw [List.any_eq_false] at hanyFalse
    intro a ha
    have hnot := hanyFalse a ha
    cases ha' : isProg a <;> simp [ha'] at hnot
    exact (isProg_eq_true_iff a).mp ha'
  · intro h
    have hanyFalse : (w.any fun a => !isProg a) = false := by
      rw [List.any_eq_false]
      intro a ha
      rw [h a ha]
      simp [isProg]
    simp [allProgBool, hanyFalse]

private lemma allFuelBool_eq_true_iff (w : List HomAlphabet) :
    allFuelBool w = true ↔ ∀ a ∈ w, a = fuelSym := by
  constructor
  · intro h
    have hanyFalse : (w.any fun a => !isFuel a) = false := by
      cases hAny : (w.any fun a => !isFuel a) <;> simp [allFuelBool, hAny] at h ⊢
    rw [List.any_eq_false] at hanyFalse
    intro a ha
    have hnot := hanyFalse a ha
    cases ha' : isFuel a <;> simp [ha'] at hnot
    exact (isFuel_eq_true_iff a).mp ha'
  · intro h
    have hanyFalse : (w.any fun a => !isFuel a) = false := by
      rw [List.any_eq_false]
      intro a ha
      rw [h a ha]
      simp [isFuel]
    simp [allFuelBool, hanyFalse]

private lemma isProg_primrec : Primrec isProg :=
  Primrec.dom_finite isProg

private lemma isFuel_primrec : Primrec isFuel :=
  Primrec.dom_finite isFuel

private lemma isDelim_primrec : Primrec isDelim :=
  Primrec.dom_finite isDelim

private lemma allProgBool_primrec : Primrec allProgBool := by
  have hAny : Primrec (fun w : List HomAlphabet => w.any (fun a => !isProg a)) := by
    refine primrec_list_any (f := fun w : List HomAlphabet => w)
      (p := fun _ a => !isProg a) Primrec.id ?_
    exact Primrec₂.mk (Primrec.not.comp (isProg_primrec.comp Primrec.snd))
  simpa [allProgBool] using Primrec.not.comp hAny

private lemma allFuelBool_primrec : Primrec allFuelBool := by
  have hAny : Primrec (fun w : List HomAlphabet => w.any (fun a => !isFuel a)) := by
    refine primrec_list_any (f := fun w : List HomAlphabet => w)
      (p := fun _ a => !isFuel a) Primrec.id ?_
    exact Primrec₂.mk (Primrec.not.comp (isFuel_primrec.comp Primrec.snd))
  simpa [allFuelBool] using Primrec.not.comp hAny

private def boundedHaltingHomTest (w : List HomAlphabet) : Bool :=
  let n := w.findIdx isDelim
  let tail := w.drop (n + 1)
  (((decide (n < w.length) && allProgBool (w.take n)) && allFuelBool tail) &&
    (Nat.Partrec.Code.evaln tail.length (Nat.Partrec.Code.ofNatCode n) 0).isSome)

private def boundedHaltingHomSource : Language HomAlphabet :=
  fun w => boundedHaltingHomTest w = true

private lemma boundedHaltingHomTest_computable :
    Computable boundedHaltingHomTest := by
  have hFind : Primrec (fun w : List HomAlphabet => w.findIdx isDelim) := by
    refine Primrec.list_findIdx (f := fun w : List HomAlphabet => w)
      (p := fun _ a => isDelim a) Primrec.id ?_
    exact Primrec₂.mk (isDelim_primrec.comp Primrec.snd)
  have hLen : Primrec (fun w : List HomAlphabet => w.length) :=
    Primrec.list_length
  have hLt : Primrec (fun w : List HomAlphabet => decide (w.findIdx isDelim < w.length)) :=
    (PrimrecRel.decide Primrec.nat_lt).comp hFind hLen
  have hTake : Primrec (fun w : List HomAlphabet => w.take (w.findIdx isDelim)) :=
    (primrec₂_list_take (α := HomAlphabet)).comp hFind Primrec.id
  have hDrop : Primrec (fun w : List HomAlphabet => w.drop (w.findIdx isDelim + 1)) :=
    (primrec₂_list_drop (α := HomAlphabet)).comp (Primrec.succ.comp hFind) Primrec.id
  have hAllTake : Primrec (fun w : List HomAlphabet => allProgBool (w.take (w.findIdx isDelim))) :=
    allProgBool_primrec.comp hTake
  have hAllTail : Primrec (fun w : List HomAlphabet => allFuelBool (w.drop (w.findIdx isDelim + 1))) :=
    allFuelBool_primrec.comp hDrop
  have hEval : Primrec (fun w : List HomAlphabet =>
      Nat.Partrec.Code.evaln (w.drop (w.findIdx isDelim + 1)).length
        (Nat.Partrec.Code.ofNatCode (w.findIdx isDelim)) 0) := by
    convert Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.list_length.comp hDrop).pair
        ((Primrec.ofNat Nat.Partrec.Code).comp hFind)).pair (Primrec.const 0)) using 1
  have hSome : Primrec (fun w : List HomAlphabet =>
      (Nat.Partrec.Code.evaln (w.drop (w.findIdx isDelim + 1)).length
        (Nat.Partrec.Code.ofNatCode (w.findIdx isDelim)) 0).isSome) :=
    Primrec.option_isSome.comp hEval
  exact (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp hLt hAllTake) hAllTail)
    hSome).to_comp.of_eq (by
      intro w
      simp [boundedHaltingHomTest])

private lemma boundedHaltingHomSource_recursive :
    is_Recursive boundedHaltingHomSource := by
  exact is_Recursive_of_computable_decide boundedHaltingHomSource boundedHaltingHomTest
    boundedHaltingHomTest_computable (fun _ => Iff.rfl)

private def eraseFuelHom : HomAlphabet → List Bool
  | Sum.inl false => [false]
  | Sum.inl true => []
  | Sum.inr () => [true]

private def sourceWitnessWord (w : List Unit) (k : ℕ) : List HomAlphabet :=
  w.map (fun _ => progSym) ++ delimSym :: List.replicate k fuelSym

private def encodeHaltingWord (w : List Unit) : List Bool :=
  w.map (fun _ => false) ++ [true]

private lemma encodeHaltingWord_computable :
    Computable encodeHaltingWord := by
  have hMap : Primrec (fun w : List Unit => w.map (fun _ => false)) := by
    refine Primrec.list_map (f := fun w : List Unit => w) (g := fun _ _ => false)
      Primrec.id ?_
    exact Primrec₂.const false
  exact (Primrec.list_append.to_comp).comp hMap.to_comp (Computable.const [true])

private lemma findIdx_sourceWitnessWord (w : List Unit) (k : ℕ) :
    List.findIdx isDelim (sourceWitnessWord w k) = w.length := by
  have hleft : List.findIdx isDelim (List.replicate w.length (Sum.inl false : HomAlphabet)) =
      w.length := by
    have hleft₀ : List.findIdx isDelim (List.replicate w.length (Sum.inl false : HomAlphabet)) =
        (List.replicate w.length (Sum.inl false : HomAlphabet)).length := by
      rw [List.findIdx_eq_length]
      intro x hx
      have hx' := List.eq_of_mem_replicate hx
      subst x
      rfl
    simpa using hleft₀
  simp [sourceWitnessWord, List.findIdx_append, hleft, List.findIdx_cons, isDelim]

private lemma take_sourceWitnessWord (w : List Unit) (k : ℕ) :
    (sourceWitnessWord w k).take w.length = w.map (fun _ => progSym) := by
  simp [sourceWitnessWord]

private lemma drop_sourceWitnessWord (w : List Unit) (k : ℕ) :
    (sourceWitnessWord w k).drop (w.length + 1) = List.replicate k fuelSym := by
  simp [sourceWitnessWord, List.drop_append]

private lemma length_lt_sourceWitnessWord (w : List Unit) (k : ℕ) :
    w.length < (sourceWitnessWord w k).length := by
  simp [sourceWitnessWord]

private lemma allProgBool_map_prog (w : List Unit) :
    allProgBool (w.map fun _ => progSym) = true := by
  rw [allProgBool_eq_true_iff]
  intro a ha
  rw [List.mem_map] at ha
  rcases ha with ⟨_, _, rfl⟩
  rfl

private lemma allProgBool_replicate_prog (n : ℕ) :
    allProgBool (List.replicate n progSym) = true := by
  rw [allProgBool_eq_true_iff]
  intro a ha
  exact List.eq_of_mem_replicate ha

private lemma allFuelBool_replicate_fuel (k : ℕ) :
    allFuelBool (List.replicate k fuelSym) = true := by
  rw [allFuelBool_eq_true_iff]
  intro a ha
  exact List.eq_of_mem_replicate ha

private lemma boundedHaltingHomTest_sourceWitnessWord (w : List Unit) (k : ℕ) :
    boundedHaltingHomTest (sourceWitnessWord w k) =
      (Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0).isSome := by
  simp [boundedHaltingHomTest, findIdx_sourceWitnessWord, take_sourceWitnessWord,
    drop_sourceWitnessWord, length_lt_sourceWitnessWord, allProgBool_replicate_prog,
    allFuelBool_replicate_fuel]

private lemma flatMap_prog_replicate (n : ℕ) :
    (List.replicate n (Sum.inl false : HomAlphabet)).flatMap eraseFuelHom =
      List.replicate n false := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, eraseFuelHom]

private lemma flatMap_fuel_replicate (n : ℕ) :
    (List.replicate n (Sum.inl true : HomAlphabet)).flatMap eraseFuelHom = [] := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, eraseFuelHom]

private lemma flatMap_sourceWitnessWord (w : List Unit) (k : ℕ) :
    (sourceWitnessWord w k).flatMap eraseFuelHom = encodeHaltingWord w := by
  simp [sourceWitnessWord, encodeHaltingWord, eraseFuelHom, List.flatMap_append,
    flatMap_prog_replicate, flatMap_fuel_replicate]

private lemma mem_prod_singletons_iff_flatMap (w : List α) (h : α → List β) (u : List β) :
    u ∈ (w.map fun a => ({h a} : Language β)).prod ↔ u = w.flatMap h := by
  induction w generalizing u with
  | nil =>
      simp
  | cons a w ih =>
      constructor
      · intro hu
        rw [show (List.map (fun a => ({h a} : Language β)) (a :: w)).prod =
            ({h a} : Language β) * (List.map (fun a => ({h a} : Language β)) w).prod by rfl] at hu
        rw [Language.mem_mul] at hu
        rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        have hu₁' : u₁ = h a := by simpa using hu₁
        have hu₂' : u₂ = w.flatMap h := (ih u₂).mp hu₂
        simp [hu₁', hu₂']
      · intro hu
        subst hu
        rw [show (List.map (fun a => ({h a} : Language β)) (a :: w)).prod =
            ({h a} : Language β) * (List.map (fun a => ({h a} : Language β)) w).prod by rfl]
        rw [Language.mem_mul]
        exact ⟨h a, Set.mem_singleton _, w.flatMap h, (ih _).mpr rfl, rfl⟩

private lemma mem_homomorphicImage_iff_flatMap (L : Language α) (h : α → List β)
    (u : List β) :
    u ∈ L.homomorphicImage h ↔ ∃ w ∈ L, w.flatMap h = u := by
  simp only [Language.homomorphicImage, Language.subst]
  constructor
  · rintro ⟨w, hwL, hu⟩
    exact ⟨w, hwL, ((mem_prod_singletons_iff_flatMap w h u).mp hu).symm⟩
  · rintro ⟨w, hwL, rfl⟩
    exact ⟨w, hwL, (mem_prod_singletons_iff_flatMap w h _).mpr rfl⟩

private lemma flatMap_canonical_of_boundedHaltingHomTest
    {x : List HomAlphabet} (hx : boundedHaltingHomTest x = true) :
    x.flatMap eraseFuelHom =
      List.replicate (x.findIdx isDelim) false ++ [true] := by
  let n := x.findIdx isDelim
  let tail := x.drop (n + 1)
  change (((decide (n < x.length) && allProgBool (x.take n)) && allFuelBool tail) &&
    (Nat.Partrec.Code.evaln tail.length (Nat.Partrec.Code.ofNatCode n) 0).isSome) = true at hx
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hx
  rcases hx with ⟨⟨⟨hnBool, hProg⟩, hFuel⟩, _hEval⟩
  have hn : n < x.length := by
    simpa using hnBool
  have hdelim : x[n] = delimSym := by
    exact (isDelim_eq_true_iff x[n]).mp (List.findIdx_getElem (p := isDelim) (xs := x) (w := hn))
  have hprefix : x.take n = List.replicate n progSym := by
    rw [List.eq_replicate_iff]
    exact ⟨List.length_take_of_le (Nat.le_of_lt hn), (allProgBool_eq_true_iff _).mp hProg⟩
  have htail : tail = List.replicate tail.length fuelSym := by
    rw [List.eq_replicate_iff]
    exact ⟨rfl, (allFuelBool_eq_true_iff _).mp hFuel⟩
  have hdrop : x.drop n = delimSym :: tail := by
    rw [List.drop_eq_getElem_cons hn, hdelim]
  calc
    x.flatMap eraseFuelHom =
        ((x.take n ++ x.drop n).flatMap eraseFuelHom) := by
          rw [List.take_append_drop]
    _ = ((List.replicate n progSym ++ delimSym :: tail).flatMap eraseFuelHom) := by
          rw [hprefix, hdrop]
    _ = List.replicate n false ++ [true] := by
          rw [htail]
          simp [eraseFuelHom, List.flatMap_append, flatMap_prog_replicate,
            flatMap_fuel_replicate]

private lemma encode_mem_homomorphicImage_iff_halting (w : List Unit) :
    encodeHaltingWord w ∈ boundedHaltingHomSource.homomorphicImage eraseFuelHom ↔
      w ∈ haltingUnaryLanguage := by
  constructor
  · intro hw
    rcases (mem_homomorphicImage_iff_flatMap boundedHaltingHomSource eraseFuelHom
      (encodeHaltingWord w)).mp hw with ⟨x, hxSource, hxFlat⟩
    change boundedHaltingHomTest x = true at hxSource
    have hxSourceTest : boundedHaltingHomTest x = true := hxSource
    let n := x.findIdx isDelim
    let tail := x.drop (n + 1)
    change (((decide (n < x.length) && allProgBool (x.take n)) && allFuelBool tail) &&
      (Nat.Partrec.Code.evaln tail.length (Nat.Partrec.Code.ofNatCode n) 0).isSome) = true
        at hxSource
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hxSource
    rcases hxSource with ⟨⟨⟨_hnBool, _hProg⟩, _hFuel⟩, hEvalSome⟩
    have hcanon := flatMap_canonical_of_boundedHaltingHomTest (x := x) hxSourceTest
    have hnLen : n = w.length := by
      have hlen := congrArg List.length (hcanon.symm.trans hxFlat)
      simp [encodeHaltingWord] at hlen
      omega
    rw [hnLen] at hEvalSome
    cases hEval : Nat.Partrec.Code.evaln tail.length (Nat.Partrec.Code.ofNatCode w.length) 0 with
    | none =>
        simp [hEval] at hEvalSome
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
    rw [mem_homomorphicImage_iff_flatMap]
    refine ⟨sourceWitnessWord w k, ?_, flatMap_sourceWitnessWord w k⟩
    change boundedHaltingHomTest (sourceWitnessWord w k) = true
    rw [boundedHaltingHomTest_sourceWitnessWord]
    cases hEval : Nat.Partrec.Code.evaln k (Nat.Partrec.Code.ofNatCode w.length) 0 with
    | none =>
        simp [hEval] at hk
    | some y =>
        rfl

/-- Recursive languages are not closed under arbitrary string homomorphism. -/
public theorem Recursive_notClosedUnderHomomorphism :
    ¬ ClosedUnderHomomorphism is_Recursive := by
  intro hclosed
  have hImage : is_Recursive (boundedHaltingHomSource.homomorphicImage eraseFuelHom) :=
    hclosed boundedHaltingHomSource eraseFuelHom boundedHaltingHomSource_recursive
  obtain ⟨f, hf, hs⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable hImage)
  have hrec : is_Recursive haltingUnaryLanguage := by
    refine is_Recursive_of_computable_decide haltingUnaryLanguage
      (fun w => f (encodeHaltingWord w)) (hf.comp encodeHaltingWord_computable) ?_
    intro w
    have hImageMem : encodeHaltingWord w ∈ boundedHaltingHomSource.homomorphicImage eraseFuelHom ↔
        f (encodeHaltingWord w) = true := by
      simpa using (iff_of_eq (congrFun hs (encodeHaltingWord w)))
    exact (encode_mem_homomorphicImage_iff_halting w).symm.trans hImageMem
  exact haltingUnaryLanguage_not_Recursive hrec

end
