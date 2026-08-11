module

public import Langlib.Classes.ContextFree.Decidability.EncodedHomomorphism
public import Langlib.Classes.Regular.Closure.Complement
public import Langlib.Classes.Regular.Closure.Homomorphism

@[expose]
public section

/-!
# Effective binary encoding of context-free grammar alphabets

This file packages the language-theoretic part of reducing a context-free
grammar over an arbitrary finite nonempty alphabet to one over `Bool`.

Symbols are represented by fixed-width one-hot Boolean blocks.  The induced
map on words is injective.  To preserve universality, the homomorphic image of
the source language is completed by the complement of the regular language of
well-formed block strings.
-/

namespace ContextFree.BinaryEncoding

open ContextFree.EncodedCFG

variable {A B : Type}

private theorem mem_homomorphicImage_iff_flatMap
    (L : Language A) (h : A → List B) (w : List B) :
    w ∈ L.homomorphicImage h ↔ ∃ x ∈ L, x.flatMap h = w := by
  simp only [Language.homomorphicImage, Language.subst]
  constructor
  · rintro ⟨x, hx, hw⟩
    exact ⟨x, hx, ((mem_prod_singletons_iff_flatMap x h w).mp hw).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (mem_prod_singletons_iff_flatMap x h _).mpr rfl⟩

/-- A symbol code of positive fixed width induces an injective code on words. -/
theorem flatMap_injective_of_fixed_length
    (code : A → List B) (width : Nat) (hwidth : 0 < width)
    (hlength : ∀ a, (code a).length = width)
    (hcode : Function.Injective code) :
    Function.Injective (fun w : List A ↦ w.flatMap code) := by
  intro u
  induction u with
  | nil =>
      intro v huv
      cases v with
      | nil => rfl
      | cons b v =>
          have hlen := congrArg List.length huv
          simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons,
            List.length_append] at hlen
          rw [hlength] at hlen
          omega
  | cons a u ih =>
      intro v huv
      cases v with
      | nil =>
          have hlen := congrArg List.length huv
          simp only [List.flatMap_cons, List.length_append, List.flatMap_nil,
            List.length_nil] at hlen
          rw [hlength] at hlen
          omega
      | cons b v =>
          simp only [List.flatMap_cons] at huv
          have hhead : code a = code b := by
            have ht := congrArg (List.take width) huv
            simpa [List.take_append_of_le_length, hlength] using ht
          have htail : u.flatMap code = v.flatMap code := by
            have hd := congrArg (List.drop width) huv
            simpa [List.drop_append_of_le_length, hlength] using hd
          have hab : a = b := hcode hhead
          subst b
          exact congrArg (List.cons a) (ih htail)

/-- The fixed-width one-hot Boolean code associated with an enumeration of a
finite alphabet. -/
def fixedBinaryCode [Fintype A]
    (e : A ≃ Fin (Fintype.card A)) (a : A) : List Bool :=
  List.ofFn fun i : Fin (Fintype.card A) ↦ decide (i = e a)

@[simp]
theorem fixedBinaryCode_length [Fintype A]
    (e : A ≃ Fin (Fintype.card A)) (a : A) :
    (fixedBinaryCode e a).length = Fintype.card A := by
  simp [fixedBinaryCode]

theorem fixedBinaryCode_injective [Fintype A]
    (e : A ≃ Fin (Fintype.card A)) :
    Function.Injective (fixedBinaryCode e) := by
  intro a b hab
  have hfun :
      (fun i : Fin (Fintype.card A) ↦ decide (i = e a)) =
        (fun i : Fin (Fintype.card A) ↦ decide (i = e b)) :=
    List.ofFn_injective hab
  have hat := congrFun hfun (e a)
  have hat' : decide (e a = e b) = true := by
    simpa using hat.symm
  exact e.injective (of_decide_eq_true hat')

theorem fixedBinaryWordCode_injective [Fintype A] [Nonempty A]
    (e : A ≃ Fin (Fintype.card A)) :
    Function.Injective
      (fun w : List A ↦ w.flatMap (fixedBinaryCode e)) := by
  apply flatMap_injective_of_fixed_length (fixedBinaryCode e)
      (Fintype.card A)
  · exact Fintype.card_pos
  · exact fixedBinaryCode_length e
  · exact fixedBinaryCode_injective e

/-- Completing an injective word encoding by all ill-formed target strings
preserves and reflects universality. -/
theorem homomorphicImage_add_compl_eq_univ_iff
    (code : A → List B)
    (hcode : Function.Injective (fun w : List A ↦ w.flatMap code))
    (L : Language A) :
    L.homomorphicImage code +
        (Language.homomorphicImage (Set.univ : Language A) code)ᶜ =
          Set.univ ↔
      L = Set.univ := by
  constructor
  · intro hall
    apply Set.eq_univ_of_forall
    intro w
    have hw : w.flatMap code ∈
        L.homomorphicImage code +
          (Language.homomorphicImage (Set.univ : Language A) code)ᶜ := by
      rw [hall]
      exact Set.mem_univ _
    rw [Language.mem_add] at hw
    rcases hw with himage | hout
    · obtain ⟨u, hu, heq⟩ :=
        (mem_homomorphicImage_iff_flatMap L code _).mp himage
      exact hcode heq |>.symm ▸ hu
    · exact False.elim (hout
        ((mem_homomorphicImage_iff_flatMap
          (Set.univ : Language A) code _).mpr
            ⟨w, Set.mem_univ _, rfl⟩))
  · intro hL
    apply Set.eq_univ_of_forall
    intro w
    rw [Language.mem_add]
    by_cases hw :
        w ∈ Language.homomorphicImage (Set.univ : Language A) code
    · exact Or.inl (by simpa [hL] using hw)
    · exact Or.inr hw

/-- A word homomorphism maps the union of epsilon and `L` to the union of
epsilon and the image of `L`. -/
theorem homomorphicImage_epsilon_add (code : A → List B)
    (L : Language A) :
    (({[]} : Language A) + L).homomorphicImage code =
      ({[]} : Language B) + L.homomorphicImage code := by
  ext w
  rw [Language.mem_add]
  constructor
  · intro hw
    obtain ⟨u, hu, heq⟩ :=
      (mem_homomorphicImage_iff_flatMap
        (({[]} : Language A) + L) code w).mp hw
    rw [Language.mem_add] at hu
    rcases hu with hu | hu
    · have hu' : u = [] := by simpa using hu
      subst u
      exact Or.inl (by simpa using heq.symm)
    · exact Or.inr
        ((mem_homomorphicImage_iff_flatMap L code w).mpr
          ⟨u, hu, heq⟩)
  · rintro (hw | hw)
    · have hw' : w = [] := by simpa using hw
      subst w
      apply (mem_homomorphicImage_iff_flatMap
        (({[]} : Language A) + L) code []).mpr
      exact ⟨[], Or.inl (Set.mem_singleton []), rfl⟩
    · obtain ⟨u, hu, heq⟩ :=
        (mem_homomorphicImage_iff_flatMap L code w).mp hw
      apply (mem_homomorphicImage_iff_flatMap
        (({[]} : Language A) + L) code w).mpr
      exact ⟨u, Or.inr hu, heq⟩

/-- Epsilon completion commutes with the injective coding argument used for
positive grammar cores. -/
theorem epsilon_add_homomorphicImage_add_compl_eq_univ_iff
    (code : A → List B)
    (hcode : Function.Injective (fun w : List A ↦ w.flatMap code))
    (L : Language A) :
    (({[]} : Language B) + L.homomorphicImage code) +
        (Language.homomorphicImage (Set.univ : Language A) code)ᶜ =
          Set.univ ↔
      ({[]} : Language A) + L = Set.univ := by
  rw [← homomorphicImage_epsilon_add code L]
  exact homomorphicImage_add_compl_eq_univ_iff code hcode _

private def universalDFA : DFA A Unit where
  start := ()
  step _ _ := ()
  accept := Set.univ

private theorem univ_isRegular :
    Language.IsRegular (Set.univ : Language A) := by
  refine ⟨Unit, inferInstance, universalDFA, ?_⟩
  apply Set.eq_univ_of_forall
  intro w
  change (universalDFA (A := A)).eval w ∈ Set.univ
  exact Set.mem_univ _

/-- Every effective grammar alphabet can be compiled into the fixed binary
alphabet while preserving universality after adding the isolated epsilon
start rule.  If the source grammar has no empty right-hand sides, neither does
the binary core produced by `encode`. -/
theorem exists_binaryEncoding
    [Fintype A] [Nonempty A] [Primcodable A] :
    ∃ encode : EncodedCFG A → EncodedCFG Bool,
      Primrec encode ∧
      (∀ G, NoEmptyRHS G → NoEmptyRHS (encode G)) ∧
      ∀ G,
        contextFreeLanguageOf (addEpsilonStart (encode G)) = Set.univ ↔
          contextFreeLanguageOf (addEpsilonStart G) = Set.univ := by
  classical
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let code : A → List Bool := fixedBinaryCode e
  have hcodeLength (a : A) :
      (code a).length = Fintype.card A := by
    exact fixedBinaryCode_length e a
  have heps : IsEpsFreeHomomorphism code := by
    intro a
    apply List.ne_nil_of_length_pos
    rw [hcodeLength]
    exact Fintype.card_pos
  have hwordCode :
      Function.Injective (fun w : List A ↦ w.flatMap code) := by
    exact fixedBinaryWordCode_injective e
  let valid : Language Bool :=
    Language.homomorphicImage (Set.univ : Language A) code
  have hvalidRegular : Language.IsRegular valid := by
    exact (univ_isRegular (A := A)).homomorphicImage code
  obtain ⟨bad, hbadNoEmpty, hbadLanguage⟩ :=
    exists_noEmptyRHS_code
      (is_CF_of_is_RG (is_RG_of_isRegular hvalidRegular.compl))
  have hemptyValid : [] ∈ valid := by
    apply (mem_homomorphicImage_iff_flatMap
      (Set.univ : Language A) code []).mpr
    exact ⟨[], Set.mem_univ _, rfl⟩
  have hbadLanguage' : contextFreeLanguageOf bad = validᶜ := by
    rw [hbadLanguage]
    apply Set.Subset.antisymm
    · exact Set.diff_subset
    · intro w hw
      refine ⟨hw, ?_⟩
      intro hnil
      have hwNil : w = [] := hnil
      subst w
      exact hw hemptyValid
  let encode : EncodedCFG A → EncodedCFG Bool := fun G ↦
    union (ContextFree.EncodedCFG.homomorphicImage code G) bad
  have hencodePrimrec : Primrec encode := by
    change Primrec (fun G ↦
      union (ContextFree.EncodedCFG.homomorphicImage code G) bad)
    exact union_primrec₂.comp
      (homomorphicImage_primrec code) (Primrec.const bad)
  refine ⟨encode, hencodePrimrec, ?_, ?_⟩
  · intro G hG
    change NoEmptyRHS
      (union (ContextFree.EncodedCFG.homomorphicImage code G) bad)
    exact noEmptyRHS_union
      (noEmptyRHS_homomorphicImage hG heps) hbadNoEmpty
  · intro G
    change
      contextFreeLanguageOf
          (addEpsilonStart
            (union (ContextFree.EncodedCFG.homomorphicImage code G) bad)) =
            Set.univ ↔
        contextFreeLanguageOf (addEpsilonStart G) = Set.univ
    rw [contextFreeLanguageOf_addEpsilonStart,
      contextFreeLanguageOf_union,
      contextFreeLanguageOf_homomorphicImage code G heps,
      hbadLanguage', contextFreeLanguageOf_addEpsilonStart]
    simpa only [valid, add_assoc] using
      (epsilon_add_homomorphicImage_add_compl_eq_univ_iff
        code hwordCode (contextFreeLanguageOf G))

end ContextFree.BinaryEncoding
