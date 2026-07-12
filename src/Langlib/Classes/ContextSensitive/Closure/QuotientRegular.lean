module

public import Langlib.Classes.ContextSensitive.Closure.IntersectionRegular
public import Langlib.Classes.ContextSensitive.Inclusion.Recursive
public import Langlib.Classes.Recursive.Decidability.Membership
public import Langlib.Classes.Recursive.Inclusion.StrictRecursivelyEnumerable
public import Langlib.Classes.RecursivelyEnumerable.Examples.Halting
public import Langlib.Classes.Regular.Closure.Concatenation
public import Langlib.Classes.Regular.Closure.Star
public import Langlib.Classes.Regular.Examples.SingletonWord
public import Langlib.Grammars.NonContracting.ErasingImage
public import Langlib.Utilities.ClosurePredicates
import Mathlib.Tactic

@[expose]
public section

/-!
# Context-Sensitive Languages Are Not Closed Under Regular Right Quotient

This is the standard Hopcroft--Ullman padding reduction.  The noncontracting simulation of an
unrestricted grammar appends padding to the generated word.  Intersecting with the regular
language `some* none*` keeps representatives whose padding is a suffix; quotienting by `none*`
then exposes the source language.  Instantiating the source with the unary halting language
contradicts the fact that every context-sensitive language is recursive.
-/

open Grammar.ErasingImage

namespace CSQuotientRegular

private def symbolStar {A : Type} (a : A) : Language A :=
  KStar.kstar ({[a]} : Language A)

private lemma flatten_singleton_of_mem {A : Type} (a : A) :
    ∀ blocks : List (List A),
      (∀ y ∈ blocks, y ∈ ({[a]} : Language A)) →
        blocks.flatten = List.replicate blocks.length a
  | [], _ => by simp
  | b :: bs, hmem => by
      have hb : b = [a] := Set.mem_singleton_iff.mp (hmem b (by simp))
      have hbs : ∀ y ∈ bs, y ∈ ({[a]} : Language A) := by
        intro y hy
        exact hmem y (by simp [hy])
      rw [List.flatten_cons, hb, flatten_singleton_of_mem a bs hbs]
      simp [List.replicate_succ]

private lemma symbolStar_mem_iff_replicate {A : Type} (a : A) {w : List A} :
    w ∈ symbolStar a ↔ ∃ k : ℕ, w = List.replicate k a := by
  constructor
  · intro hw
    rw [symbolStar, Language.mem_kstar] at hw
    rcases hw with ⟨blocks, rfl, hblocks⟩
    exact ⟨blocks.length, flatten_singleton_of_mem a blocks hblocks⟩
  · rintro ⟨k, rfl⟩
    rw [symbolStar, Language.mem_kstar]
    refine ⟨List.replicate k [a], ?_, ?_⟩
    · have hmem : ∀ y ∈ List.replicate k [a], y ∈ ({[a]} : Language A) := by
        intro y hy
        exact Set.mem_singleton_iff.mpr (List.eq_of_mem_replicate hy)
      calc
        List.replicate k a =
            List.replicate (List.replicate k [a]).length a := by
          rw [List.length_replicate]
        _ = (List.replicate k [a]).flatten :=
          (flatten_singleton_of_mem a (List.replicate k [a]) hmem).symm
    · intro y hy
      exact Set.mem_singleton_iff.mpr (List.eq_of_mem_replicate hy)

private lemma symbolStar_regular {A : Type} (a : A) : (symbolStar a).IsRegular :=
  (singletonWordLanguage_isRegular [a]).kstar'

private def someStar : Language (Option Unit) := symbolStar (some ())

private def noneStar : Language (Option Unit) := symbolStar none

private def trailingShape : Language (Option Unit) := someStar * noneStar

private lemma someStar_regular : someStar.IsRegular := symbolStar_regular (some ())

private lemma noneStar_regular : noneStar.IsRegular := symbolStar_regular none

private lemma trailingShape_regular : trailingShape.IsRegular :=
  someStar_regular.mul' noneStar_regular

private lemma map_some_mem_someStar (w : List Unit) : w.map some ∈ someStar := by
  apply (symbolStar_mem_iff_replicate (some ())).mpr
  refine ⟨w.length, ?_⟩
  induction w with
  | nil => rfl
  | cons _ w ih => simp [List.replicate_succ, ih]

private lemma someStar_eq_map_some {x : List (Option Unit)} (hx : x ∈ someStar) :
    ∃ w : List Unit, x = w.map some := by
  rcases (symbolStar_mem_iff_replicate (some ())).mp hx with ⟨k, rfl⟩
  exact ⟨List.replicate k (), by simp⟩

private lemma trailingShape_mem (w : List Unit) (k : ℕ) :
    w.map some ++ List.replicate k none ∈ trailingShape := by
  rw [trailingShape, Language.mem_mul]
  exact ⟨w.map some, map_some_mem_someStar w, List.replicate k none,
    (symbolStar_mem_iff_replicate none).mpr ⟨k, rfl⟩, rfl⟩

private lemma flatMap_map_some (w : List Unit) :
    (w.map some).flatMap erasePadding = w := by
  induction w with
  | nil => rfl
  | cons u w ih => cases u; simp [erasePadding, ih]

private lemma flatMap_replicate_none (k : ℕ) :
    (List.replicate k (none : Option Unit)).flatMap erasePadding = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, erasePadding, ih]

private noncomputable def paddedLanguage (g : grammar Unit) : Language (Option Unit) :=
  grammar_language (erasingImageGrammar g)

private noncomputable def paddedNumerator (g : grammar Unit) : Language (Option Unit) :=
  paddedLanguage g ⊓ trailingShape

private theorem paddedNumerator_is_CS (g : grammar Unit) : is_CS (paddedNumerator g) := by
  apply CS_inter_regular (paddedLanguage g) trailingShape
  · exact is_CS_of_is_noncontracting
      ⟨erasingImageGrammar g, erasingImageGrammar_noncontracting g, rfl⟩
  · exact trailingShape_regular

private theorem exposed_padded_eq_map (g : grammar Unit) :
    Language.rightQuotient (paddedNumerator g) noneStar ⊓ someStar =
      Language.map some (grammar_language g) := by
  ext x
  constructor
  · rintro ⟨⟨v, hv, hxv⟩, hxsome⟩
    rcases someStar_eq_map_some hxsome with ⟨w, rfl⟩
    rcases (symbolStar_mem_iff_replicate none).mp hv with ⟨k, rfl⟩
    have hproject := erasingImageGrammar_generates_project g hxv.1
    have hw : w ∈ grammar_language g := by
      simpa [List.flatMap_append, flatMap_map_some, flatMap_replicate_none] using hproject
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    rcases erasingImageGrammar_generates_padded g hw with ⟨k, hk⟩
    refine ⟨?_, map_some_mem_someStar w⟩
    refine ⟨List.replicate k none,
      (symbolStar_mem_iff_replicate none).mpr ⟨k, rfl⟩, ?_⟩
    exact ⟨hk, trailingShape_mem w k⟩

private lemma map_some_computable :
    Computable (fun w : List Unit => w.map some) := by
  exact (Primrec.list_map (f := fun w : List Unit => w)
    (g := fun (_ : List Unit) (u : Unit) => some u) Primrec.id
    (Primrec₂.mk (Primrec.option_some.comp Primrec.snd))).to_comp

private theorem recursive_of_recursive_map_some
    (h : is_Recursive (Language.map some haltingUnaryLanguage)) :
    is_Recursive haltingUnaryLanguage := by
  obtain ⟨f, hf, hs⟩ :=
    ComputablePred.computable_iff.mp (Recursive_membership_computable h)
  refine is_Recursive_of_computable_decide haltingUnaryLanguage
    (fun w => f (w.map some)) (hf.comp map_some_computable) ?_
  intro w
  have hmap : w ∈ haltingUnaryLanguage ↔ w.map some ∈ Language.map some haltingUnaryLanguage := by
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨v, hv, heq⟩
      have hvw : v = w := by
        exact List.map_injective_iff.mpr (Option.some_injective Unit) heq
      simpa [hvw] using hv
  have hdec : w.map some ∈ Language.map some haltingUnaryLanguage ↔
      f (w.map some) = true := by
    exact iff_of_eq (congrFun hs (w.map some))
  exact hmap.trans hdec

end CSQuotientRegular

open CSQuotientRegular

/-- Context-sensitive languages are not closed under right quotient with regular languages. -/
public theorem CS_notClosedUnderRightQuotientWithRegular :
    ¬ ClosedUnderRightQuotientWithRegular (α := Option Unit) is_CS := by
  intro hclosed
  obtain ⟨g, hg⟩ := haltingUnaryLanguage_RE
  have hquot : is_CS (Language.rightQuotient (paddedNumerator g) noneStar) :=
    hclosed (paddedNumerator g) (paddedNumerator_is_CS g) noneStar noneStar_regular
  have hexposed : is_CS
      (Language.rightQuotient (paddedNumerator g) noneStar ⊓ someStar) :=
    CS_inter_regular _ someStar hquot someStar_regular
  have hmapped : is_CS (Language.map some haltingUnaryLanguage) := by
    rw [← hg, ← exposed_padded_eq_map]
    exact hexposed
  exact haltingUnaryLanguage_not_Recursive
    (recursive_of_recursive_map_some (is_Recursive_of_is_CS hmapped))

end
