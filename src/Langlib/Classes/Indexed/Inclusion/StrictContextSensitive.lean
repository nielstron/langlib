module

public import Langlib.Classes.ContextSensitive.Basics.ErasingImage
public import Langlib.Classes.ContextSensitive.Closure.EpsFreeHomomorphism
public import Langlib.Classes.Indexed.Closure.Injection
public import Langlib.Classes.Indexed.Inclusion.ContextSensitive
import Langlib.Classes.ContextSensitive.Inclusion.Recursive
public import Langlib.Classes.RecursivelyEnumerable.Examples.Halting
import Langlib.Classes.Recursive.Inclusion.StrictRecursivelyEnumerable
import Mathlib.Data.Fintype.EquivFin

@[expose]
public section

/-!
# Strict inclusion of indexed languages in context-sensitive languages

Every recursively enumerable language over a finite alphabet is an erasing homomorphic image
of a context-sensitive language.  Apply this construction to the unary halting language.  Its
padded cover uses the binary alphabet `Option Unit` and is context-sensitive.  It cannot be
indexed: indexed languages are closed under arbitrary homomorphisms, so erasing the padding
would make the halting language indexed, hence context-sensitive and therefore recursive.

The resulting binary witness proves `Indexed ⊊ CS`.  Injective terminal relabelling and
reflection transport the witness to every finite alphabet with at least two symbols.

## Main declarations

* `exists_indexedCSStrictWitness`
* `indexedCSStrictWitness`
* `indexedCSStrictWitness_is_CS`
* `indexedCSStrictWitness_erasingImage`
* `indexedCSStrictWitness_not_Indexed`
* `Indexed_subclass_CS_and_exists_strict`
* `Indexed_strict_subclass_CS`
-/

open Grammar.ErasingImage

/-- There is a context-sensitive language over the binary alphabet `Option Unit` whose
padding-erasing image is the unary halting language. -/
public theorem exists_indexedCSStrictWitness :
    ∃ K : Language (Option Unit),
      is_CS K ∧ K.homomorphicImage erasePadding = haltingUnaryLanguage :=
  is_RE_exists_CS_homomorphicImage haltingUnaryLanguage_RE

/-- A binary context-sensitive language whose padding erases to the unary halting
language. -/
public noncomputable def indexedCSStrictWitness : Language (Option Unit) :=
  Classical.choose exists_indexedCSStrictWitness

/-- The binary strictness witness is context-sensitive. -/
public theorem indexedCSStrictWitness_is_CS :
    is_CS indexedCSStrictWitness :=
  (Classical.choose_spec exists_indexedCSStrictWitness).1

/-- Erasing the distinguished padding symbol from the binary witness gives the unary
halting language. -/
public theorem indexedCSStrictWitness_erasingImage :
    indexedCSStrictWitness.homomorphicImage erasePadding = haltingUnaryLanguage :=
  (Classical.choose_spec exists_indexedCSStrictWitness).2

/-- The binary context-sensitive witness is not indexed. -/
public theorem indexedCSStrictWitness_not_Indexed :
    ¬ is_Indexed indexedCSStrictWitness := by
  intro hIndexed
  have hImageIndexed :
      is_Indexed (indexedCSStrictWitness.homomorphicImage erasePadding) :=
    is_Indexed_homomorphicImage indexedCSStrictWitness erasePadding hIndexed
  rw [indexedCSStrictWitness_erasingImage] at hImageIndexed
  have hHaltingCS : is_CS haltingUnaryLanguage :=
    is_CS_of_is_Indexed hImageIndexed
  exact haltingUnaryLanguage_not_Recursive (is_Recursive_of_is_CS hHaltingCS)

/-- Indexed languages are included in context-sensitive languages over every alphabet,
and the inclusion is strict over at least one alphabet. -/
public theorem Indexed_subclass_CS_and_exists_strict :
    (∀ (T : Type) (L : Language T), is_Indexed L → is_CS L) ∧
      (∃ (T : Type) (L : Language T), is_CS L ∧ ¬ is_Indexed L) :=
  ⟨fun _ _ hL => is_CS_of_is_Indexed hL,
    ⟨Option Unit, indexedCSStrictWitness,
      indexedCSStrictWitness_is_CS, indexedCSStrictWitness_not_Indexed⟩⟩

/-- For every finite alphabet with at least two symbols, indexed languages form a strict
subclass of the context-sensitive languages. -/
public theorem Indexed_strict_subclass_CS {T : Type} [Fintype T]
    (hT : 2 ≤ Fintype.card T) :
    (Indexed : Set (Language T)) ⊂ (CS : Set (Language T)) := by
  classical
  have hcard : Fintype.card (Option Unit) ≤ Fintype.card T := by
    simpa using hT
  obtain ⟨e : Option Unit ↪ T⟩ :=
    Function.Embedding.nonempty_of_card_le hcard
  refine ⟨Indexed_subclass_CS, ?_⟩
  intro hCSsubsetIndexed
  have hCSMap : is_CS (Language.map e indexedCSStrictWitness) := by
    have hImage :
        is_CS (indexedCSStrictWitness.homomorphicImage fun a => [e a]) :=
      CS_closedUnderEpsFreeHomomorphism indexedCSStrictWitness
        (fun a => [e a]) (fun _ => by simp) indexedCSStrictWitness_is_CS
    rwa [Language.homomorphicImage, Language.subst_singletons_eq_map] at hImage
  have hIndexedMap : is_Indexed (Language.map e indexedCSStrictWitness) :=
    hCSsubsetIndexed hCSMap
  have hIndexedWitness : is_Indexed indexedCSStrictWitness :=
    Indexed_of_map_injective_Indexed_rev e.injective
      indexedCSStrictWitness hIndexedMap
  exact indexedCSStrictWitness_not_Indexed hIndexedWitness
