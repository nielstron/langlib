module

public import Langlib.Classes.Indexed.Closure.Intersection
public import Langlib.Classes.Indexed.Closure.Union

@[expose]
public section

/-!
# Indexed languages are not closed under complement

If indexed languages were closed under complement, their closure under union
would imply closure under intersection by De Morgan's law.  This contradicts
the binary intersection witness, and the same argument applies after its
transport to every alphabet with at least two symbols.
-/

open IndexedIntersectionNonclosure

namespace IndexedComplementNonclosure

/-- Complement closure together with indexed union closure would imply
intersection closure. -/
private theorem intersection_closed_of_complement_closed {α : Type}
    (hcomp : ClosedUnderComplement (α := α) is_Indexed) :
    ClosedUnderIntersection (α := α) is_Indexed := by
  intro L₁ L₂ hL₁ hL₂
  have hcomp₁ : is_Indexed L₁ᶜ := hcomp L₁ hL₁
  have hcomp₂ : is_Indexed L₂ᶜ := hcomp L₂ hL₂
  have hunion : is_Indexed (L₁ᶜ + L₂ᶜ) :=
    Indexed_closedUnderUnion L₁ᶜ L₂ᶜ hcomp₁ hcomp₂
  have hdouble : is_Indexed (L₁ᶜ + L₂ᶜ)ᶜ :=
    hcomp (L₁ᶜ + L₂ᶜ) hunion
  rwa [Language.add_def, Set.compl_union, compl_compl, compl_compl] at hdouble

/-- Indexed languages over the binary alphabet are not closed under
complement. -/
public theorem Indexed_notClosedUnderComplement :
    ¬ ClosedUnderComplement (α := Bool) is_Indexed := by
  intro hcomp
  exact Indexed_notClosedUnderIntersection
    (intersection_closed_of_complement_closed hcomp)

/-- An embedding of the binary alphabet gives complement nonclosure over the
target alphabet. -/
public theorem Indexed_notClosedUnderComplement_of_embedding {α : Type}
    (e : Bool ↪ α) :
    ¬ ClosedUnderComplement (α := α) is_Indexed := by
  intro hcomp
  exact Indexed_notClosedUnderIntersection_of_embedding e
    (intersection_closed_of_complement_closed hcomp)

/-- Indexed languages are not closed under complement over any alphabet
containing two specified distinct symbols. -/
public theorem Indexed_notClosedUnderComplement_of_two {α : Type}
    (a b : α) (hab : a ≠ b) :
    ¬ ClosedUnderComplement (α := α) is_Indexed := by
  intro hcomp
  exact Indexed_notClosedUnderIntersection_of_two a b hab
    (intersection_closed_of_complement_closed hcomp)

/-- Indexed languages are not closed under complement over every finite
alphabet with at least two symbols. -/
public theorem Indexed_notClosedUnderComplement_of_card {α : Type}
    [Fintype α] (hα : 2 ≤ Fintype.card α) :
    ¬ ClosedUnderComplement (α := α) is_Indexed := by
  intro hcomp
  exact Indexed_notClosedUnderIntersection_of_card hα
    (intersection_closed_of_complement_closed hcomp)

end IndexedComplementNonclosure
