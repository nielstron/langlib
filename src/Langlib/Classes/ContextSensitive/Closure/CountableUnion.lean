module

public import Langlib.Classes.ContextSensitive.Closure.FiniteLanguage
public import Langlib.Classes.ContextSensitive.Inclusion.StrictRecursive
import Langlib.Utilities.WordEnumeration

@[expose]
public section

/-!
# Context-sensitive languages and countable increasing unions

Context-sensitive languages are closed under binary union, but not under countable union, even
when the family is increasing and every member is finite.

Over any nonempty finite alphabet, choose a recursive language `L` that is not context-sensitive
using `CS_strict_subclass_Recursive_of_card`. Its bounded-length truncations

`F n = {w ∈ L | |w| ≤ n}`

are finite, hence context-sensitive, and form a monotone family. Their union is exactly `L`, so it
is recursive but not context-sensitive.

This also shows why proving that each member of an increasing sequence lies in `CS` does not by
itself put the countable union in `CS`: the witnessing grammars or automata need not be uniform.
-/

open Language

variable {T : Type}

/-- Over every nonempty finite alphabet there is an increasing sequence of finite
context-sensitive languages whose countable union is recursive but not context-sensitive. -/
public theorem CS_notClosedUnderMonotoneCountableUnion_of_card
    [Fintype T] (hT : 1 ≤ Fintype.card T) :
    ∃ F : ℕ → Language T,
      Monotone F ∧
      (∀ n, (F n : Set (List T)).Finite) ∧
      (∀ n, is_CS (F n)) ∧
      is_Recursive (⋃ n, F n) ∧
      ¬ is_CS (⋃ n, F n) := by
  classical
  obtain ⟨L, hLrec, hLnotCS⟩ :=
    Set.exists_of_ssubset (CS_strict_subclass_Recursive_of_card hT)
  change is_Recursive L at hLrec
  change ¬ is_CS L at hLnotCS
  let F : ℕ → Language T := fun n => {w | w ∈ L ∧ w.length ≤ n}
  have hmono : Monotone F := by
    intro n m hnm w hw
    exact ⟨hw.1, hw.2.trans hnm⟩
  have hfinite : ∀ n, (F n : Set (List T)).Finite := by
    intro n
    refine (List.finite_toSet
      (wordsUpTo ((Finset.univ : Finset T).toList) n)).subset ?_
    intro w hw
    rw [Set.mem_setOf_eq, mem_wordsUpTo_univ]
    exact hw.2
  have hCS : ∀ n, is_CS (F n) := fun n =>
    is_CS_of_finite_language (hfinite n)
  have hunion : (⋃ n, F n) = L := by
    ext w
    simp only [Set.mem_iUnion, F, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hwL, _⟩
      exact hwL
    · intro hwL
      exact ⟨w.length, hwL, le_rfl⟩
  refine ⟨F, hmono, hfinite, hCS, ?_, ?_⟩
  · rw [hunion]
    exact hLrec
  · rw [hunion]
    exact hLnotCS

end
