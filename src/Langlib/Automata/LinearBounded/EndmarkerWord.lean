module

public import Langlib.Automata.LinearBounded.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical endmarker tapes as finite words

The bounded-crossing finite automaton scans the initial contents of every physical tape cell.
This file records that the function-valued contents of `LBA.loadEnd` enumerate to the ordinary
word `⊢ :: map inputCell w ++ [⊣]`, including `w = []`.
-/

namespace LBA

universe u v

variable {Terminal : Type u} {Work : Type v}

/-- Embed one terminal into the input-symbol summand of the endmarker tape alphabet. -/
def inputCell (terminal : Terminal) : EndAlpha Terminal Work :=
  Sum.inl (some (Sum.inl terminal))

/-- The finite cell word `⊢ w ⊣` underlying the canonical initial endmarker tape. -/
def endWord (word : List Terminal) : List (EndAlpha Terminal Work) :=
  leftMark :: word.map inputCell ++ [rightMark]

@[simp] theorem length_endWord (word : List Terminal) :
    (endWord (Work := Work) word).length = word.length + 2 := by
  simp [endWord]

@[simp] theorem endWord_ne_nil (word : List Terminal) :
    endWord (Work := Work) word ≠ [] := by
  simp [endWord]

/-- Enumerating the contents function of `loadEnd` gives the expected bracketed word exactly. -/
theorem ofFn_loadEnd_contents (word : List Terminal) :
    List.ofFn (loadEnd (Γ := Work) word).contents =
      endWord (Work := Work) word := by
  apply List.ext_get
  · simp [endWord]
  · intro k hkLeft hkRight
    simp only [List.length_ofFn] at hkLeft
    rw [List.get_ofFn]
    simp only [loadEnd, Fin.val_cast]
    by_cases hzero : k = 0
    · subst k
      simp [endWord]
    · rw [if_neg hzero]
      by_cases hinput : k - 1 < word.length
      · rw [dif_pos hinput]
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
        simp [endWord, List.get_eq_getElem] at hinput ⊢
        rw [List.getElem_append_left (by simpa using hinput),
          List.getElem_map]
        rfl
      · rw [dif_neg hinput]
        have hk : k = word.length + 1 := by omega
        subst k
        simp [endWord]

end LBA

end
