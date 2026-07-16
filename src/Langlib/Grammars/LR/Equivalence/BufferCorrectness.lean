module

public import Langlib.Grammars.LR.Equivalence.BufferedDPDA

/-!
# Algebra of the LR lookahead buffer

These lemmas isolate the finite-control arithmetic used by the marked-input
machine.  They state that a refill implements exactly one logical shift of
`observe`, including the final no-refill phase after the marker has entered the
buffer.
-/

@[expose]
public section

namespace CF_grammar.LRk.Buffered

open CF_grammar.LRk

variable {T : Type}

@[simp]
public theorem lastBuffer_observe (k : ℕ) (hk : 0 < k) (w : List T) :
    lastBuffer hk (observe k w) = w[k - 1]? := by
  rfl

/-- Appending the next unread physical symbol after shifting the observed
head produces the observation of the remaining logical input. -/
public theorem shiftBuffer_observe_cons (k : ℕ) (hk : 0 < k)
    (a : T) (w : List T) :
    shiftBuffer hk (observe k (a :: w)) w[k - 1]? = observe k w := by
  funext i
  simp only [shiftBuffer, observe]
  split_ifs with h
  · simp only [List.getElem?_cons_succ]
  · have hi : i.val = k - 1 := by
      have hiLt := i.isLt
      omega
    rw [hi]

/-- If EOF is already visible at the back of the buffer, no physical refill
is needed: padding with EOF still implements the same logical shift. -/
public theorem shiftBuffer_observe_cons_of_last_none (k : ℕ) (hk : 0 < k)
    (a : T) (w : List T)
    (hlast : lastBuffer hk (observe k (a :: w)) = none) :
    shiftBuffer hk (observe k (a :: w)) none = observe k w := by
  rw [← shiftBuffer_observe_cons k hk a w]
  congr 1
  rw [lastBuffer_observe] at hlast
  have hbound := List.getElem?_eq_none_iff.mp hlast
  symm
  exact List.getElem?_eq_none (by simp at hbound; omega)

/-- Physical input still unread after preloading a `k`-symbol observation.
If the word is shorter than the buffer, its marker has already been consumed;
otherwise the suffix is embedded and followed by the fresh marker. -/
@[expose]
public def unreadAfter (k : ℕ) (w : List T) : List (Option T) :=
  if k ≤ w.length then (w.drop k).map some ++ [none] else []

/-- While the old buffer still ends in a real terminal, the unread marked
input has a head.  Reading that head is exactly the refill required by
`shiftBuffer`, and its tail is the unread input for the logical suffix. -/
public theorem unreadAfter_cons_split (k : ℕ) (hk : 0 < k)
    (a : T) (w : List T) {b : T}
    (hlast : lastBuffer hk (observe k (a :: w)) = some b) :
    ∃ (x : Option T) (xs : List (Option T)),
      unreadAfter k (a :: w) = x :: xs ∧
      xs = unreadAfter k w ∧
      shiftBuffer hk (observe k (a :: w)) x = observe k w := by
  rw [lastBuffer_observe] at hlast
  have hkw : k ≤ (a :: w).length := by
    by_contra h
    have hnone : (a :: w)[k - 1]? = none := by
      apply List.getElem?_eq_none
      have hlt : (a :: w).length < k := Nat.lt_of_not_ge h
      omega
    rw [hnone] at hlast
    simp at hlast
  refine ⟨w[k - 1]?, unreadAfter k w, ?_, rfl,
    shiftBuffer_observe_cons k hk a w⟩
  unfold unreadAfter
  rw [if_pos hkw]
  cases k with
  | zero => omega
  | succ n =>
      simp only [List.length_cons] at hkw
      simp only [List.drop_succ_cons, Nat.succ_sub_one]
      by_cases hn : n < w.length
      · have hkn : n + 1 ≤ w.length := by omega
        rw [if_pos hkn]
        rw [List.map_drop, List.map_drop,
          List.drop_eq_getElem_cons (l := w.map some) (by simp [hn])]
        simp [List.getElem?_eq_getElem hn]
      · have hlen : w.length = n := by omega
        rw [if_neg (by omega : ¬ n + 1 ≤ w.length)]
        subst n
        simp

end CF_grammar.LRk.Buffered
