import Langlib.Classes.ContextFree.Definition
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Utilities.ListUtils
import Langlib.Classes.ContextFree.Pumping.Pumping

/-! # Elementary Pumping Lemmas

This file proves the project's original pumping-lemma machinery for context-free languages.

## Main declarations

- `CF_pumping`
-/

open List

variable {T : Type}

/-- Pumping lemma for context-free languages.  -/
lemma CF_pumping {T : Type} {L : Language T} (cf : is_CF L) :
  ∃ n : ℕ, ∀ w ∈ L, List.length w ≥ n → (
    ∃ u v x y z : List T,
      (w = u ++ v ++ x ++ y ++ z) ∧
      (v ++ y).length > 0         ∧
      (v ++ x ++ y).length ≤ n    ∧
      (∀ i : ℕ, u ++ v ^ i ++ x ++ y ^ i ++ z ∈ L)
  ) :=
by
  obtain ⟨n, hn⟩ := Language.IsContextFree.pumping ((is_CF_iff_isContextFree).mp cf)
  refine ⟨n, ?_⟩
  intro w hw hwlen
  obtain ⟨u, v, x, y, z, hsplit, hnonempty, hbound, hpump⟩ := hn w hw hwlen
  refine ⟨u, v, x, y, z, hsplit, hnonempty, hbound, ?_⟩
  intro i
  simpa [n_times, nTimes] using hpump i
