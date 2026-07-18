module

public import Mathlib.Computability.NFA

@[expose]
public section

/-!
# Finite automata under a fixed input context and letter map

`NFA.fixedContextMap M pre post embed` reads a word over a new alphabet by mapping every input
letter through `embed`, while feeding the fixed prefix `pre` before it and the fixed suffix
`post` after it.  The state type is unchanged.  This is useful when a finite automaton scans a
canonical endmarker representation although the recognized language is stated over the original
terminal alphabet.
-/

open Set

namespace NFA

universe u v w

variable {Alpha : Type u} {Beta : Type v} {State : Type w}

/-- Pull an NFA back along a letter map while supplying fixed prefix and suffix words. -/
def fixedContextMap (M : NFA Alpha State) (pre post : List Alpha)
    (embed : Beta → Alpha) : NFA Beta State where
  step q b := M.step q (embed b)
  start := M.evalFrom M.start pre
  accept := {q | ∃ r ∈ M.accept, r ∈ M.evalFrom {q} post}

theorem fixedContextMap_evalFrom (M : NFA Alpha State)
    (pre post : List Alpha) (embed : Beta → Alpha)
    (states : Set State) (word : List Beta) :
    (fixedContextMap M pre post embed).evalFrom states word =
      M.evalFrom states (word.map embed) := by
  induction word generalizing states with
  | nil => rfl
  | cons letter word ih =>
      simp only [NFA.evalFrom_cons, List.map_cons]
      rw [ih]
      rfl

/-- Exact language semantics of fixed context and letter mapping. -/
theorem fixedContextMap_correct (M : NFA Alpha State)
    (pre post : List Alpha) (embed : Beta → Alpha) :
    (fixedContextMap M pre post embed).accepts =
      {word | pre ++ word.map embed ++ post ∈ M.accepts} := by
  ext word
  simp only [NFA.mem_accepts]
  constructor
  · rintro ⟨q, ⟨r, hrAccept, hr⟩, hq⟩
    refine ⟨r, hrAccept, ?_⟩
    rw [NFA.evalFrom_append, NFA.evalFrom_append,
      NFA.mem_evalFrom_iff_exists]
    exact ⟨q, by
      rw [fixedContextMap_evalFrom] at hq
      simpa [fixedContextMap] using hq, hr⟩
  · rintro ⟨r, hrAccept, hr⟩
    rw [NFA.evalFrom_append, NFA.evalFrom_append,
      NFA.mem_evalFrom_iff_exists] at hr
    obtain ⟨q, hq, hr⟩ := hr
    refine ⟨q, ?_, ?_⟩
    · exact ⟨r, hrAccept, hr⟩
    · rw [fixedContextMap_evalFrom]
      simpa [fixedContextMap] using hq

end NFA

end
