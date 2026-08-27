module

public import Langlib.Classes.ContextSensitive.Closure.Union
public import Langlib.Classes.RecursivelyEnumerable.Closure.Concatenation
public import Langlib.Utilities.ClosurePredicates
import Mathlib.Tactic

/-! # Context-Sensitive Closure Under Concatenation

Context-sensitive grammars in this library may have the distinguished start rule
`S -> epsilon`.  As in the union proof, we first replace each input language by a
noncontracting grammar for its nonempty part.  The unrestricted concatenation grammar
from the RE development preserves noncontracting rules, so it gives a noncontracting
grammar for the product of the nonempty parts.  The nullable cases are then added back
using context-sensitive union.
-/

variable {T : Type}

namespace ContextSensitiveConcatenation

private def nonemptyPart (L : Language T) : Language T :=
  L \ ({[]} : Set (List T))

private theorem big_grammar_noncontracting (g1 g2 : grammar T)
    (h1 : grammar_noncontracting g1) (h2 : grammar_noncontracting g2) :
    grammar_noncontracting (big_grammar g1 g2) := by
  simp only [grammar_noncontracting]
  simp only [big_grammar]
  intro r hr
  rcases List.mem_cons.mp hr with hstart | hrest
  · subst r
    simp only [List.length_nil, List.length_cons]
    norm_num
  rcases List.mem_append.mp hrest with hwrapped | hterm
  · rcases List.mem_append.mp hwrapped with hleft | hright
    · rcases List.mem_map.mp hleft with ⟨r1, hr1, rfl⟩
      simp only [wrap_grule₁]
      simp only [List.length_map]
      exact h1 r1 hr1
    · rcases List.mem_map.mp hright with ⟨r2, hr2, rfl⟩
      simp only [wrap_grule₂]
      simp only [List.length_map]
      exact h2 r2 hr2
  · rcases List.mem_append.mp hterm with hleft | hright
    · rw [rules_for_terminals₁] at hleft
      rcases List.mem_map.mp hleft with ⟨t, _ht, heq⟩
      subst r
      simp only [List.length_nil, List.length_cons]
      norm_num
    · rw [rules_for_terminals₂] at hright
      rcases List.mem_map.mp hright with ⟨t, _ht, heq⟩
      subst r
      simp only [List.length_nil, List.length_cons]
      norm_num

private theorem big_grammar_language (g1 g2 : grammar T) :
    grammar_language (big_grammar g1 g2) = grammar_language g1 * grammar_language g2 := by
  ext w
  constructor
  · exact in_concatenated_of_in_big
  · exact in_big_of_in_concatenated

private theorem concat_decompose_none {L1 L2 : Language T}
    (h1 : [] ∉ L1) (h2 : [] ∉ L2) :
    L1 * L2 = nonemptyPart L1 * nonemptyPart L2 := by
  ext w
  constructor
  · intro hw
    rw [Language.mem_mul] at hw
    rcases hw with ⟨x, hx, y, hy, hxy⟩
    rw [Language.mem_mul]
    refine ⟨x, ?_, y, ?_, hxy⟩
    · exact ⟨hx, by
        intro hxempty
        rw [Set.mem_singleton_iff] at hxempty
        exact h1 (by simpa [hxempty] using hx)⟩
    · exact ⟨hy, by
        intro hyempty
        rw [Set.mem_singleton_iff] at hyempty
        exact h2 (by simpa [hyempty] using hy)⟩
  · intro hw
    rw [Language.mem_mul] at hw
    rcases hw with ⟨x, hx, y, hy, hxy⟩
    rw [Language.mem_mul]
    exact ⟨x, hx.1, y, hy.1, hxy⟩

private theorem concat_decompose_left {L1 L2 : Language T}
    (h1 : [] ∈ L1) (h2 : [] ∉ L2) :
    L1 * L2 = nonemptyPart L1 * nonemptyPart L2 + L2 := by
  ext w
  constructor
  · intro hw
    rw [Language.mem_mul] at hw
    rcases hw with ⟨x, hx, y, hy, hxy⟩
    by_cases hxnil : x = []
    · subst x
      simp only [List.nil_append] at hxy
      subst w
      rw [Language.mem_add]
      exact Or.inr hy
    · rw [Language.mem_add]
      left
      rw [Language.mem_mul]
      refine ⟨x, ?_, y, ?_, hxy⟩
      · exact ⟨hx, by simpa [Set.mem_singleton_iff] using hxnil⟩
      · exact ⟨hy, by
          intro hyempty
          rw [Set.mem_singleton_iff] at hyempty
          exact h2 (by simpa [hyempty] using hy)⟩
  · intro hw
    rw [Language.mem_add] at hw
    rcases hw with hcore | hright
    · rw [Language.mem_mul] at hcore
      rcases hcore with ⟨x, hx, y, hy, hxy⟩
      rw [Language.mem_mul]
      exact ⟨x, hx.1, y, hy.1, hxy⟩
    · rw [Language.mem_mul]
      exact ⟨[], h1, w, hright, rfl⟩

private theorem concat_decompose_right {L1 L2 : Language T}
    (h1 : [] ∉ L1) (h2 : [] ∈ L2) :
    L1 * L2 = nonemptyPart L1 * nonemptyPart L2 + L1 := by
  ext w
  constructor
  · intro hw
    rw [Language.mem_mul] at hw
    rcases hw with ⟨x, hx, y, hy, hxy⟩
    by_cases hynil : y = []
    · subst y
      simp only [List.append_nil] at hxy
      subst w
      rw [Language.mem_add]
      exact Or.inr hx
    · rw [Language.mem_add]
      left
      rw [Language.mem_mul]
      refine ⟨x, ?_, y, ?_, hxy⟩
      · exact ⟨hx, by
          intro hxempty
          rw [Set.mem_singleton_iff] at hxempty
          exact h1 (by simpa [hxempty] using hx)⟩
      · exact ⟨hy, by simpa [Set.mem_singleton_iff] using hynil⟩
  · intro hw
    rw [Language.mem_add] at hw
    rcases hw with hcore | hright
    · rw [Language.mem_mul] at hcore
      rcases hcore with ⟨x, hx, y, hy, hxy⟩
      rw [Language.mem_mul]
      exact ⟨x, hx.1, y, hy.1, hxy⟩
    · rw [Language.mem_mul]
      exact ⟨w, hright, [], h2, by simp⟩

private theorem concat_decompose_both {L1 L2 : Language T}
    (h1 : [] ∈ L1) (h2 : [] ∈ L2) :
    L1 * L2 = (nonemptyPart L1 * nonemptyPart L2 + L1) + L2 := by
  ext w
  constructor
  · intro hw
    rw [Language.mem_mul] at hw
    rcases hw with ⟨x, hx, y, hy, hxy⟩
    by_cases hxnil : x = []
    · subst x
      simp only [List.nil_append] at hxy
      subst w
      rw [Language.mem_add]
      exact Or.inr hy
    · by_cases hynil : y = []
      · subst y
        simp only [List.append_nil] at hxy
        subst w
        rw [Language.mem_add]
        left
        rw [Language.mem_add]
        exact Or.inr hx
      · rw [Language.mem_add]
        left
        rw [Language.mem_add]
        left
        rw [Language.mem_mul]
        refine ⟨x, ?_, y, ?_, hxy⟩
        · exact ⟨hx, by simpa [Set.mem_singleton_iff] using hxnil⟩
        · exact ⟨hy, by simpa [Set.mem_singleton_iff] using hynil⟩
  · intro hw
    rw [Language.mem_add] at hw
    rcases hw with hleft | hright
    · rw [Language.mem_add] at hleft
      rcases hleft with hcore | hL1
      · rw [Language.mem_mul] at hcore
        rcases hcore with ⟨x, hx, y, hy, hxy⟩
        rw [Language.mem_mul]
        exact ⟨x, hx.1, y, hy.1, hxy⟩
      · rw [Language.mem_mul]
        exact ⟨w, hL1, [], h2, by simp⟩
    · rw [Language.mem_mul]
      exact ⟨[], h1, w, hright, rfl⟩

private theorem is_CS_nonemptyPart_concat {L1 L2 : Language T}
    (hL1 : is_CS L1) (hL2 : is_CS L2) :
    is_CS (nonemptyPart L1 * nonemptyPart L2) := by
  obtain ⟨g1, hg1, hlang1⟩ := hL1
  obtain ⟨g2, hg2, hlang2⟩ := hL2
  obtain ⟨g1', _hfin1, hnc1, hlang1'⟩ := exists_noncontracting_offEmpty_of_CS g1 hg1
  obtain ⟨g2', _hfin2, hnc2, hlang2'⟩ := exists_noncontracting_offEmpty_of_CS g2 hg2
  refine ⟨big_grammar g1' g2',
    grammar_context_sensitive_of_noncontracting _
      (big_grammar_noncontracting g1' g2' hnc1 hnc2), ?_⟩
  rw [big_grammar_language, hlang1', hlang2', hlang1, hlang2]
  rfl

end ContextSensitiveConcatenation

open ContextSensitiveConcatenation

/-- Context-sensitive languages are closed under concatenation. -/
public theorem CS_closedUnderConcatenation :
    ClosedUnderConcatenation (α := T) is_CS := by
  intro L1 L2 hL1 hL2
  by_cases hε1 : [] ∈ L1
  · by_cases hε2 : [] ∈ L2
    · rw [concat_decompose_both hε1 hε2]
      exact CS_closedUnderUnion
        (nonemptyPart L1 * nonemptyPart L2 + L1) L2
        (CS_closedUnderUnion (nonemptyPart L1 * nonemptyPart L2) L1
          (is_CS_nonemptyPart_concat hL1 hL2) hL1)
        hL2
    · rw [concat_decompose_left hε1 hε2]
      exact CS_closedUnderUnion (nonemptyPart L1 * nonemptyPart L2) L2
        (is_CS_nonemptyPart_concat hL1 hL2) hL2
  · by_cases hε2 : [] ∈ L2
    · rw [concat_decompose_right hε1 hε2]
      exact CS_closedUnderUnion (nonemptyPart L1 * nonemptyPart L2) L1
        (is_CS_nonemptyPart_concat hL1 hL2) hL1
    · rw [concat_decompose_none hε1 hε2]
      exact is_CS_nonemptyPart_concat hL1 hL2
