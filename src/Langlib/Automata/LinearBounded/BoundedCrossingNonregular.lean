module

public import Langlib.Automata.LinearBounded.BoundedCrossingLanguage

@[expose]
public section

/-!
# Nonregular languages require unbounded accepting crossings

The bounded-crossing profile construction shows that one crossing cap shared by a selected
accepting run of every accepted input forces a finite LBA language to be regular.  This module
records the exact contrapositives.  If the language is not regular, then every proposed cap
misses some accepted word; equivalently, every fixed-cap slice is a proper subset of the whole
language.

The results use the weak, selected-run quantifier order.  Thus the missing word has no accepting
run obeying the proposed cap, although it does have an unrestricted accepting run.  No lower
bound on the cardinality of any type is assumed.
-/

namespace LBA.BoundedCrossing

universe u v w

variable {Terminal : Type u} {Work : Type v} {State : Type w}

/-- A fixed crossing-cap slice is always contained in the unrestricted source language. -/
theorem languageWithBound_subset_languageEnd
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    LanguageWithBound M bound ≤ LBA.LanguageEnd M := by
  intro word haccept
  exact accepts_of_acceptsWithBound haccept

/-- Failure of a proposed uniform cap has an accepted input for which no accepting run obeys
that cap.  This logical core does not require any finiteness assumptions. -/
theorem exists_accepted_not_bounded_of_not_hasUniformAcceptingBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) {bound : Nat}
    (hbound : ¬ HasUniformAcceptingBound M bound) :
    ∃ word, word ∈ LBA.LanguageEnd M ∧
      word ∉ LanguageWithBound M bound := by
  classical
  by_contra hmiss
  apply hbound
  intro word haccept
  by_contra hnotBounded
  exact hmiss ⟨word, haccept, hnotBounded⟩

/-- An accepted word outside one fixed-cap slice forces strict growth at some larger cap.

The larger cap is the maximum of `bound + 1` and any finite crossing cap for an accepting trace
of the witness word.  This helper requires no finiteness assumptions on the machine types. -/
theorem exists_strict_larger_languageWithBound_of_accepted_not_bounded
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) {bound : Nat}
    {word : List Terminal}
    (haccept : word ∈ LBA.LanguageEnd M)
    (hnotBounded : word ∉ LanguageWithBound M bound) :
    ∃ larger, bound < larger ∧
      LanguageWithBound M bound < LanguageWithBound M larger := by
  obtain ⟨witnessBound, hwitness⟩ :=
    (accepts_iff_exists_acceptsWithBound
      (M := M) (source := LBA.initCfgEnd M word)).mp haccept
  let larger := max (bound + 1) witnessBound
  have hboundLarger : bound < larger :=
    (Nat.lt_succ_self bound).trans_le (Nat.le_max_left _ _)
  have hwitnessLarger : word ∈ LanguageWithBound M larger :=
    hwitness.mono (Nat.le_max_right _ _)
  have hslices : LanguageWithBound M bound ≤ LanguageWithBound M larger :=
    languageWithBound_mono M (Nat.le_of_lt hboundLarger)
  refine ⟨larger, hboundLarger, lt_of_le_of_ne hslices ?_⟩
  intro heq
  apply hnotBounded
  rw [heq]
  exact hwitnessLarger

/-- If one cap is not uniform for the whole source language, some strictly larger cap gives a
strictly larger fixed-cap slice. -/
theorem exists_strict_larger_languageWithBound_of_not_hasUniformAcceptingBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) {bound : Nat}
    (hbound : ¬ HasUniformAcceptingBound M bound) :
    ∃ larger, bound < larger ∧
      LanguageWithBound M bound < LanguageWithBound M larger := by
  obtain ⟨word, haccept, hnotBounded⟩ :=
    exists_accepted_not_bounded_of_not_hasUniformAcceptingBound M hbound
  exact exists_strict_larger_languageWithBound_of_accepted_not_bounded
    M haccept hnotBounded

/-! ## NFA-recognizability contrapositives -/

/-- A finite LBA whose language is not NFA-recognizable has no uniform selected-accepting
crossing cap. -/
theorem no_uniformAcceptingBound_of_not_is_NFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_NFA (LBA.LanguageEnd M)) :
    ∀ bound, ¬ HasUniformAcceptingBound M bound := by
  intro bound hbound
  exact hnonregular
    (is_NFA_languageEnd_of_hasUniformAcceptingBound M bound hbound)

/-- If a finite LBA language is not NFA-recognizable, every proposed crossing cap misses an
accepted word.  On that word no accepting run has all boundary-crossing counts below the cap. -/
theorem every_crossingCap_misses_of_not_is_NFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_NFA (LBA.LanguageEnd M)) :
    ∀ bound, ∃ word, word ∈ LBA.LanguageEnd M ∧
      word ∉ LanguageWithBound M bound := by
  intro bound
  exact exists_accepted_not_bounded_of_not_hasUniformAcceptingBound M
    (no_uniformAcceptingBound_of_not_is_NFA M hnonregular bound)

/-- Operational form of the non-NFA obstruction: for every proposed cap there is an accepted
word such that every accepting trace crosses some physical boundary more than that cap. -/
theorem every_crossingCap_exceeded_on_all_acceptingTraces_of_not_is_NFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_NFA (LBA.LanguageEnd M)) :
    ∀ bound, ∃ word,
      LBA.Accepts M (LBA.initCfgEnd M word) ∧
        ∀ (target : DLBA.Cfg (LBA.EndAlpha Terminal Work) State (word.length + 1))
          (trace : LBA.StepTrace M (LBA.initCfgEnd M word) target),
          M.accept target.state = true →
            ∃ boundary : Fin (word.length + 1),
              bound < trace.crossingCount boundary := by
  intro bound
  obtain ⟨word, haccept, hnotBounded⟩ :=
    every_crossingCap_misses_of_not_is_NFA M hnonregular bound
  refine ⟨word, haccept, ?_⟩
  exact (not_acceptsWithBound_iff_every_acceptingTrace_exceeds
    M (LBA.initCfgEnd M word) bound).mp hnotBounded

/-- In a non-NFA finite LBA language the increasing fixed-cap slices have strict growth above
every index: for each cap `c`, some `d > c` satisfies `L_c(M) < L_d(M)`. -/
theorem every_crossingCap_has_strict_larger_slice_of_not_is_NFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_NFA (LBA.LanguageEnd M)) :
    ∀ bound, ∃ larger, bound < larger ∧
      LanguageWithBound M bound < LanguageWithBound M larger := by
  intro bound
  exact exists_strict_larger_languageWithBound_of_not_hasUniformAcceptingBound M
    (no_uniformAcceptingBound_of_not_is_NFA M hnonregular bound)

/-- Every fixed-cap slice of a non-NFA finite LBA language is a proper subset of the whole
language. -/
theorem every_languageWithBound_ssubset_languageEnd_of_not_is_NFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_NFA (LBA.LanguageEnd M)) :
    ∀ bound, LanguageWithBound M bound < LBA.LanguageEnd M := by
  intro bound
  refine lt_of_le_of_ne (languageWithBound_subset_languageEnd M bound) ?_
  intro heq
  obtain ⟨word, haccept, hnotBounded⟩ :=
    every_crossingCap_misses_of_not_is_NFA M hnonregular bound
  exact hnotBounded (heq ▸ haccept)

/-- Equational form: no fixed-cap slice of a non-NFA finite LBA language is already the whole
language. -/
theorem every_languageWithBound_ne_languageEnd_of_not_is_NFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_NFA (LBA.LanguageEnd M)) :
    ∀ bound, LanguageWithBound M bound ≠ LBA.LanguageEnd M := by
  intro bound
  exact (every_languageWithBound_ssubset_languageEnd_of_not_is_NFA
    M hnonregular bound).ne

/-! ## DFA-recognizability contrapositives -/

/-- A finite LBA whose language is not DFA-recognizable has no uniform selected-accepting
crossing cap. -/
theorem no_uniformAcceptingBound_of_not_is_DFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_DFA (LBA.LanguageEnd M)) :
    ∀ bound, ¬ HasUniformAcceptingBound M bound := by
  apply no_uniformAcceptingBound_of_not_is_NFA M
  intro hnfa
  exact hnonregular (is_NFA_iff_is_DFA.mp hnfa)

/-- If a finite LBA language is not DFA-recognizable, every proposed crossing cap misses an
accepted word. -/
theorem every_crossingCap_misses_of_not_is_DFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_DFA (LBA.LanguageEnd M)) :
    ∀ bound, ∃ word, word ∈ LBA.LanguageEnd M ∧
      word ∉ LanguageWithBound M bound := by
  intro bound
  exact exists_accepted_not_bounded_of_not_hasUniformAcceptingBound M
    (no_uniformAcceptingBound_of_not_is_DFA M hnonregular bound)

/-- Operational form of the non-DFA obstruction, stated directly over all accepting traces. -/
theorem every_crossingCap_exceeded_on_all_acceptingTraces_of_not_is_DFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_DFA (LBA.LanguageEnd M)) :
    ∀ bound, ∃ word,
      LBA.Accepts M (LBA.initCfgEnd M word) ∧
        ∀ (target : DLBA.Cfg (LBA.EndAlpha Terminal Work) State (word.length + 1))
          (trace : LBA.StepTrace M (LBA.initCfgEnd M word) target),
          M.accept target.state = true →
            ∃ boundary : Fin (word.length + 1),
              bound < trace.crossingCount boundary := by
  apply every_crossingCap_exceeded_on_all_acceptingTraces_of_not_is_NFA M
  intro hnfa
  exact hnonregular (is_NFA_iff_is_DFA.mp hnfa)

/-- DFA-recognizability form of strict fixed-cap slice growth above every cap. -/
theorem every_crossingCap_has_strict_larger_slice_of_not_is_DFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_DFA (LBA.LanguageEnd M)) :
    ∀ bound, ∃ larger, bound < larger ∧
      LanguageWithBound M bound < LanguageWithBound M larger := by
  intro bound
  exact exists_strict_larger_languageWithBound_of_not_hasUniformAcceptingBound M
    (no_uniformAcceptingBound_of_not_is_DFA M hnonregular bound)

/-- Every fixed-cap slice of a non-DFA finite LBA language is a proper subset of the whole
language. -/
theorem every_languageWithBound_ssubset_languageEnd_of_not_is_DFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_DFA (LBA.LanguageEnd M)) :
    ∀ bound, LanguageWithBound M bound < LBA.LanguageEnd M := by
  intro bound
  refine lt_of_le_of_ne (languageWithBound_subset_languageEnd M bound) ?_
  intro heq
  obtain ⟨word, haccept, hnotBounded⟩ :=
    every_crossingCap_misses_of_not_is_DFA M hnonregular bound
  exact hnotBounded (heq ▸ haccept)

/-- Equational form for DFA nonrecognizability. -/
theorem every_languageWithBound_ne_languageEnd_of_not_is_DFA
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ is_DFA (LBA.LanguageEnd M)) :
    ∀ bound, LanguageWithBound M bound ≠ LBA.LanguageEnd M := by
  intro bound
  exact (every_languageWithBound_ssubset_languageEnd_of_not_is_DFA
    M hnonregular bound).ne

/-! ## Mathlib regularity contrapositives -/

/-- `Language.IsRegular` form of the absence of a uniform crossing cap. -/
theorem no_uniformAcceptingBound_of_not_isRegular
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ (LBA.LanguageEnd M).IsRegular) :
    ∀ bound, ¬ HasUniformAcceptingBound M bound := by
  apply no_uniformAcceptingBound_of_not_is_DFA M
  exact hnonregular

/-- For a nonregular finite LBA language, every proposed crossing cap misses an accepted word. -/
theorem every_crossingCap_misses_of_not_isRegular
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ (LBA.LanguageEnd M).IsRegular) :
    ∀ bound, ∃ word, word ∈ LBA.LanguageEnd M ∧
      word ∉ LanguageWithBound M bound := by
  intro bound
  exact exists_accepted_not_bounded_of_not_hasUniformAcceptingBound M
    (no_uniformAcceptingBound_of_not_isRegular M hnonregular bound)

/-- Operational Mathlib-regularity form: every cap is exceeded on every accepting trace of
some accepted word. -/
theorem every_crossingCap_exceeded_on_all_acceptingTraces_of_not_isRegular
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ (LBA.LanguageEnd M).IsRegular) :
    ∀ bound, ∃ word,
      LBA.Accepts M (LBA.initCfgEnd M word) ∧
        ∀ (target : DLBA.Cfg (LBA.EndAlpha Terminal Work) State (word.length + 1))
          (trace : LBA.StepTrace M (LBA.initCfgEnd M word) target),
          M.accept target.state = true →
            ∃ boundary : Fin (word.length + 1),
              bound < trace.crossingCount boundary := by
  apply every_crossingCap_exceeded_on_all_acceptingTraces_of_not_is_DFA M
  exact hnonregular

/-- Mathlib-regularity form of strict fixed-cap slice growth above every cap. -/
theorem every_crossingCap_has_strict_larger_slice_of_not_isRegular
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ (LBA.LanguageEnd M).IsRegular) :
    ∀ bound, ∃ larger, bound < larger ∧
      LanguageWithBound M bound < LanguageWithBound M larger := by
  intro bound
  exact exists_strict_larger_languageWithBound_of_not_hasUniformAcceptingBound M
    (no_uniformAcceptingBound_of_not_isRegular M hnonregular bound)

/-- Every fixed-cap slice of a nonregular finite LBA language is a proper subset of the whole
language. -/
theorem every_languageWithBound_ssubset_languageEnd_of_not_isRegular
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ (LBA.LanguageEnd M).IsRegular) :
    ∀ bound, LanguageWithBound M bound < LBA.LanguageEnd M := by
  intro bound
  refine lt_of_le_of_ne (languageWithBound_subset_languageEnd M bound) ?_
  intro heq
  obtain ⟨word, haccept, hnotBounded⟩ :=
    every_crossingCap_misses_of_not_isRegular M hnonregular bound
  exact hnotBounded (heq ▸ haccept)

/-- Equational form for Mathlib nonregularity: the increasing fixed-cap union never stabilizes
at any finite cap. -/
theorem every_languageWithBound_ne_languageEnd_of_not_isRegular
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (hnonregular : ¬ (LBA.LanguageEnd M).IsRegular) :
    ∀ bound, LanguageWithBound M bound ≠ LBA.LanguageEnd M := by
  intro bound
  exact (every_languageWithBound_ssubset_languageEnd_of_not_isRegular
    M hnonregular bound).ne

end LBA.BoundedCrossing

end
