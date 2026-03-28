import Grammars.Classes.ContextSensitive.Basics.Toolbox
import Grammars.Utilities.LanguageOperations
import Grammars.Utilities.ListUtils

/-! # Context-Sensitive Closure Under Reversal

This file proves that context-sensitive languages are closed under word reversal.

## Main declarations

- `CS_of_reverse_CS`
-/

variable {T : Type}

section auxiliary

private def reversal_csrule {N : Type} (r : csrule T N) : csrule T N :=
  csrule.mk r.context_right.reverse r.input_nonterminal r.context_left.reverse r.output_string.reverse

private lemma dual_of_reversal_csrule {N : Type} (r : csrule T N) :
    reversal_csrule (reversal_csrule r) = r := by
  cases r
  unfold reversal_csrule
  simp [List.reverse_reverse]

private lemma reversal_csrule_reversal_csrule {N : Type} :
    @reversal_csrule T N ∘ @reversal_csrule T N = id := by
  ext; apply dual_of_reversal_csrule

private def reversal_CS_grammar (g : CS_grammar T) : CS_grammar T :=
  CS_grammar.mk g.nt g.initial (List.map reversal_csrule g.rules)

private lemma dual_of_reversal_CS_grammar (g : CS_grammar T) :
    reversal_CS_grammar (reversal_CS_grammar g) = g := by
  cases g
  unfold reversal_CS_grammar
  simp [List.map_map, reversal_csrule_reversal_csrule]

private lemma CS_derives_reversed (g : CS_grammar T) (v : List (symbol T g.nt)) :
    CS_derives (reversal_CS_grammar g) [symbol.nonterminal (reversal_CS_grammar g).initial] v →
      CS_derives g [symbol.nonterminal g.initial] v.reverse := by
  intro hv
  induction hv with
  | refl =>
    rw [List.reverse_singleton]
    exact CS_deri_self
  | tail _ orig ih =>
    apply CS_deri_of_deri_tran ih
    rcases orig with ⟨r, u, w, rin, bef, aft⟩
    change r ∈ (List.map _ g.rules) at rin
    rw [List.mem_map] at rin
    rcases rin with ⟨r₀, rin₀, r_from_r₀⟩
    refine ⟨r₀, w.reverse, u.reverse, rin₀, ?_, ?_⟩
    · -- Show the "before" side matches
      have hcl : r₀.context_left = r.context_right.reverse := by
        rw [← r_from_r₀]; unfold reversal_csrule; simp [List.reverse_reverse]
      have hnt : r₀.input_nonterminal = r.input_nonterminal := by
        rw [← r_from_r₀]; rfl
      have hcr : r₀.context_right = r.context_left.reverse := by
        rw [← r_from_r₀]; unfold reversal_csrule; simp [List.reverse_reverse]
      rw [hcl, hnt, hcr]
      have hrev := congr_arg List.reverse bef
      simp [List.reverse_append, List.reverse_reverse] at hrev
      rw [hrev]
      simp [List.append_assoc]
    · -- Show the "after" side matches
      have hcl : r₀.context_left = r.context_right.reverse := by
        rw [← r_from_r₀]; unfold reversal_csrule; simp [List.reverse_reverse]
      have hcr : r₀.context_right = r.context_left.reverse := by
        rw [← r_from_r₀]; unfold reversal_csrule; simp [List.reverse_reverse]
      have hout : r₀.output_string = r.output_string.reverse := by
        rw [← r_from_r₀]; unfold reversal_csrule; simp [List.reverse_reverse]
      rw [hcl, hcr, hout]
      have hrev := congr_arg List.reverse aft
      simp [List.reverse_append, List.reverse_reverse] at hrev
      rw [hrev]
      simp [List.append_assoc]

private lemma reversed_word_in_original_CS_language {g : CS_grammar T} {w : List T}
    (hyp : w ∈ CS_language (reversal_CS_grammar g)) :
    w.reverse ∈ CS_language g := by
  unfold CS_language at *
  have almost := CS_derives_reversed g (List.map symbol.terminal w) hyp
  rw [← List.map_reverse] at almost
  exact almost

end auxiliary


/-- The class of context-sensitive languages is closed under reversal. -/
theorem CS_of_reverse_CS (L : Language T) :
    is_CS L → is_CS (L.reverse) := by
  rintro ⟨g, hgL⟩
  rw [← hgL]
  refine ⟨reversal_CS_grammar g, ?_⟩
  unfold Language.reverse
  ext w
  constructor
  · intro hwL
    change w.reverse ∈ CS_language g
    exact reversed_word_in_original_CS_language hwL
  · intro hwL
    change w.reverse ∈ CS_language g at hwL
    obtain ⟨g₀, pre_reversal⟩ : ∃ g₀, g = reversal_CS_grammar g₀ := by
      exact ⟨reversal_CS_grammar g, (dual_of_reversal_CS_grammar g).symm⟩
    rw [pre_reversal] at hwL ⊢
    have finished := reversed_word_in_original_CS_language hwL
    simpa [dual_of_reversal_CS_grammar, List.reverse_reverse] using finished

/-- The converse direction: if the reversal is CS then so is the original. -/
theorem CS_of_reverse_CS_rev (L : Language T) :
    is_CS (L.reverse) → is_CS L := by
  intro h
  have h' := CS_of_reverse_CS L.reverse h
  simpa using h'

/-- A language is context-sensitive iff its reversal is. -/
@[simp] theorem CS_reverse_iff_CS (L : Language T) :
    is_CS (L.reverse) ↔ is_CS L := by
  constructor
  · exact CS_of_reverse_CS_rev L
  · exact CS_of_reverse_CS L
