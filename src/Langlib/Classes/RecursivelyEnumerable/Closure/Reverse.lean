import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Utilities.LanguageOperations
import Langlib.Utilities.ListUtils
import Langlib.Utilities.ClosurePredicates


/-! # RE Closure Under Reversal

This file proves closure of recursively enumerable languages under reversal.

The key construction `reversal_grammar` reverses each rule of an unrestricted grammar.
The central result `grammar_language_reversal_grammar` shows that the language of the
reversed grammar equals the reversal of the original language.  This fact is then reused
by the context-free and context-sensitive reversal proofs, avoiding duplicated derivation
arguments.

## Main declarations

- `reversal_grule`        — reverse a single unrestricted rule
- `reversal_grammar`      — reverse every rule of an unrestricted grammar
- `grammar_language_reversal_grammar` — language of reversed grammar = reversed language
- `RE_of_reverse_RE`
-/

variable {T : Type}

section reversal_defs

/-- Reverse a single unrestricted rule by swapping and reversing the left/right context
and reversing the output string. -/
def reversal_grule {N : Type} (r : grule T N) : grule T N :=
  grule.mk r.input_R.reverse r.input_N r.input_L.reverse r.output_string.reverse

lemma dual_of_reversal_grule {N : Type} (r : grule T N) :
    reversal_grule (reversal_grule r) = r := by
  cases r
  unfold reversal_grule
  dsimp only
  simp [List.reverse_reverse]

lemma reversal_grule_reversal_grule {N : Type} :
    @reversal_grule T N ∘ @reversal_grule T N = id := by
  ext
  apply dual_of_reversal_grule

/-- Reverse every rule of an unrestricted grammar. -/
def reversal_grammar (g : grammar T) : grammar T :=
  grammar.mk g.nt g.initial (List.map reversal_grule g.rules)

lemma dual_of_reversal_grammar (g : grammar T) :
    reversal_grammar (reversal_grammar g) = g := by
  cases g
  unfold reversal_grammar
  dsimp only
  rw [List.map_map, reversal_grule_reversal_grule, List.map_id]

end reversal_defs

section reversal_language

private lemma derives_reversed (g : grammar T) (v : List (symbol T g.nt)) :
    grammar_derives (reversal_grammar g) [symbol.nonterminal (reversal_grammar g).initial] v →
      grammar_derives g [symbol.nonterminal g.initial] v.reverse := by
  intro hv
  induction hv with
  | refl =>
      rw [List.reverse_singleton]
      exact grammar_deri_self
  | tail _ orig ih =>
      apply grammar_deri_of_deri_tran ih
      rcases orig with ⟨r, rin, x, y, bef, aft⟩
      change r ∈ (List.map _ g.rules) at rin
      rw [List.mem_map] at rin
      rcases rin with ⟨r₀, rin₀, r_from_r₀⟩
      refine ⟨r₀, rin₀, y.reverse, x.reverse, ?_, ?_⟩
      ·
        have rid₁ : r₀.input_L = r.input_R.reverse := by
          rw [←r_from_r₀]
          unfold reversal_grule
          rw [List.reverse_reverse]
        have rid₂ :
            [symbol.nonterminal r₀.input_N] =
              ([symbol.nonterminal r.input_N] : List (symbol T g.nt)).reverse := by
          rw [←r_from_r₀]
          rw [List.reverse_singleton]
          rfl
        have rid₃ : r₀.input_R = r.input_L.reverse := by
          rw [←r_from_r₀]
          unfold reversal_grule
          rw [List.reverse_reverse]
        rw [
          rid₁, rid₂, rid₃,
          ←List.reverse_append_append, ←List.reverse_append_append,
          ←List.append_assoc, ←List.append_assoc
        ]
        simp [bef]
      ·
        have snd_from_r : r₀.output_string = r.output_string.reverse := by
          rw [←r_from_r₀]
          unfold reversal_grule
          rw [List.reverse_reverse]
        rw [snd_from_r, ←List.reverse_append_append]
        exact congrArg List.reverse aft

private lemma reversed_word_in_original_language {g : grammar T} {w : List T}
    (hyp : w ∈ grammar_language (reversal_grammar g)) :
    w.reverse ∈ grammar_language g := by
  unfold grammar_language at *
  have almost_done := derives_reversed g (List.map symbol.terminal w) hyp
  rw [←List.map_reverse] at almost_done
  exact almost_done

/-- The language of the reversed grammar is exactly the reversal of the original language.

This is the key lemma that is reused by the context-free and context-sensitive reversal
closure proofs, so that the derivation-reversal argument need only be given once. -/
theorem grammar_language_reversal_grammar (g : grammar T) :
    grammar_language (reversal_grammar g) = (grammar_language g).reverse := by
  ext w
  constructor
  · intro hwL
    change w.reverse ∈ grammar_language g
    exact reversed_word_in_original_language hwL
  · intro hwL
    change w.reverse ∈ grammar_language g at hwL
    obtain ⟨g₀, pre_reversal⟩ : ∃ g₀, g = reversal_grammar g₀ := by
      refine ⟨reversal_grammar g, ?_⟩
      rw [dual_of_reversal_grammar]
    rw [pre_reversal] at hwL ⊢
    have finished_up_to_reverses := reversed_word_in_original_language hwL
    simpa [dual_of_reversal_grammar, List.reverse_reverse] using finished_up_to_reverses

end reversal_language

/-- The class of recursively-enumerable languages is closed under reversal. -/
theorem RE_of_reverse_RE (L : Language T) :
    is_RE L → is_RE (L.reverse) := by
  rintro ⟨g, hgL⟩
  exact ⟨reversal_grammar g, by rw [grammar_language_reversal_grammar, hgL]⟩

/-- The converse direction: if the reversal is RE then so is the original. -/
theorem RE_of_reverse_RE_rev (L : Language T) :
    is_RE (L.reverse) → is_RE L := by
  intro h
  have h' := RE_of_reverse_RE L.reverse h
  simpa using h'

/-- A language is RE iff its reversal is RE. -/
@[simp] theorem RE_reverse_iff_RE (L : Language T) :
    is_RE (L.reverse) ↔ is_RE L := by
  constructor
  · exact RE_of_reverse_RE_rev L
  · exact RE_of_reverse_RE L

/-- The class of recursively enumerable languages is closed under reversal. -/
theorem RE_closedUnderReverse : ClosedUnderReverse (α := T) is_RE :=
  fun L hL => RE_of_reverse_RE L hL
