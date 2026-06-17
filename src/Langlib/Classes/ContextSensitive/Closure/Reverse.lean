module

public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.RecursivelyEnumerable.Closure.Reverse
public import Langlib.Utilities.ClosurePredicates

@[expose]
public section

/-! # Context-Sensitive Closure Under Reversal

This file proves that context-sensitive languages are closed under word reversal.
-/

variable {T : Type}

private theorem reversal_grule_context_sensitive {g : grammar T} {r : grule T g.nt}
    (hr : initial_epsilon_rule g r ∨ grule_noncontracting r) :
    initial_epsilon_rule (reversal_grammar g) (reversal_grule r) ∨
      grule_noncontracting (reversal_grule r) := by
  rcases hr with hε | hnc
  · left
    rcases hε with ⟨hL, hN, hR, hO⟩
    simp [initial_epsilon_rule, reversal_grammar, reversal_grule, hL, hN, hR, hO]
  · right
    simpa [grule_noncontracting, reversal_grule, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hnc

private theorem reversal_grammar_context_sensitive (g : grammar T)
    (hg : grammar_context_sensitive g) :
    grammar_context_sensitive (reversal_grammar g) := by
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    exact reversal_grule_context_sensitive (hg.1 r₀ hr₀)
  · -- The ε-rule on the reversed grammar comes from an ε-rule on `g`.
    rintro ⟨r, hr, hε⟩
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    have hε₀ : initial_epsilon_rule g r₀ := by
      rcases hε with ⟨hL, hN, hR, hO⟩
      simp only [reversal_grule, reversal_grammar, List.reverse_eq_nil_iff] at hL hN hR hO
      exact ⟨hR, hN, hL, by simpa [List.reverse_eq_nil_iff] using hO⟩
    have hrhs := hg.2 ⟨r₀, hr₀, hε₀⟩
    intro r' hr'
    obtain ⟨r₀', hr₀', rfl⟩ := List.mem_map.mp hr'
    have := hrhs r₀' hr₀'
    -- `S ∈ out.reverse ↔ S ∈ out`.
    simpa [reversal_grammar, reversal_grule, List.mem_reverse] using this

/-- The class of context-sensitive languages is closed under reversal. -/
public theorem CS_of_reverse_CS (L : Language T) :
    is_CS L → is_CS (L.reverse) := by
  rintro ⟨g, hcs, hgL⟩
  exact ⟨reversal_grammar g, reversal_grammar_context_sensitive g hcs,
    by rw [grammar_language_reversal_grammar, hgL]⟩

/-- The converse direction: if the reversal is context-sensitive then so is the original. -/
public theorem CS_of_reverse_CS_rev (L : Language T) :
    is_CS (L.reverse) → is_CS L := by
  intro h
  have h' := CS_of_reverse_CS L.reverse h
  simpa using h'

/-- A language is context-sensitive iff its reversal is. -/
@[simp] public theorem CS_reverse_iff_CS (L : Language T) :
    is_CS (L.reverse) ↔ is_CS L := by
  constructor
  · exact CS_of_reverse_CS_rev L
  · exact CS_of_reverse_CS L

/-- The class of context-sensitive languages is closed under reversal. -/
public theorem CS_closedUnderReverse : ClosedUnderReverse (α := T) is_CS :=
  fun L hL => CS_of_reverse_CS L hL

