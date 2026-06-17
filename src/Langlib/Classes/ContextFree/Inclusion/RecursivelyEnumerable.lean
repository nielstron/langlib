module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Classes.RecursivelyEnumerable.Definition
@[expose]
public section

/-! # Context-free languages are recursively enumerable

A context-free language is presented by an unrestricted grammar (`grammar T`) carrying the
extra `grammar_context_free` constraint, so dropping that constraint exhibits the very same
grammar as a recursively-enumerable witness. The inclusion is therefore immediate.
-/

variable {T : Type}

/-- Every context-free language is recursively enumerable. -/
theorem is_RE_of_is_CF {L : Language T} (h : is_CF L) : is_RE L := by
  obtain ⟨g, _, hL⟩ := h
  exact ⟨g, hL⟩

/-- Context-free languages form a subclass of the recursively enumerable languages. -/
theorem CF_subclass_RE : (CF : Set (Language T)) ⊆ (RE : Set (Language T)) :=
  fun _ h => is_RE_of_is_CF h

end
