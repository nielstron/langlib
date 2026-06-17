module

public import Langlib.Classes.Linear.Definition
public import Langlib.Classes.RecursivelyEnumerable.Definition
@[expose]
public section

/-! # Linear languages are recursively enumerable

A linear language is presented by an unrestricted grammar (`grammar T`) carrying the extra
`grammar_linear` constraint, so dropping that constraint exhibits the same grammar as a
recursively-enumerable witness. The inclusion is therefore immediate.
-/

variable {T : Type}

/-- Every linear language is recursively enumerable. -/
theorem is_RE_of_is_Linear {L : Language T} (h : is_Linear L) : is_RE L := by
  obtain ⟨g, _, hL⟩ := h
  exact ⟨g, hL⟩

/-- Linear languages form a subclass of the recursively enumerable languages. -/
theorem Linear_subclass_RE : (Linear : Set (Language T)) ⊆ (RE : Set (Language T)) :=
  fun _ h => is_RE_of_is_Linear h

end
