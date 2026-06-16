module

public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.ContextSensitive.Closure.EmptyWord
public import Langlib.Classes.RecursivelyEnumerable.Examples.AnBnCn
public import Langlib.Examples.AnBnCn
public import Langlib.Examples.AnBnCnPos
public import Langlib.Examples.AlphabetABC
@[expose]
public section

/-! # `{aⁿbⁿcⁿ}` is context-sensitive

The grammar `grammar_anbncn` (defined in
`Langlib.Classes.RecursivelyEnumerable.Examples.AnBnCn`) generates `{aⁿbⁿcⁿ | n ≥ 1}`.
Every one of its rules is non-contracting (the output is at least as long as the input
pattern), so the grammar is non-contracting and hence the positive language is
context-sensitive. Adjoining the empty word (`n = 0`) via
`is_CS_insert_empty_of_noncontracting` yields `{aⁿbⁿcⁿ | n ≥ 0} = lang_eq_eq`.

## Main declarations

- `grammar_anbncn_noncontracting`
- `lang_eq_eq_is_CS`
-/

/-- The grammar `grammar_anbncn` is non-contracting: every rule's output string is at least
as long as its full input pattern. -/
public theorem grammar_anbncn_noncontracting : grammar_noncontracting grammar_anbncn := by
  intro r hr
  simp only [grammar_anbncn, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The language `{aⁿbⁿcⁿ}` is context-sensitive.

`grammar_anbncn` is non-contracting and generates the positive language `{aⁿbⁿcⁿ | n ≥ 1}`
(`grammar_anbncn_language`); `is_CS_insert_empty_of_noncontracting` re-adjoins the empty
word `n = 0`, which is exactly the difference between `lang_eq_eq_pos` and `lang_eq_eq`. -/
public theorem lang_eq_eq_is_CS : is_CS lang_eq_eq := by
  have h := is_CS_insert_empty_of_noncontracting grammar_anbncn grammar_anbncn_noncontracting
  rw [grammar_anbncn_language] at h
  have heq : lang_eq_eq = (fun w => w = [] ∨ lang_eq_eq_pos w) := by
    funext w
    apply propext
    constructor
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => exact Or.inl (by simp)
      | succ m => exact Or.inr ⟨m, by simp [a_, b_, c_]⟩
    · rintro (rfl | ⟨n, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨n + 1, by simp [a_, b_, c_]⟩
  rw [heq]
  exact h

end
