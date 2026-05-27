import Langlib.Classes.Recursive.Closure.Complement
import Langlib.Classes.Recursive.Inclusion.RecursivelyEnumerable
import Langlib.Classes.RecursivelyEnumerable.Closure.Complement

/-! # Strict Inclusion: Recursive ⊊ RE

This file proves that recursive languages form a strict subclass of recursively
enumerable languages.

The proof is indirect.  If every RE language over the unary alphabet were recursive,
then RE would be closed under complement: move an RE language into `Recursive`, take
the recursive complement, and use `Recursive ⊆ RE`.  This contradicts
`RE_notClosedUnderComplement`.

## Main declarations

- `Recursive_strict_subclass_RE_unit` — strict inclusion over `Unit`.
- `Recursive_subclass_RE_and_exists_strict` — class-level inclusion plus a strict
  witness alphabet.
-/

open Language

/-- Recursive languages over the unary alphabet form a strict subclass of RE. -/
theorem Recursive_strict_subclass_RE_unit :
    (Recursive : Set (Language Unit)) ⊂ (RE : Set (Language Unit)) := by
  refine ⟨Recursive_subset_RE, ?_⟩
  intro hREsubsetRecursive
  exact RE_notClosedUnderComplement (fun L hL => by
    exact Recursive_subset_RE (is_Recursive_complement (hREsubsetRecursive hL)))

/-- Recursive languages are included in RE for every finite alphabet, and the inclusion
is strict for at least one alphabet. -/
theorem Recursive_subclass_RE_and_exists_strict :
    (∀ T : Type, [DecidableEq T] → [Fintype T] →
      (Recursive : Set (Language T)) ⊆ (RE : Set (Language T))) ∧
    (∃ T : Type, (Recursive : Set (Language T)) ⊂ (RE : Set (Language T))) :=
  ⟨fun _ _ _ => Recursive_subset_RE, ⟨Unit, Recursive_strict_subclass_RE_unit⟩⟩
