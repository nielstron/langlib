module

public import Langlib.Classes.ContextSensitive.Inclusion.StrictRecursive
public import Langlib.Classes.Recursive.Inclusion.RecursivelyEnumerable
@[expose]
public section


/-! # Strict Inclusion: CS ⊊ RE

Context-sensitive languages form a strict subclass of the recursively enumerable languages over
every finite nonempty terminal alphabet.  The result follows by composing the already strict
inclusion `CS ⊊ Recursive` with the inclusion `Recursive ⊆ RE`.

The nonemptiness threshold is optimal.  If the terminal alphabet is empty, then `List T` contains
only the empty word, so there are only two languages; both are context-sensitive.  Consequently
`CS` and `RE` coincide rather than being strictly separated in that case.

## Main declarations

- `CS_strict_subclass_RE_of_nonempty` gives the instance-based formulation.
- `CS_strict_subclass_RE_of_card` gives the encoding-independent finite-alphabet formulation.
-/

open Language

variable {T : Type}

/-- Context-sensitive languages form a strict subclass of recursively enumerable languages over
every nonempty finite, computably encoded terminal alphabet. -/
public theorem CS_strict_subclass_RE_of_nonempty
    [DecidableEq T] [Fintype T] [Primcodable T] [Nonempty T] :
    (CS : Set (Language T)) ⊂ (RE : Set (Language T)) := by
  have hCSRecursive :
      (CS : Set (Language T)) ⊂ (Recursive : Set (Language T)) :=
    CS_strict_subclass_Recursive
  refine ⟨fun L hL ↦ Recursive_subset_RE (hCSRecursive.1 hL), ?_⟩
  intro hRECS
  exact hCSRecursive.2 (fun L hL ↦ hRECS (Recursive_subset_RE hL))

/-- Context-sensitive languages form a strict subclass of recursively enumerable languages over
every finite terminal alphabet with at least one symbol.  The cardinality hypothesis supplies all
computability instances internally and is best possible: strictness fails at cardinality zero. -/
public theorem CS_strict_subclass_RE_of_card {T : Type} [Fintype T]
    (hT : 1 ≤ Fintype.card T) :
    (CS : Set (Language T)) ⊂ (RE : Set (Language T)) := by
  letI : DecidableEq T := Classical.decEq T
  have hCSRecursive :
      (CS : Set (Language T)) ⊂ (Recursive : Set (Language T)) :=
    CS_strict_subclass_Recursive_of_card hT
  refine ⟨fun L hL ↦ Recursive_subset_RE (hCSRecursive.1 hL), ?_⟩
  intro hRECS
  exact hCSRecursive.2 (fun L hL ↦ hRECS (Recursive_subset_RE hL))
