module

public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
import Langlib.Classes.ContextSensitive.Inclusion.StrictRecursive
import Mathlib.Tactic
@[expose]
public section



/-!
# LBA Languages ⊆ Recursive Languages

Every language recognised by a (nondeterministic) linearly bounded automaton is
**recursive** (decidable). This follows immediately from two results already in the
library, composed:

* `LBA_subset_CS` — every endmarker-LBA language is context-sensitive (Myhill, the
  `LBA ⊆ CS` direction of `CS = LBA`, `Equivalence/ContextSensitive.lean`);
* `CS_subset_Recursive_class` — every context-sensitive language is recursive, via Post's
  theorem (`Classes/ContextSensitive/Inclusion/Recursive.lean`).

So the membership problem for an LBA is decidable, even though the open `LBA ⇔? DLBA`
question (whether nondeterministic and deterministic LBAs recognise the same class) is
not settled here.

## Main results

* `LBA_subset_Recursive` — `(LBA : Set (Language T)) ⊆ Recursive`.
* `LBA_strict_subclass_Recursive` — `(LBA : Set (Language T)) ⊂ Recursive` over
  every nonempty finite computably encoded alphabet.
* `LBA_strict_subclass_Recursive_of_card` — the cardinality-based strict variant.
-/

variable {T : Type}

/-- **Every LBA language is recursive (decidable).** Compose `LBA ⊆ CS` (Myhill) with
`CS ⊆ Recursive` (Post). -/
theorem LBA_subset_Recursive [Fintype T] [DecidableEq T] [Primcodable T] :
    (LBA : Set (Language T)) ⊆ (Recursive : Set (Language T)) :=
  fun _ hL => CS_subset_Recursive_class (LBA_subset_CS hL)

/-- LBA-recognizable languages form a strict subclass of recursive languages over
every nonempty finite computably encoded alphabet. -/
public theorem LBA_strict_subclass_Recursive
    [Fintype T] [DecidableEq T] [Primcodable T] [Nonempty T] :
    (LBA : Set (Language T)) ⊂ (Recursive : Set (Language T)) := by
  simpa only [CS_eq_LBA] using (CS_strict_subclass_Recursive (T := T))

/-- LBA-recognizable languages form a strict subclass of recursive languages over
every finite alphabet containing at least one symbol. -/
public theorem LBA_strict_subclass_Recursive_of_card [Fintype T] [DecidableEq T]
    (hT : 1 ≤ Fintype.card T) :
    (LBA : Set (Language T)) ⊂ (Recursive : Set (Language T)) := by
  simpa only [CS_eq_LBA] using (CS_strict_subclass_Recursive_of_card (T := T) hT)
