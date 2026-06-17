module

public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
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

## Main result

* `LBA_subset_Recursive` — `(LBA : Set (Language T)) ⊆ Recursive`.
-/

variable {T : Type}

/-- **Every LBA language is recursive (decidable).** Compose `LBA ⊆ CS` (Myhill) with
`CS ⊆ Recursive` (Post). -/
theorem LBA_subset_Recursive [Fintype T] [DecidableEq T] [Primcodable T] :
    (LBA : Set (Language T)) ⊆ (Recursive : Set (Language T)) :=
  fun _ hL => CS_subset_Recursive_class (LBA_subset_CS hL)
