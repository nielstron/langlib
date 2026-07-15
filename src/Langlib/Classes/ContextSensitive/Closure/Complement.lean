module

public import Langlib.Automata.LinearBounded.Complement
public import Langlib.Automata.LinearBounded.Equivalence.ContextSensitive
public import Langlib.Classes.ContextSensitive.Closure.EmptyWord
public import Langlib.Utilities.ClosurePredicates

@[expose]
public section

/-!
# Context-sensitive languages are closed under complement

The automaton-level inductive-counting theorem complements the nonempty part of a
language.  For a context-sensitive language `L`, we first remove `ε`, complement
that positive LBA language, and then use the existing empty-word closure theorem to
recover the ordinary complement `Lᶜ`.

This is the Immerman–Szelepcsényi theorem specialized to nondeterministic linear
space.
-/

variable {T : Type} [Fintype T]

/-- Removing the empty word from a context-sensitive language yields a language
recognized by the marker-free, input-sized LBA model. -/
private theorem is_LBA_pos_diff_empty_of_is_CS [DecidableEq T]
    {L : Language T} (hL : is_CS L) :
    is_LBA_pos (L \ ({[]} : Set (List T))) := by
  obtain ⟨g, hg, hlang⟩ := hL
  obtain ⟨g₀, _hfinite, hnc, hcore⟩ := exists_noncontracting_offEmpty_of_CS g hg
  apply is_LBA_pos_of_isCS_not_nil
  · rw [← hlang, ← hcore]
    exact is_CS_of_is_noncontracting ⟨g₀, hnc, rfl⟩
  · rintro ⟨_, hnil⟩
    exact hnil rfl

/-- Complementing after deleting `ε` and then restricting back to nonempty words
is the same as restricting the ordinary complement to nonempty words. -/
private theorem diff_empty_complement_diff_empty (L : Language T) :
    (L \ ({[]} : Set (List T)))ᶜ \ ({[]} : Set (List T)) =
      Lᶜ \ ({[]} : Set (List T)) := by
  ext w
  constructor
  · rintro ⟨hnot, hwne⟩
    exact ⟨fun hw => hnot ⟨hw, hwne⟩, hwne⟩
  · rintro ⟨hnot, hwne⟩
    exact ⟨fun hw => hnot hw.1, hwne⟩

/-- The complement of a context-sensitive language over a finite alphabet is
context-sensitive. -/
public theorem is_CS_complement {L : Language T} (hL : is_CS L) : is_CS Lᶜ := by
  classical
  have hpos : is_LBA_pos (L \ ({[]} : Set (List T))) :=
    is_LBA_pos_diff_empty_of_is_CS hL
  have hcomp := is_LBA_pos_complement hpos
  rw [diff_empty_complement_diff_empty] at hcomp
  exact is_CS_of_diff_empty_of_is_CS (is_LBA_pos_imp_isCS hcomp)

/-- A language is context-sensitive if and only if its complement is. -/
@[simp]
public theorem CS_complement_iff {L : Language T} : is_CS Lᶜ ↔ is_CS L := by
  classical
  constructor
  · intro h
    simpa using is_CS_complement h
  · exact is_CS_complement

/-- Context-sensitive languages over a finite alphabet are closed under complement. -/
public theorem CS_closedUnderComplement : ClosedUnderComplement (α := T) is_CS :=
  fun _L hL => is_CS_complement hL
