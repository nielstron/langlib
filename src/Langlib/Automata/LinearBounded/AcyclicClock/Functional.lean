module

public import Langlib.Automata.LinearBounded.AcyclicClock.Construction
public import Langlib.Automata.LinearBounded.Functional

@[expose]
public section

/-!
# Functionality of the acyclic-clock compiler

The operational clock protocol makes a source-machine choice only in a `ready` state.  There its
transition set is the image of the corresponding source transition set under `sourceChoice`.
Every other phase has either no transition or a singleton transition.  Consequently the clock
compiler preserves local functionality.
-/

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- The operational acyclic-clock compiler preserves a single-valued local transition table. -/
public theorem machine_functional
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (hfunctional : M.Functional) :
    (machine M).Functional := by
  intro state symbol
  letI : Nonempty Λ := ⟨M.initial⟩
  rcases symbol with (inner | boundary)
  · rcases inner with (_ | tagged)
    · cases state <;> simp [machine, transition]
    · rcases tagged with (input | cell)
      · cases state <;> simp [machine, transition]
      · cases state with
        | ready source =>
            simp only [machine, transition]
            split
            · exact (hfunctional source cell.src).image (sourceChoice cell)
            · exact Set.subsingleton_empty
        | initFirst | initSweep | initBack | mark | seek | cleanR | cleanL | carry |
            carryCheck | returnL | findMark =>
              simp only [machine, transition]
              repeat' first | split
              all_goals simp
  · cases boundary <;> cases state <;> simp [machine, transition]

end LBA.AcyclicClock
