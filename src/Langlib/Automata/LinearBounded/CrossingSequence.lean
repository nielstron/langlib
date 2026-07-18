module

public import Langlib.Automata.LinearBounded.StepTraceCrossing

@[expose]
public section

/-!
# Chronological crossing sequences of LBA traces

For a concrete finite LBA trace and one physical tape boundary, the crossing sequence records
the target control state of each step crossing that boundary, in chronological order.  Its list
length is exactly `StepTrace.crossingCount`, and trace concatenation becomes list concatenation.

These state sequences are the finite interfaces shared by adjacent single-cell histories in the
bounded-crossing finite-automaton construction.
-/

namespace LBA.StepTrace

universe u v

variable {Gamma : Type u} {State : Type v} {n : Nat}
variable {M : LBA.Machine Gamma State}
variable {source target : DLBA.Cfg Gamma State n}

/-- Target control states of the crossings of `b`, in chronological order. -/
def crossingSequence (b : Fin n) :
    {source target : DLBA.Cfg Gamma State n} →
      LBA.StepTrace M source target → List State
  | _, _, .refl _ => []
  | source, _, .head (next := next) _ rest =>
      if CrossesBoundary b source next then
        next.state :: crossingSequence b rest
      else
        crossingSequence b rest

@[simp] theorem crossingSequence_refl (b : Fin n)
    (cfg : DLBA.Cfg Gamma State n) :
    crossingSequence b (.refl cfg : LBA.StepTrace M cfg cfg) = [] := rfl

/-- A crossing sequence has one state for every crossing of its boundary. -/
@[simp] theorem crossingSequence_length (b : Fin n)
    (trace : LBA.StepTrace M source target) :
    (crossingSequence b trace).length = crossingCount b trace := by
  induction trace with
  | refl => rfl
  | @head source next target hstep rest ih =>
      simp only [crossingSequence, crossingCount]
      split
      · simp_all
        omega
      · simp_all

/-- Crossing sequences concatenate in chronological order when traces concatenate. -/
@[simp] theorem crossingSequence_append (b : Fin n)
    {middle : DLBA.Cfg Gamma State n}
    (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target) :
    crossingSequence b (append first second) =
      crossingSequence b first ++ crossingSequence b second := by
  induction first with
  | refl => rfl
  | @head source next middle hstep rest ih =>
      simp only [append, crossingSequence]
      split <;> simp_all

end LBA.StepTrace

end
