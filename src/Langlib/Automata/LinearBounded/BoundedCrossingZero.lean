module

public import Langlib.Automata.LinearBounded.BoundedCrossingRegularCharacterization
import Mathlib.Tactic

@[expose]
public section

/-!
# The zero-crossing slice

A zero-crossing run on a canonical endmarker tape cannot leave the left endmarker.  Indeed,
the boundary immediately to its right exists even for the empty input, and the first departure
would cross that boundary.  Such a run therefore sees only the left-endmarker cell.  Its same
sequence of transitions can be replayed at every other tape width, starting from any
configuration with the same state and symbol under a head at cell zero.

It follows that `LanguageWithBound M 0` is independent of the input word.  Consequently the
cap-zero slice class is exactly the two trivial languages, while every positive cap gives all
regular languages by `BoundedCrossingSlice_eq_DFA`.

All trace-level results below are independent of finiteness.  The final class characterization
quantifies over arbitrary finite work and state types and applies to every terminal type,
including the empty type; there is no inhabitedness or cardinality lower bound.
-/

namespace LBA.BoundedCrossing

universe u v

variable {Gamma : Type u} {State : Type v} {n m : Nat}
variable {M : LBA.Machine Gamma State}

/-- Two configurations, possibly at different tape widths, have the same local view at the
left boundary.  Both heads are at cell zero, while their states and scanned symbols agree. -/
private def SameLeftView
    (source : DLBA.Cfg Gamma State n) (source' : DLBA.Cfg Gamma State m) : Prop :=
  source.state = source'.state ∧
    source.tape.head.val = 0 ∧ source'.tape.head.val = 0 ∧
      source.tape.read = source'.tape.read

/-- A step between configurations whose heads both lie at cell zero can be replayed at any
other width with the same left-boundary local view, provided the source step also ends at cell
zero. -/
private theorem exists_step_sameLeftView
    (hn : 0 < n)
    {source next : DLBA.Cfg Gamma State n}
    {source' : DLBA.Cfg Gamma State m}
    (hstep : LBA.Step M source next)
    (hview : SameLeftView source source')
    (hnext : next.tape.head.val = 0) :
    ∃ next' : DLBA.Cfg Gamma State m,
      LBA.Step M source' next' ∧ SameLeftView next next' := by
  rcases hstep with ⟨state, written, direction, henabled, rfl⟩
  rcases hview with ⟨hstate, hsourceHead, hsourceHead', hread⟩
  let next' : DLBA.Cfg Gamma State m :=
    ⟨state, (source'.tape.write written).moveHead direction⟩
  refine ⟨next', ?_, ?_⟩
  · refine ⟨state, written, direction, ?_, rfl⟩
    simpa only [← hstate, ← hread] using henabled
  · refine ⟨rfl, hnext, ?_, ?_⟩
    · cases direction <;>
        simp_all [next', DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    · cases direction <;>
        simp_all [next', DLBA.BoundedTape.read, DLBA.BoundedTape.write,
          DLBA.BoundedTape.moveHead, Function.update_self]

/-- A zero count at the first boundary, together with a head initially at cell zero, permits
replaying a concrete trace at every other width with the same left local view.

The replay has zero crossings at *every* target boundary.  Its final state agrees with the
original final state, which is the fact needed to transport acceptance. -/
private theorem exists_zeroCrossing_replay
    (hn : 0 < n)
    {source target : DLBA.Cfg Gamma State n}
    {source' : DLBA.Cfg Gamma State m}
    (trace : LBA.StepTrace M source target)
    (hview : SameLeftView source source')
    (hcross : trace.crossingCount (⟨0, hn⟩ : Fin n) = 0) :
    ∃ target' : DLBA.Cfg Gamma State m,
      ∃ trace' : LBA.StepTrace M source' target',
        target.state = target'.state ∧
          (∀ boundary : Fin m, trace'.crossingCount boundary = 0) := by
  induction trace generalizing source' with
  | refl =>
      exact ⟨source', .refl source', hview.1, fun boundary ↦ rfl⟩
  | @head source next target hstep rest ih =>
      have hnotCross :
          ¬ LBA.StepTrace.CrossesBoundary (⟨0, hn⟩ : Fin n) source next := by
        intro hcrosses
        simp [LBA.StepTrace.crossingCount, hcrosses] at hcross
      have hnextHead : next.tape.head.val = 0 := by
        have hsourceHead : source.tape.head.val = 0 := hview.2.1
        by_contra hne
        apply hnotCross
        exact Or.inl ⟨by simpa [LBA.StepTrace.HeadAtOrLeft] using hsourceHead.le,
          by simp only [LBA.StepTrace.HeadRight]; omega⟩
      have hrestCross :
          rest.crossingCount (⟨0, hn⟩ : Fin n) = 0 := by
        simp only [LBA.StepTrace.crossingCount] at hcross
        omega
      obtain ⟨next', hstep', hnextView⟩ :=
        exists_step_sameLeftView hn hstep hview hnextHead
      obtain ⟨target', trace', hstate, htraceCross⟩ :=
        ih hnextView hrestCross
      refine ⟨target', .head hstep' trace', hstate, ?_⟩
      intro boundary
      simp only [LBA.StepTrace.crossingCount, htraceCross boundary, Nat.add_zero]
      have hsourceHead' : source'.tape.head.val = 0 := hview.2.2.1
      have hnextHead' : next'.tape.head.val = 0 := hnextView.2.2.1
      have hnotCross' :
          ¬ LBA.StepTrace.CrossesBoundary boundary source' next' := by
        simp only [LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
          LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
          LBA.StepTrace.HeadRight]
        omega
      simp [hnotCross']

/-- Zero-crossing acceptance from a positive-width source can be replayed at any width from a
configuration with the same state and scanned symbol at a head positioned on cell zero.  No
finiteness assumptions are needed. -/
public theorem acceptsWithBound_zero_of_same_left_view
    (hn : 0 < n)
    {source : DLBA.Cfg Gamma State n}
    {source' : DLBA.Cfg Gamma State m}
    (hstate : source.state = source'.state)
    (hsourceHead : source.tape.head.val = 0)
    (hsourceHead' : source'.tape.head.val = 0)
    (hread : source.tape.read = source'.tape.read)
    (haccept : AcceptsWithBound M source 0) :
    AcceptsWithBound M source' 0 := by
  obtain ⟨target, trace, hfinal, hcross⟩ := haccept
  have hfirst : trace.crossingCount (⟨0, hn⟩ : Fin n) = 0 := by
    exact Nat.eq_zero_of_le_zero (hcross ⟨0, hn⟩)
  obtain ⟨target', trace', htargetState, htraceCross⟩ :=
    exists_zeroCrossing_replay hn trace
      ⟨hstate, hsourceHead, hsourceHead', hread⟩ hfirst
  exact ⟨target', trace', by simpa [← htargetState] using hfinal,
    fun boundary ↦ by simp [htraceCross boundary]⟩

variable {Terminal Work : Type*}

/-- Cap-zero bounded acceptance on canonical endmarker tapes is independent of the input word.
This includes the empty word: its tape still has the boundary between `⊢` and `⊣`. -/
public theorem acceptsWithBound_zero_initCfgEnd_iff
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (left right : List Terminal) :
    AcceptsWithBound M (LBA.initCfgEnd M left) 0 ↔
      AcceptsWithBound M (LBA.initCfgEnd M right) 0 := by
  constructor <;> intro haccept
  · apply acceptsWithBound_zero_of_same_left_view
      (n := left.length + 1) (m := right.length + 1)
      (Nat.succ_pos _) rfl
      (by simp [LBA.initCfgEnd, LBA.loadEnd])
      (by simp [LBA.initCfgEnd, LBA.loadEnd])
      (by simp [LBA.initCfgEnd, LBA.loadEnd, DLBA.BoundedTape.read])
      haccept
  · apply acceptsWithBound_zero_of_same_left_view
      (n := right.length + 1) (m := left.length + 1)
      (Nat.succ_pos _) rfl
      (by simp [LBA.initCfgEnd, LBA.loadEnd])
      (by simp [LBA.initCfgEnd, LBA.loadEnd])
      (by simp [LBA.initCfgEnd, LBA.loadEnd, DLBA.BoundedTape.read])
      haccept

/-- The cap-zero language slice of every endmarker LBA is either empty or universal.  This
machine-level statement requires neither finite component types nor a finite terminal alphabet. -/
public theorem languageWithBound_zero_eq_empty_or_univ
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) :
    LanguageWithBound M 0 = (∅ : Set (List Terminal)) ∨
      LanguageWithBound M 0 = (Set.univ : Set (List Terminal)) := by
  by_cases hemptyWord : ([] : List Terminal) ∈ LanguageWithBound M 0
  · right
    ext input
    change AcceptsWithBound M (LBA.initCfgEnd M input) 0 ↔ True
    exact ⟨fun _ ↦ trivial,
      fun _ ↦ (acceptsWithBound_zero_initCfgEnd_iff M [] input).mp hemptyWord⟩
  · left
    ext input
    change AcceptsWithBound M (LBA.initCfgEnd M input) 0 ↔ False
    exact ⟨fun haccept ↦ hemptyWord
      ((acceptsWithBound_zero_initCfgEnd_iff M input []).mp haccept), False.elim⟩

/-! ## Exact cap-zero class -/

variable {T : Type}

/-- A transition-free one-state machine used as the explicit empty and universal cap-zero
witness. -/
private def zeroCrossingTrivialMachine
    (Gamma : Type*) (accepts : Bool) : LBA.Machine Gamma Unit where
  transition _ _ := ∅
  accept _ := accepts
  initial := ()

/-- The empty language has a cap-zero crossing-slice presentation over arbitrary terminal
types. -/
public theorem is_BoundedCrossingSlice_zero_empty :
    is_BoundedCrossingSlice (T := T) 0 (∅ : Set (List T)) := by
  let M := zeroCrossingTrivialMachine (LBA.EndAlpha T Unit) false
  refine ⟨Unit, Unit, inferInstance, inferInstance, M, ?_⟩
  ext input
  constructor
  · rintro ⟨target, _trace, hfinal, _hcross⟩
    simp [M, zeroCrossingTrivialMachine] at hfinal
  · exact False.elim

/-- The universal language has a cap-zero crossing-slice presentation over arbitrary terminal
types. -/
public theorem is_BoundedCrossingSlice_zero_univ :
    is_BoundedCrossingSlice (T := T) 0 (Set.univ : Set (List T)) := by
  let M := zeroCrossingTrivialMachine (LBA.EndAlpha T Unit) true
  refine ⟨Unit, Unit, inferInstance, inferInstance, M, ?_⟩
  ext input
  change AcceptsWithBound M (LBA.initCfgEnd M input) 0 ↔ True
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨LBA.initCfgEnd M input, .refl _, by rfl, fun boundary ↦ by rfl⟩

/-- Exact language-level characterization of cap-zero crossing slices.  The result is uniform
over arbitrary finite component types and imposes no assumption at all on the terminal type. -/
public theorem is_BoundedCrossingSlice_zero_iff_eq_empty_or_univ
    {language : Language T} :
    is_BoundedCrossingSlice 0 language ↔
      language = (∅ : Set (List T)) ∨
        language = (Set.univ : Set (List T)) := by
  constructor
  · rintro ⟨Work, State, hWork, hState, M, hM⟩
    rcases languageWithBound_zero_eq_empty_or_univ M with hempty | huniv
    · exact Or.inl (hM ▸ hempty)
    · exact Or.inr (hM ▸ huniv)
  · rintro (rfl | rfl)
    · exact is_BoundedCrossingSlice_zero_empty
    · exact is_BoundedCrossingSlice_zero_univ

/-- The cap-zero crossing-slice class consists exactly of the empty and universal languages. -/
public theorem BoundedCrossingSlice_zero_eq_trivial_languages :
    (BoundedCrossingSlice 0 : Set (Language T)) =
      ({(∅ : Set (List T)), (Set.univ : Set (List T))} :
        Set (Language T)) := by
  ext language
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact is_BoundedCrossingSlice_zero_iff_eq_empty_or_univ

end LBA.BoundedCrossing

end
