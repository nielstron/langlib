module

public import Langlib.Automata.LinearBounded.BoundedCrossingLanguage
import Mathlib.Tactic

@[expose]
public section

/-!
# Exact regular-language characterization of bounded-crossing LBA presentations

The bounded-profile construction proves that every fixed crossing slice of a finite LBA is
regular, and that an LBA with one uniform selected-accepting crossing cap recognizes a regular
language.  This file proves the converses and packages both statements as exact language-class
equalities.

For the converse, a DFA is run by the existing canonical one-way endmarker scanner.  Its
explicit accepting trace crosses every physical tape boundary exactly once, including on the
two-cell tape for the empty word.  Consequently every positive fixed cap already presents all
regular languages, and allowing an existential uniform cap gives exactly the same class.

The class definitions make sense over an arbitrary terminal type.  The equality theorems use
only the finiteness assumption required by the existing bounded-profile automaton.  They impose
no inhabitedness or cardinality lower bound.  Cap zero is deliberately excluded from the
fixed-cap equality: the one-way scanner necessarily crosses each physical boundary once.
-/

open LBA.BoundedCrossing

variable {T : Type}

/-- Languages obtained as the at-most-`bound` crossing slice of some LBA with finite work and
state types.  The source machine may accept additional words using traces that exceed the cap;
only its semantic `LanguageWithBound` slice is used here. -/
public def is_BoundedCrossingSlice (bound : Nat) (language : Language T) : Prop :=
  ∃ (Work State : Type) (_ : Fintype Work) (_ : Fintype State)
    (M : LBA.Machine (LBA.EndAlpha T Work) State),
    LanguageWithBound M bound = language

/-- The language class of fixed at-most-cap bounded-crossing slices. -/
public def BoundedCrossingSlice (bound : Nat) : Set (Language T) :=
  setOf (is_BoundedCrossingSlice bound)

/-- Every fixed crossing slice over finite component types is DFA-recognizable. -/
public theorem is_DFA_of_is_BoundedCrossingSlice
    [Fintype T] {bound : Nat} {language : Language T}
    (hlanguage : is_BoundedCrossingSlice bound language) :
    is_DFA language := by
  obtain ⟨Work, State, hWork, hState, M, hM⟩ := hlanguage
  letI : Fintype Work := hWork
  letI : Fintype State := hState
  rw [← hM]
  exact is_DFA_languageWithBound M bound

/-- Every DFA language is an at-most-`bound` crossing slice for every positive cap.  The witness
is the canonical one-way endmarker scanner, whose accepting trace has crossing count exactly
one at every boundary. -/
public theorem is_BoundedCrossingSlice_of_is_DFA
    {bound : Nat} (hbound : 1 ≤ bound) {language : Language T}
    (hlanguage : is_DFA language) :
    is_BoundedCrossingSlice bound language := by
  classical
  obtain ⟨State, hState, D, hD⟩ := hlanguage
  letI : Fintype State := hState
  let M := DFA.endmarkerLBA (Work := Unit) D
  have huniform : HasUniformAcceptingBound M bound := by
    intro word haccept
    exact (DFA.endmarkerLBA_hasUniformAcceptingBound_one
      (Work := Unit) D word haccept).mono hbound
  refine ⟨Unit, DFA.EndmarkerLBAState State, inferInstance, inferInstance, M, ?_⟩
  calc
    LanguageWithBound M bound = LBA.LanguageEnd M :=
      (languageWithBound_eq_languageEnd_iff_hasUniformAcceptingBound M bound).2 huniform
    _ = D.accepts := DFA.languageEnd_endmarkerLBA_eq D
    _ = language := hD

/-- For every positive cap, being a fixed-cap LBA crossing slice is exactly DFA
recognizability. -/
public theorem is_BoundedCrossingSlice_iff_is_DFA
    [Fintype T] {bound : Nat} (hbound : 1 ≤ bound) (language : Language T) :
    is_BoundedCrossingSlice bound language ↔ is_DFA language :=
  ⟨is_DFA_of_is_BoundedCrossingSlice,
    is_BoundedCrossingSlice_of_is_DFA hbound⟩

/-- Every positive fixed crossing cap gives exactly the DFA language class. -/
public theorem BoundedCrossingSlice_eq_DFA
    [Fintype T] {bound : Nat} (hbound : 1 ≤ bound) :
    (BoundedCrossingSlice bound : Set (Language T)) = DFA.Class := by
  ext language
  exact is_BoundedCrossingSlice_iff_is_DFA hbound language

/-- Nondeterministic finite-state form of the positive fixed-cap characterization. -/
public theorem is_BoundedCrossingSlice_iff_is_NFA
    [Fintype T] {bound : Nat} (hbound : 1 ≤ bound) (language : Language T) :
    is_BoundedCrossingSlice bound language ↔ is_NFA language :=
  (is_BoundedCrossingSlice_iff_is_DFA hbound language).trans
    is_NFA_iff_is_DFA.symm

/-- Every positive fixed crossing cap also gives exactly the NFA language class. -/
public theorem BoundedCrossingSlice_eq_NFA
    [Fintype T] {bound : Nat} (hbound : 1 ≤ bound) :
    (BoundedCrossingSlice bound : Set (Language T)) = NFA.Class := by
  rw [BoundedCrossingSlice_eq_DFA hbound, ← NFA_eq_DFA]

/-- Mathlib-regular form of the positive fixed-cap characterization. -/
public theorem is_BoundedCrossingSlice_iff_isRegular
    [Fintype T] {bound : Nat} (hbound : 1 ≤ bound) (language : Language T) :
    is_BoundedCrossingSlice bound language ↔ language.IsRegular := by
  rw [is_BoundedCrossingSlice_iff_is_DFA hbound]
  exact Language.isRegular_iff.symm

/-- Languages recognized by an LBA having one crossing cap that works uniformly for a selected
accepting trace of every accepted word.  The cap is part of the semantic presentation witness,
while other accepting and rejecting traces remain unrestricted. -/
public def is_UniformBoundedCrossingLBA (language : Language T) : Prop :=
  ∃ (Work State : Type) (_ : Fintype Work) (_ : Fintype State)
    (M : LBA.Machine (LBA.EndAlpha T Work) State) (bound : Nat),
    HasUniformAcceptingBound M bound ∧ LBA.LanguageEnd M = language

/-- The class of languages having a uniformly bounded selected-accepting-crossing LBA
presentation. -/
public def UniformBoundedCrossingLBA : Set (Language T) :=
  setOf is_UniformBoundedCrossingLBA

/-- A uniformly bounded-crossing finite LBA presentation recognizes a DFA language. -/
public theorem is_DFA_of_is_UniformBoundedCrossingLBA
    [Fintype T] {language : Language T}
    (hlanguage : is_UniformBoundedCrossingLBA language) :
    is_DFA language := by
  obtain ⟨Work, State, hWork, hState, M, bound, hbound, hM⟩ := hlanguage
  letI : Fintype Work := hWork
  letI : Fintype State := hState
  rw [← hM]
  exact is_DFA_languageEnd_of_hasUniformAcceptingBound M bound hbound

/-- Every DFA language has a uniformly bounded-crossing LBA presentation, already with the
explicit scanner cap one. -/
public theorem is_UniformBoundedCrossingLBA_of_is_DFA
    {language : Language T} (hlanguage : is_DFA language) :
    is_UniformBoundedCrossingLBA language := by
  classical
  obtain ⟨State, hState, D, hD⟩ := hlanguage
  letI : Fintype State := hState
  refine ⟨Unit, DFA.EndmarkerLBAState State, inferInstance, inferInstance,
    DFA.endmarkerLBA (Work := Unit) D, 1,
    DFA.endmarkerLBA_hasUniformAcceptingBound_one D, ?_⟩
  exact (DFA.languageEnd_endmarkerLBA_eq D).trans hD

/-- A language has a uniformly bounded-crossing LBA presentation exactly when it is
DFA-recognizable. -/
public theorem is_UniformBoundedCrossingLBA_iff_is_DFA
    [Fintype T] (language : Language T) :
    is_UniformBoundedCrossingLBA language ↔ is_DFA language :=
  ⟨is_DFA_of_is_UniformBoundedCrossingLBA,
    is_UniformBoundedCrossingLBA_of_is_DFA⟩

/-- Uniformly bounded selected-accepting crossings characterize exactly the regular
languages. -/
public theorem UniformBoundedCrossingLBA_eq_DFA [Fintype T] :
    (UniformBoundedCrossingLBA : Set (Language T)) = DFA.Class := by
  ext language
  exact is_UniformBoundedCrossingLBA_iff_is_DFA language

/-- Nondeterministic finite-state form of the uniform bounded-crossing characterization. -/
public theorem is_UniformBoundedCrossingLBA_iff_is_NFA
    [Fintype T] (language : Language T) :
    is_UniformBoundedCrossingLBA language ↔ is_NFA language :=
  (is_UniformBoundedCrossingLBA_iff_is_DFA language).trans
    is_NFA_iff_is_DFA.symm

/-- Uniformly bounded selected-accepting crossings also characterize exactly the NFA class. -/
public theorem UniformBoundedCrossingLBA_eq_NFA [Fintype T] :
    (UniformBoundedCrossingLBA : Set (Language T)) = NFA.Class := by
  rw [UniformBoundedCrossingLBA_eq_DFA, ← NFA_eq_DFA]

/-- Mathlib-regular form of the uniform bounded-crossing characterization. -/
public theorem is_UniformBoundedCrossingLBA_iff_isRegular
    [Fintype T] (language : Language T) :
    is_UniformBoundedCrossingLBA language ↔ language.IsRegular := by
  rw [is_UniformBoundedCrossingLBA_iff_is_DFA]
  exact Language.isRegular_iff.symm

end
