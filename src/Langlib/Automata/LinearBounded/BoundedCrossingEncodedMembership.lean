module

public import Langlib.Automata.LinearBounded.BoundedCrossingEffective
public import Langlib.Automata.LinearBounded.BoundedCrossingLanguage
public import Langlib.Utilities.ComputabilityPredicates
public import Mathlib.Computability.Halting
public import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

@[expose]
public section

/-!
# Encoded membership for fixed crossing caps

This file turns the relative transition-table interface for bounded crossing profiles into a
genuine code-and-word membership theorem.  A `FiniteCode` contains only finite local machine
data: an initial state, one accepting bit per state, and one finite move set per state and tape
symbol.  It is never supplied the input word or a language-membership predicate.

For each fixed crossing cap, `boundedSliceMembershipBool` evaluates the exact profile NFA on the
canonical endmarked word.  Its correctness theorem identifies the result with
`LanguageWithBound`; its computability theorem treats the pair `(machineCode, word)` as the input.
The construction is uniform over every fixed choice of finite terminal, work, and state types and
does not assume that any of them is nonempty.
-/

namespace LBA.Machine

universe u v

/-- A finite, local presentation of an LBA over fixed tape-symbol and state types.

Unlike `LBA.Machine`, the transition data is a `Finset`, not an arbitrary semantic `Set`.
Consequently this type cannot store a word-dependent language-membership oracle. -/
public structure FiniteCode (Gamma : Type u) (State : Type v) where
  initial : State
  accept : State → Bool
  next : State → Gamma → Finset (State × Gamma × DLBA.Dir)

public noncomputable instance [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State] : Fintype (FiniteCode Gamma State) :=
  Fintype.ofInjective
    (fun code => (code.initial, code.accept, code.next))
    (by intro left right h; cases left; cases right; simpa using h)

/-- Every fixed finite local-code type has a computable numeric presentation.  The chosen
equivalence is intentionally local to the fixed tape-symbol and state types; the theorem below
does not pretend that their cardinalities are themselves part of this code. -/
public noncomputable instance [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State] : Primcodable (FiniteCode Gamma State) :=
  Primcodable.ofEquiv (Fin (Fintype.card (FiniteCode Gamma State)))
    (Fintype.equivFin (FiniteCode Gamma State))

namespace FiniteCode

variable {Gamma : Type u} {State : Type v}

/-- Interpret finite local syntax as the semantic LBA structure used elsewhere in the library. -/
def toMachine [DecidableEq Gamma] [DecidableEq State]
    (code : FiniteCode Gamma State) : LBA.Machine Gamma State where
  transition state symbol := {move | move ∈ code.next state symbol}
  accept := code.accept
  initial := code.initial

/-- The transition table extracted from finite syntax.  Its exactness proof is definitional. -/
def transitionTable [DecidableEq Gamma] [DecidableEq State]
    (code : FiniteCode Gamma State) : code.toMachine.TransitionTable where
  next := code.next
  mem_next_iff := Iff.rfl

@[simp] theorem toMachine_initial [DecidableEq Gamma] [DecidableEq State]
    (code : FiniteCode Gamma State) : code.toMachine.initial = code.initial := rfl

@[simp] theorem toMachine_accept [DecidableEq Gamma] [DecidableEq State]
    (code : FiniteCode Gamma State) (state : State) :
    code.toMachine.accept state = code.accept state := rfl

@[simp] theorem mem_toMachine_transition [DecidableEq Gamma] [DecidableEq State]
    (code : FiniteCode Gamma State) (state : State) (symbol : Gamma)
    (move : State × Gamma × DLBA.Dir) :
    move ∈ code.toMachine.transition state symbol ↔ move ∈ code.next state symbol := Iff.rfl

end FiniteCode

end LBA.Machine

namespace LBA.BoundedCrossing.EncodedMembership

open LBA.BoundedCrossing.Effective

universe u v w

variable {Terminal : Type u} {Work : Type v} {State : Type w}

abbrev TapeAlpha := LBA.EndAlpha Terminal Work

abbrev Code := LBA.Machine.FiniteCode (TapeAlpha (Terminal := Terminal) (Work := Work)) State

abbrev ProfileState (bound : Nat) :=
  ScanState (TapeAlpha (Terminal := Terminal) (Work := Work)) State bound

/-- Explicit finite set of initial states of the profile NFA. -/
def profileStartFinset
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (_code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat) : Finset (ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound) :=
  Finset.univ.filter fun state => profileStartBool state = true

/-- One explicit subset-construction step for the profile NFA. -/
def profileStepFinset
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat)
    (current : Finset (ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound))
    (symbol : TapeAlpha (Terminal := Terminal) (Work := Work)) :
    Finset (ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound) :=
  Finset.univ.filter fun target =>
    (current.filter fun source =>
      profileStepBool code.toMachine code.transitionTable bound source symbol target = true).Nonempty

/-- Deterministically evaluate the finite profile NFA from an explicit current-state set. -/
def profileEvalFrom
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat)
    (current : Finset (ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound))
    (word : List (TapeAlpha (Terminal := Terminal) (Work := Work))) :
    Finset (ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound) :=
  word.foldl (profileStepFinset code bound) current

/-- Boolean test that an explicit active subset contains a profile-NFA accepting state. -/
def profileAcceptsFinsetBool
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat)
    (current : Finset (ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound)) :
    Bool :=
  decide <| (current.filter fun state =>
    profileAcceptBool code.toMachine code.transitionTable bound state = true).Nonempty

/-- Boolean acceptance of a tape-alphabet word by the exact bounded-profile NFA. -/
def profileTapeMembershipBool
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat) (word : List (TapeAlpha (Terminal := Terminal) (Work := Work))) : Bool :=
  profileAcceptsFinsetBool code bound
    (profileEvalFrom code bound (profileStartFinset code bound) word)

/-- The actual code-and-word decision function for one fixed crossing cap. -/
def boundedSliceMembershipBool
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat) (word : List Terminal) : Bool :=
  profileTapeMembershipBool code bound (LBA.endWord (Work := Work) word)

/-- The fixed-signature language denoted by a finite local code at one crossing cap. -/
def boundedSliceLanguageOf
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (bound : Nat)
    (code : Code (Terminal := Terminal) (Work := Work) (State := State)) : Language Terminal :=
  LanguageWithBound code.toMachine bound

/-- The language class represented when the component types and crossing cap are fixed. -/
def FixedSignatureBoundedSliceClass
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (bound : Nat) : Set (Language Terminal) :=
  Set.range (boundedSliceLanguageOf (Terminal := Terminal) (Work := Work) (State := State) bound)

theorem mem_profileStartFinset_iff
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat)
    (state : ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound) :
    state ∈ profileStartFinset code bound ↔
      state ∈ (profileNFA code.toMachine bound).start := by
  simp only [profileStartFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact profileStartBool_eq_true_iff code.toMachine bound state

theorem coe_profileStartFinset
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat) :
    (profileStartFinset code bound : Set _) =
      (profileNFA code.toMachine bound).start := by
  ext state
  exact mem_profileStartFinset_iff code bound state

theorem mem_profileStepFinset_iff
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat)
    (current : Finset (ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound))
    (symbol : TapeAlpha (Terminal := Terminal) (Work := Work))
    (target : ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound) :
    target ∈ profileStepFinset code bound current symbol ↔
      target ∈ (profileNFA code.toMachine bound).stepSet (current : Set _) symbol := by
  simp only [profileStepFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.filter_nonempty_iff, NFA.mem_stepSet]
  constructor
  · rintro ⟨source, hsource, hstep⟩
    exact ⟨source, hsource,
      (profileStepBool_eq_true_iff code.toMachine code.transitionTable bound
        source symbol target).mp hstep⟩
  · rintro ⟨source, hsource, hstep⟩
    exact ⟨source, hsource,
      (profileStepBool_eq_true_iff code.toMachine code.transitionTable bound
        source symbol target).mpr hstep⟩

theorem coe_profileStepFinset
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat)
    (current : Finset (ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound))
    (symbol : TapeAlpha (Terminal := Terminal) (Work := Work)) :
    (profileStepFinset code bound current symbol : Set _) =
      (profileNFA code.toMachine bound).stepSet (current : Set _) symbol := by
  ext target
  exact mem_profileStepFinset_iff code bound current symbol target

theorem coe_profileEvalFrom
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat)
    (current : Finset (ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound))
    (word : List (TapeAlpha (Terminal := Terminal) (Work := Work))) :
    (profileEvalFrom code bound current word : Set _) =
      (profileNFA code.toMachine bound).evalFrom (current : Set _) word := by
  induction word generalizing current with
  | nil => rfl
  | cons symbol word ih =>
      simp only [profileEvalFrom, List.foldl_cons, NFA.evalFrom_cons]
      rw [← coe_profileStepFinset]
      exact ih (profileStepFinset code bound current symbol)

/-- Exact Boolean correctness on arbitrary tape-alphabet words. -/
theorem profileTapeMembershipBool_eq_true_iff
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat) (word : List (TapeAlpha (Terminal := Terminal) (Work := Work))) :
    profileTapeMembershipBool code bound word = true ↔
      word ∈ (profileNFA code.toMachine bound).accepts := by
  simp only [profileTapeMembershipBool, profileAcceptsFinsetBool, decide_eq_true_eq,
    Finset.filter_nonempty_iff, NFA.mem_accepts]
  constructor
  · rintro ⟨state, hstate, haccept⟩
    have hstate' : state ∈
        (profileNFA code.toMachine bound).evalFrom
          (profileNFA code.toMachine bound).start word := by
      rw [← coe_profileStartFinset, ← coe_profileEvalFrom]
      exact hstate
    exact ⟨state,
      (profileAcceptBool_eq_true_iff code.toMachine code.transitionTable bound state).mp haccept,
      hstate'⟩
  · rintro ⟨state, haccept, hstate⟩
    have hstate' : state ∈
        profileEvalFrom code bound (profileStartFinset code bound) word := by
      change state ∈
        (profileEvalFrom code bound (profileStartFinset code bound) word : Set _)
      rw [coe_profileEvalFrom, coe_profileStartFinset]
      exact hstate
    exact ⟨state, hstate',
      (profileAcceptBool_eq_true_iff code.toMachine code.transitionTable bound state).mpr haccept⟩

/-- Exact correctness of the joint machine-code-and-word membership decision. -/
public theorem boundedSliceMembershipBool_eq_true_iff
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (code : Code (Terminal := Terminal) (Work := Work) (State := State))
    (bound : Nat) (word : List Terminal) :
    boundedSliceMembershipBool code bound word = true ↔
      word ∈ LanguageWithBound code.toMachine bound := by
  rw [boundedSliceMembershipBool, profileTapeMembershipBool_eq_true_iff,
    ← mem_terminalProfileNFA_iff_mem_endWord,
    terminalProfileNFA_accepts_eq_languageWithBound]

/-! ## Joint computability in the finite machine code and the word -/

attribute [local irreducible] profileAcceptsFinsetBool

/-- For every fixed cap and fixed arbitrary finite component types, the Boolean checker is
computable jointly in the finite local machine code and the unbounded input word.

The proof uses finite-domain primitive recursiveness only for local code/state/symbol queries.
The word itself is processed by an explicit primitive-recursive `List.foldl`. -/
public theorem boundedSliceMembershipBool_computable
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    [Primcodable Terminal]
    (bound : Nat) :
    Computable (fun input :
        Code (Terminal := Terminal) (Work := Work) (State := State) × List Terminal =>
      boundedSliceMembershipBool input.1 bound input.2) := by
  let S := ProfileState (Terminal := Terminal) (Work := Work) (State := State) bound
  let C := Code (Terminal := Terminal) (Work := Work) (State := State)
  let A := TapeAlpha (Terminal := Terminal) (Work := Work)
  letI : Primcodable Work :=
    Primcodable.ofEquiv (Fin (Fintype.card Work)) (Fintype.equivFin Work)
  letI : Primcodable (Finset S) :=
    Primcodable.ofEquiv (Fin (Fintype.card (Finset S)))
      (Fintype.equivFin (Finset S))
  have hinputCell : Primrec (LBA.inputCell : Terminal → A) :=
    Primrec.dom_finite _
  have hmapped : Primrec (fun input : C × List Terminal =>
      input.2.map (LBA.inputCell : Terminal → A)) := by
    apply Primrec.list_map Primrec.snd
    apply Primrec₂.mk
    exact hinputCell.comp Primrec.snd
  have hword : Primrec (fun input : C × List Terminal =>
      LBA.endWord (Work := Work) input.2) := by
    apply (Primrec.list_append.comp
      (Primrec.list_cons.comp (Primrec.const (LBA.leftMark : A)) hmapped)
      (Primrec.const [LBA.rightMark])).of_eq
    intro input
    rfl
  have hinitialCode : Primrec (fun code : C =>
      profileStartFinset code bound) :=
    Primrec.dom_finite _
  have hinitial : Primrec (fun input : C × List Terminal =>
      profileStartFinset input.1 bound) :=
    hinitialCode.comp Primrec.fst
  have hcodedWord : Primrec (fun input : C × List Terminal =>
      (LBA.endWord (Work := Work) input.2).map fun symbol => (input.1, symbol)) := by
    apply Primrec.list_map hword
    apply Primrec₂.mk
    exact Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hstepFinite : Primrec (fun input : Finset S × (C × A) =>
      profileStepFinset input.2.1 bound input.1 input.2.2) :=
    Primrec.dom_finite _
  have hstep : Primrec₂ (fun (_input : C × List Terminal)
      (step : Finset S × (C × A)) =>
      profileStepFinset step.2.1 bound step.1 step.2.2) := by
    apply Primrec₂.mk
    exact hstepFinite.comp Primrec.snd
  have hevalCoded : Primrec (fun input : C × List Terminal =>
      ((LBA.endWord (Work := Work) input.2).map fun symbol => (input.1, symbol)).foldl
        (fun current coded => profileStepFinset coded.1 bound current coded.2)
        (profileStartFinset input.1 bound)) := by
    exact Primrec.list_foldl hcodedWord hinitial hstep
  have heval : Primrec (fun input : C × List Terminal =>
      profileEvalFrom input.1 bound (profileStartFinset input.1 bound)
        (LBA.endWord (Work := Work) input.2)) := by
    apply hevalCoded.of_eq
    intro input
    simp only [List.foldl_map]
    rfl
  have hacceptFinite : Primrec (fun input : C × Finset S =>
      profileAcceptsFinsetBool input.1 bound input.2) :=
    Primrec.dom_finite _
  have hresult : Primrec (fun input : C × List Terminal =>
      profileAcceptsFinsetBool input.1 bound
        (profileEvalFrom input.1 bound (profileStartFinset input.1 bound)
          (LBA.endWord (Work := Work) input.2))) :=
    hacceptFinite.comp (Primrec.pair Primrec.fst heval)
  exact (hresult.of_eq fun _ => rfl).to_comp

/-- Uniform fixed-cap membership as a genuine computability predicate whose input is the pair
`(finite local machine code, word)`. -/
public theorem boundedSliceMembership_computablePred
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    [Primcodable Terminal]
    (bound : Nat) :
    ComputablePred (fun input :
        Code (Terminal := Terminal) (Work := Work) (State := State) × List Terminal =>
      input.2 ∈ LanguageWithBound input.1.toMachine bound) := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun input => boundedSliceMembershipBool input.1 bound input.2,
    boundedSliceMembershipBool_computable bound, ?_⟩
  funext input
  apply propext
  exact (boundedSliceMembershipBool_eq_true_iff input.1 bound input.2).symm

/-- The fixed finite-code semantics has uniformly semidecidable membership as a direct
corollary of the stronger joint decision theorem. -/
public theorem boundedSliceLanguageOf_membershipSemiDecidable
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    [Primcodable Terminal]
    (bound : Nat) :
    MembershipSemiDecidable
      (boundedSliceLanguageOf (Terminal := Terminal) (Work := Work) (State := State) bound) :=
  (boundedSliceMembership_computablePred bound).to_re

/-- `boundedSliceLanguageOf` characterizes its fixed-signature, fixed-cap range exactly. -/
public theorem boundedSliceLanguageOf_characterizes
    {Terminal Work State : Type}
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    (bound : Nat) :
    Characterizes
      (FixedSignatureBoundedSliceClass
        (Terminal := Terminal) (Work := Work) (State := State) bound)
      (boundedSliceLanguageOf
        (Terminal := Terminal) (Work := Work) (State := State) bound) := by
  intro language
  rfl

/-- Genuine `ComputableMembership` package for finite local machine codes at a fixed signature
and crossing cap.  Both the code and word are inputs to the one decision procedure. -/
public theorem fixedSignatureBoundedSlice_computableMembership
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    [DecidableEq Terminal] [DecidableEq Work] [DecidableEq State]
    [Primcodable Terminal]
    (bound : Nat) :
    ComputableMembership
      (FixedSignatureBoundedSliceClass
        (Terminal := Terminal) (Work := Work) (State := State) bound)
      (boundedSliceLanguageOf
        (Terminal := Terminal) (Work := Work) (State := State) bound) := by
  refine ⟨(boundedSliceLanguageOf_characterizes bound).onTrue,
    boundedSliceLanguageOf_membershipSemiDecidable bound, ?_⟩
  exact ComputablePredOnPromise.ofComputablePred
    (boundedSliceMembership_computablePred bound)

end LBA.BoundedCrossing.EncodedMembership

end
