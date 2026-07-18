module

public import Langlib.Automata.LinearBounded.BoundedCrossingVaryingEncodedMembership
import Mathlib.Tactic

@[expose]
public section

/-!
# Uniform encoded membership for ordinary linear-bounded automata

This module turns the varying-signature local table format from
`BoundedCrossingVaryingEncodedMembership` into an encoding of unrestricted LBAs.  The code and
the query word are both runtime inputs to one evaluator.  In particular, an ordinary code
contains only the work/state cardinalities, initial and accepting states, and a finite local
transition table.  It contains neither the query word, a crossing cap, nor a membership
procedure.

The evaluator reuses the bounded-crossing checker with a word-dependent cap equal to the number
of configurations on the canonical endmarker tape.  Loop erasure shows that every accepting run
has a simple accepting subrun below this cap, so this executable reduction is exact for ordinary
LBA acceptance.  It is an external decision procedure over finite configurations, not a
determinization of the encoded LBA and not a same-space `DLBA` construction.

All statements permit zero work symbols and impose no `Nonempty` or cardinality lower bound on
the terminal alphabet.  A zero state count is the total raw-code convention for the empty
language; a supplied semantic machine necessarily has a positive state count because it carries
an initial state.  Thus an empty terminal type is covered as well, with `epsilon` evaluated on
the ordinary two-cell endmarker tape.
-/

namespace LBA.EncodedMembership

universe u

variable {Terminal : Type u}

open LBA.BoundedCrossing
/-! ## Ordinary local codes and conversion to the bounded checker -/

/-- One primitive-codable local code for an unrestricted canonical-endmarker LBA.

The five fields are the work-symbol count, state count, initial-state index, accepting-state
indices, and local transition entries.  The transition-entry format is shared with the bounded
checker, but an ordinary code deliberately has no crossing-cap or query-word field. -/
public abbrev Code (Terminal : Type u) :=
  Nat × Nat × Nat × List Nat ×
    List (LBA.BoundedCrossing.VaryingEncodedMembership.TransitionEntry Terminal)

namespace Code

def workCount (code : Code Terminal) : Nat := code.1
def stateCount (code : Code Terminal) : Nat := code.2.1
def initialIndex (code : Code Terminal) : Nat := code.2.2.1
def accepting (code : Code Terminal) : List Nat := code.2.2.2.1
def transitions (code : Code Terminal) :
    List (LBA.BoundedCrossing.VaryingEncodedMembership.TransitionEntry Terminal) :=
  code.2.2.2.2

end Code

theorem code_workCount_primrec [Primcodable Terminal] :
    Primrec (Code.workCount : Code Terminal → Nat) :=
  Primrec.fst

theorem code_stateCount_primrec [Primcodable Terminal] :
    Primrec (Code.stateCount : Code Terminal → Nat) :=
  Primrec.fst.comp Primrec.snd

theorem code_initialIndex_primrec [Primcodable Terminal] :
    Primrec (Code.initialIndex : Code Terminal → Nat) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

theorem code_accepting_primrec [Primcodable Terminal] :
    Primrec (Code.accepting : Code Terminal → List Nat) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem code_transitions_primrec [Primcodable Terminal] :
    Primrec (Code.transitions : Code Terminal →
      List (LBA.BoundedCrossing.VaryingEncodedMembership.TransitionEntry Terminal)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

/-- Supply the auxiliary cap expected by the bounded-crossing checker.  This conversion uses
only the five raw local-code fields and the separately supplied natural number. -/
def withCrossingCap (code : Code Terminal) (crossingCap : Nat) :
    LBA.BoundedCrossing.VaryingEncodedMembership.Code Terminal :=
  (code.workCount, code.stateCount, code.initialIndex, crossingCap,
    code.accepting, code.transitions)

@[simp] theorem withCrossingCap_workCount (code : Code Terminal) (crossingCap : Nat) :
    (withCrossingCap code crossingCap).workCount = code.workCount := rfl

@[simp] theorem withCrossingCap_stateCount (code : Code Terminal) (crossingCap : Nat) :
    (withCrossingCap code crossingCap).stateCount = code.stateCount := rfl

@[simp] theorem withCrossingCap_initialIndex (code : Code Terminal) (crossingCap : Nat) :
    (withCrossingCap code crossingCap).initialIndex = code.initialIndex := rfl

@[simp] theorem withCrossingCap_crossingCap (code : Code Terminal) (crossingCap : Nat) :
    (withCrossingCap code crossingCap).crossingCap = crossingCap := rfl

@[simp] theorem withCrossingCap_accepting (code : Code Terminal) (crossingCap : Nat) :
    (withCrossingCap code crossingCap).accepting = code.accepting := rfl

@[simp] theorem withCrossingCap_transitions (code : Code Terminal) (crossingCap : Nat) :
    (withCrossingCap code crossingCap).transitions = code.transitions := rfl

/-- Erase the auxiliary cap from a bounded-checker code. -/
def eraseCrossingCap
    (code : LBA.BoundedCrossing.VaryingEncodedMembership.Code Terminal) :
    Code Terminal :=
  (code.workCount, code.stateCount, code.initialIndex, code.accepting, code.transitions)

@[simp] theorem eraseCrossingCap_withCrossingCap
    (code : Code Terminal) (crossingCap : Nat) :
    eraseCrossingCap (withCrossingCap code crossingCap) = code := by
  rcases code with ⟨workCount, stateCount, initialIndex, accepting, transitions⟩
  rfl

/-- At every supplied cap, the adapter embeds ordinary local codes injectively into bounded
codes. -/
theorem withCrossingCap_injective (crossingCap : Nat) :
    Function.Injective
      (fun code : Code Terminal ↦ withCrossingCap code crossingCap) := by
  intro left right heq
  simpa only [eraseCrossingCap_withCrossingCap] using
    congrArg eraseCrossingCap heq

theorem withCrossingCap_eraseCrossingCap
    (code : LBA.BoundedCrossing.VaryingEncodedMembership.Code Terminal) :
    withCrossingCap (eraseCrossingCap code) code.crossingCap = code := by
  rcases code with
    ⟨workCount, stateCount, initialIndex, crossingCap, accepting, transitions⟩
  rfl

/-- The finite machine denoted by a positive-state ordinary code.  The fixed zero supplied to
the bounded-code adapter is semantically inert: caps are not fields of `LBA.Machine`. -/
def toMachine (code : Code Terminal) (stateCountPositive : 0 < code.stateCount) :
    LBA.Machine (LBA.EndAlpha Terminal (Fin code.workCount)) (Fin code.stateCount) :=
  LBA.BoundedCrossing.VaryingEncodedMembership.toMachine
    (withCrossingCap code 0) (by simpa using stateCountPositive)

/-- Supplying any auxiliary cap changes no part of the denoted finite machine. -/
theorem toMachine_withCrossingCap (code : Code Terminal) (crossingCap : Nat)
    (hpos : 0 < code.stateCount) :
    LBA.BoundedCrossing.VaryingEncodedMembership.toMachine
        (withCrossingCap code crossingCap)
        (by simpa using hpos) =
      toMachine code hpos := by
  rcases code with ⟨workCount, stateCount, initialIndex, accepting, transitions⟩
  rfl

/-- The full number of configurations on the code's canonical endmarker tape for `word`.

The tape has `|word| + 2` cells and alphabet cardinality
`|Terminal| + workCount + 3`. -/
def fullTraceBudget [Fintype Terminal]
    (code : Code Terminal) (word : List Terminal) : Nat :=
  code.stateCount *
    (Fintype.card Terminal + code.workCount + 3) ^ (word.length + 2) *
    (word.length + 2)

/-- Total semantics of an ordinary varying-signature LBA code.  Zero states denotes the empty
language; positive state counts denote ordinary endmarker-LBA acceptance. -/
noncomputable def languageOf (code : Code Terminal) : Language Terminal :=
  if hpos : 0 < code.stateCount then
    LBA.LanguageEnd (toMachine code hpos)
  else
    fun _ => False

@[simp] theorem languageOf_of_stateCount_eq_zero (code : Code Terminal)
    (hzero : code.stateCount = 0) :
    languageOf code = (fun _ => False) := by
  simp [languageOf, hzero]

theorem languageOf_of_stateCount_pos (code : Code Terminal)
    (hpos : 0 < code.stateCount) :
    languageOf code = LBA.LanguageEnd (toMachine code hpos) := by
  simp only [languageOf, dif_pos hpos]

/-- The joint input supplied to the already-verified bounded evaluator.  Its cap is computed
from the ordinary local code and the query word rather than stored in either input. -/
def boundedInput [Fintype Terminal]
    (input : Code Terminal × List Terminal) :
    VaryingEncodedMembership.Code Terminal × List Terminal :=
  (withCrossingCap input.1 (fullTraceBudget input.1 input.2), input.2)

/-- One executable ordinary-membership test on the genuine joint runtime input. -/
def membershipInputBool [Fintype Terminal] [DecidableEq Terminal]
    (input : Code Terminal × List Terminal) : Bool :=
  VaryingEncodedMembership.membershipBool
    (boundedInput input).1 (boundedInput input).2

/-- Binary convenience interface for the joint ordinary-membership evaluator. -/
def membershipBool [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) : Bool :=
  membershipInputBool (code, word)

/-- The expanded full-trace budget is exactly the configuration-space cardinality of the
positive-state machine on the canonical endmarker tape. -/
theorem fullTraceBudget_eq_card_cfg [Fintype Terminal]
    (code : Code Terminal) (word : List Terminal) :
    fullTraceBudget code word =
      Fintype.card
        (DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
          (Fin code.stateCount) (word.length + 1)) := by
  simp only [fullTraceBudget, DLBA.card_cfg, Fintype.card_fin,
    VaryingEncodedMembership.card_endAlpha_fin]

/-- Ordinary acceptance is equivalent, word by word, to acceptance with the full finite-
configuration crossing cap. -/
theorem acceptsWithBound_fullTraceBudget_iff
    [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) (hpos : 0 < code.stateCount) :
    AcceptsWithBound (toMachine code hpos)
        (LBA.initCfgEnd (toMachine code hpos) word)
        (fullTraceBudget code word) ↔
      LBA.Accepts (toMachine code hpos)
        (LBA.initCfgEnd (toMachine code hpos) word) := by
  constructor
  · exact accepts_of_acceptsWithBound
  · intro haccept
    obtain ⟨target, trace, hfinal, _hsimple, hlength⟩ :=
      LBA.StepTrace.exists_simple_acceptingTrace_card_mul_pow_mul_of_accepts haccept
    refine ⟨target, trace, hfinal, ?_⟩
    intro boundary
    have hcross : trace.crossingCount boundary ≤ trace.length :=
      LBA.StepTrace.crossingCount_le_length boundary trace
    apply hcross.trans
    have hbudget : trace.length + 1 ≤ fullTraceBudget code word := by
      simpa only [fullTraceBudget, Fintype.card_fin,
        VaryingEncodedMembership.card_endAlpha_fin] using hlength
    omega

/-- Exact correctness of unrestricted encoded LBA membership. -/
public theorem membershipBool_eq_true_iff
    [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) :
    membershipBool code word = true ↔ word ∈ languageOf code := by
  by_cases hpos : 0 < code.stateCount
  · let capped := withCrossingCap code (fullTraceBudget code word)
    have hcappedPos : 0 < capped.stateCount := by simpa [capped] using hpos
    rw [membershipBool, membershipInputBool, boundedInput,
      VaryingEncodedMembership.membershipBool_eq_true_iff,
      VaryingEncodedMembership.languageOf_of_stateCount_pos capped hcappedPos,
      languageOf_of_stateCount_pos code hpos]
    change AcceptsWithBound
        (VaryingEncodedMembership.toMachine capped hcappedPos)
        (LBA.initCfgEnd
          (VaryingEncodedMembership.toMachine capped hcappedPos) word)
        capped.crossingCap ↔
      LBA.Accepts (toMachine code hpos)
        (LBA.initCfgEnd (toMachine code hpos) word)
    have hmachine :
        VaryingEncodedMembership.toMachine capped hcappedPos =
          toMachine code hpos := by
      simpa [capped] using
        (toMachine_withCrossingCap code (fullTraceBudget code word) hpos)
    rw [hmachine]
    change AcceptsWithBound (toMachine code hpos)
        (LBA.initCfgEnd (toMachine code hpos) word) (fullTraceBudget code word) ↔ _
    exact acceptsWithBound_fullTraceBudget_iff code word hpos
  · have hzero : code.stateCount = 0 := Nat.eq_zero_of_not_pos hpos
    rw [languageOf_of_stateCount_eq_zero code hzero]
    change membershipBool code word = true ↔ False
    rw [membershipBool, membershipInputBool, boundedInput,
      VaryingEncodedMembership.membershipBool_eq_true_iff]
    have hcappedZero :
        (withCrossingCap code (fullTraceBudget code word)).stateCount = 0 := by
      simpa using hzero
    rw [VaryingEncodedMembership.languageOf_of_stateCount_eq_zero _ hcappedZero]
    rfl

/-! ## Joint computability in the complete code and unbounded query word -/

theorem withCrossingCap_primrec [Primcodable Terminal] :
    Primrec fun input : Code Terminal × Nat =>
      withCrossingCap input.1 input.2 := by
  exact Primrec.pair
    ((code_workCount_primrec (Terminal := Terminal)).comp Primrec.fst)
    (Primrec.pair
      ((code_stateCount_primrec (Terminal := Terminal)).comp Primrec.fst)
      (Primrec.pair
        ((code_initialIndex_primrec (Terminal := Terminal)).comp Primrec.fst)
        (Primrec.pair Primrec.snd
          (Primrec.pair
            ((code_accepting_primrec (Terminal := Terminal)).comp Primrec.fst)
            ((code_transitions_primrec (Terminal := Terminal)).comp Primrec.fst)))))

theorem fullTraceBudget_primrec
    [Fintype Terminal] [Primcodable Terminal] :
    Primrec fun input : Code Terminal × List Terminal =>
      fullTraceBudget input.1 input.2 := by
  have hstates : Primrec fun input : Code Terminal × List Terminal =>
      input.1.stateCount :=
    (code_stateCount_primrec (Terminal := Terminal)).comp Primrec.fst
  have hwork : Primrec fun input : Code Terminal × List Terminal =>
      input.1.workCount :=
    (code_workCount_primrec (Terminal := Terminal)).comp Primrec.fst
  have hcells : Primrec fun input : Code Terminal × List Terminal =>
      input.2.length + 2 :=
    Primrec.nat_add.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2)
  have halphabet : Primrec fun input : Code Terminal × List Terminal =>
      Fintype.card Terminal + input.1.workCount + 3 :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const (Fintype.card Terminal)) hwork)
      (Primrec.const 3)
  have hpow : Primrec₂ (fun base exponent : Nat => base ^ exponent) :=
    Primrec₂.unpaired'.1 Nat.Primrec.pow
  unfold fullTraceBudget
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp hstates (hpow.comp halphabet hcells)) hcells

set_option maxHeartbeats 1000000 in
/-- Attaching the computed finite-configuration cap and retaining the query word is primitive
recursive jointly in the cap-free code and word. -/
theorem boundedInput_primrec
    [Fintype Terminal] [Primcodable Terminal] :
    Primrec (boundedInput : Code Terminal × List Terminal →
      VaryingEncodedMembership.Code Terminal × List Terminal) := by
  let Input := Code Terminal × List Terminal
  let CapInput := Code Terminal × Nat
  let capInputFn : Input → CapInput := fun input =>
    (input.1, fullTraceBudget input.1 input.2)
  have hcapInput : Primrec capInputFn := by
    exact Primrec.pair Primrec.fst fullTraceBudget_primrec
  have hcap := @Primrec.comp Input CapInput
    (VaryingEncodedMembership.Code Terminal)
    inferInstance inferInstance inferInstance
    (fun input => withCrossingCap input.1 input.2) capInputFn
    withCrossingCap_primrec hcapInput
  unfold boundedInput
  exact Primrec.pair hcap Primrec.snd

set_option maxHeartbeats 1000000 in
/-- The named joint evaluator is primitive recursive by direct composition with the varying
bounded evaluator. -/
theorem membershipInputBool_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec (membershipInputBool : Code Terminal × List Terminal → Bool) := by
  unfold membershipInputBool
  exact @Primrec.comp
    (Code Terminal × List Terminal)
    (VaryingEncodedMembership.Code Terminal × List Terminal) Bool
    inferInstance inferInstance inferInstance
    (fun input => VaryingEncodedMembership.membershipBool input.1 input.2)
    boundedInput VaryingEncodedMembership.membershipBool_primrec boundedInput_primrec

public theorem membershipBool_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec fun input : Code Terminal × List Terminal =>
      membershipBool input.1 input.2 := by
  exact membershipInputBool_primrec.of_eq (fun _ => rfl)

/-- The ordinary membership evaluator is computable jointly in the full local machine code and
the unbounded query word. -/
public theorem membershipBool_computable
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Computable fun input : Code Terminal × List Terminal =>
      membershipBool input.1 input.2 :=
  membershipBool_primrec.to_comp

/-- Exact joint decidability of ordinary LBA membership under the numeric local encoding. -/
public theorem membership_computablePred
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    ComputablePred fun input : Code Terminal × List Terminal =>
      input.2 ∈ languageOf input.1 := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun input => membershipBool input.1 input.2,
    membershipBool_computable, ?_⟩
  funext input
  apply propext
  exact (membershipBool_eq_true_iff input.1 input.2).symm

/-- Uniform semidecidability follows from the stronger joint decision theorem. -/
public theorem languageOf_membershipSemiDecidable
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    [Primcodable Terminal] :
    MembershipSemiDecidable (languageOf (Terminal := Terminal)) :=
  membership_computablePred.to_re

/-! ## Adequacy for the named LBA class -/

/-- Compile a machine over canonical finite signatures to the five-field ordinary code by
erasing the auxiliary zero cap from the bounded checker's exact local-table compiler. -/
noncomputable def codeOfFinMachine
    {Terminal : Type} [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount)) :
    Code Terminal :=
  eraseCrossingCap (VaryingEncodedMembership.codeOfFinMachine M 0)

@[simp] theorem codeOfFinMachine_stateCount
    {Terminal : Type} [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount)) :
    (codeOfFinMachine M).stateCount = stateCount := by
  simp [codeOfFinMachine, eraseCrossingCap, Code.stateCount]

theorem codeOfFinMachine_stateCount_pos
    {Terminal : Type} [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount)) :
    0 < (codeOfFinMachine M).stateCount := by
  rw [codeOfFinMachine_stateCount]
  exact Nat.zero_lt_of_lt M.initial.isLt

/-- Reattaching any cap to an ordinary compiled code gives exactly the bounded compiler at that
cap.  In particular, no stored cap survives in the ordinary encoding. -/
theorem withCrossingCap_codeOfFinMachine
    {Terminal : Type} [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (crossingCap : Nat) :
    withCrossingCap (codeOfFinMachine M) crossingCap =
      VaryingEncodedMembership.codeOfFinMachine M crossingCap := by
  classical
  simp [codeOfFinMachine, eraseCrossingCap, withCrossingCap,
    Code.workCount, Code.stateCount, Code.initialIndex,
    Code.accepting, Code.transitions,
    VaryingEncodedMembership.codeOfFinMachine,
    VaryingEncodedMembership.Code.workCount,
    VaryingEncodedMembership.Code.stateCount,
    VaryingEncodedMembership.Code.initialIndex,
    VaryingEncodedMembership.Code.accepting,
    VaryingEncodedMembership.Code.transitions]

/-- Compiling a canonical finite-signature machine and decoding it recovers exactly that
machine. -/
theorem toMachine_codeOfFinMachine
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount)) :
    toMachine (codeOfFinMachine M) (codeOfFinMachine_stateCount_pos M) = M := by
  unfold toMachine
  have hcode := withCrossingCap_codeOfFinMachine M 0
  cases hcode
  exact VaryingEncodedMembership.toMachine_codeOfFinMachine M 0

/-- Compile arbitrary finite work and state signatures by their canonical `Fin` transport.
This compiler is used only for adequacy; the runtime evaluator never invokes it. -/
noncomputable def codeOfFiniteMachine
    {Terminal : Type} [Fintype Terminal]
    {Work State : Type*} [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) : Code Terminal :=
  codeOfFinMachine M.finSignatureTransport

/-- Reattaching a runtime cap after compiling arbitrary finite signatures agrees exactly with
the bounded compiler supplied that cap from the outset. -/
theorem withCrossingCap_codeOfFiniteMachine
    {Terminal : Type} [Fintype Terminal]
    {Work State : Type*} [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (crossingCap : Nat) :
    withCrossingCap (codeOfFiniteMachine M) crossingCap =
      VaryingEncodedMembership.codeOfFiniteMachine M crossingCap := by
  exact withCrossingCap_codeOfFinMachine M.finSignatureTransport crossingCap

/-- The arbitrary-finite-signature compiler covers ordinary LBA semantics exactly. -/
public theorem languageOf_codeOfFiniteMachine
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    {Work State : Type*} [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) :
    languageOf (codeOfFiniteMachine M) = LBA.LanguageEnd M := by
  let normalized := M.finSignatureTransport
  have hpos : 0 < (codeOfFiniteMachine M).stateCount :=
    codeOfFinMachine_stateCount_pos normalized
  rw [languageOf_of_stateCount_pos _ hpos]
  change LBA.LanguageEnd
      (toMachine (codeOfFinMachine normalized) hpos) =
    LBA.LanguageEnd M
  rw [toMachine_codeOfFinMachine]
  exact LBA.BoundedCrossing.languageEnd_finSignatureTransport M

/-- Every total raw code denotes an LBA language.  The zero-state convention is witnessed by an
ordinary transition-free rejecting LBA; no inhabitance assumption on the terminal or work
alphabet is needed. -/
public theorem is_LBA_languageOf
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) : is_LBA (languageOf code) := by
  by_cases hpos : 0 < code.stateCount
  · refine ⟨Fin code.workCount, Fin code.stateCount, inferInstance, inferInstance,
      inferInstance, inferInstance, toMachine code hpos, ?_⟩
    exact (languageOf_of_stateCount_pos code hpos).symm
  · have hzero : code.stateCount = 0 := Nat.eq_zero_of_not_pos hpos
    let reject : LBA.Machine (LBA.EndAlpha Terminal (Fin 0)) (Fin 1) :=
      { transition := fun _ _ => ∅
        accept := fun _ => false
        initial := 0 }
    refine ⟨Fin 0, Fin 1, inferInstance, inferInstance, inferInstance, inferInstance,
      reject, ?_⟩
    rw [languageOf_of_stateCount_eq_zero code hzero]
    funext word
    apply propext
    constructor
    · rintro ⟨target, _hreach, hfinal⟩
      simp [reject] at hfinal
    · exact False.elim

/-- Every language in the canonical endmarker LBA class is represented by a numeric local code.
The noncomputable finite-type enumeration occurs only in this adequacy witness, never in the
membership evaluator. -/
public theorem exists_code_languageOf_eq_of_is_LBA
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    {language : Language Terminal} (hlanguage : is_LBA language) :
    ∃ code : Code Terminal, languageOf code = language := by
  obtain ⟨Work, State, workFinite, stateFinite, workEq, stateEq, M, hM⟩ := hlanguage
  letI : Fintype Work := workFinite
  letI : Fintype State := stateFinite
  letI : DecidableEq Work := workEq
  letI : DecidableEq State := stateEq
  refine ⟨codeOfFiniteMachine M, ?_⟩
  exact (languageOf_codeOfFiniteMachine M).trans hM

/-- The ordinary varying-signature numeric semantics characterizes exactly the repository's
named canonical endmarker `LBA` class. -/
public theorem languageOf_characterizes_LBA
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal] :
    Characterizes LBA (languageOf (Terminal := Terminal)) := by
  intro language
  constructor
  · exact exists_code_languageOf_eq_of_is_LBA
  · rintro ⟨code, rfl⟩
    exact is_LBA_languageOf code

/-- Headline encoded-membership theorem for unrestricted LBAs: one effective local code family
is adequate for exactly `LBA`, and one algorithm decides membership jointly from the complete
code and the unbounded query word. -/
public theorem LBA_computableMembership
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    [Primcodable Terminal] :
    ComputableMembership LBA (languageOf (Terminal := Terminal)) := by
  refine ⟨languageOf_characterizes_LBA.onTrue,
    languageOf_membershipSemiDecidable, ?_⟩
  exact ComputablePredOnPromise.ofComputablePred membership_computablePred

end LBA.EncodedMembership

end
