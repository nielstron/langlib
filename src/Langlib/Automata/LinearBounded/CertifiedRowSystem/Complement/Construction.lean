module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.EnumerationScanners
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.PathActions
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

@[expose]
public section

/-!
# Certified-row complement protocol construction

This module implements the synchronous scanners and row actions of the
inductive-counting complement protocol.
-/

open Classical

namespace CertifiedRowSystem
namespace Complement

/-! ### Boot action -/

/-- State of the first, initialization scan. -/
public inductive BootVerifier where
  | start
  | scan (one : RowNumeral.OneState) (ok : Bool)
  | bad
  deriving DecidableEq, Repr

public noncomputable instance BootVerifier.instFintype : Fintype BootVerifier := by
  classical
  let encode : BootVerifier → Unit ⊕ (RowNumeral.OneState × Bool) ⊕ Unit
    | .start => .inl ()
    | .scan one ok => .inr (.inl (one, ok))
    | .bad => .inr (.inr ())
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp [encode] at h ⊢
    simp_all)

/-- Cell-local conditions of the boot transition, apart from the LSD-first `one` check
on the new `oldCount` track. -/
public noncomputable def bootLocalOK
    {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (old new : ProtocolCell A) : Bool :=
  decide (
    old.phase = .input ∧ new.phase = .roundStart ∧
    old.vertex.source = new.vertex.source ∧
    old.vertex.depth = (vertexCodec A).zero ∧
    new.vertex.depth = (vertexCodec A).zero ∧
    old.vertex.outer = (vertexCodec A).zero ∧
    new.vertex.outer = (vertexCodec A).zero ∧
    old.vertex.inner = (vertexCodec A).zero ∧
    new.vertex.inner = (vertexCodec A).zero ∧
    old.vertex.path = (vertexCodec A).zero ∧
    new.vertex.path = (vertexCodec A).zero ∧
    old.vertex.fuel = (vertexCodec A).zero ∧
    new.vertex.fuel = (vertexCodec A).zero ∧
    old.counter.oldCount = (countCodec A).zero ∧
    old.counter.newCount = (countCodec A).zero ∧
    new.counter.newCount = (countCodec A).zero ∧
    old.counter.seenCount = (countCodec A).zero ∧
    new.counter.seenCount = (countCodec A).zero ∧
    old.found = false ∧ new.found = false)

@[simp]
public theorem bootLocalOK_eq_true_iff
    {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    {old new : ProtocolCell A} :
    bootLocalOK old new = true ↔
      old.phase = .input ∧ new.phase = .roundStart ∧
      old.vertex.source = new.vertex.source ∧
      old.vertex.depth = (vertexCodec A).zero ∧
      new.vertex.depth = (vertexCodec A).zero ∧
      old.vertex.outer = (vertexCodec A).zero ∧
      new.vertex.outer = (vertexCodec A).zero ∧
      old.vertex.inner = (vertexCodec A).zero ∧
      new.vertex.inner = (vertexCodec A).zero ∧
      old.vertex.path = (vertexCodec A).zero ∧
      new.vertex.path = (vertexCodec A).zero ∧
      old.vertex.fuel = (vertexCodec A).zero ∧
      new.vertex.fuel = (vertexCodec A).zero ∧
      old.counter.oldCount = (countCodec A).zero ∧
      old.counter.newCount = (countCodec A).zero ∧
      new.counter.newCount = (countCodec A).zero ∧
      old.counter.seenCount = (countCodec A).zero ∧
      new.counter.seenCount = (countCodec A).zero ∧
      old.found = false ∧ new.found = false := by
  simp [bootLocalOK]

/-- One cell of the initialization scan.  The certificate must request `boot` in every
cell; `OneState.first` makes the first count digit one and every later digit zero. -/
public noncomputable def bootStepCell
    {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A] :
    BootVerifier → ProtocolCell A → ProtocolCell A → ProtocolAction → BootVerifier
  | .bad, _, _, _ => .bad
  | .start, old, new, .boot =>
      .scan
        ((countCodec A).oneStep (countRadix_gt_one A) .first new.counter.oldCount)
        (bootLocalOK old new)
  | .scan one ok, old, new, .boot =>
      .scan
        ((countCodec A).oneStep (countRadix_gt_one A) one new.counter.oldCount)
        (ok && bootLocalOK old new)
  | _, _, _, _ => .bad

/-- Successful terminal state of the initialization scan. -/
public def bootDone : BootVerifier → Bool
  | .scan .rest true => true
  | _ => false

/-- Run only the boot verifier across aligned rows. -/
public noncomputable def evalBoot
    {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A] :
    BootVerifier → ProtocolRow A → ProtocolRow A → List ProtocolAction →
      Option BootVerifier
  | q, [], [], [] => some q
  | q, old :: olds, new :: news, action :: actions =>
      evalBoot (bootStepCell q old new action) olds news actions
  | _, _, _, _ => none

/-- `evalBoot` is the ordinary certified-row evaluator for `bootStepCell`. -/
public theorem evalBoot_eq_evalStep
    {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (q : BootVerifier) (old new : ProtocolRow A) (actions : List ProtocolAction) :
    evalBoot q old new actions =
      CertifiedRowSystem.evalStep
        ({ inputCell := fun cell : ProtocolCell A => cell
           stepStart := BootVerifier.start
           stepCell := bootStepCell
           stepDone := bootDone
           finalStart := true
           finalCell := fun ok _ => ok
           finalDone := id } :
          CertifiedRowSystem (ProtocolCell A) (ProtocolCell A)
            ProtocolAction BootVerifier Bool)
        q old new actions := by
  induction old generalizing q new actions with
  | nil => cases new <;> cases actions <;> rfl
  | cons old olds ih =>
      cases new <;> cases actions <;> simp only [evalBoot, CertifiedRowSystem.evalStep]
      exact ih _ _ _

/-- A certified row system exposing the initialization action.  It is also the prefix
of the complete protocol system: subsequent actions extend `BootVerifier` with the
counting scanners while leaving this transition unchanged. -/
public noncomputable def bootSystem
    {I A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (sourceCell : I → A) :
    CertifiedRowSystem I (ProtocolCell A) ProtocolAction BootVerifier Bool where
  inputCell := inputProtocolCell sourceCell
  stepStart := .start
  stepCell := bootStepCell
  stepDone := bootDone
  finalStart := true
  finalCell ok cell := ok && decide (cell.phase = .roundStart)
  finalDone := id

/-! ## Integrated protocol system -/

/-- Finite verifier state of the complete protocol.  The outer constructor records which
small synchronous scanner was selected by the repeated action certificate. -/
public inductive ProtocolVerifier (Q F : Type*) where
  | start
  | boot (state : BootVerifier)
  | enumeration (state : EnumerationVerifier)
  | startPath (finalScan : Bool) (state : StartPathVerifier)
  | pathStep (finalScan : Bool) (state : PathStepVerifier Q)
  | finishWitness (state : FinishWitnessVerifier Q)
  | finalWitness (state : FinalWitnessVerifier F)
  | bad
  deriving DecidableEq

public noncomputable instance ProtocolVerifier.instFintype
    {Q F : Type*} [Fintype Q] [Fintype F] : Fintype (ProtocolVerifier Q F) := by
  classical
  let encode : ProtocolVerifier Q F →
      Unit ⊕ BootVerifier ⊕ EnumerationVerifier ⊕
        (Bool × StartPathVerifier) ⊕ (Bool × PathStepVerifier Q) ⊕
        FinishWitnessVerifier Q ⊕ FinalWitnessVerifier F ⊕ Unit
    | .start => .inl ()
    | .boot q => .inr (.inl q)
    | .enumeration q => .inr (.inr (.inl q))
    | .startPath finalScan q => .inr (.inr (.inr (.inl (finalScan, q))))
    | .pathStep finalScan q => .inr (.inr (.inr (.inr (.inl (finalScan, q)))))
    | .finishWitness q => .inr (.inr (.inr (.inr (.inr (.inl q)))))
    | .finalWitness q => .inr (.inr (.inr (.inr (.inr (.inr (.inl q))))))
    | .bad => .inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))
  exact Fintype.ofInjective encode (by
    intro x y h
    cases x <;> cases y <;> simp [encode] at h ⊢
    all_goals simp_all)

/-- Select and run the first cell of the scanner named by an action. -/
public noncomputable def startProtocolAction
    {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F)
    (old new : ProtocolCell A) : ProtocolAction → ProtocolVerifier Q F
  | .boot => .boot (bootStepCell .start old new .boot)
  | .beginRound =>
      .enumeration (enumerationStepCell enumerationStart old new .beginRound)
  | .skipInner =>
      .enumeration (enumerationStepCell enumerationStart old new .skipInner)
  | .finishOuter =>
      .enumeration (enumerationStepCell enumerationStart old new .finishOuter)
  | .finishRound =>
      .enumeration (enumerationStepCell enumerationStart old new .finishRound)
  | .finalSkip =>
      .enumeration (enumerationStepCell enumerationStart old new .finalSkip)
  | .finalFinish =>
      .enumeration (enumerationStepCell enumerationStart old new .finalFinish)
  | .startPath =>
      .startPath false (startPathCell true old new)
  | .finalStartPath =>
      .startPath true (finalStartPathCell true old new)
  | .pathStep =>
      .pathStep false (countingPathStepCell D (pathStepStart D) old new)
  | .finalPathStep =>
      .pathStep true (finalPathStepCell D (pathStepStart D) old new)
  | .finishWitness =>
      .finishWitness (finishWitnessCell D (finishWitnessStart D) old new)
  | .finalFinishWitness =>
      .finalWitness (finalWitnessCell D (finalWitnessStart D) old new)
  | .beginFinal => .bad

/-- One cell of the complete complement-protocol verifier. -/
public noncomputable def protocolStepCell
    {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) :
    ProtocolVerifier Q F → ProtocolCell A → ProtocolCell A →
      ProtocolAction → ProtocolVerifier Q F
  | .bad, _, _, _ => .bad
  | .start, old, new, action => startProtocolAction D old new action
  | .boot q, old, new, action => .boot (bootStepCell q old new action)
  | .enumeration q, old, new, action =>
      .enumeration (enumerationStepCell q old new action)
  | .startPath finalScan q, old, new, action =>
      if action = (if finalScan then .finalStartPath else .startPath) then
        .startPath finalScan
          (if finalScan then finalStartPathCell q old new else startPathCell q old new)
      else .bad
  | .pathStep finalScan q, old, new, action =>
      if action = (if finalScan then .finalPathStep else .pathStep) then
        .pathStep finalScan
          (if finalScan then finalPathStepCell D q old new
           else countingPathStepCell D q old new)
      else .bad
  | .finishWitness q, old, new, action =>
      if action = .finishWitness then
        .finishWitness (finishWitnessCell D q old new)
      else .bad
  | .finalWitness q, old, new, action =>
      if action = .finalFinishWitness then
        .finalWitness (finalWitnessCell D q old new)
      else .bad

/-- Terminal predicate of the integrated scanner. -/
public def protocolStepDone
    {I A Q F : Type*} (D : CertifiedRowSystem I A Unit Q F) :
    ProtocolVerifier Q F → Bool
  | .boot q => bootDone q
  | .enumeration q => enumerationDone q
  | .startPath _ q => startPathDone q
  | .pathStep _ q => pathStepDone D q
  | .finishWitness q => finishWitnessDone D q
  | .finalWitness q => finalWitnessDone D q
  | _ => false

/-- The full inductive-counting row system for a source system whose edge verifier is
deterministic (`Unit`-certified). -/
public noncomputable def deterministicComplementSystem
    {I A Q F : Type*}
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) :
    CertifiedRowSystem I (ProtocolCell A) ProtocolAction (ProtocolVerifier Q F) Bool where
  inputCell := inputProtocolCell D.inputCell
  stepStart := .start
  stepCell := protocolStepCell D
  stepDone := protocolStepDone D
  finalStart := true
  finalCell ok cell := ok && decide (cell.phase = .accept)
  finalDone := id

private theorem fold_accept_eq_true_iff
    {A : Type*} [Fintype A] (init : Bool) (row : ProtocolRow A) :
    row.foldl (fun ok cell ↦ ok && decide (cell.phase = .accept)) init = true ↔
      init = true ∧ HasPhase .accept row := by
  induction row generalizing init with
  | nil => simp [HasPhase]
  | cons cell row ih =>
      rw [List.foldl_cons, ih]
      simp only [Bool.and_eq_true, decide_eq_true_eq, HasPhase, List.mem_cons,
        forall_eq_or_imp]
      tauto

/-- A protocol row is final exactly when every cell carries the accepting phase. -/
@[simp]
public theorem final_deterministicComplementSystem_iff
    {I A Q F : Type*}
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (row : ProtocolRow A) :
    (deterministicComplementSystem D).Final row ↔ HasPhase .accept row := by
  change row.foldl (fun ok cell ↦ ok && decide (cell.phase = .accept)) true = true ↔ _
  simpa using fold_accept_eq_true_iff true row

/-- Machine-independent Immerman--Szelepcsényi construction for an arbitrary finite
certified row system.  The source edge verifier is determinized before the counting
protocol is installed. -/
public noncomputable def complementSystem
    {I A C Q F : Type*}
    [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype C] [Fintype Q] [DecidableEq Q] [Fintype F]
    (S : CertifiedRowSystem I A C Q F) :
    CertifiedRowSystem I (ProtocolCell A) ProtocolAction
      (ProtocolVerifier (Finset Q) F) Bool :=
  deterministicComplementSystem S.determinize

/-! ## Machine-independent protocol relation -/

/-- List-level initialization action implemented by the boot scanner. -/
public def IsBoot
    {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (old new : ProtocolRow A) : Prop :=
  ∃ out,
    evalBoot .start old new (List.replicate old.length .boot) = some out ∧
      bootDone out = true

private theorem evalBoot_initialized_rest
    {I A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (sourceCell : I → A) (input : List I) :
    evalBoot (.scan .rest true)
      (input.map (inputProtocolCell sourceCell))
      (input.map (initializedProtocolCell false ∘ sourceCell))
      (List.replicate input.length .boot) = some (.scan .rest true) := by
  induction input with
  | nil => rfl
  | cons input inputs ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ, evalBoot]
      have hlocal : bootLocalOK (inputProtocolCell sourceCell input)
          (initializedProtocolCell false (sourceCell input)) = true := by
        simp [bootLocalOK, inputProtocolCell, initializedProtocolCell]
      have hstep : bootStepCell (.scan .rest true)
          (inputProtocolCell sourceCell input)
          (initializedProtocolCell false (sourceCell input)) .boot =
          .scan .rest true := by
        rw [bootStepCell, hlocal]
        simp [RowNumeral.DigitCodec.oneStep, initializedProtocolCell]
      have hstep' : bootStepCell (.scan .rest true)
          (inputProtocolCell sourceCell input)
          ((initializedProtocolCell false ∘ sourceCell) input) .boot =
          .scan .rest true := by simpa using hstep
      rw [hstep']
      simpa [Function.comp_def] using ih

/-- Every nonempty input row performs the canonical boot action. -/
public theorem isBoot_input_initialized
    {I A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (sourceCell : I → A) {input : List I} (hne : input ≠ []) :
    IsBoot (input.map (inputProtocolCell sourceCell))
      (initializedProtocolRow (input.map sourceCell)) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨.scan .rest true, ?_, rfl⟩
  simp only [List.map_cons, initializedProtocolRow, List.length_cons,
    List.replicate_succ, evalBoot]
  have hlocal : bootLocalOK (inputProtocolCell sourceCell first)
      (initializedProtocolCell true (sourceCell first)) = true := by
    simp [bootLocalOK, inputProtocolCell, initializedProtocolCell]
  have hstep : bootStepCell .start
      (inputProtocolCell sourceCell first)
      (initializedProtocolCell true (sourceCell first)) .boot =
      .scan .rest true := by
    rw [bootStepCell, hlocal]
    simp [RowNumeral.DigitCodec.oneStep, initializedProtocolCell]
  rw [hstep]
  simpa [Function.comp_def] using evalBoot_initialized_rest sourceCell rest

/-- The union of all semantic actions in one complement-protocol step.

This relation is independent of the compiler to an LBA.  Its source parameter is already
deterministic, so both `D.RowStep` and its negation are certified synchronously. -/
public def ProtocolStep
    {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) : Prop :=
  old ≠ [] ∧ (
    IsBoot old new ∨
    BeginRoundSpec old new ∨
    SkipInnerSpec old new ∨
    StartsPath .chooseInner .path old new ∨
    IsPathStep D .path old new ∨
    IsFinishWitness D old new ∨
    FinishOuterSpec old new ∨
    FinishRoundSpec old new ∨
    FinalSkipSpec old new ∨
    StartsPath .finalChoose .finalPath old new ∨
    IsPathStep D .finalPath old new ∨
    IsFinalWitness D old new ∨
    FinalFinishSpec old new)


end Complement

end CertifiedRowSystem
