module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.Construction
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.EnumerationScannerCorrectness
import Mathlib.Tactic

@[expose]
public section

/-!
# Correctness interface for integrated complement-protocol steps

The complete protocol verifier is a tagged sum of small synchronous scanners.  This
module hides that dispatch: a row transition whose certificate repeats one action is
reduced to the corresponding scanner, then to its declarative list-level specification.
-/

open Classical

namespace CertifiedRowSystem
namespace Complement

variable {I A Q F : Type*}

/-- Acceptance of one fixed, replicated protocol action by the integrated row verifier. -/
public def ProtocolActionAccepts
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (action : ProtocolAction)
    (old new : ProtocolRow A) : Prop :=
  ∃ out,
    (deterministicComplementSystem D).evalStep .start old new
        (List.replicate old.length action) = some out ∧
      protocolStepDone D out = true

private theorem exists_map_accept_iff
    (value : Option α) (tag : α → β) (doneα : α → Bool) (doneβ : β → Bool)
    (hdone : ∀ q, doneβ (tag q) = doneα q) :
    (∃ out, value.map tag = some out ∧ doneβ out = true) ↔
      ∃ q, value = some q ∧ doneα q = true := by
  constructor
  · rintro ⟨out, hout, haccept⟩
    rw [Option.map_eq_some_iff] at hout
    obtain ⟨q, hq, rfl⟩ := hout
    refine ⟨q, hq, ?_⟩
    rw [← hdone q]
    exact haccept
  · rintro ⟨q, hq, haccept⟩
    refine ⟨tag q, by simp [hq], ?_⟩
    rw [hdone q]
    exact haccept

/-! ## Arbitrary-certificate normalization -/

/-- The action selected by a live tagged verifier state. -/
public def ProtocolVerifier.selectedAction : ProtocolVerifier Q F → Option ProtocolAction
  | .boot _ => some .boot
  | .enumeration ⟨mode, acc⟩ =>
      if mode = .scan then some acc.action else none
  | .startPath finalScan _ => some (if finalScan then .finalStartPath else .startPath)
  | .pathStep finalScan _ => some (if finalScan then .finalPathStep else .pathStep)
  | .finishWitness _ => some .finishWitness
  | .finalWitness _ => some .finalFinishWitness
  | _ => none

/-- Dead verifier states are precisely the three absorbing rejecting states. -/
public def ProtocolVerifier.Live : ProtocolVerifier Q F → Prop
  | .bad => False
  | .boot .bad => False
  | .enumeration ⟨.bad, _⟩ => False
  | _ => True

private theorem scanEnumerationCell_action
    [Fintype A] [Nonempty A] [DecidableEq A]
    (acc : EnumerationAccumulator) (old new : ProtocolCell A) :
    (scanEnumerationCell acc old new).action = acc.action := by
  rcases acc with ⟨action, overflow, found, vertexSucc, countSucc, comparison, ok⟩
  cases action <;> rfl

private theorem enumerationStepCell_start_mode
    [Fintype A] [Nonempty A] [DecidableEq A]
    (old new : ProtocolCell A) (action : ProtocolAction) :
    (enumerationStepCell enumerationStart old new action).mode = .scan := by
  rfl

private theorem enumerationStepCell_start_action
    [Fintype A] [Nonempty A] [DecidableEq A]
    (old new : ProtocolCell A) (action : ProtocolAction) :
    (enumerationStepCell enumerationStart old new action).acc.action = action := by
  change (scanEnumerationCell (startEnumerationAccumulator action old new) old new).action = action
  exact (scanEnumerationCell_action _ _ _).trans rfl

private theorem selectedAction_startEnumeration
    [Fintype A] [Nonempty A] [DecidableEq A]
    (old new : ProtocolCell A) (action : ProtocolAction) :
    (ProtocolVerifier.enumeration
      (enumerationStepCell enumerationStart old new action) : ProtocolVerifier Q F).selectedAction =
        some action := by
  rw [ProtocolVerifier.selectedAction,
    if_pos (enumerationStepCell_start_mode old new action)]
  exact congrArg some (enumerationStepCell_start_action old new action)

private theorem protocolStepDone_implies_live
    (D : CertifiedRowSystem I A Unit Q F) (q : ProtocolVerifier Q F)
    (h : protocolStepDone D q = true) : q.Live := by
  cases q with
  | start => simp [ProtocolVerifier.Live]
  | boot q =>
      cases q <;> simp [protocolStepDone, bootDone, ProtocolVerifier.Live] at h ⊢
  | enumeration q =>
      rcases q with ⟨mode, acc⟩
      cases mode <;> simp [protocolStepDone, enumerationDone,
        ProtocolVerifier.Live] at h ⊢
  | startPath finalScan q => simp [ProtocolVerifier.Live]
  | pathStep finalScan q => simp [ProtocolVerifier.Live]
  | finishWitness q => simp [ProtocolVerifier.Live]
  | finalWitness q => simp [ProtocolVerifier.Live]
  | bad => simp [protocolStepDone] at h

private theorem evalProtocol_absorbing
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (q out : ProtocolVerifier Q F)
    (hstep : ∀ old new action, protocolStepCell D q old new action = q)
    (old new : ProtocolRow A) (actions : List ProtocolAction)
    (heval : (deterministicComplementSystem D).evalStep q old new actions = some out) :
    out = q := by
  induction old generalizing new actions with
  | nil =>
      cases new <;> cases actions <;>
        simp [CertifiedRowSystem.evalStep] at heval
      exact heval.symm
  | cons old olds ih =>
      cases new with
      | nil => cases actions <;> simp [CertifiedRowSystem.evalStep] at heval
      | cons new news =>
          cases actions with
          | nil => simp [CertifiedRowSystem.evalStep] at heval
          | cons action actions =>
              simp only [CertifiedRowSystem.evalStep, deterministicComplementSystem] at heval
              rw [hstep] at heval
              exact ih _ _ heval

private theorem evalProtocol_live_of_accept
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (q out : ProtocolVerifier Q F)
    (old new : ProtocolRow A) (actions : List ProtocolAction)
    (heval : (deterministicComplementSystem D).evalStep q old new actions = some out)
    (hdone : protocolStepDone D out = true) : q.Live := by
  have houtLive := protocolStepDone_implies_live D out hdone
  cases q with
  | start => trivial
  | boot q =>
      cases q with
      | bad =>
          have hout : out = .boot .bad := evalProtocol_absorbing D (.boot .bad) out
            (by intros; rfl) old new actions heval
          subst out
          contradiction
      | _ => trivial
  | enumeration q =>
      rcases q with ⟨mode, acc⟩
      cases mode with
      | bad =>
          cases old with
          | nil =>
              cases new <;> cases actions <;>
                simp [CertifiedRowSystem.evalStep] at heval
              subst out
              contradiction
          | cons old olds =>
              cases new with
              | nil => cases actions <;> simp [CertifiedRowSystem.evalStep] at heval
              | cons new news =>
                  cases actions with
                  | nil => simp [CertifiedRowSystem.evalStep] at heval
                  | cons action actions =>
                      simp only [CertifiedRowSystem.evalStep,
                        deterministicComplementSystem, protocolStepCell,
                        enumerationStepCell] at heval
                      have hout : out = .enumeration enumerationBad :=
                        evalProtocol_absorbing D (.enumeration enumerationBad) out
                          (by intros; rfl) olds news actions heval
                      subst out
                      contradiction
      | _ => trivial
  | startPath finalScan q => trivial
  | pathStep finalScan q => trivial
  | finishWitness q => trivial
  | finalWitness q => trivial
  | bad =>
      have hout : out = .bad := evalProtocol_absorbing D .bad out
        (by intros; rfl) old new actions heval
      subst out
      contradiction

private theorem selectedAction_step_of_live
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (q : ProtocolVerifier Q F)
    (expected action : ProtocolAction) (old new : ProtocolCell A)
    (hselected : q.selectedAction = some expected)
    (hlive : (protocolStepCell D q old new action).Live) :
    action = expected ∧
      (protocolStepCell D q old new action).selectedAction = some expected := by
  cases q with
  | start => simp [ProtocolVerifier.selectedAction] at hselected
  | bad => simp [ProtocolVerifier.selectedAction] at hselected
  | boot q =>
      simp only [ProtocolVerifier.selectedAction, Option.some.injEq] at hselected
      subst expected
      cases q <;> cases action <;>
        simp [protocolStepCell, bootStepCell, ProtocolVerifier.Live,
          ProtocolVerifier.selectedAction] at hlive ⊢
  | enumeration q =>
      rcases q with ⟨mode, acc⟩
      cases mode with
      | start => simp [ProtocolVerifier.selectedAction] at hselected
      | bad => simp [ProtocolVerifier.selectedAction] at hselected
      | scan =>
          have hselected' : acc.action = expected := by
            simpa [ProtocolVerifier.selectedAction] using hselected
          subst expected
          by_cases ha : action = acc.action
          · subst action
            constructor
            · rfl
            · simp only [protocolStepCell, enumerationStepCell,
                ProtocolVerifier.selectedAction]
              have haction : (scanEnumerationCell acc old new).action = acc.action := by
                rcases acc with ⟨action, overflow, found, vertexSucc, countSucc,
                  comparison, ok⟩
                cases action <;> rfl
              exact congrArg some haction
          · simp [protocolStepCell, enumerationStepCell, ha,
              ProtocolVerifier.Live, enumerationBad] at hlive
  | startPath finalScan q =>
      cases finalScan <;> cases action <;>
        simp [ProtocolVerifier.selectedAction, protocolStepCell,
          ProtocolVerifier.Live] at hselected hlive ⊢
      all_goals exact hselected
  | pathStep finalScan q =>
      cases finalScan <;> cases action <;>
        simp [ProtocolVerifier.selectedAction, protocolStepCell,
          ProtocolVerifier.Live] at hselected hlive ⊢
      all_goals exact hselected
  | finishWitness q =>
      cases action <;>
        simp [ProtocolVerifier.selectedAction, protocolStepCell,
          ProtocolVerifier.Live] at hselected hlive ⊢
      all_goals exact hselected
  | finalWitness q =>
      cases action <;>
        simp [ProtocolVerifier.selectedAction, protocolStepCell,
          ProtocolVerifier.Live] at hselected hlive ⊢
      all_goals exact hselected

/-- Once an action has been selected, every certificate cell of an accepting run must
repeat it. -/
public theorem evalProtocol_actions_eq_replicate
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (q out : ProtocolVerifier Q F)
    (expected : ProtocolAction) (old new : ProtocolRow A) (actions : List ProtocolAction)
    (hselected : q.selectedAction = some expected)
    (heval : (deterministicComplementSystem D).evalStep q old new actions = some out)
    (hdone : protocolStepDone D out = true) :
    actions = List.replicate old.length expected := by
  induction old generalizing q out new actions with
  | nil =>
      cases new <;> cases actions <;>
        simp [CertifiedRowSystem.evalStep] at heval ⊢
  | cons old olds ih =>
      cases new with
      | nil => cases actions <;> simp [CertifiedRowSystem.evalStep] at heval
      | cons new news =>
          cases actions with
          | nil => simp [CertifiedRowSystem.evalStep] at heval
          | cons action actions =>
              simp only [CertifiedRowSystem.evalStep, deterministicComplementSystem] at heval
              have hlive := evalProtocol_live_of_accept D
                (protocolStepCell D q old new action) out olds news actions heval hdone
              obtain ⟨haction, hnext⟩ :=
                selectedAction_step_of_live D q expected action old new hselected hlive
              subst action
              rw [List.length_cons, List.replicate_succ]
              exact congrArg (List.cons expected)
                (ih _ _ _ _ hnext heval hdone)

private theorem selectedAction_startProtocolAction_of_live
    [Fintype A] [Nonempty A] [DecidableEq A]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolCell A)
    (action : ProtocolAction)
    (hlive : (startProtocolAction D old new action).Live) :
    (startProtocolAction D old new action).selectedAction = some action := by
  cases action with
  | boot => rfl
  | beginRound => exact selectedAction_startEnumeration old new .beginRound
  | beginFinal => simp [startProtocolAction, ProtocolVerifier.Live] at hlive
  | skipInner => exact selectedAction_startEnumeration old new .skipInner
  | startPath => rfl
  | pathStep => rfl
  | finishWitness => rfl
  | finishOuter => exact selectedAction_startEnumeration old new .finishOuter
  | finishRound => exact selectedAction_startEnumeration old new .finishRound
  | finalSkip => exact selectedAction_startEnumeration old new .finalSkip
  | finalStartPath => rfl
  | finalPathStep => rfl
  | finalFinishWitness => rfl
  | finalFinish => exact selectedAction_startEnumeration old new .finalFinish

/-- Every accepting arbitrary certificate is equivalent to repeating its first action.
This is the normalization bridge between `CertifiedRowSystem.RowStep` and the per-action
correctness interface. -/
public theorem deterministicComplementSystem_rowStep_iff_exists_action
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    (deterministicComplementSystem D).RowStep old new ↔
      ∃ action, ProtocolActionAccepts D action old new := by
  constructor
  · rintro ⟨cert, out, heval, hdone⟩
    have hlens := (deterministicComplementSystem D).evalStep_nil_iff heval
    cases old with
    | nil =>
        have hnew : new = [] := List.length_eq_zero_iff.mp (by simpa using hlens.1.symm)
        have hcert : cert = [] := List.length_eq_zero_iff.mp (by simpa using hlens.2.symm)
        subst new
        subst cert
        simp [CertifiedRowSystem.evalStep] at heval
        subst out
        change false = true at hdone
        contradiction
    | cons old olds =>
        cases new with
        | nil => simp at hlens
        | cons new news =>
            cases cert with
            | nil => simp at hlens
            | cons action actions =>
                simp only [CertifiedRowSystem.evalStep,
                  deterministicComplementSystem] at heval
                let firstState := startProtocolAction D old new action
                have heval' :
                    (deterministicComplementSystem D).evalStep firstState
                      olds news actions = some out := by
                  simpa [firstState, protocolStepCell] using heval
                have hlive := evalProtocol_live_of_accept D firstState out
                  olds news actions heval' hdone
                have hselected := selectedAction_startProtocolAction_of_live
                  D old new action hlive
                have hactions := evalProtocol_actions_eq_replicate D firstState out action
                  olds news actions hselected heval' hdone
                refine ⟨action, ?_⟩
                refine ⟨out, ?_, hdone⟩
                rw [List.length_cons, List.replicate_succ, ← hactions]
                simpa only [CertifiedRowSystem.evalStep,
                  deterministicComplementSystem, protocolStepCell] using heval'
  · rintro ⟨action, out, heval, hdone⟩
    exact ⟨List.replicate old.length action, out, heval, hdone⟩

/-! ## Dispatch simulations -/

/-- Once the boot scanner has been selected, the integrated verifier is its tagged map. -/
public theorem evalProtocol_from_boot
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (q : BootVerifier)
    (old new : ProtocolRow A) (actions : List ProtocolAction) :
    (deterministicComplementSystem D).evalStep (.boot q) old new actions =
      (evalBoot q old new actions).map .boot := by
  induction old generalizing q new actions with
  | nil => cases new <;> cases actions <;> rfl
  | cons old olds ih =>
      cases new with
      | nil => cases actions <;> rfl
      | cons new news =>
          cases actions with
          | nil => rfl
          | cons action actions =>
              simp only [CertifiedRowSystem.evalStep, deterministicComplementSystem,
                protocolStepCell, evalBoot]
              exact ih _ _ _

/-- Once an enumeration scanner has been selected, the integrated verifier is its
tagged map. -/
public theorem evalProtocol_from_enumeration
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (q : EnumerationVerifier)
    (old new : ProtocolRow A) (actions : List ProtocolAction) :
    (deterministicComplementSystem D).evalStep (.enumeration q) old new actions =
      (evalEnumeration q old new actions).map .enumeration := by
  induction old generalizing q new actions with
  | nil => cases new <;> cases actions <;> rfl
  | cons old olds ih =>
      cases new with
      | nil => cases actions <;> rfl
      | cons new news =>
          cases actions with
          | nil => rfl
          | cons action actions =>
              simp only [CertifiedRowSystem.evalStep, deterministicComplementSystem,
                protocolStepCell, evalEnumeration]
              exact ih _ _ _

/-- A selected path-initialization scanner remains in its tagged summand when every
remaining certificate cell repeats its action. -/
public theorem evalProtocol_from_startPath
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (finalScan : Bool)
    (q : StartPathVerifier) (old new : ProtocolRow A) :
    (deterministicComplementSystem D).evalStep (.startPath finalScan q) old new
        (List.replicate old.length
          (if finalScan then .finalStartPath else .startPath)) =
      (evalStartPath
        (if finalScan then .finalChoose else .chooseInner)
        (if finalScan then .finalPath else .path) q old new).map
          (.startPath finalScan) := by
  cases finalScan <;>
    induction old generalizing q new with
    | nil => cases new <;> rfl
    | cons old olds ih =>
        cases new with
        | nil => rfl
        | cons new news =>
            simp only [List.length_cons, List.replicate_succ,
              CertifiedRowSystem.evalStep, deterministicComplementSystem,
              protocolStepCell, Bool.false_eq_true, ite_false, ite_true,
              evalStartPath]
            simpa using ih (q := startPathStepCell _ _ q old new) (new := news)

/-- A selected path-extension scanner remains in its tagged summand. -/
public theorem evalProtocol_from_pathStep
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (finalScan : Bool)
    (q : PathStepVerifier Q) (old new : ProtocolRow A) :
    (deterministicComplementSystem D).evalStep (.pathStep finalScan q) old new
        (List.replicate old.length
          (if finalScan then .finalPathStep else .pathStep)) =
      (evalPathStep D (if finalScan then .finalPath else .path) q old new).map
        (.pathStep finalScan) := by
  cases finalScan <;>
    induction old generalizing q new with
    | nil => cases new <;> rfl
    | cons old olds ih =>
        cases new with
        | nil => rfl
        | cons new news =>
            simp only [List.length_cons, List.replicate_succ,
              CertifiedRowSystem.evalStep, deterministicComplementSystem,
              protocolStepCell, Bool.false_eq_true, ite_false, ite_true,
              evalPathStep]
            simpa using ih (q := pathStepCell D _ q old new) (new := news)

/-- A selected counting-round witness-completion scanner remains tagged. -/
public theorem evalProtocol_from_finishWitness
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (q : FinishWitnessVerifier Q)
    (old new : ProtocolRow A) :
    (deterministicComplementSystem D).evalStep (.finishWitness q) old new
        (List.replicate old.length .finishWitness) =
      (evalFinishWitness D q old new).map .finishWitness := by
  induction old generalizing q new with
  | nil => cases new <;> rfl
  | cons old olds ih =>
      cases new with
      | nil => rfl
      | cons new news =>
          simp only [List.length_cons, List.replicate_succ,
            CertifiedRowSystem.evalStep, deterministicComplementSystem,
            protocolStepCell, evalFinishWitness, if_pos]
          exact ih _ _

/-- A selected final witness-completion scanner remains tagged. -/
public theorem evalProtocol_from_finalWitness
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (q : FinalWitnessVerifier F)
    (old new : ProtocolRow A) :
    (deterministicComplementSystem D).evalStep (.finalWitness q) old new
        (List.replicate old.length .finalFinishWitness) =
      (evalFinalWitness D q old new).map .finalWitness := by
  induction old generalizing q new with
  | nil => cases new <;> rfl
  | cons old olds ih =>
      cases new with
      | nil => rfl
      | cons new news =>
          simp only [List.length_cons, List.replicate_succ,
            CertifiedRowSystem.evalStep, deterministicComplementSystem,
            protocolStepCell, evalFinalWitness, if_pos]
          exact ih _ _

/-! ## Fixed path-action correctness -/

private theorem protocol_boot_eval_of_ne
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) (hne : old ≠ []) :
    (deterministicComplementSystem D).evalStep .start old new
        (List.replicate old.length .boot) =
      (evalBoot .start old new (List.replicate old.length .boot)).map .boot := by
  cases old with
  | nil => contradiction
  | cons old olds =>
      cases new with
      | nil => rfl
      | cons new news =>
          simp only [List.length_cons, List.replicate_succ,
            CertifiedRowSystem.evalStep, deterministicComplementSystem,
            protocolStepCell, startProtocolAction, evalBoot]
          simpa using evalProtocol_from_boot D
            (bootStepCell .start old new .boot) olds news
            (List.replicate olds.length .boot)

private theorem protocol_enumeration_eval_of_ne
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (action : ProtocolAction)
    (old new : ProtocolRow A) (hne : old ≠ [])
    (hroute : ∀ oldCell newCell,
      startProtocolAction D oldCell newCell action =
        .enumeration (enumerationStepCell enumerationStart oldCell newCell action)) :
    (deterministicComplementSystem D).evalStep .start old new
        (List.replicate old.length action) =
      (evalEnumeration enumerationStart old new
        (List.replicate old.length action)).map .enumeration := by
  cases old with
  | nil => contradiction
  | cons old olds =>
      cases new with
      | nil => rfl
      | cons new news =>
          simp only [List.length_cons, List.replicate_succ,
            CertifiedRowSystem.evalStep, deterministicComplementSystem,
            protocolStepCell, evalEnumeration]
          rw [hroute]
          simpa using evalProtocol_from_enumeration D
            (enumerationStepCell enumerationStart old new action) olds news
            (List.replicate olds.length action)

private theorem evalProtocolAction_enumeration_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (action : ProtocolAction)
    (old new : ProtocolRow A)
    (hroute : ∀ oldCell newCell,
      startProtocolAction D oldCell newCell action =
        .enumeration (enumerationStepCell enumerationStart oldCell newCell action)) :
    ProtocolActionAccepts D action old new ↔ EnumerationAccepts action old new := by
  by_cases hne : old = []
  · subst old
    cases new <;> simp [ProtocolActionAccepts, EnumerationAccepts,
      CertifiedRowSystem.evalStep, protocolStepDone, evalEnumeration,
      enumerationDone, enumerationStart]
  · rw [ProtocolActionAccepts,
      protocol_enumeration_eval_of_ne D action old new hne hroute]
    rw [exists_map_accept_iff _ _ enumerationDone (protocolStepDone D)
      (by intro q; rfl)]
    rfl

private theorem protocol_startPath_eval_of_ne
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (finalScan : Bool)
    (old new : ProtocolRow A) (hne : old ≠ []) :
    (deterministicComplementSystem D).evalStep .start old new
        (List.replicate old.length
          (if finalScan then .finalStartPath else .startPath)) =
      (evalStartPath
        (if finalScan then .finalChoose else .chooseInner)
        (if finalScan then .finalPath else .path) true old new).map
          (.startPath finalScan) := by
  cases old with
  | nil => contradiction
  | cons old olds =>
      cases new with
      | nil => rfl
      | cons new news =>
          cases finalScan <;>
            simp only [List.length_cons, List.replicate_succ,
              CertifiedRowSystem.evalStep, deterministicComplementSystem,
              evalStartPath, ite_true]
          · simpa using evalProtocol_from_startPath D false
              (startPathCell true old new) olds news
          · simpa using evalProtocol_from_startPath D true
              (finalStartPathCell true old new) olds news

private theorem protocol_pathStep_eval_of_ne
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (finalScan : Bool)
    (old new : ProtocolRow A) (hne : old ≠ []) :
    (deterministicComplementSystem D).evalStep .start old new
        (List.replicate old.length
          (if finalScan then .finalPathStep else .pathStep)) =
      (evalPathStep D (if finalScan then .finalPath else .path)
        (pathStepStart D) old new).map (.pathStep finalScan) := by
  cases old with
  | nil => contradiction
  | cons old olds =>
      cases new with
      | nil => rfl
      | cons new news =>
          cases finalScan <;>
            simp only [List.length_cons, List.replicate_succ,
              CertifiedRowSystem.evalStep, deterministicComplementSystem,
              evalPathStep, ite_true]
          · simpa using evalProtocol_from_pathStep D false
              (countingPathStepCell D (pathStepStart D) old new) olds news
          · simpa using evalProtocol_from_pathStep D true
              (finalPathStepCell D (pathStepStart D) old new) olds news

private theorem protocol_finishWitness_eval_of_ne
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) (hne : old ≠ []) :
    (deterministicComplementSystem D).evalStep .start old new
        (List.replicate old.length .finishWitness) =
      (evalFinishWitness D (finishWitnessStart D) old new).map .finishWitness := by
  cases old with
  | nil => contradiction
  | cons old olds =>
      cases new with
      | nil => rfl
      | cons new news =>
          simp only [List.length_cons, List.replicate_succ,
            CertifiedRowSystem.evalStep, deterministicComplementSystem,
            evalFinishWitness]
          simpa using evalProtocol_from_finishWitness D
            (finishWitnessCell D (finishWitnessStart D) old new) olds news

private theorem protocol_finalWitness_eval_of_ne
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) (hne : old ≠ []) :
    (deterministicComplementSystem D).evalStep .start old new
        (List.replicate old.length .finalFinishWitness) =
      (evalFinalWitness D (finalWitnessStart D) old new).map .finalWitness := by
  cases old with
  | nil => contradiction
  | cons old olds =>
      cases new with
      | nil => rfl
      | cons new news =>
          simp only [List.length_cons, List.replicate_succ,
            CertifiedRowSystem.evalStep, deterministicComplementSystem,
            evalFinalWitness]
          simpa using evalProtocol_from_finalWitness D
            (finalWitnessCell D (finalWitnessStart D) old new) olds news

/-- Integrated correctness of the initialization action. -/
public theorem evalProtocolAction_boot_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .boot old new ↔ IsBoot old new := by
  by_cases hne : old = []
  · subst old
    cases new <;> simp [ProtocolActionAccepts, CertifiedRowSystem.evalStep,
      protocolStepDone, IsBoot, evalBoot, bootDone]
  · rw [ProtocolActionAccepts, protocol_boot_eval_of_ne D old new hne]
    rw [exists_map_accept_iff _ _ bootDone (protocolStepDone D)
      (by intro q; rfl)]
    rfl

/-- `beginFinal` is intentionally not a primitive transition: the plateau branch of
`finishRound` enters the final scan. -/
public theorem evalProtocolAction_beginFinal_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .beginFinal old new ↔ False := by
  constructor
  · rintro ⟨out, heval, hdone⟩
    cases old with
    | nil =>
        cases new with
        | nil =>
            simp [CertifiedRowSystem.evalStep] at heval
            subst out
            simp [protocolStepDone] at hdone
        | cons new news => simp [CertifiedRowSystem.evalStep] at heval
    | cons old olds =>
        cases new with
        | nil => simp [CertifiedRowSystem.evalStep] at heval
        | cons new news =>
            simp only [List.length_cons, List.replicate_succ,
              CertifiedRowSystem.evalStep, deterministicComplementSystem,
              protocolStepCell, startProtocolAction] at heval
            exact evalProtocol_live_of_accept D .bad out olds news
              (List.replicate olds.length .beginFinal) heval hdone
  · intro h
    exact h.elim

/-- Integrated correctness of the transition entering an inner enumeration round. -/
public theorem evalProtocolAction_beginRound_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .beginRound old new ↔
      old ≠ [] ∧ BeginRoundSpec old new := by
  exact (evalProtocolAction_enumeration_iff D .beginRound old new
    (by intros; rfl)).trans (enumerationAccepts_beginRound_iff old new)

/-- Integrated correctness of one canonical inner-enumeration successor. -/
public theorem evalProtocolAction_skipInner_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .skipInner old new ↔
      old ≠ [] ∧ SkipInnerSpec old new := by
  exact (evalProtocolAction_enumeration_iff D .skipInner old new
    (by intros; rfl)).trans (enumerationAccepts_skipInner_iff old new)

/-- Integrated correctness of classifying and advancing one outer vertex. -/
public theorem evalProtocolAction_finishOuter_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .finishOuter old new ↔
      old ≠ [] ∧ FinishOuterSpec old new := by
  exact (evalProtocolAction_enumeration_iff D .finishOuter old new
    (by intros; rfl)).trans (enumerationAccepts_finishOuter_iff old new)

/-- Integrated correctness of the boundary between two counting rounds. -/
public theorem evalProtocolAction_finishRound_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .finishRound old new ↔
      old ≠ [] ∧ FinishRoundSpec old new := by
  exact (evalProtocolAction_enumeration_iff D .finishRound old new
    (by intros; rfl)).trans (enumerationAccepts_finishRound_iff old new)

/-- Integrated correctness of one canonical successor in the final scan. -/
public theorem evalProtocolAction_finalSkip_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .finalSkip old new ↔
      old ≠ [] ∧ FinalSkipSpec old new := by
  exact (evalProtocolAction_enumeration_iff D .finalSkip old new
    (by intros; rfl)).trans (enumerationAccepts_finalSkip_iff old new)

/-- Integrated correctness of the accepting final-enumeration transition. -/
public theorem evalProtocolAction_finalFinish_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .finalFinish old new ↔
      old ≠ [] ∧ FinalFinishSpec old new := by
  exact (evalProtocolAction_enumeration_iff D .finalFinish old new
    (by intros; rfl)).trans (enumerationAccepts_finalFinish_iff old new)

/-- Integrated correctness of the `startPath` action. -/
public theorem evalProtocolAction_startPath_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .startPath old new ↔
      old ≠ [] ∧ StartsPath .chooseInner .path old new := by
  by_cases hne : old = []
  · subst old
    cases new <;> simp [ProtocolActionAccepts, CertifiedRowSystem.evalStep,
      protocolStepDone, StartsPath]
  · rw [ProtocolActionAccepts, show
        (deterministicComplementSystem D).evalStep .start old new
            (List.replicate old.length .startPath) =
          (evalStartPath .chooseInner .path true old new).map (.startPath false) by
        simpa using protocol_startPath_eval_of_ne D false old new hne]
    rw [exists_map_accept_iff _ _ startPathDone (protocolStepDone D)
      (by intro q; rfl)]
    constructor
    · rintro ⟨q, hq, hdone⟩
      have hqtrue : q = true := by simpa [startPathDone] using hdone
      subst q
      exact ⟨hne, (evalStartPath_done_iff _ _ _ _).1 hq⟩
    · rintro ⟨_, hspec⟩
      exact ⟨true, (evalStartPath_done_iff _ _ _ _).2 hspec, rfl⟩

/-- Integrated correctness of the `finalStartPath` action. -/
public theorem evalProtocolAction_finalStartPath_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .finalStartPath old new ↔
      old ≠ [] ∧ StartsPath .finalChoose .finalPath old new := by
  by_cases hne : old = []
  · subst old
    cases new <;> simp [ProtocolActionAccepts, CertifiedRowSystem.evalStep,
      protocolStepDone, StartsPath]
  · rw [ProtocolActionAccepts, show
        (deterministicComplementSystem D).evalStep .start old new
            (List.replicate old.length .finalStartPath) =
          (evalStartPath .finalChoose .finalPath true old new).map (.startPath true) by
        simpa using protocol_startPath_eval_of_ne D true old new hne]
    rw [exists_map_accept_iff _ _ startPathDone (protocolStepDone D)
      (by intro q; rfl)]
    constructor
    · rintro ⟨q, hq, hdone⟩
      have hqtrue : q = true := by simpa [startPathDone] using hdone
      subst q
      exact ⟨hne, (evalStartPath_done_iff _ _ _ _).1 hq⟩
    · rintro ⟨_, hspec⟩
      exact ⟨true, (evalStartPath_done_iff _ _ _ _).2 hspec, rfl⟩

/-- Integrated correctness of `pathStep`. -/
public theorem evalProtocolAction_pathStep_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .pathStep old new ↔ IsPathStep D .path old new := by
  by_cases hne : old = []
  · subst old
    cases new with
    | nil => simp [ProtocolActionAccepts, CertifiedRowSystem.evalStep,
        protocolStepDone, IsPathStep, fuelTrack,
        RowNumeral.DigitCodec.evalSucc]
    | cons new news => simp [ProtocolActionAccepts, CertifiedRowSystem.evalStep,
        protocolStepDone, IsPathStep]
  · rw [ProtocolActionAccepts, show
        (deterministicComplementSystem D).evalStep .start old new
            (List.replicate old.length .pathStep) =
          (evalPathStep D .path (pathStepStart D) old new).map (.pathStep false) by
        simpa using protocol_pathStep_eval_of_ne D false old new hne]
    rw [exists_map_accept_iff _ _ (pathStepDone D) (protocolStepDone D)
      (by intro q; rfl)]
    exact evalPathStep_done_iff D .path old new

/-- Integrated correctness of `finalPathStep`. -/
public theorem evalProtocolAction_finalPathStep_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .finalPathStep old new ↔
      IsPathStep D .finalPath old new := by
  by_cases hne : old = []
  · subst old
    cases new with
    | nil => simp [ProtocolActionAccepts, CertifiedRowSystem.evalStep,
        protocolStepDone, IsPathStep, fuelTrack,
        RowNumeral.DigitCodec.evalSucc]
    | cons new news => simp [ProtocolActionAccepts, CertifiedRowSystem.evalStep,
        protocolStepDone, IsPathStep]
  · rw [ProtocolActionAccepts, show
        (deterministicComplementSystem D).evalStep .start old new
            (List.replicate old.length .finalPathStep) =
          (evalPathStep D .finalPath (pathStepStart D) old new).map (.pathStep true) by
        simpa using protocol_pathStep_eval_of_ne D true old new hne]
    rw [exists_map_accept_iff _ _ (pathStepDone D) (protocolStepDone D)
      (by intro q; rfl)]
    exact evalPathStep_done_iff D .finalPath old new

/-- Integrated correctness of `finishWitness`. -/
public theorem evalProtocolAction_finishWitness_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .finishWitness old new ↔ IsFinishWitness D old new := by
  by_cases hne : old = []
  · subst old
    cases new <;> simp [ProtocolActionAccepts, CertifiedRowSystem.evalStep,
      protocolStepDone, IsFinishWitness, scanBits]
  · rw [ProtocolActionAccepts, protocol_finishWitness_eval_of_ne D old new hne]
    rw [exists_map_accept_iff _ _ (finishWitnessDone D) (protocolStepDone D)
      (by intro q; rfl)]
    exact evalFinishWitness_done_iff D old new

/-- Integrated correctness of `finalFinishWitness`. -/
public theorem evalProtocolAction_finalFinishWitness_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    ProtocolActionAccepts D .finalFinishWitness old new ↔ IsFinalWitness D old new := by
  by_cases hne : old = []
  · subst old
    cases new <;> simp [ProtocolActionAccepts, CertifiedRowSystem.evalStep,
      protocolStepDone, IsFinalWitness, scanPhases]
  · rw [ProtocolActionAccepts, protocol_finalWitness_eval_of_ne D old new hne]
    rw [exists_map_accept_iff _ _ (finalWitnessDone D) (protocolStepDone D)
      (by intro q; rfl)]
    exact evalFinalWitness_done_iff D old new

private theorem protocolActionAccepts_old_ne_nil
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (action : ProtocolAction)
    (old new : ProtocolRow A) (h : ProtocolActionAccepts D action old new) :
    old ≠ [] := by
  intro hold
  subst old
  rcases h with ⟨out, heval, hdone⟩
  cases new with
  | nil =>
      simp [CertifiedRowSystem.evalStep] at heval
      subst out
      simp [protocolStepDone] at hdone
  | cons new news => simp [CertifiedRowSystem.evalStep] at heval

/-- The compiled row checker accepts exactly the declarative protocol transition
relation.  In particular, this theorem covers arbitrary action certificates, not only
certificates that were assumed in advance to repeat one action. -/
public theorem deterministicComplementSystem_rowStep_iff
    [Fintype A] [Nonempty A] [DecidableEq A] [Fintype Q] [Fintype F]
    (D : CertifiedRowSystem I A Unit Q F) (old new : ProtocolRow A) :
    (deterministicComplementSystem D).RowStep old new ↔ ProtocolStep D old new := by
  rw [deterministicComplementSystem_rowStep_iff_exists_action]
  constructor
  · rintro ⟨action, haction⟩
    have hne := protocolActionAccepts_old_ne_nil D action old new haction
    refine ⟨hne, ?_⟩
    cases action <;> simp_all only [
      evalProtocolAction_boot_iff, evalProtocolAction_beginRound_iff,
      evalProtocolAction_beginFinal_iff, evalProtocolAction_skipInner_iff,
      evalProtocolAction_startPath_iff, evalProtocolAction_pathStep_iff,
      evalProtocolAction_finishWitness_iff, evalProtocolAction_finishOuter_iff,
      evalProtocolAction_finishRound_iff, evalProtocolAction_finalSkip_iff,
      evalProtocolAction_finalStartPath_iff, evalProtocolAction_finalPathStep_iff,
      evalProtocolAction_finalFinishWitness_iff, evalProtocolAction_finalFinish_iff,
      true_or, or_true]
  · rintro ⟨hne, hstep⟩
    rcases hstep with hboot | hbeginRound | hskipInner | hstartPath | hpathStep |
      hfinishWitness | hfinishOuter | hfinishRound | hfinalSkip | hfinalStartPath |
      hfinalPathStep | hfinalFinishWitness | hfinalFinish
    · exact ⟨.boot, (evalProtocolAction_boot_iff D old new).2 hboot⟩
    · exact ⟨.beginRound,
        (evalProtocolAction_beginRound_iff D old new).2 ⟨hne, hbeginRound⟩⟩
    · exact ⟨.skipInner,
        (evalProtocolAction_skipInner_iff D old new).2 ⟨hne, hskipInner⟩⟩
    · exact ⟨.startPath,
        (evalProtocolAction_startPath_iff D old new).2 ⟨hne, hstartPath⟩⟩
    · exact ⟨.pathStep, (evalProtocolAction_pathStep_iff D old new).2 hpathStep⟩
    · exact ⟨.finishWitness,
        (evalProtocolAction_finishWitness_iff D old new).2 hfinishWitness⟩
    · exact ⟨.finishOuter,
        (evalProtocolAction_finishOuter_iff D old new).2 ⟨hne, hfinishOuter⟩⟩
    · exact ⟨.finishRound,
        (evalProtocolAction_finishRound_iff D old new).2 ⟨hne, hfinishRound⟩⟩
    · exact ⟨.finalSkip,
        (evalProtocolAction_finalSkip_iff D old new).2 ⟨hne, hfinalSkip⟩⟩
    · exact ⟨.finalStartPath,
        (evalProtocolAction_finalStartPath_iff D old new).2 ⟨hne, hfinalStartPath⟩⟩
    · exact ⟨.finalPathStep,
        (evalProtocolAction_finalPathStep_iff D old new).2 hfinalPathStep⟩
    · exact ⟨.finalFinishWitness,
        (evalProtocolAction_finalFinishWitness_iff D old new).2 hfinalFinishWitness⟩
    · exact ⟨.finalFinish,
        (evalProtocolAction_finalFinish_iff D old new).2 ⟨hne, hfinalFinish⟩⟩

end Complement
end CertifiedRowSystem
