module

public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.BootCorrectness
public import Langlib.Automata.LinearBounded.CertifiedRowSystem.Complement.ProtocolSemantics
import Mathlib.Tactic

@[expose]
public section

/-!
# Phase inversion for semantic protocol steps

Every declarative action fixes the replicated phase of its old row.  On a nonempty row
the phase is unique, so one `ProtocolStep` can be reduced to exactly the actions enabled
at the current control phase.
-/

namespace CertifiedRowSystem.Complement

variable {I A Q F : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

/-- Actions enabled at one protocol phase. -/
public def ActionsAtPhase (D : CertifiedRowSystem I A Unit Q F)
    (phase : ProtocolPhase) (old new : ProtocolRow A) : Prop :=
  match phase with
  | .input => IsBoot old new
  | .roundStart => BeginRoundSpec old new
  | .chooseInner => SkipInnerSpec old new ∨ StartsPath .chooseInner .path old new
  | .path => IsPathStep D .path old new ∨ IsFinishWitness D old new
  | .finishWitness => False
  | .finishOuter => FinishOuterSpec old new
  | .finishRound => FinishRoundSpec old new
  | .finalChoose => FinalSkipSpec old new ∨ StartsPath .finalChoose .finalPath old new
  | .finalPath => IsPathStep D .finalPath old new ∨ IsFinalWitness D old new
  | .finalWitness => False
  | .finalFinish => FinalFinishSpec old new
  | .accept => False

/-- A semantic transition out of a uniformly phased nonempty row uses exactly an action
enabled at that phase. -/
public theorem protocolStep_action_of_phase
    (D : CertifiedRowSystem I A Unit Q F) {phase : ProtocolPhase}
    {old new : ProtocolRow A} (hphase : HasPhase phase old)
    (hstep : ProtocolStep D old new) : ActionsAtPhase D phase old new := by
  rcases hstep with ⟨hne, hstep⟩
  rcases hstep with hboot | hbegin | hskip | hstart | hpath | hfinishWitness |
    hfinishOuter | hfinishRound | hfinalSkip | hfinalStart | hfinalPath |
    hfinalWitness | hfinalFinish
  · have heq := hasPhase_unique hne hphase (isBoot_phases_length hboot).1
    subst phase
    exact hboot
  · have heq := hasPhase_unique hne hphase hbegin.1
    subst phase
    exact hbegin
  · have heq := hasPhase_unique hne hphase hskip.1
    subst phase
    exact Or.inl hskip
  · have heq := hasPhase_unique hne hphase (StartsPath.spec hstart).2.1
    subst phase
    exact Or.inr hstart
  · have heq := hasPhase_unique hne hphase (IsPathStep.persistent_spec hpath).2.1
    subst phase
    exact Or.inl hpath
  · have heq := hasPhase_unique hne hphase (IsFinishWitness.persistent_spec hfinishWitness).2.1
    subst phase
    exact Or.inr hfinishWitness
  · have heq := hasPhase_unique hne hphase hfinishOuter.1
    subst phase
    exact hfinishOuter
  · have heq := hasPhase_unique hne hphase hfinishRound.1
    subst phase
    exact hfinishRound
  · have heq := hasPhase_unique hne hphase hfinalSkip.1
    subst phase
    exact Or.inl hfinalSkip
  · have heq := hasPhase_unique hne hphase (StartsPath.spec hfinalStart).2.1
    subst phase
    exact Or.inr hfinalStart
  · have heq := hasPhase_unique hne hphase
      (IsPathStep.persistent_spec hfinalPath).2.1
    subst phase
    exact Or.inl hfinalPath
  · have heq := hasPhase_unique hne hphase
      (IsFinalWitness.persistent_spec hfinalWitness).2.1
    subst phase
    exact Or.inr hfinalWitness
  · have heq := hasPhase_unique hne hphase hfinalFinish.1
    subst phase
    exact hfinalFinish

end CertifiedRowSystem.Complement
