import Mathlib.Computability.DFA
import Langlib.Classes.DeterministicContextFree.Totalization.EpsilonPhase
import Langlib.Classes.DeterministicContextFree.Totalization.Saturation

/-! # Regular Epsilon Analysis for DPDA Totalization

The totalizer needs finite, stack-regular lookahead for two semantic questions:

* Does the forced epsilon phase from `(q, γ)` reach a stable configuration?
* If the input is already exhausted at `(q, γ)`, does the epsilon closure encounter
  an accepting state?

This file packages the finite analysis data.  The remaining existence theorem is
provided by the pushdown-system saturation construction: every finite DPDA has
such an analysis.
-/

open PDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A finite regular analysis of the epsilon-only behavior of a DPDA. -/
structure RegularEpsilonAnalysis (M : DPDA Q T S) where
  StopState : Q → Type
  stopDecidableEq : ∀ q, DecidableEq (StopState q)
  stopFintype : ∀ q, Fintype (StopState q)
  stopDFA : ∀ q, DFA S (StopState q)
  stop_correct :
    ∀ q γ, (stopDFA q).evalFrom (stopDFA q).start γ ∈ (stopDFA q).accept ↔
      ∃ c', M.EpsilonStopsAt (q, γ) c'
  AcceptState : Q → Type
  acceptDecidableEq : ∀ q, DecidableEq (AcceptState q)
  acceptFintype : ∀ q, Fintype (AcceptState q)
  acceptDFA : ∀ q, DFA S (AcceptState q)
  accept_correct :
    ∀ q γ, (acceptDFA q).evalFrom (acceptDFA q).start γ ∈ (acceptDFA q).accept ↔
      ∃ q' γ', M.EpsilonReaches (q, γ) (q', γ') ∧ q' ∈ M.final_states

attribute [instance] RegularEpsilonAnalysis.stopFintype
attribute [instance] RegularEpsilonAnalysis.stopDecidableEq
attribute [instance] RegularEpsilonAnalysis.acceptFintype
attribute [instance] RegularEpsilonAnalysis.acceptDecidableEq

/-- The semantic epsilon-analysis existence theorem needed by the finite totalizer. -/
def HasRegularEpsilonAnalysis (M : DPDA Q T S) : Prop :=
  Nonempty M.RegularEpsilonAnalysis

noncomputable section

/-- The saturation construction supplies the finite regular epsilon analysis used
by the totalizer.  For each control state `q`, the DFA state is the current set of
P-automaton states reachable after reading the stack prefix. -/
def regularEpsilonAnalysisOfSaturation (M : DPDA Q T S) :
    M.RegularEpsilonAnalysis where
  StopState := fun _ => Set (PAutState Q)
  stopDecidableEq := fun _ => by
    classical
    infer_instance
  stopFintype := fun _ => by
    classical
    infer_instance
  stopDFA := fun q => stopSaturationDFA M q
  stop_correct := by
    intro q γ
    exact stopSaturationDFA_correct M q γ
  AcceptState := fun _ => Set (PAutState Q)
  acceptDecidableEq := fun _ => by
    classical
    infer_instance
  acceptFintype := fun _ => by
    classical
    infer_instance
  acceptDFA := fun q => finalSaturationDFA M q
  accept_correct := by
    intro q γ
    exact finalSaturationDFA_correct M q γ

/-- Every finite DPDA has a regular epsilon analysis. -/
theorem hasRegularEpsilonAnalysis (M : DPDA Q T S) :
    M.HasRegularEpsilonAnalysis :=
  ⟨regularEpsilonAnalysisOfSaturation M⟩

end

end DPDA
