module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.CanonicalReflection

@[expose]
public section

/-!
# Language correctness of the marked Euler probe

This module composes the raw-protocol reflection theorem with the semantic
marked-Euler simulation theorem.  It is deliberately independent of the
degree and matching decomposition of the raw machine.

The result is stated for the repository's marker-free deterministic
presentation, including its explicit empty-word bit.  The compiled raw
machine itself uses the canonical endmarker presentation, so the empty input
is represented uniformly by the two-cell tape `left right`.
-/

namespace GraphWalking

open Relation

universe uTerminal uWork uState

namespace MarkedEulerProbe

noncomputable section

/-- Pointwise semantic correctness of the complete raw compiler.  A word is
accepted by the source marker-free deterministic machine (with its explicit
empty-word decision) exactly when the raw marked-Euler machine accepts its
canonical endmarker encoding. -/
public theorem sourceLanguage_iff_rawMachine_accepts_initCfgEnd
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) Q)
    (acceptEmpty : Bool) (word : List T) :
    DLBA.LanguageRecognized machine (fun input => some (Sum.inl input))
        acceptEmpty word <->
      let simulator :=
        EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty
      LBA.Accepts (rawMachine simulator)
        (LBA.initCfgEnd (rawMachine simulator) word) := by
  let simulator :=
    EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty
  have hsource := sourceLanguage_iff_markedSimulatorEuler
    machine acceptEmpty word
  have hraw :=
    rawMachine_accepts_initCfgEnd_iff_exists_eulerAccepting simulator word
  exact hsource.trans (by
    simpa [simulator, markedPorts, ports, GraphWalking.Machine.Accepting,
      BoundedTapeController.machine, markedMachine, forgetDirection] using
        hraw.symm)

/-- Language-level correctness of the complete raw compiler.  No lower bound
on any alphabet or state type is needed. -/
public theorem languageEnd_rawMachine_deterministicSimMachine_eq
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) Q)
    (acceptEmpty : Bool) :
    LBA.LanguageEnd
        (rawMachine
          (EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty)) =
      DLBA.LanguageRecognized machine (fun input => some (Sum.inl input))
        acceptEmpty := by
  funext word
  apply propext
  exact (sourceLanguage_iff_rawMachine_accepts_initCfgEnd
    machine acceptEmpty word).symm

/-- Explicit epsilon specialization.  This records that semantic correctness
does not rely on a nonempty-input side condition: the raw machine runs on the
two-cell canonical endmarker tape. -/
public theorem rawMachine_accepts_nil_iff_sourceLanguage
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) Q)
    (acceptEmpty : Bool) :
    LBA.Accepts
        (rawMachine
          (EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty))
        (LBA.initCfgEnd
          (rawMachine
            (EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty))
          ([] : List T)) <->
      DLBA.LanguageRecognized machine (fun input => some (Sum.inl input))
        acceptEmpty [] := by
  exact (sourceLanguage_iff_rawMachine_accepts_initCfgEnd
    machine acceptEmpty ([] : List T)).symm

end

end MarkedEulerProbe

end GraphWalking

end
