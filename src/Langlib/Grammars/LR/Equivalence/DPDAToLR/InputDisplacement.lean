module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.GlobalCutComparison

/-!
# Comparing FS→ES cuts at displaced input positions

Visible characteristic prefixes may differ by a terminal block.  Lifting the
earlier global prefix path by that unconsumed block puts both operational cuts
under one global input.  This module packages the resulting comparisons,
including the phase split needed when one endpoint has already entered the
FS→ES drain.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Globally reachable simulation cuts are comparable even when they have
consumed different amounts of the common input. -/
public theorem emptyStack_global_simulation_cuts_comparable_any_input
    (M : DPDA Q T S)
    {w input₁ input₂ : List T} {q₁ q₂ : Q × Bool}
    {stack₁ stack₂ : List (Option S)}
    (h₁ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inl q₁, input₁, stack₁⟩)
    (h₂ : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inl q₂, input₂, stack₂⟩) :
    (emptyStackPDA M).Reaches
        ⟨Sum.inl q₁, input₁, stack₁⟩
        ⟨Sum.inl q₂, input₂, stack₂⟩ ∨
      (emptyStackPDA M).Reaches
        ⟨Sum.inl q₂, input₂, stack₂⟩
        ⟨Sum.inl q₁, input₁, stack₁⟩ := by
  obtain ⟨underStack₁, hstack₁, hnormalized₁⟩ :=
    emptyStack_reachable_simulation_shape M h₁
  obtain ⟨underStack₂, hstack₂, hnormalized₂⟩ :=
    emptyStack_reachable_simulation_shape M h₂
  subst stack₁
  subst stack₂
  rcases M.firstFinal.toPDA_reaches_comparable
      hnormalized₁ hnormalized₂ with h₁₂ | h₂₁
  · left
    simpa [emptyStackPDA, liftConf] using
      simulation_reaches M.firstFinal.toPDA _ _ h₁₂
  · right
    simpa [emptyStackPDA, liftConf] using
      simulation_reaches M.firstFinal.toPDA _ _ h₂₁

/-- A nonempty-input simulation cut must precede a globally reachable drain
cut at empty input.  In the normalized machine the opposite ordering would
have to grow empty input back into a nonempty word. -/
private theorem emptyStack_global_simulation_drain_of_nonempty_input
    (M : DPDA Q T S)
    {w simInput : List T} {q : Q × Bool}
    {simStack drainStack : List (Option S)}
    (hsimInput : simInput ≠ [])
    (hsimGlobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inl q, simInput, simStack⟩)
    (hdrainGlobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inr 1, [], drainStack⟩) :
    (emptyStackPDA M).Reaches
      ⟨Sum.inl q, simInput, simStack⟩
      ⟨Sum.inr 1, [], drainStack⟩ := by
  obtain ⟨gamma, hsimStack, hnormalizedSim⟩ :=
    emptyStack_reachable_simulation_shape M hsimGlobal
  obtain ⟨p, delta, entryStack, hp, hnormalizedFinal,
      hentry, htail⟩ :=
    emptyStack_global_drain_factorization M hdrainGlobal
  rcases M.firstFinal.toPDA_reaches_comparable
      hnormalizedSim hnormalizedFinal with hsimFinal | hfinalSim
  · have hlift :=
      simulation_reaches M.firstFinal.toPDA _ _ hsimFinal
    have hsuffix : (emptyStackPDA M).Reaches
        (liftConf M.firstFinal.toPDA ⟨p, [], delta⟩)
        ⟨Sum.inr 1, [], drainStack⟩ :=
      (Relation.ReflTransGen.single hentry).trans htail
    subst simStack
    simpa [emptyStackPDA, liftConf] using hlift.trans hsuffix
  · obtain ⟨consumed, hconsumed⟩ := PDA.decreasing_input hfinalSim
    have hnil : simInput = [] :=
      (List.eq_nil_of_append_eq_nil hconsumed.symm).2
    exact False.elim (hsimInput hnil)

/-- A useful simulation cut precedes a useful drain cut even when the two
global prefixes expose different remaining inputs.  Drain usefulness forces
its input to be empty.  A nonempty simulation input orients the normalized
comparison by input monotonicity; the empty-input case is the existing
first-final comparison. -/
public theorem emptyStack_global_simulation_drain_useful_any_input
    (M : DPDA Q T S)
    {w simInput drainInput : List T} {q : Q × Bool}
    {simStack drainStack : List (Option S)}
    {final₁ final₂ : EState M}
    (hsimGlobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inl q, simInput, simStack⟩)
    (hdrainGlobal : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inr 1, drainInput, drainStack⟩)
    (hsimUseful : (emptyStackPDA M).Reaches
      ⟨Sum.inl q, simInput, simStack⟩ ⟨final₁, [], []⟩)
    (hdrainUseful : (emptyStackPDA M).Reaches
      ⟨Sum.inr 1, drainInput, drainStack⟩ ⟨final₂, [], []⟩) :
    (emptyStackPDA M).Reaches
      ⟨Sum.inl q, simInput, simStack⟩
      ⟨Sum.inr 1, drainInput, drainStack⟩ := by
  have hdrainInput : drainInput = [] := by
    have hsame := drain_reaches_input_eq M hdrainUseful
    simpa using hsame.symm
  subst drainInput
  by_cases hsimInput : simInput = []
  · subst simInput
    exact emptyStack_global_simulation_drain_useful M
      hsimGlobal hdrainGlobal hsimUseful hdrainUseful
  · exact emptyStack_global_simulation_drain_of_nonempty_input M
      hsimInput hsimGlobal hdrainGlobal

/-- A globally reachable boot configuration is the literal initial
configuration; the fresh boot state cannot be re-entered. -/
private theorem emptyStack_global_boot_eq_initial (M : DPDA Q T S)
    {w input : List T} {stack : List (Option S)}
    (h : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inr 0, input, stack⟩) :
    (⟨Sum.inr 0, input, stack⟩ : PDA.conf (emptyStackPDA M)) =
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩ := by
  have hinv := FSES_Inv_reaches M.firstFinal.toPDA w
    (⟨Sum.inr 0, w, [none]⟩ : PDA.conf (emptyStackPDA M))
    ⟨Sum.inr 0, input, stack⟩
    (FSES_Inv_init M.firstFinal.toPDA w)
    (by simpa [emptyStackPDA] using h)
  rcases hinv with hboot | hsim | hdrain
  · simpa [emptyStackPDA, PDA_FS_to_ES_pda] using hboot
  · rcases hsim with ⟨q, remaining, gamma, heq, hnormalized⟩
    have hstate := congrArg PDA.conf.state heq
    simp at hstate
  · simp at hdrain

/-- If two globally reached productive cuts are separated by a nonempty
terminal block, the earlier cut processes exactly that block to the later
cut.  The proof is phase-aware: simulation cuts use normalized determinism,
a later drain cut uses the oriented mixed comparison, and a boot endpoint is
inverted to the literal initial configuration. -/
public theorem emptyStack_global_productive_extension
    (M : DPDA Q T S)
    {u z sOne sTwo : List T}
    {qOne qTwo : EState M}
    {stackOne stackTwo : List (EStack M)}
    {finalOne finalTwo : EState M}
    (hz : z ≠ [])
    (hOne : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, u,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨qOne, [], stackOne⟩)
    (hTwo : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, u ++ z,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨qTwo, [], stackTwo⟩)
    (useOne : (emptyStackPDA M).Reaches
      ⟨qOne, sOne, stackOne⟩ ⟨finalOne, [], []⟩)
    (useTwo : (emptyStackPDA M).Reaches
      ⟨qTwo, sTwo, stackTwo⟩ ⟨finalTwo, [], []⟩)
    (hlook : sOne.take 1 = (z ++ sTwo).take 1) :
    (emptyStackPDA M).Reaches
      ⟨qOne, z, stackOne⟩ ⟨qTwo, [], stackTwo⟩ := by
  have hOneLift : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, u ++ z,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨qOne, z, stackOne⟩ := by
    simpa [PDA.conf.appendInput] using
      (PDA.unconsumed_input z).mp hOne
  cases qOne with
  | inl qOne =>
      cases qTwo with
      | inl qTwo =>
          rcases emptyStack_global_simulation_cuts_comparable_any_input M
              hOneLift hTwo with hforward | hbackward
          · exact hforward
          · obtain ⟨consumed, hconsumed⟩ :=
              PDA.decreasing_input hbackward
            have hzNil : z = [] :=
              (List.eq_nil_of_append_eq_nil hconsumed.symm).2
            exact False.elim (hz hzNil)
      | inr i =>
          rcases i with ⟨i, hi⟩
          have hi' : i = 0 ∨ i = 1 := by omega
          rcases hi' with rfl | rfl
          · have hboot := emptyStack_global_boot_eq_initial M
              (by simpa using hTwo)
            have hinput := congrArg PDA.conf.input hboot
            have huz : u ++ z = [] := by simpa using hinput.symm
            have hzNil := (List.append_eq_nil_iff.mp huz).2
            exact False.elim (hz hzNil)
          · exact emptyStack_global_simulation_drain_of_nonempty_input M
              hz hOneLift (by simpa using hTwo)
  | inr i =>
      rcases i with ⟨i, hi⟩
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · have hboot := emptyStack_global_boot_eq_initial M
          (by simpa using hOne)
        have hu : u = [] := by
          simpa using (congrArg PDA.conf.input hboot).symm
        have hstack : stackOne = [(emptyStackPDA M).start_symbol] := by
          simpa using congrArg PDA.conf.stack hboot
        subst u
        subst stackOne
        simpa using hTwo
      · have hsOne : sOne = [] := by
          have hsame := drain_reaches_input_eq M useOne
          simpa using hsame.symm
        subst sOne
        obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hz
        simp at hlook

end

end DPDA_to_LR
