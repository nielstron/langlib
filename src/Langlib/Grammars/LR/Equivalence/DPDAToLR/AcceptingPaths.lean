module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.Construction

/-!
# Accepting paths of the normalized empty-stack PDA

The final-state-to-empty-stack conversion has a fresh boot state and a fresh
drain state.  A globally reachable configuration with empty input and empty
stack cannot still be the boot configuration or a simulated configuration:
both of those retain the fresh bottom-of-stack marker.  Consequently every
globally accepting path ends in the drain state.
-/

@[expose]
public section

open PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A globally reachable simulation state still has the fresh bottom marker,
and its prefix above that marker is the image of an actual normalized-DPDA
stack. -/
public theorem emptyStack_reachable_simulation_shape (M : DPDA Q T S)
    {w input : List T} {q : Q × Bool} {stack : List (Option S)}
    (h : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨Sum.inl q, input, stack⟩) :
    ∃ gamma : List S,
      stack = gamma.map some ++ [none] ∧
      M.firstFinal.toPDA.Reaches
        ⟨M.firstFinal.initial_state, w,
          [M.firstFinal.start_symbol]⟩
        ⟨q, input, gamma⟩ := by
  have hinv : FSES_Inv M.firstFinal.toPDA w
      (⟨Sum.inl q, input, stack⟩ : PDA.conf (emptyStackPDA M)) := by
    apply FSES_Inv_reaches M.firstFinal.toPDA w
      (⟨Sum.inr 0, w, [none]⟩ : PDA.conf (emptyStackPDA M))
      ⟨Sum.inl q, input, stack⟩
    · exact FSES_Inv_init M.firstFinal.toPDA w
    · simpa [emptyStackPDA] using h
  rcases hinv with hboot | hsim | hdrain
  · have hstate := congrArg PDA.conf.state hboot
    simp at hstate
  · rcases hsim with ⟨p, input', gamma, heq, hreach⟩
    cases heq
    exact ⟨gamma, rfl, hreach⟩
  · simp at hdrain

/-- Every empty-stack computation of the normalized machine, when started at
its global initial configuration, finishes in the distinguished drain state.
-/
public theorem emptyStack_accepting_state_eq_drain (M : DPDA Q T S)
    {w : List T} {q : (Q × Bool) ⊕ Fin 2}
    (h : (emptyStackPDA M).Reaches
      ⟨(emptyStackPDA M).initial_state, w,
        [(emptyStackPDA M).start_symbol]⟩
      ⟨q, [], []⟩) :
    q = Sum.inr 1 := by
  have hinv : FSES_Inv M.firstFinal.toPDA w
      (⟨q, [], []⟩ : PDA.conf (emptyStackPDA M)) := by
    apply FSES_Inv_reaches M.firstFinal.toPDA w
      (⟨Sum.inr 0, w, [none]⟩ : PDA.conf (emptyStackPDA M))
      ⟨q, [], []⟩
    · exact FSES_Inv_init M.firstFinal.toPDA w
    · simpa [emptyStackPDA] using h
  rcases hinv with hboot | hsim | hdrain
  · have hstack := congrArg PDA.conf.stack hboot
    simp at hstack
  · rcases hsim with ⟨p, input, stack, heq, _⟩
    have hstack := congrArg PDA.conf.stack heq
    simp at hstack
  · exact hdrain.1

end

end DPDA_to_LR
