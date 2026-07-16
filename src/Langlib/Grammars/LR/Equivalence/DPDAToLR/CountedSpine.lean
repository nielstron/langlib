module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.RetainedFrameRun
public import Langlib.Grammars.LR.Equivalence.DPDAToLR.ZeroVisibleSpine

/-!
# Counted operational semantics of characteristic spines

The ordinary zipper invariant records reachability of every active grammar
node.  Return-interval arguments additionally need the exact position of the
node on a selected computation.  This file supplies that counted view and a
retained-frame realization of completed `single` nonterminals.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

private theorem reachesIn_trans_exact
    {P : PDA Q T S} {n m : ℕ} {a b c : PDA.conf P}
    (hab : P.ReachesIn n a b) (hbc : P.ReachesIn m b c) :
    P.ReachesIn (n + m) a c := by
  induction hbc with
  | refl => simpa using hab
  | @step m b middle c hprefix hlast ih =>
      simpa [Nat.add_assoc] using PDA.ReachesIn.step (ih hab) hlast

/-- A concrete operational spine carries a selected counted prefix run to
its exact physical cut. -/
public theorem ConcreteOperationalSpine.exists_prefixRunIn
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix preWord : List T} {context : List (StackSymbol M)}
    (h : ConcreteOperationalSpine M p A suffix preWord context) :
    ∃ n : ℕ,
      (emptyStackPDA M).ReachesIn n
        ⟨(emptyStackPDA M).initial_state, preWord,
          [(emptyStackPDA M).start_symbol]⟩
        ⟨spineCutState M A, [], spineCutStack M A context⟩ := by
  have hreach := (h.focusedExact M)
  cases hreach with
  | start => exact ⟨0, PDA.ReachesIn.refl _⟩
  | single q target Z preWord suffix context final prefixPath continuation =>
      rw [PDA.reaches_iff_reachesIn] at prefixPath
      obtain ⟨n, hn⟩ := prefixPath
      exact ⟨n, by simpa [spineCutState, spineCutStack] using hn⟩
  | list q target gamma preWord suffix context final prefixPath continuation =>
      rw [PDA.reaches_iff_reachesIn] at prefixPath
      obtain ⟨n, hn⟩ := prefixPath
      exact ⟨n, by simpa [spineCutState, spineCutStack] using hn⟩

/-- A terminal completion of a characteristic `single` is a selected
nonempty net-pop interval which retains any supplied outer stack frame. -/
public theorem completedSingle_exists_retainedFrameRun
    (M : DPDA Q T S)
    {q target : State M} {Z : StackSymbol M}
    {word : List T} {frame : List (StackSymbol M)}
    (hcomplete : (characteristicGrammar M).DerivesRightmost
      [symbol.nonterminal (PDA_to_CFG.N.single q Z target)]
      (word.map symbol.terminal)) :
    ∃ n : ℕ, 0 < n ∧
      PDA.RetainedFrameRun (emptyStackPDA M) frame n
        ⟨q, word, Z :: frame⟩ ⟨target, [], frame⟩ := by
  have hreach := reaches_of_characteristic_derives_single M hcomplete
  rw [PDA.reaches_iff_reachesIn] at hreach
  obtain ⟨n, hn⟩ := hreach
  have hretained := PDA.RetainedFrameRun.ofReachesIn
    (frame := frame) hn
  have hpos : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    subst n
    have heq := PDA.reachesIn_zero hn
    have hstack := congrArg PDA.conf.stack heq
    simp at hstack
  refine ⟨n, hpos, ?_⟩
  simpa [PDA.conf.appendStack, List.append_assoc] using hretained

/-- Concatenate a counted global prefix with a retained return interval. -/
public theorem prefixRunIn_trans_retainedFrameRun
    {P : PDA Q T S} {n m : ℕ} {root source target : PDA.conf P}
    {frame : List S}
    (hprefix : P.ReachesIn n root source)
    (hreturn : PDA.RetainedFrameRun P frame m source target) :
    P.ReachesIn (n + m) root target :=
  reachesIn_trans_exact hprefix hreturn.toReachesIn

end

end DPDA_to_LR
