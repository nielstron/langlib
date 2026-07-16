module

public import Langlib.Grammars.LR.Equivalence.DPDAToLR.CountedSpine

/-!
# Counted traces of pending characteristic frontiers

A concrete characteristic spine records which grammar symbols have become
visible, but ordinary reachability forgets when that happened.  This module
keeps the two views together.  A trace starts with one fixed input word and
records, at every spine position, the already completed part and the still
unconsumed part of that word.

The visible constructors have their literal operational cost.  A `read`
consumes one terminal and appends that terminal to the pending frontier.  A
`splitRight` executes the selected positive retained-frame completion of its
left `single`, and appends the `single` marker only at the return endpoint.
`start`, `epsilon`, and `splitLeft` do not change the pending frontier.

The final section packages structural extension of a trace.  If such an
extension has the same pending frontier at both ends, its read and split-right
cases are impossible; the extension is therefore a counted zero-visible tail.
This is the ancestry statement needed before comparing independently selected
return intervals.
-/

@[expose]
public section

open Language PDA

namespace DPDA_to_LR

noncomputable section

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- All indices attached to one point of a pending-frontier execution. -/
@[ext]
public structure PendingFrontierPosition (M : DPDA Q T S) where
  frontier : List (symbol T (Nonterminal M))
  node : Nonterminal M
  suffix : List T
  consumed : List T
  context : List (StackSymbol M)
  remaining : List T

/-- The physical PDA configuration represented by a frontier position. -/
public def PendingFrontierPosition.cut (M : DPDA Q T S)
    (position : PendingFrontierPosition M) :
    PDA.conf (emptyStackPDA M) :=
  ⟨spineCutState M position.node, position.remaining,
    spineCutStack M position.node position.context⟩

/-- A normalized spine annotated by an exact counted computation on one
fixed whole input word.  The word consumed by a completed `single` is stored
on the `splitRight` constructor, together with its positive retained run. -/
public inductive PendingFrontierTrace (M : DPDA Q T S) (word : List T) :
    PendingFrontierPosition M → ℕ → Prop
  | root : PendingFrontierTrace M word
      ⟨[], PDA_to_CFG.N.start, [], [], [], word⟩ 0
  | start
      {target : State M}
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      PendingFrontierTrace M word
        ⟨[], PDA_to_CFG.N.list (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target, [], [], [], word⟩ 0
  | read
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed remaining : List T}
      {context : List (StackSymbol M)} {steps : ℕ}
      {q target next : State M} {a : T} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierTrace M word
        ⟨p, PDA_to_CFG.N.single q Z target, suffix, consumed,
          context, a :: remaining⟩ steps)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun q a Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      PendingFrontierTrace M word
        ⟨p ++ [symbol.terminal a],
          PDA_to_CFG.N.list next gamma target, suffix,
          consumed ++ [a], context, remaining⟩ (steps + 1)
  | epsilon
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed remaining : List T}
      {context : List (StackSymbol M)} {steps : ℕ}
      {q target next : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierTrace M word
        ⟨p, PDA_to_CFG.N.single q Z target, suffix, consumed,
          context, remaining⟩ steps)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun' q Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      PendingFrontierTrace M word
        ⟨p, PDA_to_CFG.N.list next gamma target, suffix, consumed,
          context, remaining⟩ (steps + 1)
  | splitLeft
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed z remaining : List T}
      {context : List (StackSymbol M)} {steps : ℕ}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierTrace M word
        ⟨p, PDA_to_CFG.N.list q (Z :: gamma) target, suffix,
          consumed, context, remaining⟩ steps)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hright : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal)) :
      PendingFrontierTrace M word
        ⟨p, PDA_to_CFG.N.single q Z middle, z ++ suffix, consumed,
          gamma ++ context, remaining⟩ steps
  | splitRight
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed leftWord remaining : List T}
      {context : List (StackSymbol M)} {steps returnSteps : ℕ}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierTrace M word
        ⟨p, PDA_to_CFG.N.list q (Z :: gamma) target, suffix,
          consumed, context, leftWord ++ remaining⟩ steps)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hleft : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)]
        (leftWord.map symbol.terminal))
      (hpositive : 0 < returnSteps)
      (hreturn : PDA.RetainedFrameRun (emptyStackPDA M)
        (gamma ++ context) returnSteps
        ⟨q, leftWord, Z :: (gamma ++ context)⟩
        ⟨middle, [], gamma ++ context⟩) :
      PendingFrontierTrace M word
        ⟨p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)],
          PDA_to_CFG.N.list middle gamma target, suffix,
          consumed ++ leftWord, context, remaining⟩
        (steps + returnSteps)

private theorem reachesIn_trans_exact
    {P : PDA Q T S} {n m : ℕ} {a b c : PDA.conf P}
    (hab : P.ReachesIn n a b) (hbc : P.ReachesIn m b c) :
    P.ReachesIn (n + m) a c := by
  induction hbc with
  | refl => simpa using hab
  | @step m b middle c hprefix hlast ih =>
      simpa [Nat.add_assoc] using PDA.ReachesIn.step (ih hab) hlast

/-- The completion word is always the consumed prefix followed by the input
still present at the represented cut. -/
public theorem PendingFrontierTrace.word_eq
    (M : DPDA Q T S) {word : List T}
    {position : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierTrace M word position steps) :
    word = position.consumed ++ position.remaining := by
  induction h with
  | root => simp
  | start hrule => simp
  | read previous htransition hrule ih =>
      simpa [List.append_assoc] using ih
  | epsilon previous htransition hrule ih => exact ih
  | splitLeft previous hlength hrule hright ih => exact ih
  | splitRight previous hlength hrule hleft hpositive hreturn ih =>
      simpa [List.append_assoc] using ih

/-- Forgetting counts and the unconsumed completion suffix recovers the
underlying normalized concrete spine. -/
public theorem PendingFrontierTrace.concreteOperationalSpine
    (M : DPDA Q T S) {word : List T}
    {position : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierTrace M word position steps) :
    ConcreteOperationalSpine M position.frontier position.node
      position.suffix position.consumed position.context := by
  induction h with
  | root => exact ConcreteOperationalSpine.root
  | start hrule => exact ConcreteOperationalSpine.start hrule
  | read previous htransition hrule ih =>
      exact ConcreteOperationalSpine.read ih htransition hrule
  | epsilon previous htransition hrule ih =>
      exact ConcreteOperationalSpine.epsilon ih htransition hrule
  | splitLeft previous hlength hrule hright ih =>
      exact ConcreteOperationalSpine.splitLeft ih hlength hrule hright
  | splitRight previous hlength hrule hleft hpositive hreturn ih =>
      exact ConcreteOperationalSpine.splitRight ih hlength hrule hleft

/-- Exact counted operational meaning of an annotated trace. -/
public theorem PendingFrontierTrace.reachesIn
    (M : DPDA Q T S) {word : List T}
    {position : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierTrace M word position steps) :
    (emptyStackPDA M).ReachesIn steps
      ⟨(emptyStackPDA M).initial_state, word,
        [(emptyStackPDA M).start_symbol]⟩
      (position.cut M) := by
  induction h with
  | root => exact PDA.ReachesIn.refl _
  | start hrule =>
      exact PDA.ReachesIn.refl _
  | @read p suffix consumed remaining context steps q target next a Z gamma
      previous htransition hrule ih =>
      have hstep : (emptyStackPDA M).Reaches₁
          ⟨q, a :: remaining, Z :: context⟩
          ⟨next, remaining, gamma ++ context⟩ := by
        exact Or.inl ⟨next, gamma, htransition, by simp⟩
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack]
        using PDA.ReachesIn.step ih hstep
  | @epsilon p suffix consumed remaining context steps
      q target next Z gamma previous htransition hrule ih =>
      have hcore : (emptyStackPDA M).Reaches₁
          ⟨q, [], Z :: context⟩
          ⟨next, [], gamma ++ context⟩ := by
        exact ⟨next, gamma, htransition, by simp⟩
      have hstep : (emptyStackPDA M).Reaches₁
          ⟨q, remaining, Z :: context⟩
          ⟨next, remaining, gamma ++ context⟩ := by
        apply PDA.reaches₁_iff_reachesIn_one.mpr
        have hlift := (PDA.unconsumed_input_N
          (pda := emptyStackPDA M) remaining).mp
          (PDA.reaches₁_iff_reachesIn_one.mp hcore)
        simpa [PDA.conf.appendInput] using hlift
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack]
        using PDA.ReachesIn.step ih hstep
  | @splitLeft p suffix consumed z remaining context steps
      q middle target Z gamma previous hlength hrule hright ih =>
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack,
        List.append_assoc] using ih
  | @splitRight p suffix consumed leftWord remaining context steps
      returnSteps q middle target Z gamma previous hlength hrule hleft
      hpositive hreturn ih =>
      have hreturn' : (emptyStackPDA M).ReachesIn returnSteps
          ⟨q, leftWord ++ remaining, Z :: (gamma ++ context)⟩
          ⟨middle, remaining, gamma ++ context⟩ := by
        have hrun := hreturn.toReachesIn
        have hlift := (PDA.unconsumed_input_N
          (pda := emptyStackPDA M) remaining).mp hrun
        simpa [PDA.conf.appendInput] using hlift
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack,
        List.append_assoc] using reachesIn_trans_exact ih hreturn'

/-- Every normalized concrete spine admits a counted annotation after an
arbitrary still-unconsumed suffix is appended to its chosen completion. -/
public theorem ConcreteOperationalSpine.exists_pendingFrontierTrace
    (M : DPDA Q T S)
    {p : List (symbol T (Nonterminal M))} {A : Nonterminal M}
    {suffix consumed remaining : List T}
    {context : List (StackSymbol M)}
    (h : ConcreteOperationalSpine M p A suffix consumed context) :
    ∃ steps : ℕ, PendingFrontierTrace M (consumed ++ remaining)
      ⟨p, A, suffix, consumed, context, remaining⟩ steps := by
  induction h generalizing remaining with
  | root => exact ⟨0, by simpa using PendingFrontierTrace.root⟩
  | @read p suffix consumed context q target next a Z gamma
      parent htransition hrule ih =>
      obtain ⟨steps, htrace⟩ := ih (remaining := a :: remaining)
      exact ⟨steps + 1, by
        simpa [List.append_assoc] using
          PendingFrontierTrace.read htrace htransition hrule⟩
  | @epsilon p suffix consumed context q target next Z gamma
      parent htransition hrule ih =>
      obtain ⟨steps, htrace⟩ := ih (remaining := remaining)
      exact ⟨steps + 1,
        PendingFrontierTrace.epsilon htrace htransition hrule⟩
  | @splitLeft p suffix consumed z context q middle target Z gamma
      parent hlength hrule hright ih =>
      obtain ⟨steps, htrace⟩ := ih (remaining := remaining)
      exact ⟨steps,
        PendingFrontierTrace.splitLeft htrace hlength hrule hright⟩
  | @splitRight p suffix consumed leftWord context
      q middle target Z gamma parent hlength hrule hleft ih =>
      obtain ⟨steps, htrace⟩ := ih
        (remaining := leftWord ++ remaining)
      obtain ⟨returnSteps, hpositive, hreturn⟩ :=
        completedSingle_exists_retainedFrameRun M
          (frame := gamma ++ context) hleft
      exact ⟨steps + returnSteps, by
        simpa [List.append_assoc] using PendingFrontierTrace.splitRight
          htrace hlength hrule hleft hpositive hreturn⟩
  | @start target hrule =>
      exact ⟨0, by simpa using PendingFrontierTrace.start (word := remaining) hrule⟩

/-! ## Structural extension and zero-visible ancestry -/

/-- A suffix of an annotated execution.  Its step count is relative to the
starting position. -/
public inductive PendingFrontierExtension (M : DPDA Q T S)
    (startPosition : PendingFrontierPosition M) :
    PendingFrontierPosition M → ℕ → Prop
  | refl : PendingFrontierExtension M startPosition startPosition 0
  | start
      {p : List (symbol T (Nonterminal M))}
      {consumed remaining : List T} {steps : ℕ}
      (previous : PendingFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.start, [], consumed, [], remaining⟩ steps)
      {target : State M}
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      PendingFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.list (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target, [], consumed, [],
          remaining⟩ steps
  | read
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed remaining : List T}
      {context : List (StackSymbol M)} {steps : ℕ}
      {q target next : State M} {a : T} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.single q Z target, suffix, consumed,
          context, a :: remaining⟩ steps)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun q a Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.terminal a,
            symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      PendingFrontierExtension M startPosition
        ⟨p ++ [symbol.terminal a], PDA_to_CFG.N.list next gamma target,
          suffix, consumed ++ [a], context, remaining⟩ (steps + 1)
  | epsilon
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed remaining : List T}
      {context : List (StackSymbol M)} {steps : ℕ}
      {q target next : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.single q Z target, suffix, consumed,
          context, remaining⟩ steps)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun' q Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      PendingFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.list next gamma target, suffix, consumed,
          context, remaining⟩ (steps + 1)
  | splitLeft
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed z remaining : List T}
      {context : List (StackSymbol M)} {steps : ℕ}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.list q (Z :: gamma) target, suffix,
          consumed, context, remaining⟩ steps)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hright : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal)) :
      PendingFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.single q Z middle, z ++ suffix, consumed,
          gamma ++ context, remaining⟩ steps
  | splitRight
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed leftWord remaining : List T}
      {context : List (StackSymbol M)} {steps returnSteps : ℕ}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : PendingFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.list q (Z :: gamma) target, suffix,
          consumed, context, leftWord ++ remaining⟩ steps)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hleft : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)]
        (leftWord.map symbol.terminal))
      (hpositive : 0 < returnSteps)
      (hreturn : PDA.RetainedFrameRun (emptyStackPDA M)
        (gamma ++ context) returnSteps
        ⟨q, leftWord, Z :: (gamma ++ context)⟩
        ⟨middle, [], gamma ++ context⟩) :
      PendingFrontierExtension M startPosition
        ⟨p ++ [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)],
          PDA_to_CFG.N.list middle gamma target, suffix,
          consumed ++ leftWord, context, remaining⟩
        (steps + returnSteps)

/-- The counted subrun represented by a structural frontier extension. -/
public theorem PendingFrontierExtension.reachesIn
    (M : DPDA Q T S)
    {startPosition endPosition : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierExtension M startPosition endPosition steps) :
    (emptyStackPDA M).ReachesIn steps
      (startPosition.cut M) (endPosition.cut M) := by
  induction h with
  | refl => exact PDA.ReachesIn.refl _
  | start previous hrule ih =>
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack]
        using ih
  | @read p suffix consumed remaining context steps q target next a Z gamma
      previous htransition hrule ih =>
      have hstep : (emptyStackPDA M).Reaches₁
          ⟨q, a :: remaining, Z :: context⟩
          ⟨next, remaining, gamma ++ context⟩ := by
        exact Or.inl ⟨next, gamma, htransition, by simp⟩
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack]
        using PDA.ReachesIn.step ih hstep
  | @epsilon p suffix consumed remaining context steps
      q target next Z gamma previous htransition hrule ih =>
      have hcore : (emptyStackPDA M).Reaches₁
          ⟨q, [], Z :: context⟩
          ⟨next, [], gamma ++ context⟩ := by
        exact ⟨next, gamma, htransition, by simp⟩
      have hstep : (emptyStackPDA M).Reaches₁
          ⟨q, remaining, Z :: context⟩
          ⟨next, remaining, gamma ++ context⟩ := by
        apply PDA.reaches₁_iff_reachesIn_one.mpr
        have hlift := (PDA.unconsumed_input_N
          (pda := emptyStackPDA M) remaining).mp
          (PDA.reaches₁_iff_reachesIn_one.mp hcore)
        simpa [PDA.conf.appendInput] using hlift
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack]
        using PDA.ReachesIn.step ih hstep
  | @splitLeft p suffix consumed z remaining context steps
      q middle target Z gamma previous hlength hrule hright ih =>
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack,
        List.append_assoc] using ih
  | @splitRight p suffix consumed leftWord remaining context steps
      returnSteps q middle target Z gamma previous hlength hrule hleft
      hpositive hreturn ih =>
      have hreturn' : (emptyStackPDA M).ReachesIn returnSteps
          ⟨q, leftWord ++ remaining, Z :: (gamma ++ context)⟩
          ⟨middle, remaining, gamma ++ context⟩ := by
        have hrun := hreturn.toReachesIn
        have hlift := (PDA.unconsumed_input_N
          (pda := emptyStackPDA M) remaining).mp hrun
        simpa [PDA.conf.appendInput] using hlift
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack,
        List.append_assoc] using reachesIn_trans_exact ih hreturn'

/-- The characteristic start node occurs only at the zero-step root trace. -/
private theorem PendingFrontierTrace.eq_root_of_node_eq_start
    (M : DPDA Q T S) {word : List T}
    {position : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierTrace M word position steps)
    (hnode : position.node = PDA_to_CFG.N.start) :
    position = ⟨[], PDA_to_CFG.N.start, [], [], [], word⟩ ∧ steps = 0 := by
  cases h with
  | root => exact ⟨rfl, rfl⟩
  | start hrule => cases hnode
  | read previous htransition hrule => cases hnode
  | epsilon previous htransition hrule => cases hnode
  | splitLeft previous hlength hrule hright => cases hnode
  | splitRight previous hlength hrule hleft hpositive hreturn => cases hnode

/-- Extending an annotated trace by a structural suffix preserves the fixed
whole input word and adds the suffix's exact step count. -/
public theorem PendingFrontierTrace.extend
    (M : DPDA Q T S) {word : List T}
    {startPosition endPosition : PendingFrontierPosition M}
    {startSteps extraSteps : ℕ}
    (htrace : PendingFrontierTrace M word startPosition startSteps)
    (hextension : PendingFrontierExtension M startPosition
      endPosition extraSteps) :
    PendingFrontierTrace M word endPosition
      (startSteps + extraSteps) := by
  induction hextension generalizing startSteps with
  | refl => simpa using htrace
  | start previous hrule ih =>
      have hprevious := ih htrace
      obtain ⟨hposition, hsteps⟩ :=
        hprevious.eq_root_of_node_eq_start M rfl
      have hp := congrArg PendingFrontierPosition.frontier hposition
      have hconsumed := congrArg PendingFrontierPosition.consumed hposition
      have hremaining := congrArg PendingFrontierPosition.remaining hposition
      simp only at hp hconsumed hremaining
      subst_vars
      simpa [hsteps] using PendingFrontierTrace.start hrule
  | read previous htransition hrule ih =>
      simpa [Nat.add_assoc] using PendingFrontierTrace.read
        (ih htrace) htransition hrule
  | epsilon previous htransition hrule ih =>
      simpa [Nat.add_assoc] using PendingFrontierTrace.epsilon
        (ih htrace) htransition hrule
  | splitLeft previous hlength hrule hright ih =>
      simpa using PendingFrontierTrace.splitLeft
        (ih htrace) hlength hrule hright
  | splitRight previous hlength hrule hleft hpositive hreturn ih =>
      simpa [Nat.add_assoc] using PendingFrontierTrace.splitRight
        (ih htrace) hlength hrule hleft hpositive hreturn

/-- The end frontier of an extension is the start frontier followed by the
visible events occurring in that extension. -/
public theorem PendingFrontierExtension.prefix_eq_append
    (M : DPDA Q T S)
    {startPosition endPosition : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierExtension M startPosition endPosition steps) :
    ∃ added, endPosition.frontier = startPosition.frontier ++ added := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | start previous hrule ih => exact ih
  | @read p suffix consumed remaining context steps q target next a Z gamma
      previous htransition hrule ih =>
      obtain ⟨added, hadded⟩ := ih
      change p = startPosition.frontier ++ added at hadded
      exact ⟨added ++ [symbol.terminal a], by
        change p ++ [symbol.terminal a] = _
        rw [hadded, List.append_assoc]⟩
  | epsilon previous htransition hrule ih => exact ih
  | splitLeft previous hlength hrule hright ih => exact ih
  | @splitRight p suffix consumed leftWord remaining context steps
      returnSteps q middle target Z gamma previous hlength hrule hleft
      hpositive hreturn ih =>
      obtain ⟨added, hadded⟩ := ih
      change p = startPosition.frontier ++ added at hadded
      exact ⟨added ++
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)], by
        change p ++
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)] = _
        rw [hadded, List.append_assoc]⟩

/-- A counted structural suffix containing only start, epsilon, and
split-left events. -/
public inductive ZeroVisibleFrontierExtension (M : DPDA Q T S)
    (startPosition : PendingFrontierPosition M) :
    PendingFrontierPosition M → ℕ → Prop
  | refl : ZeroVisibleFrontierExtension M startPosition startPosition 0
  | start
      {p : List (symbol T (Nonterminal M))}
      {consumed remaining : List T} {steps : ℕ}
      (previous : ZeroVisibleFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.start, [], consumed, [], remaining⟩ steps)
      {target : State M}
      (hrule : (PDA_to_CFG.N.start,
          [symbol.nonterminal (PDA_to_CFG.N.list
            (emptyStackPDA M).initial_state
            [(emptyStackPDA M).start_symbol] target)]) ∈
        (characteristicGrammar M).rules) :
      ZeroVisibleFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.list (emptyStackPDA M).initial_state
          [(emptyStackPDA M).start_symbol] target, [], consumed, [],
          remaining⟩ steps
  | epsilon
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed remaining : List T}
      {context : List (StackSymbol M)} {steps : ℕ}
      {q target next : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : ZeroVisibleFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.single q Z target, suffix, consumed,
          context, remaining⟩ steps)
      (htransition : (next, gamma) ∈
        (emptyStackPDA M).transition_fun' q Z)
      (hrule : (PDA_to_CFG.N.single q Z target,
          [symbol.nonterminal (PDA_to_CFG.N.list next gamma target)]) ∈
        (characteristicGrammar M).rules) :
      ZeroVisibleFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.list next gamma target, suffix, consumed,
          context, remaining⟩ (steps + 1)
  | splitLeft
      {p : List (symbol T (Nonterminal M))}
      {suffix consumed z remaining : List T}
      {context : List (StackSymbol M)} {steps : ℕ}
      {q middle target : State M} {Z : StackSymbol M}
      {gamma : List (StackSymbol M)}
      (previous : ZeroVisibleFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.list q (Z :: gamma) target, suffix,
          consumed, context, remaining⟩ steps)
      (hlength : (Z :: gamma).length ≤
        PDA_to_CFG.max_push (emptyStackPDA M))
      (hrule : (PDA_to_CFG.N.list q (Z :: gamma) target,
          [symbol.nonterminal (PDA_to_CFG.N.single q Z middle),
            symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]) ∈
        (characteristicGrammar M).rules)
      (hright : (characteristicGrammar M).DerivesRightmost
        [symbol.nonterminal (PDA_to_CFG.N.list middle gamma target)]
        (z.map symbol.terminal)) :
      ZeroVisibleFrontierExtension M startPosition
        ⟨p, PDA_to_CFG.N.single q Z middle, z ++ suffix, consumed,
          gamma ++ context, remaining⟩ steps

/-- Equal pending frontiers force a structural extension to contain no read
or completed-single event, even when that `single` completes on epsilon. -/
public theorem PendingFrontierExtension.zeroVisible_of_prefix_eq
    (M : DPDA Q T S)
    {startPosition endPosition : PendingFrontierPosition M} {steps : ℕ}
    (h : PendingFrontierExtension M startPosition endPosition steps)
    (hprefix : endPosition.frontier = startPosition.frontier) :
    ZeroVisibleFrontierExtension M startPosition endPosition steps := by
  induction h with
  | refl => exact ZeroVisibleFrontierExtension.refl
  | start previous hrule ih =>
      exact ZeroVisibleFrontierExtension.start (ih hprefix) hrule
  | @read p suffix consumed remaining context steps q target next a Z gamma
      previous htransition hrule ih =>
      obtain ⟨added, hadded⟩ := previous.prefix_eq_append M
      change p = startPosition.frontier ++ added at hadded
      change p ++ [symbol.terminal a] = startPosition.frontier at hprefix
      rw [hadded] at hprefix
      have hlength := congrArg List.length hprefix
      simp at hlength
  | epsilon previous htransition hrule ih =>
      exact ZeroVisibleFrontierExtension.epsilon (ih hprefix)
        htransition hrule
  | splitLeft previous hlength hrule hright ih =>
      exact ZeroVisibleFrontierExtension.splitLeft (ih hprefix)
        hlength hrule hright
  | @splitRight p suffix consumed leftWord remaining context steps
      returnSteps q middle target Z gamma previous hlength hrule hleft
      hpositive hreturn ih =>
      obtain ⟨added, hadded⟩ := previous.prefix_eq_append M
      change p = startPosition.frontier ++ added at hadded
      change p ++
        [symbol.nonterminal (PDA_to_CFG.N.single q Z middle)] =
          startPosition.frontier at hprefix
      rw [hadded] at hprefix
      have hlen := congrArg List.length hprefix
      simp at hlen

/-- A counted zero-visible frontier suffix is the existing structural
`ZeroVisibleTail` after forgetting its count and remaining input. -/
public theorem ZeroVisibleFrontierExtension.zeroVisibleTail
    (M : DPDA Q T S)
    {startPosition endPosition : PendingFrontierPosition M} {steps : ℕ}
    (h : ZeroVisibleFrontierExtension M startPosition endPosition steps) :
    ZeroVisibleTail M startPosition.frontier startPosition.consumed
      startPosition.node startPosition.suffix startPosition.context
      endPosition.node endPosition.suffix endPosition.context := by
  induction h with
  | refl => exact ZeroVisibleTail.refl
  | start previous hrule ih => exact ZeroVisibleTail.start ih hrule
  | epsilon previous htransition hrule ih =>
      exact ZeroVisibleTail.epsilon ih htransition hrule
  | splitLeft previous hlength hrule hright ih =>
      exact ZeroVisibleTail.splitLeft ih hlength hrule hright

/-- Zero-visible frontier suffixes retain their remaining input and have the
exact counted operational meaning advertised by their index. -/
public theorem ZeroVisibleFrontierExtension.reachesIn
    (M : DPDA Q T S)
    {startPosition endPosition : PendingFrontierPosition M} {steps : ℕ}
    (h : ZeroVisibleFrontierExtension M startPosition endPosition steps) :
    (emptyStackPDA M).ReachesIn steps
      (startPosition.cut M) (endPosition.cut M) := by
  induction h with
  | refl => exact PDA.ReachesIn.refl _
  | start previous hrule ih =>
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack]
        using ih
  | @epsilon p suffix consumed remaining context steps
      q target next Z gamma previous htransition hrule ih =>
      have hcore : (emptyStackPDA M).Reaches₁
          ⟨q, [], Z :: context⟩
          ⟨next, [], gamma ++ context⟩ := by
        exact ⟨next, gamma, htransition, by simp⟩
      have hstep : (emptyStackPDA M).Reaches₁
          ⟨q, remaining, Z :: context⟩
          ⟨next, remaining, gamma ++ context⟩ := by
        apply PDA.reaches₁_iff_reachesIn_one.mpr
        have hlift := (PDA.unconsumed_input_N
          (pda := emptyStackPDA M) remaining).mp
          (PDA.reaches₁_iff_reachesIn_one.mp hcore)
        simpa [PDA.conf.appendInput] using hlift
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack]
        using PDA.ReachesIn.step ih hstep
  | @splitLeft p suffix consumed z remaining context steps
      q middle target Z gamma previous hlength hrule hright ih =>
      simpa [PendingFrontierPosition.cut, spineCutState, spineCutStack,
        List.append_assoc] using ih

/-- Zero-visible suffixes preserve the unconsumed part of the fixed word. -/
public theorem ZeroVisibleFrontierExtension.remaining_eq
    (M : DPDA Q T S)
    {startPosition endPosition : PendingFrontierPosition M} {steps : ℕ}
    (h : ZeroVisibleFrontierExtension M startPosition endPosition steps) :
    endPosition.remaining = startPosition.remaining := by
  induction h with
  | refl => rfl
  | start previous hrule ih => exact ih
  | epsilon previous htransition hrule ih => exact ih
  | splitLeft previous hlength hrule hright ih => exact ih

/-- Zero-visible suffixes preserve the completed part of the fixed word. -/
public theorem ZeroVisibleFrontierExtension.consumed_eq
    (M : DPDA Q T S)
    {startPosition endPosition : PendingFrontierPosition M} {steps : ℕ}
    (h : ZeroVisibleFrontierExtension M startPosition endPosition steps) :
    endPosition.consumed = startPosition.consumed := by
  induction h with
  | refl => rfl
  | start previous hrule ih => exact ih
  | epsilon previous htransition hrule ih => exact ih
  | splitLeft previous hlength hrule hright ih => exact ih

/-- Packaged ancestry consequence for two points of one annotated execution.
The endpoint trace has the summed count, and equality of visible frontiers
forces the entire extra counted segment to be zero-visible. -/
public theorem PendingFrontierTrace.extend_same_frontier
    (M : DPDA Q T S) {word : List T}
    {startPosition endPosition : PendingFrontierPosition M}
    {startSteps extraSteps : ℕ}
    (htrace : PendingFrontierTrace M word startPosition startSteps)
    (hextension : PendingFrontierExtension M startPosition
      endPosition extraSteps)
    (hfrontier : endPosition.frontier = startPosition.frontier) :
    PendingFrontierTrace M word endPosition (startSteps + extraSteps) ∧
      endPosition.remaining = startPosition.remaining ∧
      endPosition.consumed = startPosition.consumed ∧
      ZeroVisibleTail M startPosition.frontier startPosition.consumed
        startPosition.node startPosition.suffix startPosition.context
        endPosition.node endPosition.suffix endPosition.context ∧
      (emptyStackPDA M).ReachesIn extraSteps
        (startPosition.cut M) (endPosition.cut M) := by
  have hzero := hextension.zeroVisible_of_prefix_eq M hfrontier
  exact ⟨htrace.extend M hextension, hzero.remaining_eq M,
    hzero.consumed_eq M, hzero.zeroVisibleTail M, hzero.reachesIn M⟩

end

end DPDA_to_LR
