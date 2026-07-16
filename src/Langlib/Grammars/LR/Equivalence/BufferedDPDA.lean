module

public import Langlib.Grammars.LR.Equivalence.Table
public import Langlib.Automata.DeterministicPushdown.Definition

@[expose]
public section

/-!
# Buffered canonical LR machine

This file is the concrete finite-control compilation of the canonical LR
table.  Its input alphabet is `Option T`: `some a` encodes an ordinary terminal
and `none` is a consumed right endmarker.  The machine keeps a positive fixed
lookahead buffer in its control, so EOF-only reductions never need to test raw
input exhaustion.
-/

open Language

namespace CF_grammar.LRk.Buffered

open CF_grammar.LRk

variable {T : Type} [Fintype T]

/-- Finite cursor used while popping the right-hand side of a reduction. -/
public abbrev ReductionCursor (G : CF_grammar T) :=
  Σ r : RuleIndex G.augment, Position G.augment r

public noncomputable instance instFintypeReductionCursor (G : CF_grammar T) :
    Fintype (ReductionCursor G) := by
  classical
  exact Sigma.instFintype

@[expose]
public def ReductionCursor.rule {G : CF_grammar T} (c : ReductionCursor G) :
    RuleIndex G.augment := c.1

@[expose]
public def ReductionCursor.remaining {G : CF_grammar T}
    (c : ReductionCursor G) : ℕ := c.2.val

@[expose]
public def fullCursor (G : CF_grammar T) (r : RuleIndex G.augment) :
    ReductionCursor G :=
  ⟨r, ⟨(ruleAt G.augment r).2.length, by omega⟩⟩

@[expose]
public def ReductionCursor.pred {G : CF_grammar T} (c : ReductionCursor G)
    (_h : 0 < c.remaining) : ReductionCursor G :=
  ⟨c.1, ⟨c.2.val - 1, by
    have := c.2.isLt
    omega⟩⟩

/-- Replace one slot in a fixed lookahead buffer. -/
@[expose]
public def setBuffer (u : Lookahead T k) (n : ℕ) (x : Option T) :
    Lookahead T k :=
  fun i => if i.val = n then x else u i

/-- On consuming the explicit endmarker during preload, preserve the already
loaded prefix and pad every remaining slot with EOF. -/
@[expose]
public def finishBuffer (u : Lookahead T k) (n : ℕ) : Lookahead T k :=
  fun i => if i.val < n then u i else none

/-- Shift a positive lookahead buffer left and append one newly read symbol. -/
@[expose]
public def shiftBuffer (_hk : 0 < k) (u : Lookahead T k) (x : Option T) :
    Lookahead T k :=
  fun i =>
    if h : i.val + 1 < k then u ⟨i.val + 1, h⟩ else x

/-- Last buffered symbol. -/
@[expose]
public def lastBuffer (hk : 0 < k) (u : Lookahead T k) : Option T :=
  u ⟨k - 1, by omega⟩

noncomputable section

/-- Finite control of the marked-input LR machine. -/
public inductive Control (G : CF_grammar T) (k : ℕ) where
  | load (count : Fin (k + 1)) (buffer : Lookahead T k)
  | parse (kernel : KernelState G k) (buffer : Lookahead T k)
  | refill (kernel : KernelState G k) (buffer : Lookahead T k)
  | pop (cursor : ReductionCursor G) (buffer : Lookahead T k)
  | accept
  | reject
deriving Fintype

/-- Stack symbols are saved raw canonical kernels; `none` is the permanent
bottom marker. -/
public abbrev StackSymbol (G : CF_grammar T) (k : ℕ) :=
  Option (KernelState G k)

public noncomputable instance instFintypeStackSymbol
    (G : CF_grammar T) (k : ℕ) : Fintype (StackSymbol G k) := by
  classical
  infer_instance

/-- Kernel represented by a stack top, interpreting the bottom marker as the
initial kernel. -/
@[expose]
public def kernelOfTop (G : CF_grammar T) (k : ℕ) :
    StackSymbol G k → KernelState G k
  | none => startKernel G k
  | some q => q

/-- Initial buffered control.  The positive-lookahead machine starts with an
all-EOF scratch buffer and overwrites it from left to right. -/
@[expose]
public def initialControl (G : CF_grammar T) (k : ℕ) : Control G k :=
  .load ⟨0, by omega⟩ (eofLookahead T k)

/-- Input-reading transitions.  Only preload and refill controls read the
marked input; all parser operations are epsilon moves over already buffered
symbols. -/
@[expose]
public noncomputable def inputTransition (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k)
    (q : Control G k) (x : Option T) (Z : StackSymbol G k) :
    Option (Control G k × List (StackSymbol G k)) := by
  classical
  exact match q with
  | .load count buffer =>
      if hc : count.val < k then
        match x with
        | none => some (.parse (startKernel G k)
            (finishBuffer buffer count.val), [Z])
        | some a =>
            let buffer' := setBuffer buffer count.val (some a)
            if hfull : count.val + 1 = k then
              some (.parse (startKernel G k) buffer', [Z])
            else
              some (.load ⟨count.val + 1, by omega⟩ buffer', [Z])
      else none
  | .refill kernel buffer =>
      some (.parse kernel (shiftBuffer hk buffer x), [Z])
  | _ => none

/-- Epsilon transitions implementing table actions and finite reduction pops. -/
@[expose]
public noncomputable def epsilonTransition (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k)
    (q : Control G k) (Z : StackSymbol G k) :
    Option (Control G k × List (StackSymbol G k)) := by
  classical
  exact match q with
  | .parse kernel buffer =>
      match tableAction G k kernel buffer with
      | .accept => some (.accept, [Z])
      | .error => some (.reject, [Z])
      | .reduce r => some (.pop (fullCursor G r) buffer, [Z])
      | .shift =>
          match lookaheadHead k buffer with
          | none => some (.reject, [Z])
          | some a =>
              let next := nextKernel G k kernel (symbol.terminal a)
              if lastBuffer hk buffer = none then
                some (.parse next (shiftBuffer hk buffer none),
                  some next :: [Z])
              else
                some (.refill next buffer, some next :: [Z])
  | .pop cursor buffer =>
      if h : 0 < cursor.remaining then
        match Z with
        | none => some (.reject, [Z])
        | some _ => some (.pop (cursor.pred h) buffer, [])
      else
        let previous := kernelOfTop G k Z
        let rule := ruleAt G.augment cursor.rule
        let next := nextKernel G k previous (symbol.nonterminal rule.1)
        some (.parse next buffer, some next :: [Z])
  | _ => none

/-- The concrete DPDA recognizing the explicitly endmarked canonical parser
language. -/
@[expose]
public noncomputable def machine (G : CF_grammar T) (k : ℕ) (hk : 0 < k) :
    DPDA (Control G k) (Option T) (StackSymbol G k) where
  initial_state := initialControl G k
  start_symbol := none
  final_states := {Control.accept}
  transition := inputTransition G k hk
  epsilon_transition := epsilonTransition G k hk
  no_mixed := by
    intro q Z hepsilon x
    cases q <;> simp [epsilonTransition, inputTransition] at hepsilon ⊢

end

end CF_grammar.LRk.Buffered
