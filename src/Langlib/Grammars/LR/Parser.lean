module

public import Langlib.Grammars.LR.Definition

/-!
# LR Parser Semantics

This file defines the table-driven parser side of LR parsing.  It is intentionally
separate from `Langlib.Grammars.LR.Definition`, which contains the grammar-side
LR(k) predicate.

The definitions here are the parser object used by the LR(k)-to-DPDA
construction: a deterministic action/goto table, stack configurations, and the
induced one-step parser transition.

As elsewhere in this development, a context-free rule is a pair
`rule : N × List (symbol T N)` whose first component `rule.1` is the left-hand
nonterminal and whose second component `rule.2` is the right-hand output string.
-/

open Language

namespace LR

variable {T N State : Type}

/-- Parser action selected by the current parser state and one lookahead symbol.

The lookahead will be `none` exactly at end-of-input. -/
public inductive Action (T N State : Type) where
  | shift (next : State)
  | reduce (rule : N × List (symbol T N))
  | accept
  | error

/-- A deterministic LR parsing table.

`action q lookahead` decides whether to shift, reduce, accept, or reject.
`goto q A` is consulted after reducing to the nonterminal `A`. -/
public structure Parser (T N State : Type) where
  initial : State
  action : State → Option T → Action T N State
  goto : State → N → Option State

namespace Parser

variable (p : Parser T N State)

/-- A parser stack entry stores the grammar symbol and the state reached after
placing that symbol on the stack.  The top of the stack is the head of the list. -/
public abbrev StackEntry (T N State : Type) :=
  symbol T N × State

/-- LR parser configurations. -/
public structure Config (T N State : Type) where
  input : List T
  stack : List (StackEntry T N State)

/-- Initial parser configuration on an input word. -/
public def initialConfig (w : List T) : Config T N State where
  input := w
  stack := []

/-- The current parser state: either the state stored at the top of the stack or
the parser's initial state when the stack is empty. -/
public def stateOfStack (stack : List (StackEntry T N State)) : State :=
  match stack with
  | [] => p.initial
  | (_, q) :: _ => q

/-- The grammar symbols stored in the top `n` parser-stack entries. -/
public def topSymbols (n : ℕ) (stack : List (StackEntry T N State)) : List (symbol T N) :=
  (stack.take n).map Prod.fst

variable [DecidableEq T] [DecidableEq N]

/-- Perform a reduce action, if the top stack symbols match the rule's right-hand side
and the goto table is defined. -/
public def reduce? (rule : N × List (symbol T N)) (input : List T)
    (stack : List (StackEntry T N State)) : Option (Config T N State) :=
  if topSymbols rule.2.length stack = rule.2.reverse then
    let rest := stack.drop rule.2.length
    match p.goto (p.stateOfStack rest) rule.1 with
    | some next =>
        some { input := input, stack := (symbol.nonterminal rule.1, next) :: rest }
    | none => none
  else
    none

/-- One deterministic parser transition, if any. -/
public def step? (c : Config T N State) : Option (Config T N State) :=
  let q := p.stateOfStack c.stack
  match c.input with
  | a :: rest =>
      match p.action q (some a) with
      | Action.shift next =>
          some { input := rest, stack := (symbol.terminal a, next) :: c.stack }
      | Action.reduce rule => p.reduce? rule c.input c.stack
      | Action.accept => none
      | Action.error => none
  | [] =>
      match p.action q none with
      | Action.reduce rule => p.reduce? rule [] c.stack
      | Action.accept => none
      | Action.shift _ => none
      | Action.error => none

/-- Relational view of one parser transition. -/
public def Step (c d : Config T N State) : Prop :=
  p.step? c = some d

/-- Reflexive-transitive closure of parser steps. -/
public abbrev Reaches : Config T N State → Config T N State → Prop :=
  Relation.ReflTransGen p.Step

/-- A parser accepts an input word when it reaches an end-of-input configuration
whose action is `accept`. -/
public def Accepts (w : List T) : Prop :=
  ∃ c : Config T N State,
    p.Reaches (initialConfig w) c ∧
      c.input = [] ∧
      p.action (p.stateOfStack c.stack) none = Action.accept

/-- The language accepted by a table-driven LR parser. -/
public def language : Language T :=
  setOf p.Accepts

/-- The parser transition is deterministic because it is defined by a function. -/
public theorem step_functional {c d₁ d₂ : Config T N State}
    (h₁ : p.Step c d₁) (h₂ : p.Step c d₂) : d₁ = d₂ := by
  unfold Step at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

end Parser

end LR
