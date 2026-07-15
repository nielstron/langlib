module

public import Langlib.Grammars.LR.Equivalence.Completeness

@[expose]
public section

/-!
# Finite canonical LR action table

Canonical parser states are the raw finite kernels stored on the parse stack;
their epsilon closure is inspected for actions.  Reduction has priority in the
total table definition.  On reachable states LR(k) uniqueness proves that the
arbitrary finite choice of a complete item cannot affect the selected grammar
rule.
-/

open Language

namespace CF_grammar.LRk

variable {T : Type}

/-- Finite raw states of the canonical viable-prefix automaton. -/
public abbrev KernelState [Fintype T] (G : CF_grammar T) (k : ℕ) :=
  Finset (Item G.augment k)

/-- A complete item enabled in a raw state at the displayed lookahead. -/
@[expose]
public def EnabledReduction [Fintype T] (G : CF_grammar T) (k : ℕ)
    (q : KernelState G k) (u : Lookahead T k) (i : Item G.augment k) : Prop :=
  i ∈ closure G.augment k q ∧ i.Complete ∧ i.lookahead = u

/-- Choose one enabled reduction item.  The choice is deliberately finite and
noncomputable: automata in this repository are mathematical transition
functions, and LR(k) uniqueness later proves rule-independence. -/
@[expose]
public noncomputable def reductionItem? [Fintype T]
    (G : CF_grammar T) (k : ℕ) (q : KernelState G k)
    (u : Lookahead T k) : Option (Item G.augment k) := by
  classical
  exact if h : ∃ i, EnabledReduction G k q u i then
    some (Classical.choose h)
  else none

public theorem reductionItem?_eq_some_iff [Fintype T]
    (G : CF_grammar T) (k : ℕ) (q : KernelState G k)
    (u : Lookahead T k) (i : Item G.augment k) :
    reductionItem? G k q u = some i → EnabledReduction G k q u i := by
  classical
  unfold reductionItem?
  split
  · intro hsome
    have hi : Classical.choose ‹∃ i, EnabledReduction G k q u i› = i :=
      Option.some.inj hsome
    subst i
    exact Classical.choose_spec ‹∃ i, EnabledReduction G k q u i›
  · simp

public theorem reductionItem?_eq_none_iff [Fintype T]
    (G : CF_grammar T) (k : ℕ) (q : KernelState G k)
    (u : Lookahead T k) :
    reductionItem? G k q u = none ↔
      ¬ ∃ i, EnabledReduction G k q u i := by
  classical
  unfold reductionItem?
  split <;> simp_all

public theorem exists_reductionItem?_eq_some [Fintype T]
    (G : CF_grammar T) (k : ℕ) (q : KernelState G k)
    (u : Lookahead T k) (h : ∃ i, EnabledReduction G k q u i) :
    ∃ i, reductionItem? G k q u = some i := by
  classical
  unfold reductionItem?
  simp [h]

/-- A terminal is syntactically shift-supported when some closed item has it
immediately after the dot.  The total table below safely defaults to shifting
whenever no semantic reduction is enabled; this predicate remains useful for
the usual canonical-item characterization of reachable shifts. -/
@[expose]
public def ShiftEnabled [Fintype T] (G : CF_grammar T) (k : ℕ)
    (q : KernelState G k) (a : T) : Prop :=
  ∃ i ∈ closure G.augment k q,
    i.next? = some (symbol.terminal a)

/-- Total finite action selected by a canonical table. -/
public inductive TableAction (G : CF_grammar T) where
  | shift
  | reduce (rule : RuleIndex G.augment)
  | accept
  | error

/-- First buffered symbol, returning EOF for the degenerate zero-lookahead
buffer.  The final construction uses `k+1`, so its reachable buffers are
always nondegenerate. -/
@[expose]
public def lookaheadHead (k : ℕ) (u : Lookahead T k) : Option T :=
  if h : 0 < k then u ⟨0, h⟩ else none

/-- Canonical table action.  A completed augmented-start item is acceptance;
all other completed items are reductions.  If there is no reduction, a
syntactically enabled terminal is shifted. -/
@[expose]
public noncomputable def tableAction [Fintype T] (G : CF_grammar T) (k : ℕ)
    (q : KernelState G k) (u : Lookahead T k) : TableAction G := by
  classical
  exact match reductionItem? G k q u with
  | some i =>
      if i.rule = startRuleIndex G then .accept else .reduce i.rule
  | none =>
      match lookaheadHead k u with
      | some _ => .shift
      | none => .error

/-- The raw goto state used after shifting or reducing a grammar symbol. -/
@[expose]
public noncomputable def nextKernel [Fintype T] (G : CF_grammar T) (k : ℕ)
    (q : KernelState G k) (X : symbol T G.augment.nt) : KernelState G k :=
  goto G.augment k q X

public theorem tableAction_accept_iff [Fintype T]
    (G : CF_grammar T) (k : ℕ) (q : KernelState G k)
    (u : Lookahead T k) :
    tableAction G k q u = .accept ↔
      ∃ i, reductionItem? G k q u = some i ∧
        i.rule = startRuleIndex G := by
  classical
  cases hred : reductionItem? G k q u with
  | none =>
      cases hhead : lookaheadHead k u <;>
        simp [tableAction, hred, hhead]
  | some i =>
      by_cases hi : i.rule = startRuleIndex G <;>
        simp [tableAction, hred, hi]

public theorem tableAction_reduce_iff [Fintype T]
    (G : CF_grammar T) (k : ℕ) (q : KernelState G k)
    (u : Lookahead T k) (r : RuleIndex G.augment) :
    tableAction G k q u = .reduce r ↔
      ∃ i, reductionItem? G k q u = some i ∧
        i.rule ≠ startRuleIndex G ∧ i.rule = r := by
  classical
  cases hred : reductionItem? G k q u with
  | none =>
      cases hhead : lookaheadHead k u <;>
        simp [tableAction, hred, hhead]
  | some i =>
      by_cases hi : i.rule = startRuleIndex G <;>
        simp [tableAction, hred, hi]

public theorem tableAction_shift_of_none [Fintype T]
    (G : CF_grammar T) (k : ℕ) (q : KernelState G k)
    (u : Lookahead T k) {a : T}
    (hred : reductionItem? G k q u = none)
    (hhead : lookaheadHead k u = some a) :
    tableAction G k q u = .shift := by
  classical
  unfold tableAction
  rw [hred, hhead]

/-- On a reachable state, every chosen complete item is a semantic reduction
candidate at the corresponding scanned prefix. -/
public theorem reductionItem?_reductionCandidate [Fintype T]
    (G : CF_grammar T) (k : ℕ)
    {gamma : List (symbol T G.augment.nt)} {u : Lookahead T k}
    {i : Item G.augment k}
    (h : reductionItem? G k (scanKernel G k gamma) u = some i) :
    ReductionCandidate G.augment k gamma u (ruleAt G.augment i.rule) := by
  have hi := reductionItem?_eq_some_iff G k (scanKernel G k gamma) u i h
  exact (itemState_valid G k gamma hi.1).reductionCandidate hi.2.1 hi.2.2

/-- If a particular semantic reduction is exposed in a reachable state, the
finite table chooses an item naming the same production value. -/
public theorem reductionItem?_rule_eq_of_stateReduction [Fintype T]
    (G : CF_grammar T) (k : ℕ) (hLR : G.IsLRk k)
    {gamma : List (symbol T G.augment.nt)} {u : Lookahead T k}
    {r : G.augment.nt × List (symbol T G.augment.nt)}
    (hr : StateReduction G k gamma u r) :
    ∃ i, reductionItem? G k (scanKernel G k gamma) u = some i ∧
      ruleAt G.augment i.rule = r := by
  have hjcand : ReductionCandidate G.augment k gamma u r :=
    StateReduction.reductionCandidate hr
  rcases hr with ⟨j, hj, hcomplete, hlook, hjrule⟩
  have henabled : EnabledReduction G k (scanKernel G k gamma) u j :=
    ⟨hj, hcomplete, hlook⟩
  obtain ⟨i, hi⟩ := exists_reductionItem?_eq_some G k _ u ⟨j, henabled⟩
  refine ⟨i, hi, ?_⟩
  have hcand := reductionItem?_reductionCandidate G k hi
  exact CoreIsLRk.reductionCandidate_unique (G := G.augment) hLR hcand hjcand

end CF_grammar.LRk
