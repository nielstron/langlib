module

public import Mathlib.Computability.Primrec.List

@[expose]
public section

/-!
# Encoded deterministic first-order grammars

This file provides the finite syntax and labelled transition system used by the
Jančar route to deterministic pushdown-automaton equivalence.  Runtime terms are
finite pointed graphs, rather than finite trees.  They can therefore represent
regular (possibly infinite) first-order terms by cycles.

Every code has executable semantics.  Rules are stored in a list and the first
row with a requested root symbol and action is used, so duplicate raw rows do not
introduce nondeterminism.  `WellFormed` is only a decidable structural check; no
semantic promise or oracle is built into the code type.

## Proof-source boundary

The syntax and regular-term semantics below agree with Petr Jančar,
*Bisimulation Equivalence of First-Order Grammars* (2014), arXiv:1405.7923.  The
later positive semidecision layer uses only the deterministic trace-equivalence
system in arXiv:1010.4760v4, culminating in its Theorem 51.  Version 4 explicitly
reworks the proof and omits the nondeterministic extension from version 3.

This version distinction matters: Géraud Sénizergues' arXiv:1101.5046 gives a
semantically false derivation in, and identifies a flawed soundness argument for,
the **nondeterministic extension in arXiv:1010.4760v3**.  We neither reproduce
that extension nor appeal to its soundness.  The executable negative
semidecision is proved directly from finite traces, and the positive side is
scoped to action-deterministic grammars.

A well-formed grammar has at most one row for a pair `(root symbol, action)`, so
bisimilarity coincides with equality of finite traces.  Variables have private
observable self-loop labels.  Those labels ensure that two different variables
are not identified during balancing; they are unreachable from the ground terms
produced by the eventual DPDA translation.
-/

namespace DCFEquivalence

/-! ## Finite graphs for regular first-order terms -/

/-- A raw graph node is either a variable, or a ranked-symbol application whose
children are node indices in the same graph. -/
public abbrev RawNode := ℕ ⊕ (ℕ × List ℕ)

/-- A finite graph together with the index of its distinguished root.  Cycles in
the graph encode regular infinite terms. -/
public def RegularTerm := List RawNode × ℕ

namespace RegularTerm

public instance : Primcodable RegularTerm :=
  inferInstanceAs (Primcodable (List RawNode × ℕ))

public instance : DecidableEq RegularTerm :=
  inferInstanceAs (DecidableEq (List RawNode × ℕ))

@[expose] public def nodes (t : RegularTerm) : List RawNode := t.1

@[expose] public def root (t : RegularTerm) : ℕ := t.2

/-- Read a node.  An out-of-range reference is deliberately stuck; well-formed
codes never contain one. -/
@[expose] public def nodeAt? (t : RegularTerm) (i : ℕ) : Option RawNode :=
  t.nodes[i]?

/-- Read the distinguished root node. -/
@[expose] public def rootNode? (t : RegularTerm) : Option RawNode :=
  t.nodeAt? t.root

/-- Change only the distinguished root, retaining the shared finite graph. -/
@[expose] public def withRoot (t : RegularTerm) (i : ℕ) : RegularTerm :=
  (t.nodes, i)

/-- The root symbol and its child references, when the root is an application. -/
@[expose] public def rootApplication? (t : RegularTerm) : Option (ℕ × List ℕ) :=
  match t.rootNode? with
  | some (.inr app) => some app
  | _ => none

/-- Shift every child reference in an application node by `offset`. -/
@[expose] public def shiftNode (offset : ℕ) : RawNode → RawNode
  | .inl x => .inl x
  | .inr (X, children) => .inr (X, children.map (offset + ·))

/-- Advance the running offset by one argument graph, retaining the unprocessed
argument suffix. -/
@[expose] public def advanceArgumentOffset
    (state : ℕ × List RegularTerm) : ℕ × List RegularTerm :=
  match state.2 with
  | [] => state
  | term :: terms => (state.1 + term.nodes.length, terms)

/-- The start index of the `i`th argument graph after all argument graphs have
been appended behind a right-hand-side graph. -/
@[expose] public def argumentOffset (base : ℕ)
    (arguments : List RegularTerm) (i : ℕ) : ℕ :=
  (Nat.rec (motive := fun _ => ℕ × List RegularTerm) (base, arguments)
    (fun _ state => advanceArgumentOffset state) i).1

/-- The embedded root reference of an argument, if that argument exists. -/
@[expose] public def argumentRoot? (rhs : RegularTerm)
    (arguments : List RegularTerm) (x : ℕ) : Option ℕ :=
  (arguments[x]?).map fun argument =>
    argumentOffset rhs.nodes.length arguments x + argument.root

/-- Redirect a right-hand-side reference which points at a variable node to the
root of the corresponding argument graph.  Unbound variables and malformed
references remain stuck in the raw graph. -/
@[expose] public def resolveRHSRef (rhs : RegularTerm)
    (arguments : List RegularTerm) (i : ℕ) : ℕ :=
  match rhs.nodeAt? i with
  | some (.inl x) => (rhs.argumentRoot? arguments x).getD i
  | _ => i

/-- Redirect the children of one right-hand-side node during substitution. -/
@[expose] public def instantiateNode (rhs : RegularTerm)
    (arguments : List RegularTerm) : RawNode → RawNode
  | .inl x => .inl x
  | .inr (X, children) =>
      .inr (X, children.map (rhs.resolveRHSRef arguments))

/-- Add one argument graph to an offset/output accumulator. -/
@[expose] public def appendArgumentNodes
    (state : ℕ × List RawNode) (argument : RegularTerm) :
    ℕ × List RawNode :=
  (state.1 + argument.nodes.length,
    state.2 ++ argument.nodes.map (shiftNode state.1))

/-- Append argument graphs, shifting their internal references into the combined
graph. -/
@[expose] public def appendArguments (offset : ℕ)
    (arguments : List RegularTerm) : List RawNode :=
  (arguments.foldl appendArgumentNodes (offset, [])).2

/-- Simultaneously instantiate the variables of a right-hand-side graph.

The original RHS nodes are retained (variable nodes become unreachable when they
are bound), and disjoint shifted copies of all argument graphs are appended.  The
operation is total on raw codes and agrees with ordinary graph substitution on
well-formed codes. -/
@[expose] public def instantiate (rhs : RegularTerm)
    (arguments : List RegularTerm) : RegularTerm :=
  (rhs.nodes.map (rhs.instantiateNode arguments) ++
      appendArguments rhs.nodes.length arguments,
    rhs.resolveRHSRef arguments rhs.root)

/-! ### Decidable structural well-formedness -/

/-- Check that the unfolding below a node is finite.  `visiting` is the current
DFS path; sharing is permitted, while a reachable cycle is rejected.  Fuel makes
this a total executable check even for malformed graphs. -/
@[expose] public def unfoldsFiniteFrom (nodes : List RawNode) :
    ℕ → List ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, visiting, i =>
      if i ∈ visiting then false
      else
        match nodes[i]? with
        | none => false
        | some (.inl _) => true
        | some (.inr (_, children)) =>
            children.all fun child =>
              unfoldsFiniteFrom nodes fuel (i :: visiting) child

/-- Executable check that the term denoted from the distinguished root is
finite.  Unreachable garbage in a raw graph is irrelevant to the unfolding. -/
@[expose] public def unfoldsFiniteCode (t : RegularTerm) : Bool :=
  unfoldsFiniteFrom t.nodes (t.nodes.length + 1) [] t.root

/-- The regular term represented by a graph happens to be finite. -/
@[expose] public def UnfoldsFinite (t : RegularTerm) : Prop :=
  t.unfoldsFiniteCode = true

/-- Check one node against a rank table, a variable bound, and the size of its
containing graph. -/
@[expose] public def nodeWellFormedCode (ranks : List ℕ)
    (variableBound nodeCount : ℕ) : RawNode → Bool
  | .inl x => decide (x < variableBound)
  | .inr (X, children) =>
      match ranks[X]? with
      | none => false
      | some rank =>
          decide (children.length = rank) &&
            children.all fun child => decide (child < nodeCount)

/-- Executable structural check for a pointed regular-term graph. -/
@[expose] public def wellFormedCode (ranks : List ℕ)
    (variableBound : ℕ) (t : RegularTerm) : Bool :=
  decide (t.root < t.nodes.length) &&
    t.nodes.all (nodeWellFormedCode ranks variableBound t.nodes.length)

/-- A term graph is well formed when its root and edges are in range, every
application has the declared rank, and every variable is below the supplied
bound. -/
@[expose] public def WellFormed (ranks : List ℕ)
    (variableBound : ℕ) (t : RegularTerm) : Prop :=
  t.wellFormedCode ranks variableBound = true

/-! ### Runtime ground graphs

Substitution deliberately retains schema-variable nodes as unreachable garbage.
Consequently, runtime groundness must concern the unfolding reachable from the
distinguished root, rather than every raw node in the presentation.  We still
check rank and reference correctness globally; this excludes malformed offset
aliasing while allowing the harmless retained variable nodes.
-/

/-- Global rank/reference validity while permitting variable nodes with any
index. -/
@[expose] public def nodeShapeWellFormedCode (ranks : List ℕ)
    (nodeCount : ℕ) : RawNode → Bool
  | .inl _ => true
  | .inr (X, children) =>
      match ranks[X]? with
      | none => false
      | some rank =>
          decide (children.length = rank) &&
            children.all fun child => decide (child < nodeCount)

/-- Executable global rank/reference check which ignores variable indices. -/
@[expose] public def shapeWellFormedCode (ranks : List ℕ)
    (t : RegularTerm) : Bool :=
  decide (t.root < t.nodes.length) &&
    t.nodes.all (nodeShapeWellFormedCode ranks t.nodes.length)

/-- Global rank/reference correctness of a runtime graph. -/
@[expose] public def ShapeWellFormed (ranks : List ℕ)
    (t : RegularTerm) : Prop :=
  t.shapeWellFormedCode ranks = true

/-- A finite support witnesses that every node reachable from the root is an
application: it contains the root and is closed under application children,
and it contains no variable node. -/
@[expose] public def GroundWitness (t : RegularTerm)
    (support : List ℕ) : Prop :=
  t.root ∈ support ∧
    ∀ i ∈ support, ∃ X children,
      t.nodeAt? i = some (.inr (X, children)) ∧
        ∀ child ∈ children, child ∈ support

/-- Executable check of one proposed closed ground support. -/
@[expose] public def groundWitnessCode (t : RegularTerm)
    (support : List ℕ) : Bool :=
  decide (t.root ∈ support) && support.all fun i =>
    match t.nodeAt? i with
    | some (.inr (_, children)) =>
        children.all fun child => decide (child ∈ support)
    | _ => false

/-- Executable reachable-groundness check.  `List.sublists` enumerates every
subset of the finite node-index range; a cyclic unfolding is accepted exactly
when one of those subsets is a closed application-only support. -/
@[expose] public def groundCode (ranks : List ℕ)
    (t : RegularTerm) : Bool :=
  t.shapeWellFormedCode ranks &&
    (List.range t.nodes.length).sublists'.any t.groundWitnessCode

/-- A runtime graph is ground when it is globally rank/reference correct and
its reachable unfolding has a finite application-only closed support.
Unreachable variable nodes retained by substitution are allowed. -/
@[expose] public def Ground (ranks : List ℕ) (t : RegularTerm) : Prop :=
  t.ShapeWellFormed ranks ∧
    ∃ support ∈ (List.range t.nodes.length).sublists',
      t.GroundWitness support

public theorem groundWitnessCode_eq_true_iff
    (t : RegularTerm) (support : List ℕ) :
    t.groundWitnessCode support = true ↔ t.GroundWitness support := by
  simp only [groundWitnessCode, GroundWitness, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨hroot, hnodes⟩
    refine ⟨hroot, ?_⟩
    intro i hi
    have hnode := hnodes i hi
    cases h : t.nodeAt? i with
    | none => simp [h] at hnode
    | some node =>
        cases node with
        | inl x => simp [h] at hnode
        | inr app =>
            rcases app with ⟨X, children⟩
            refine ⟨X, children, rfl, ?_⟩
            simpa [h, List.all_eq_true] using hnode
  · rintro ⟨hroot, hnodes⟩
    refine ⟨hroot, ?_⟩
    intro i hi
    obtain ⟨X, children, hnode, hchildren⟩ := hnodes i hi
    simp only [hnode, List.all_eq_true]
    intro child hchild
    exact decide_eq_true (hchildren child hchild)

/-- Exactness of the finite support checker. -/
public theorem groundCode_eq_true_iff (ranks : List ℕ) (t : RegularTerm) :
    t.groundCode ranks = true ↔ t.Ground ranks := by
  simp [groundCode, Ground, ShapeWellFormed, List.any_eq_true,
    groundWitnessCode_eq_true_iff]

end RegularTerm

/-! ## Raw deterministic first-order grammars -/

/-- One rule row `(root symbol, action, right-hand side)`.  Variables in the RHS
refer positionally to the children of the rewritten root. -/
public abbrev RawRule (Action : Type) := ℕ × Action × RegularTerm

/-- Observable labels in the corrected first-order-grammar semantics.  Ordinary
grammar actions are on the left; `inr x` is the private label of variable `x`. -/
public abbrev Label (Action : Type) := Action ⊕ ℕ

namespace RawRule

@[expose] public def lhs (r : RawRule Action) : ℕ := r.1

@[expose] public def action (r : RawRule Action) : Action := r.2.1

@[expose] public def rhs (r : RawRule Action) : RegularTerm := r.2.2

end RawRule

/-- Finite raw syntax for a deterministic first-order grammar: a rank table and
an ordered rule table. -/
public def EncodedFirstOrderGrammar (Action : Type) :=
  List ℕ × List (RawRule Action)

namespace EncodedFirstOrderGrammar

variable {Action : Type}

public instance [Primcodable Action] :
    Primcodable (EncodedFirstOrderGrammar Action) :=
  inferInstanceAs (Primcodable (List ℕ × List (RawRule Action)))

public instance [DecidableEq Action] :
    DecidableEq (EncodedFirstOrderGrammar Action) :=
  inferInstanceAs (DecidableEq (List ℕ × List (RawRule Action)))

@[expose] public def ranks (g : EncodedFirstOrderGrammar Action) : List ℕ := g.1

@[expose] public def rawRules (g : EncodedFirstOrderGrammar Action) :
    List (RawRule Action) := g.2

/-- First-match lookup in the raw finite rule table. -/
@[expose] public def findRule [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (X : ℕ) (a : Action) :
    Option (RawRule Action) :=
  g.rawRules.find? fun r => r.lhs = X ∧ r.action = a

/-- First-match lookup, projected to the selected right-hand side. -/
@[expose] public def ruleLookup [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (X : ℕ) (a : Action) :
    Option RegularTerm :=
  (g.findRule X a).map RawRule.rhs

/-- A found row really occurs in the finite table. -/
public theorem findRule_mem [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} {X : ℕ} {a : Action}
    {r : RawRule Action} (h : g.findRule X a = some r) :
    r ∈ g.rawRules := by
  exact List.mem_of_find?_eq_some h

/-- A found row has the requested root symbol and action. -/
public theorem findRule_key [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} {X : ℕ} {a : Action}
    {r : RawRule Action} (h : g.findRule X a = some r) :
    r.lhs = X ∧ r.action = a := by
  unfold findRule at h
  have hkey := List.find?_some
    (p := fun row : RawRule Action => decide (row.lhs = X ∧ row.action = a))
    (a := r) (l := g.rawRules) h
  exact of_decide_eq_true hkey

/-- Check that a rule's root symbol exists and that its RHS uses exactly the
variables supplied by that root's declared rank. -/
@[expose] public def ruleWellFormedCode
    (g : EncodedFirstOrderGrammar Action) (r : RawRule Action) : Bool :=
  match g.ranks[r.lhs]? with
  | none => false
  | some rank =>
      r.rhs.wellFormedCode g.ranks rank && r.rhs.unfoldsFiniteCode

/-- Check pairwise uniqueness of `(root symbol, action)` keys.  This is the
mathematical determinism hypothesis used when specializing the corrected 2014
bisimilarity theorem to trace equivalence. -/
@[expose] public def actionDeterministicRulesCode [DecidableEq Action] :
    List (RawRule Action) → Bool
  | [] => true
  | r :: rules =>
      (rules.all fun s => decide (r.lhs ≠ s.lhs ∨ r.action ≠ s.action)) &&
        actionDeterministicRulesCode rules

/-- Executable action-determinism check for a raw grammar. -/
@[expose] public def actionDeterministicCode [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) : Bool :=
  actionDeterministicRulesCode g.rawRules

/-- No two raw rows have the same root/action key. -/
@[expose] public def ActionDeterministic [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) : Prop :=
  g.actionDeterministicCode = true

/-- Executable structural check for the complete finite grammar.  It checks both
finite, ranked right-hand sides and uniqueness of root/action keys. -/
@[expose] public def wellFormedCode [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) : Bool :=
  g.rawRules.all g.ruleWellFormedCode && g.actionDeterministicCode

/-- Purely syntactic well-formedness of an encoded grammar. -/
@[expose] public def WellFormed [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) : Prop :=
  g.wellFormedCode = true

/-! ## Labelled root rewriting and traces -/

/-- Execute one ordinary grammar-labelled root rewrite.  At an application root
`X(t₁,…,tₙ)`,
the first `X -a→ rhs` row is selected and `rhs` is instantiated by the child
subterms.  Variable roots and malformed roots are stuck. -/
@[expose] public def rootRewrite? [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (a : Action)
    (source : RegularTerm) : Option RegularTerm :=
  match source.rootApplication? with
  | none => none
  | some (X, children) =>
      (g.ruleLookup X a).map fun rhs =>
        rhs.instantiate (children.map source.withRoot)

/-- Execute one observable transition.  Besides ordinary root rewrites, a
variable root `x` has exactly the private self-loop labelled `inr x`, as in the
corrected 2014 semantics. -/
@[expose] public def step? [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (label : Label Action)
    (source : RegularTerm) : Option RegularTerm :=
  match label with
  | .inl a => g.rootRewrite? a source
  | .inr x =>
      match source.rootNode? with
      | some (.inl y) => if x = y then some source else none
      | _ => none

/-- Relational presentation of one labelled root rewrite. -/
@[expose] public def Step [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (a : Label Action)
    (source target : RegularTerm) : Prop :=
  g.step? a source = some target

/-- Run a finite action word from a term. -/
@[expose] public def run? [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) :
    List (Label Action) → RegularTerm → Option RegularTerm
  | [], source => some source
  | a :: word, source => (g.step? a source).bind (g.run? word)

/-- A labelled word takes `source` to `target`. -/
@[expose] public def Executes [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (source : RegularTerm)
    (word : List (Label Action)) (target : RegularTerm) : Prop :=
  g.run? word source = some target

/-- A word is a trace of `source` when all of its root rewrites are enabled. -/
@[expose] public def IsTrace [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (source : RegularTerm)
    (word : List (Label Action)) : Prop :=
  (g.run? word source).isSome = true

/-- The trace language of a regular term in a grammar. -/
@[expose] public def traceLanguage [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (source : RegularTerm) :
    Set (List (Label Action)) :=
  {word | g.IsTrace source word}

/-- The semantic equivalence decided by the deterministic first-order-grammar
route: equality of all finite traces. -/
@[expose] public def TraceEquivalent [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (left right : RegularTerm) : Prop :=
  g.traceLanguage left = g.traceLanguage right

@[simp] public theorem run?_nil [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (source : RegularTerm) :
    g.run? [] source = some source := rfl

@[simp] public theorem run?_cons [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (a : Label Action)
    (word : List (Label Action)) (source : RegularTerm) :
    g.run? (a :: word) source = (g.step? a source).bind (g.run? word) := rfl

/-- For a fixed source and action there is at most one successor. -/
public theorem step_deterministic [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} {a : Label Action}
    {source left right : RegularTerm}
    (hl : g.Step a source left) (hr : g.Step a source right) :
    left = right := by
  exact Option.some.inj (hl.symm.trans hr)

/-- A fixed action word also has at most one target. -/
public theorem executes_deterministic [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} {source : RegularTerm}
    {word : List (Label Action)} {left right : RegularTerm}
    (hl : g.Executes source word left) (hr : g.Executes source word right) :
    left = right := by
  exact Option.some.inj (hl.symm.trans hr)

/-- Traces are exactly words with a (necessarily unique) target. -/
public theorem isTrace_iff_exists_executes [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} {source : RegularTerm}
    {word : List (Label Action)} :
    g.IsTrace source word ↔ ∃ target, g.Executes source word target := by
  unfold IsTrace Executes
  cases g.run? word source <;> simp

/-- One action can be peeled from the front of a trace. -/
public theorem isTrace_cons_iff [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} {source : RegularTerm}
    {a : Label Action} {word : List (Label Action)} :
    g.IsTrace source (a :: word) ↔
      ∃ target, g.Step a source target ∧ g.IsTrace target word := by
  unfold IsTrace Step
  cases h : g.step? a source with
  | none => simp [h]
  | some target => simp [h]

/-- Executing concatenated words is Kleisli composition of their executions. -/
public theorem run?_append [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action)
    (first second : List (Label Action))
    (source : RegularTerm) :
    g.run? (first ++ second) source =
      (g.run? first source).bind (g.run? second) := by
  induction first generalizing source with
  | nil => rfl
  | cons a first ih =>
      simp only [List.cons_append, run?_cons]
      cases h : g.step? a source with
      | none => simp
      | some target => simpa [h] using ih target

/-- Trace equivalence is reflexive. -/
@[refl] public theorem traceEquivalent_refl [DecidableEq Action]
    (g : EncodedFirstOrderGrammar Action) (source : RegularTerm) :
    g.TraceEquivalent source source := rfl

/-- Trace equivalence is symmetric. -/
@[symm] public theorem TraceEquivalent.symm [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} {left right : RegularTerm}
    (h : g.TraceEquivalent left right) :
    g.TraceEquivalent right left := Eq.symm h

/-- Trace equivalence is transitive. -/
@[trans] public theorem TraceEquivalent.trans [DecidableEq Action]
    {g : EncodedFirstOrderGrammar Action} {left middle right : RegularTerm}
    (hlm : g.TraceEquivalent left middle)
    (hmr : g.TraceEquivalent middle right) :
    g.TraceEquivalent left right := Eq.trans hlm hmr

end EncodedFirstOrderGrammar

end DCFEquivalence
