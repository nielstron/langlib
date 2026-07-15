module

public import Langlib.Grammars.LR.Definition
public import Mathlib

@[expose]
public section

/-!
# Finite canonical LR(k) items

This file supplies the finite data used by the canonical viable-prefix
automaton.  Productions are represented by positions in the grammar's rule
list, rather than by their (possibly infinitely typed) nonterminals.  Thus the
item and parser-state types are finite without imposing a `Fintype` instance on
the grammar's nonterminal type.
-/

open Language

namespace CF_grammar.LRk

variable {T : Type}

/-- A production occurrence in the finite rule list. -/
public abbrev RuleIndex (G : CF_grammar T) := Fin G.rules.length

/-- The production represented by a rule-list index. -/
@[expose]
public def ruleAt (G : CF_grammar T) (i : RuleIndex G) :
    G.nt × List (symbol T G.nt) :=
  G.rules.get i

@[simp]
public theorem ruleAt_mem (G : CF_grammar T) (i : RuleIndex G) :
    ruleAt G i ∈ G.rules :=
  List.get_mem G.rules i

/-- A dot position in a production, including the completed position just past
the right-hand side. -/
public abbrev Position (G : CF_grammar T) (i : RuleIndex G) :=
  Fin ((ruleAt G i).2.length + 1)

/-- Exactly `k` symbols of terminal lookahead.  `none` is the explicit
end-of-input marker; after the first `none`, all semantically reachable
lookaheads are also `none`.  Keeping the ambient function type unrestricted
makes finiteness immediate, while well-formedness is enforced by the semantic
relations below. -/
public abbrev Lookahead (T : Type) (k : ℕ) := Fin k → Option T

/-- Observe the first `k` terminals of a suffix, padding with the explicit EOF
marker. -/
@[expose]
public def observe (k : ℕ) (w : List T) : Lookahead T k :=
  fun i => w[i.val]?

/-- The all-EOF lookahead. -/
@[expose]
public def eofLookahead (T : Type) (k : ℕ) : Lookahead T k :=
  fun _ => none

/-- Prefix a finite terminal word to a padded lookahead. -/
@[expose]
public def prependLookahead (k : ℕ) (z : List T) (u : Lookahead T k) :
    Lookahead T k :=
  fun i =>
    if h : i.val < z.length then
      z[i.val]?
    else
      u ⟨i.val - z.length, by omega⟩

@[simp]
public theorem observe_append (k : ℕ) (z s : List T) :
    observe k (z ++ s) = prependLookahead k z (observe k s) := by
  funext i
  simp only [observe, prependLookahead, List.getElem?_append]
  split <;> rfl

/-- A canonical LR item `[A → α · β, u]`.

The first component identifies the production, the second its dot position,
and the third the padded terminal lookahead. -/
public abbrev Item (G : CF_grammar T) (k : ℕ) :=
  Σ i : RuleIndex G, Position G i × Lookahead T k

public noncomputable instance instFintypeItem [Fintype T]
    (G : CF_grammar T) (k : ℕ) : Fintype (Item G k) := by
  classical
  exact @Sigma.instFintype (RuleIndex G)
    (fun i => Position G i × Lookahead T k)
    (fun _ => inferInstance) inferInstance

/-- The production index of an item. -/
@[expose]
public def Item.rule {G : CF_grammar T} {k : ℕ} (i : Item G k) : RuleIndex G :=
  i.1

/-- The dot position of an item. -/
@[expose]
public def Item.position {G : CF_grammar T} {k : ℕ} (i : Item G k) :
    Position G i.rule :=
  i.2.1

/-- The terminal lookahead of an item. -/
@[expose]
public def Item.lookahead {G : CF_grammar T} {k : ℕ} (i : Item G k) :
    Lookahead T k :=
  i.2.2

/-- Symbols before the dot. -/
@[expose]
public def Item.before {G : CF_grammar T} {k : ℕ} (i : Item G k) :
    List (symbol T G.nt) :=
  (ruleAt G i.rule).2.take i.position.val

/-- Symbols at and after the dot. -/
@[expose]
public def Item.after {G : CF_grammar T} {k : ℕ} (i : Item G k) :
    List (symbol T G.nt) :=
  (ruleAt G i.rule).2.drop i.position.val

/-- The symbol immediately after the dot, if any. -/
@[expose]
public def Item.next? {G : CF_grammar T} {k : ℕ} (i : Item G k) :
    Option (symbol T G.nt) :=
  (ruleAt G i.rule).2[i.position.val]?

/-- An item is complete when its dot is just past the right-hand side. -/
@[expose]
public def Item.Complete {G : CF_grammar T} {k : ℕ} (i : Item G k) : Prop :=
  i.position.val = (ruleAt G i.rule).2.length

/-- Relational dot advancement.  A relational presentation avoids dependent
casts between the position types while retaining a finite decidable relation. -/
@[expose]
public def Advances {G : CF_grammar T} {k : ℕ}
    (i : Item G k) (X : symbol T G.nt) (j : Item G k) : Prop :=
  j.rule = i.rule ∧
    j.position.val = i.position.val + 1 ∧
    i.next? = some X ∧
    j.lookahead = i.lookahead

/-- The right-hand suffix after the nonterminal immediately following an
item's dot. -/
@[expose]
public def Item.afterNext {G : CF_grammar T} {k : ℕ} (i : Item G k) :
    List (symbol T G.nt) :=
  i.after.drop 1

/-- A lookahead `v` can follow a just-opened nonterminal when the remaining
sentential suffix is `beta` and the enclosing item has lookahead `u`.

This semantic `FIRST_k` relation is deliberately stated with rightmost
derivations.  It is a finite decidable table by classical choice because its
arguments range over the finite item universe. -/
@[expose]
public def CanFollow (G : CF_grammar T) (k : ℕ)
    (beta : List (symbol T G.nt)) (u v : Lookahead T k) : Prop :=
  ∃ z : List T,
    G.DerivesRightmost beta (z.map symbol.terminal) ∧
      prependLookahead k z u = v

/-- One epsilon-closure edge between canonical items. -/
@[expose]
public def ClosureStep (G : CF_grammar T) (k : ℕ)
    (i j : Item G k) : Prop :=
  i.next? = some (symbol.nonterminal (ruleAt G j.rule).1) ∧
    j.position.val = 0 ∧
    CanFollow G k i.afterNext i.lookahead j.lookahead

/-- Epsilon closure of a finite item set. -/
@[expose]
public noncomputable def closure [Fintype T] (G : CF_grammar T) (k : ℕ)
    (I : Finset (Item G k)) : Finset (Item G k) := by
  classical
  exact Finset.univ.filter fun j =>
    ∃ i ∈ I, Relation.ReflTransGen (ClosureStep G k) i j

@[simp]
public theorem mem_closure [Fintype T] (G : CF_grammar T) (k : ℕ)
    (I : Finset (Item G k)) (j : Item G k) :
    j ∈ closure G k I ↔
      ∃ i ∈ I, Relation.ReflTransGen (ClosureStep G k) i j := by
  classical
  simp [closure]

public theorem subset_closure [Fintype T] (G : CF_grammar T) (k : ℕ)
    (I : Finset (Item G k)) : I ⊆ closure G k I := by
  intro i hi
  exact (mem_closure G k I i).2 ⟨i, hi, Relation.ReflTransGen.refl⟩

@[simp]
public theorem closure_closure [Fintype T] (G : CF_grammar T) (k : ℕ)
    (I : Finset (Item G k)) :
    closure G k (closure G k I) = closure G k I := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨x, hx, hxj⟩ := (mem_closure G k (closure G k I) j).1 hj
    obtain ⟨i, hi, hix⟩ := (mem_closure G k I x).1 hx
    exact (mem_closure G k I j).2 ⟨i, hi, hix.trans hxj⟩
  · intro hj
    exact (mem_closure G k (closure G k I) j).2
      ⟨j, hj, Relation.ReflTransGen.refl⟩

/-- Canonical goto on one grammar symbol. -/
@[expose]
public noncomputable def goto [Fintype T] (G : CF_grammar T) (k : ℕ)
    (I : Finset (Item G k)) (X : symbol T G.nt) : Finset (Item G k) := by
  classical
  exact Finset.univ.filter fun j =>
    ∃ i ∈ closure G k I, Advances i X j

@[simp]
public theorem mem_goto [Fintype T] (G : CF_grammar T) (k : ℕ)
    (I : Finset (Item G k)) (X : symbol T G.nt) (j : Item G k) :
    j ∈ goto G k I X ↔
      ∃ i ∈ closure G k I, Advances i X j := by
  classical
  simp [goto]

end CF_grammar.LRk
