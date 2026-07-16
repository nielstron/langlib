module

public import Langlib.Grammars.LR.Equivalence.ViablePrefix

@[expose]
public section

/-!
# Initial item of an augmented grammar

The fresh-start rule is the head of the augmented grammar's rule list.  This
file records its finite rule index and the canonical item
`[S' -> . S, EOF^k]`, and proves the semantic validity of the initial item
closure.
-/

open Language

namespace CF_grammar.LRk

variable {T : Type}

/-- The rule-list index of the distinguished augmentation rule. -/
@[expose]
public def startRuleIndex (G : CF_grammar T) : RuleIndex G.augment :=
  ⟨0, by simp [CF_grammar.augment]⟩

@[simp]
public theorem ruleAt_startRuleIndex (G : CF_grammar T) :
    ruleAt G.augment (startRuleIndex G) = G.augmentStartRule := by
  simp [ruleAt, startRuleIndex, CF_grammar.augment]

/-- The canonical kernel item `[S' -> . S, EOF^k]`. -/
@[expose]
public def startItem (G : CF_grammar T) (k : ℕ) : Item G.augment k :=
  ⟨startRuleIndex G,
    ⟨⟨0, by simp [ruleAt_startRuleIndex, CF_grammar.augmentStartRule]⟩,
      eofLookahead T k⟩⟩

@[simp]
public theorem startItem_rule (G : CF_grammar T) (k : ℕ) :
    (startItem G k).rule = startRuleIndex G := rfl

@[simp]
public theorem startItem_position (G : CF_grammar T) (k : ℕ) :
    (startItem G k).position.val = 0 := rfl

@[simp]
public theorem startItem_lookahead (G : CF_grammar T) (k : ℕ) :
    (startItem G k).lookahead = eofLookahead T k := rfl

@[simp]
public theorem startItem_before (G : CF_grammar T) (k : ℕ) :
    (startItem G k).before = [] := by
  change List.take 0 (ruleAt G.augment (startRuleIndex G)).2 = []
  rfl

@[simp]
public theorem startItem_next (G : CF_grammar T) (k : ℕ) :
    (startItem G k).next? =
      some (symbol.nonterminal (some G.initial)) := by
  change (ruleAt G.augment (startRuleIndex G)).2[0]? =
    some (symbol.nonterminal (some G.initial))
  rw [ruleAt_startRuleIndex]
  rfl

@[simp]
public theorem observe_nil (k : ℕ) :
    observe k ([] : List T) = eofLookahead T k := by
  funext i
  simp [observe, eofLookahead]

/-- The fresh-start item is semantically valid before scanning any grammar
symbol. -/
public theorem startItem_valid (G : CF_grammar T) (k : ℕ) :
    Valid G.augment k [] (startItem G k) := by
  refine ⟨[], [], ?_, ?_, ?_⟩
  · simpa [ruleAt_startRuleIndex, CF_grammar.augmentStartRule] using
      (Relation.ReflTransGen.refl :
        G.augment.DerivesRightmost
          [symbol.nonterminal G.augment.initial]
          [symbol.nonterminal G.augment.initial])
  · simp
  · simp

/-- The raw kernel of the canonical viable-prefix automaton. -/
@[expose]
public def startKernel (G : CF_grammar T) (k : ℕ) : Finset (Item G.augment k) :=
  {startItem G k}

/-- Every item in the epsilon closure of the start kernel is valid at the empty
prefix. -/
public theorem startClosure_valid [Fintype T] (G : CF_grammar T) (k : ℕ)
    {i : Item G.augment k} (hi : i ∈ closure G.augment k (startKernel G k)) :
    Valid G.augment k [] i := by
  apply Valid.of_mem_closure (I := startKernel G k) (j := i) ?_ hi
  intro j hj
  have : j = startItem G k := Finset.mem_singleton.mp hj
  subst j
  exact startItem_valid G k

end CF_grammar.LRk
