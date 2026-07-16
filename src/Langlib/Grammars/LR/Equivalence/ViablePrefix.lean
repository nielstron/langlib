module

public import Langlib.Grammars.LR.Equivalence.Items

@[expose]
public section

/-!
# Semantic validity of canonical LR(k) items

An item `[A → alpha · beta, u]` is valid for a prefix `gamma` when a
rightmost derivation reaches `p A s`, `gamma = p alpha`, and `u` is the
EOF-padded `k`-lookahead of `s`.  This file establishes the easy (soundness)
half of the canonical viable-prefix theorem: item closure and goto preserve
that semantic invariant.
-/

open Language

namespace CF_grammar.LRk

variable {T : Type}

/-! ## Context closure of rightmost derivations -/

public theorem rewritesRightmost_append_left {N : Type}
    {r : N × List (symbol T N)} {u v : List (symbol T N)}
    (h : CF_grammar.RewritesRightmost r u v) (pre : List (symbol T N)) :
    CF_grammar.RewritesRightmost r (pre ++ u) (pre ++ v) := by
  rcases h with ⟨p, s, hu, hv⟩
  refine ⟨pre ++ p, s, ?_, ?_⟩ <;>
    simp [hu, hv, List.append_assoc]

public theorem producesRightmost_append_left (G : CF_grammar T)
    {u v : List (symbol T G.nt)} (h : G.ProducesRightmost u v)
    (pre : List (symbol T G.nt)) :
    G.ProducesRightmost (pre ++ u) (pre ++ v) := by
  rcases h with ⟨r, hr, hrewrite⟩
  exact ⟨r, hr, rewritesRightmost_append_left hrewrite pre⟩

public theorem derivesRightmost_append_left (G : CF_grammar T)
    {u v : List (symbol T G.nt)} (h : G.DerivesRightmost u v)
    (pre : List (symbol T G.nt)) :
    G.DerivesRightmost (pre ++ u) (pre ++ v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (producesRightmost_append_left G hstep pre)

public theorem rewritesRightmost_append_terminals_right {N : Type}
    {r : N × List (symbol T N)} {u v : List (symbol T N)}
    (h : CF_grammar.RewritesRightmost r u v) (suffix : List T) :
    CF_grammar.RewritesRightmost r
      (u ++ suffix.map symbol.terminal)
      (v ++ suffix.map symbol.terminal) := by
  rcases h with ⟨p, s, hu, hv⟩
  refine ⟨p, s ++ suffix, ?_, ?_⟩ <;>
    simp [hu, hv, List.map_append, List.append_assoc]

public theorem producesRightmost_append_terminals_right (G : CF_grammar T)
    {u v : List (symbol T G.nt)} (h : G.ProducesRightmost u v)
    (suffix : List T) :
    G.ProducesRightmost
      (u ++ suffix.map symbol.terminal)
      (v ++ suffix.map symbol.terminal) := by
  rcases h with ⟨r, hr, hrewrite⟩
  exact ⟨r, hr, rewritesRightmost_append_terminals_right hrewrite suffix⟩

public theorem derivesRightmost_append_terminals_right (G : CF_grammar T)
    {u v : List (symbol T G.nt)} (h : G.DerivesRightmost u v)
    (suffix : List T) :
    G.DerivesRightmost
      (u ++ suffix.map symbol.terminal)
      (v ++ suffix.map symbol.terminal) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (producesRightmost_append_terminals_right G hstep suffix)

/-! ## Item decomposition -/

/-- If the dot is followed by `X`, the production splits into the prefix before
the dot, `X`, and the suffix after `X`. -/
public theorem Item.rule_eq_before_next_afterNext {G : CF_grammar T} {k : ℕ}
    (i : Item G k) {X : symbol T G.nt} (hnext : i.next? = some X) :
    (ruleAt G i.rule).2 = i.before ++ [X] ++ i.afterNext := by
  have hlt : i.position.val < (ruleAt G i.rule).2.length :=
    (List.getElem?_eq_some_iff.mp hnext).choose
  have hget : (ruleAt G i.rule).2[i.position.val] = X :=
    (List.getElem?_eq_some_iff.mp hnext).choose_spec
  rw [← List.take_append_drop i.position.val (ruleAt G i.rule).2]
  rw [List.drop_eq_getElem_cons hlt, hget]
  simp [Item.before, Item.afterNext, Item.after, List.drop_drop,
    Nat.add_comm]

/-- Advancing an item appends exactly the traversed symbol to its before-dot
prefix. -/
public theorem before_eq_of_advances {G : CF_grammar T} {k : ℕ}
    {i j : Item G k} {X : symbol T G.nt} (h : Advances i X j) :
    j.before = i.before ++ [X] := by
  rcases h with ⟨hrule, hpos, hnext, _⟩
  have htake := List.take_add_one (l := (ruleAt G i.rule).2) (i := i.position.val)
  have hnext' : (ruleAt G i.rule).2[i.position.val]? = some X := by
    simpa [Item.next?] using hnext
  rw [hnext'] at htake
  simp at htake
  unfold Item.before
  let n : ℕ := j.position.val
  change List.take n (ruleAt G j.rule).2 = i.before ++ [X]
  have hn : n = i.position.val + 1 := hpos
  have hrhs : (ruleAt G j.rule).2 = (ruleAt G i.rule).2 :=
    congrArg (fun r => (ruleAt G r).2) hrule
  rw [hrhs, hn]
  change List.take (i.position.val + 1) (ruleAt G i.rule).2 =
    List.take i.position.val (ruleAt G i.rule).2 ++ [X]
  exact htake

/-! ## Semantic validity -/

/-- Semantic validity of an LR item for an already scanned grammar-symbol
prefix. -/
@[expose]
public def Valid (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.nt)) (i : Item G k) : Prop :=
  ∃ (p : List (symbol T G.nt)) (s : List T),
    G.DerivesRightmost [symbol.nonterminal G.initial]
      (p ++ [symbol.nonterminal (ruleAt G i.rule).1] ++
        s.map symbol.terminal) ∧
    gamma = p ++ i.before ∧
    observe k s = i.lookahead

/-- The finite set of all semantically valid items at a prefix. -/
@[expose]
public noncomputable def validItems [Fintype T] (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.nt)) : Finset (Item G k) := by
  classical
  exact Finset.univ.filter (Valid G k gamma)

@[simp]
public theorem mem_validItems [Fintype T] (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.nt)) (i : Item G k) :
    i ∈ validItems G k gamma ↔ Valid G k gamma i := by
  classical
  simp [validItems]

/-- Applying the production named by a valid item reaches its complete
right-sentential form. -/
public theorem Valid.apply_rule {G : CF_grammar T} {k : ℕ}
    {gamma : List (symbol T G.nt)} {i : Item G k}
    (hi : Valid G k gamma i) :
    ∃ (p : List (symbol T G.nt)) (s : List T),
      gamma = p ++ i.before ∧
      observe k s = i.lookahead ∧
      G.DerivesRightmost [symbol.nonterminal G.initial]
        (p ++ (ruleAt G i.rule).2 ++ s.map symbol.terminal) := by
  rcases hi with ⟨p, s, hpre, hgamma, hlook⟩
  refine ⟨p, s, hgamma, hlook, hpre.tail ?_⟩
  exact ⟨ruleAt G i.rule, ruleAt_mem G i.rule, p, s, rfl, rfl⟩

/-- One item-closure edge preserves semantic validity at the same prefix. -/
public theorem Valid.closureStep {G : CF_grammar T} {k : ℕ}
    {gamma : List (symbol T G.nt)} {i j : Item G k}
    (hi : Valid G k gamma i) (hij : ClosureStep G k i j) :
    Valid G k gamma j := by
  rcases hi with ⟨p, s, hpre, hgamma, hlook⟩
  rcases hij with ⟨hnext, hjzero, z, hzder, hzlook⟩
  have hrule := i.rule_eq_before_next_afterNext hnext
  have hafter : i.afterNext =
      (ruleAt G i.rule).2.drop (i.position.val + 1) := by
    simp [Item.afterNext, Item.after, List.drop_drop, Nat.add_comm]
  have hproduced :
      G.DerivesRightmost [symbol.nonterminal G.initial]
        (p ++ (ruleAt G i.rule).2 ++ s.map symbol.terminal) := by
    exact hpre.tail
      ⟨ruleAt G i.rule, ruleAt_mem G i.rule, p, s, rfl, rfl⟩
  have htail :
      G.DerivesRightmost
        (i.afterNext ++ s.map symbol.terminal)
        ((z ++ s).map symbol.terminal) := by
    have hz := derivesRightmost_append_terminals_right G hzder s
    simpa [List.map_append] using hz
  have hlift := derivesRightmost_append_left G htail
    (gamma ++ [symbol.nonterminal (ruleAt G j.rule).1])
  refine ⟨gamma, z ++ s, ?_, ?_, ?_⟩
  · have hshape :
        p ++ (ruleAt G i.rule).2 ++ s.map symbol.terminal =
          gamma ++ [symbol.nonterminal (ruleAt G j.rule).1] ++
            (i.afterNext ++ s.map symbol.terminal) := by
      rw [hrule, hgamma]
      simp [List.append_assoc]
    rw [← hshape] at hlift
    simpa [List.map_append, List.append_assoc] using hproduced.trans hlift
  · simp [Item.before, hjzero]
  · rw [observe_append, hlook, hzlook]

/-- The whole finite epsilon closure preserves semantic validity. -/
public theorem Valid.of_mem_closure [Fintype T] {G : CF_grammar T} {k : ℕ}
    {gamma : List (symbol T G.nt)} {I : Finset (Item G k)}
    (hI : ∀ i ∈ I, Valid G k gamma i) {j : Item G k}
    (hj : j ∈ closure G k I) : Valid G k gamma j := by
  obtain ⟨i, hi, hij⟩ := (mem_closure G k I j).1 hj
  have hreach : ∀ {x y : Item G k},
      Relation.ReflTransGen (ClosureStep G k) x y →
      Valid G k gamma x → Valid G k gamma y := by
    intro x y hxy hx
    induction hxy with
    | refl => exact hx
    | tail _ hstep ih => exact ih.closureStep hstep
  exact hreach hij (hI i hi)

/-- A goto edge advances semantic validity by the traversed grammar symbol. -/
public theorem Valid.goto [Fintype T] {G : CF_grammar T} {k : ℕ}
    {gamma : List (symbol T G.nt)} {I : Finset (Item G k)}
    (hI : ∀ i ∈ I, Valid G k gamma i)
    {X : symbol T G.nt} {j : Item G k} (hj : j ∈ goto G k I X) :
    Valid G k (gamma ++ [X]) j := by
  obtain ⟨i, hi, hij⟩ := (mem_goto G k I X j).1 hj
  have hvalid := Valid.of_mem_closure hI hi
  rcases hvalid with ⟨p, s, hpre, hgamma, hlook⟩
  refine ⟨p, s, ?_, ?_, ?_⟩
  · simpa [hij.1] using hpre
  · rw [before_eq_of_advances hij, hgamma]
    simp [List.append_assoc]
  · exact hlook.trans hij.2.2.2.symm

end CF_grammar.LRk
