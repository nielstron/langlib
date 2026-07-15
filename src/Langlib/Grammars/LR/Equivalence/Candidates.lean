module

public import Langlib.Grammars.LR.Equivalence.Automaton
public import Langlib.Grammars.LR.Equivalence.Conflicts

@[expose]
public section

/-!
# Reduction and shift candidates in canonical item states

Complete valid items give semantic reduction candidates.  A valid item whose
dot precedes a terminal gives a genuine later handle whenever the remainder of
its production can derive a terminal word.  The latter proof follows that
rightmost derivation to its final step; this is what turns an ordinary shift
item into exactly the second handle required by Knuth's semantic LR(k)
condition.
-/

open Language

namespace CF_grammar.LRk

variable {T : Type}

/-- A complete valid item is a semantic reduction candidate. -/
public theorem Valid.reductionCandidate {G : CF_grammar T} {k : ℕ}
    {gamma : List (symbol T G.nt)} {u : Lookahead T k} {i : Item G k}
    (hi : Valid G k gamma i) (hcomplete : i.Complete)
    (hlook : i.lookahead = u) :
    ReductionCandidate G k gamma u (ruleAt G i.rule) := by
  rcases hi with ⟨p, s, hder, hgamma, hiLook⟩
  refine ⟨ruleAt_mem G i.rule, p, s, hder, ?_, ?_⟩
  · have hbefore : i.before = (ruleAt G i.rule).2 := by
      unfold Item.before
      rw [hcomplete, List.take_length]
    rw [hgamma, hbefore]
  · exact hiLook.trans hlook

/-- Semantic data attached to a shift item.  `z` is the terminal yield of the
production suffix after the shifted terminal; consequently `a :: z`, followed
by the item's own lookahead, is the current input lookahead. -/
@[expose]
public def ShiftItemCandidate (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.nt)) (u : Lookahead T k) (a : T)
    (i : Item G k) : Prop :=
  Valid G k gamma i ∧
    i.next? = some (symbol.terminal a) ∧
    ∃ z : List T,
      G.DerivesRightmost i.afterNext (z.map symbol.terminal) ∧
      prependLookahead k (a :: z) i.lookahead = u

/-- A semantic shift item supplies a later handle in the precise form consumed
by `CoreIsLRk.not_reductionCandidate_and_laterHandleCandidate`. -/
public theorem ShiftItemCandidate.laterHandleCandidate
    {G : CF_grammar T} {k : ℕ} {gamma : List (symbol T G.nt)}
    {u : Lookahead T k} {a : T} {i : Item G k}
    (hi : ShiftItemCandidate G k gamma u a i) :
    LaterHandleCandidate G k gamma u := by
  rcases hi with ⟨hvalid, hnext, z, hz, hbuffer⟩
  rcases hvalid with ⟨p, s, hpre, hgamma, hitemLook⟩
  have hrule := i.rule_eq_before_next_afterNext hnext
  have hproduced :
      G.DerivesRightmost [symbol.nonterminal G.initial]
        (p ++ (ruleAt G i.rule).2 ++ s.map symbol.terminal) := by
    exact hpre.tail
      ⟨ruleAt G i.rule, ruleAt_mem G i.rule, p, s, rfl, rfl⟩
  have hlook : observe k (a :: z ++ s) = u := by
    rw [show a :: z ++ s = (a :: z) ++ s by rfl, observe_append,
      hitemLook, hbuffer]
  rcases Relation.ReflTransGen.cases_tail hz with hzeq | ⟨beta', hbeta, hstep⟩
  ·
      refine ⟨ruleAt G i.rule, ruleAt_mem G i.rule,
        p, s, a :: z ++ s, a, i.afterNext, hpre, ?_, ?_, hlook⟩
      · rw [hrule, hgamma]
        simp [List.append_assoc]
      · rw [hrule, hgamma]
        simp [List.map_append, hzeq, List.append_assoc]
  ·
      rcases hstep with ⟨r, hr, q, t, hsource, htarget⟩
      have htail := derivesRightmost_append_terminals_right G hbeta s
      have hlift := derivesRightmost_append_left G htail
        (gamma ++ [symbol.terminal a])
      have hshape :
          p ++ (ruleAt G i.rule).2 ++ s.map symbol.terminal =
            gamma ++ [symbol.terminal a] ++
              (i.afterNext ++ s.map symbol.terminal) := by
        rw [hrule, hgamma]
        simp [List.append_assoc]
      rw [← hshape] at hlift
      have htoSource :
          G.DerivesRightmost [symbol.nonterminal G.initial]
            ((gamma ++ [symbol.terminal a] ++ q) ++
              [symbol.nonterminal r.1] ++
              (t ++ s).map symbol.terminal) := by
        have hrun := hproduced.trans hlift
        rw [hsource] at hrun
        simpa [List.map_append, List.append_assoc] using hrun
      refine ⟨r, hr, gamma ++ [symbol.terminal a] ++ q,
        t ++ s, a :: z ++ s, a, q ++ r.2,
        htoSource, ?_, ?_, hlook⟩
      · simp [List.append_assoc]
      · simp [List.map_append, List.append_assoc, htarget]

/-- A reduction exposed by a canonical item state. -/
@[expose]
public def StateReduction [Fintype T] (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.augment.nt)) (u : Lookahead T k)
    (r : G.augment.nt × List (symbol T G.augment.nt)) : Prop :=
  ∃ i ∈ itemState G k gamma,
    i.Complete ∧ i.lookahead = u ∧ ruleAt G.augment i.rule = r

/-- A terminal shift exposed by a canonical item state, filtered by productive
continuation and the complete `k`-symbol input buffer. -/
@[expose]
public def StateShift [Fintype T] (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.augment.nt)) (u : Lookahead T k)
    (a : T) : Prop :=
  ∃ i ∈ itemState G k gamma,
    i.next? = some (symbol.terminal a) ∧
    ∃ z : List T,
      G.augment.DerivesRightmost i.afterNext (z.map symbol.terminal) ∧
      prependLookahead k (a :: z) i.lookahead = u

public theorem StateReduction.reductionCandidate [Fintype T]
    {G : CF_grammar T} {k : ℕ} {gamma : List (symbol T G.augment.nt)}
    {u : Lookahead T k} {r : G.augment.nt × List (symbol T G.augment.nt)}
    (h : StateReduction G k gamma u r) :
    ReductionCandidate G.augment k gamma u r := by
  rcases h with ⟨i, hi, hcomplete, hlook, hrule⟩
  subst r
  exact (itemState_valid G k gamma hi).reductionCandidate hcomplete hlook

public theorem StateShift.laterHandleCandidate [Fintype T]
    {G : CF_grammar T} {k : ℕ} {gamma : List (symbol T G.augment.nt)}
    {u : Lookahead T k} {a : T} (h : StateShift G k gamma u a) :
    LaterHandleCandidate G.augment k gamma u := by
  rcases h with ⟨i, hi, hnext, z, hz, hlook⟩
  exact ShiftItemCandidate.laterHandleCandidate
    ⟨itemState_valid G k gamma hi, hnext, z, hz, hlook⟩

/-- At a canonical state and fixed lookahead, an LR(k) augmented grammar cannot
both reduce and shift. -/
public theorem IsLRk.not_stateReduction_and_stateShift [Fintype T]
    {G : CF_grammar T} {k : ℕ} (hLR : G.IsLRk k)
    {gamma : List (symbol T G.augment.nt)} {u : Lookahead T k}
    {r : G.augment.nt × List (symbol T G.augment.nt)}
    (hred : StateReduction G k gamma u r) {a : T} :
    ¬ StateShift G k gamma u a := by
  intro hshift
  exact CoreIsLRk.not_reductionCandidate_and_laterHandleCandidate
    (G := G.augment) hLR hred.reductionCandidate
      hshift.laterHandleCandidate

/-- Reductions exposed by a canonical LR(k) state are unique. -/
public theorem IsLRk.stateReduction_unique [Fintype T]
    {G : CF_grammar T} {k : ℕ} (hLR : G.IsLRk k)
    {gamma : List (symbol T G.augment.nt)} {u : Lookahead T k}
    {r₁ r₂ : G.augment.nt × List (symbol T G.augment.nt)}
    (h₁ : StateReduction G k gamma u r₁)
    (h₂ : StateReduction G k gamma u r₂) : r₁ = r₂ :=
  CoreIsLRk.reductionCandidate_unique (G := G.augment) hLR
    h₁.reductionCandidate h₂.reductionCandidate

end CF_grammar.LRk
