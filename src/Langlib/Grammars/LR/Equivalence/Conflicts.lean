module

public import Langlib.Grammars.LR.Equivalence.ViablePrefix

@[expose]
public section

/-!
# Semantic conflict freedom for LR(k) grammars

This file packages the two direct consequences of Knuth's handle-uniqueness
condition needed by a deterministic bottom-up parser.  A reduction candidate
is a handle ending at the current prefix.  A later-handle candidate witnesses
that the handle ending in the same right-sentential form lies strictly to the
right of that prefix.  `CoreIsLRk` makes reductions unique and rules out a
reduction/later-handle conflict at equal lookahead.
-/

open Language

namespace CF_grammar.LRk

variable {T : Type}

/-- Equality of padded `k`-observations implies equality of the usual
length-at-most-`k` terminal prefixes. -/
public theorem lrLookahead_eq_of_observe_eq {k : ℕ} {u v : List T}
    (h : observe k u = observe k v) :
    CF_grammar.lrLookahead k u = CF_grammar.lrLookahead k v := by
  apply List.ext_getElem?
  intro i
  simp only [CF_grammar.lrLookahead, List.getElem?_take]
  by_cases hi : i < k
  · simp only [hi, ↓reduceIte]
    simpa [observe] using congrFun h (⟨i, hi⟩ : Fin k)
  · simp [hi]

/-- A production is reducible at `gamma` with padded lookahead `u` when a
rightmost derivation has reached its left-hand nonterminal and applying the
production ends exactly at `gamma`. -/
@[expose]
public def ReductionCandidate (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.nt)) (u : Lookahead T k)
    (r : G.nt × List (symbol T G.nt)) : Prop :=
  r ∈ G.rules ∧
    ∃ (p : List (symbol T G.nt)) (s : List T),
      G.DerivesRightmost [symbol.nonterminal G.initial]
        (p ++ [symbol.nonterminal r.1] ++ s.map symbol.terminal) ∧
      gamma = p ++ r.2 ∧
      observe k s = u

/-- A handle lies genuinely later than `gamma` in a right-sentential form
whose terminal suffix has padded lookahead `u`.  The displayed terminal `a`
is the first grammar symbol beyond `gamma`; retaining it makes strictness
structural rather than an inequality on lengths. -/
@[expose]
public def LaterHandleCandidate (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.nt)) (u : Lookahead T k) : Prop :=
  ∃ (r : G.nt × List (symbol T G.nt)), r ∈ G.rules ∧
    ∃ (p : List (symbol T G.nt)) (s y : List T)
      (a : T) (delta : List (symbol T G.nt)),
      G.DerivesRightmost [symbol.nonterminal G.initial]
        (p ++ [symbol.nonterminal r.1] ++ s.map symbol.terminal) ∧
      p ++ r.2 = gamma ++ symbol.terminal a :: delta ∧
      p ++ r.2 ++ s.map symbol.terminal =
        gamma ++ y.map symbol.terminal ∧
      observe k y = u

/-- Two reductions enabled at the same prefix and lookahead use the same
production (and, internally, the same handle position). -/
public theorem CoreIsLRk.reductionCandidate_unique {G : CF_grammar T} {k : ℕ}
    (hLR : G.CoreIsLRk k) {gamma : List (symbol T G.nt)}
    {u : Lookahead T k} {r₁ r₂ : G.nt × List (symbol T G.nt)}
    (h₁ : ReductionCandidate G k gamma u r₁)
    (h₂ : ReductionCandidate G k gamma u r₂) : r₁ = r₂ := by
  rcases h₁ with ⟨hr₁, p₁, s₁, hd₁, hgamma₁, hlook₁⟩
  rcases h₂ with ⟨hr₂, p₂, s₂, hd₂, hgamma₂, hlook₂⟩
  have hform :
      p₂ ++ r₂.2 ++ s₂.map symbol.terminal =
        p₁ ++ r₁.2 ++ s₂.map symbol.terminal := by
    rw [← hgamma₂, ← hgamma₁]
  have hlook : CF_grammar.lrLookahead k s₁ =
      CF_grammar.lrLookahead k s₂ :=
    lrLookahead_eq_of_observe_eq (hlook₁.trans hlook₂.symm)
  exact (hLR r₁ r₂ hr₁ hr₂ p₁ p₂ s₁ s₂ s₂ hd₁ hd₂ hform hlook).2

/-- An LR(k) reduction cannot coexist with a handle ending strictly later in
the same right-sentential form at the same lookahead.  This is the semantic
shift/reduce-conflict theorem; unlike reduce/reduce uniqueness, it uses the
full sentential-form equality in `CoreIsLRk`. -/
public theorem CoreIsLRk.not_reductionCandidate_and_laterHandleCandidate
    {G : CF_grammar T} {k : ℕ} (hLR : G.CoreIsLRk k)
    {gamma : List (symbol T G.nt)} {u : Lookahead T k}
    {r₁ : G.nt × List (symbol T G.nt)}
    (hred : ReductionCandidate G k gamma u r₁) :
    ¬ LaterHandleCandidate G k gamma u := by
  intro hlater
  rcases hred with ⟨hr₁, p₁, s₁, hd₁, hgamma, hlook₁⟩
  rcases hlater with
    ⟨r₂, hr₂, p₂, s₂, y, a, delta, hd₂, hstrict, hform, hlook₂⟩
  have hform' :
      p₂ ++ r₂.2 ++ s₂.map symbol.terminal =
        p₁ ++ r₁.2 ++ y.map symbol.terminal := by
    simpa [hgamma] using hform
  have hlook : CF_grammar.lrLookahead k s₁ =
      CF_grammar.lrLookahead k y :=
    lrLookahead_eq_of_observe_eq (hlook₁.trans hlook₂.symm)
  obtain ⟨hp, hr⟩ :=
    hLR r₁ r₂ hr₁ hr₂ p₁ p₂ s₁ s₂ y hd₁ hd₂ hform' hlook
  have hbad : gamma = gamma ++ symbol.terminal a :: delta := by
    calc
      gamma = p₁ ++ r₁.2 := hgamma
      _ = p₂ ++ r₂.2 := by rw [hp, hr]
      _ = gamma ++ symbol.terminal a :: delta := hstrict
  have hlength := congrArg List.length hbad
  simp at hlength

end CF_grammar.LRk
