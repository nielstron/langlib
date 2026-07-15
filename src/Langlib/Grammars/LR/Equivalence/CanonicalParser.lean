module

public import Langlib.Grammars.LR.Equivalence.Table

@[expose]
public section

/-!
# Correctness of the canonical LR table

This file gives a small grammar-symbol-stack semantics for the canonical
table.  It separates the mathematical handle-pruning proof from the later
finite-control/buffer simulation by the concrete DPDA.
-/

open Language

namespace CF_grammar.LRk.CanonicalParser

open CF_grammar.LRk

variable {T : Type} [Fintype T]

public structure Config (T : Type) (G : CF_grammar T) where
  stack : List (symbol T G.augment.nt)
  input : List T

@[expose]
public def Config.form (c : Config T G) : List (symbol T G.augment.nt) :=
  c.stack ++ c.input.map (symbol.terminal (N := G.augment.nt))

@[expose]
public def initialConfig (G : CF_grammar T) (w : List T) : Config T G :=
  ⟨[], w⟩

/-- One trusted table step.  The suffix equation in the reduction constructor
is not an extra parser test: on reachable kernels it follows from semantic
item validity.  Recording it here makes the handle-pruning invariant explicit.
-/
public inductive Step (G : CF_grammar T) (k : ℕ) :
    Config T G → Config T G → Prop
  | shift {gamma : List (symbol T G.augment.nt)} {a : T} {w : List T}
      (haction : tableAction G k (scanKernel G k gamma)
        (observe k (a :: w)) = .shift) :
      Step G k ⟨gamma, a :: w⟩
        ⟨gamma ++ [symbol.terminal a], w⟩
  | reduce {gamma p : List (symbol T G.augment.nt)} {w : List T}
      {r : RuleIndex G.augment}
      (haction : tableAction G k (scanKernel G k gamma)
        (observe k w) = .reduce r)
      (hgamma : gamma = p ++ (ruleAt G.augment r).2) :
      Step G k ⟨gamma, w⟩
        ⟨p ++ [symbol.nonterminal (ruleAt G.augment r).1], w⟩

public abbrev Reaches (G : CF_grammar T) (k : ℕ) :
    Config T G → Config T G → Prop :=
  Relation.ReflTransGen (Step G k)

@[expose]
public def Accepting (G : CF_grammar T) (k : ℕ) (c : Config T G) : Prop :=
  c.input = [] ∧
    tableAction G k (scanKernel G k c.stack) (eofLookahead T k) = .accept

@[expose]
public def Accepts (G : CF_grammar T) (k : ℕ) (w : List T) : Prop :=
  ∃ c, Reaches G k (initialConfig G w) c ∧ Accepting G k c

@[simp]
public theorem lookaheadHead_observe_cons (k : ℕ) (hk : 0 < k)
    (a : T) (w : List T) :
    lookaheadHead k (observe k (a :: w)) = some a := by
  simp [lookaheadHead, hk, observe]

/-- A convenient completed item naming a rule occurrence. -/
@[expose]
public def completedItem (G : CF_grammar T) (k : ℕ)
    (r : RuleIndex G.augment) (u : Lookahead T k) : Item G.augment k :=
  ⟨r, ⟨⟨(ruleAt G.augment r).2.length, by omega⟩, u⟩⟩

@[simp]
public theorem completedItem_complete (G : CF_grammar T) (k : ℕ)
    (r : RuleIndex G.augment) (u : Lookahead T k) :
    (completedItem G k r u).Complete := rfl

@[simp]
public theorem completedItem_before (G : CF_grammar T) (k : ℕ)
    (r : RuleIndex G.augment) (u : Lookahead T k) :
    (completedItem G k r u).before = (ruleAt G.augment r).2 := by
  change (ruleAt G.augment r).2.take (ruleAt G.augment r).2.length = _
  simp

@[simp]
public theorem completedItem_lookahead (G : CF_grammar T) (k : ℕ)
    (r : RuleIndex G.augment) (u : Lookahead T k) :
    (completedItem G k r u).lookahead = u := rfl

/-- Fresh augmentation never inserts the fresh start symbol into an embedded
right-hand side. -/
public theorem fresh_not_mem_augmentString (G : CF_grammar T)
    (w : List (symbol T G.nt)) :
    symbol.nonterminal none ∉ CF_grammar.augmentString w := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨X, _, hX⟩
  cases X <;> simp [CF_grammar.augmentSymbol] at hX

/-- No augmented production has the fresh start nonterminal in its right-hand
side. -/
public theorem fresh_not_mem_rule_rhs (G : CF_grammar T)
    {r : G.augment.nt × List (symbol T G.augment.nt)}
    (hr : r ∈ G.augment.rules) : symbol.nonterminal none ∉ r.2 := by
  rcases List.mem_cons.mp hr with hstart | hmapped
  · subst r
    simp [CF_grammar.augmentStartRule]
  · rcases List.mem_map.mp hmapped with ⟨r, hr, rfl⟩
    exact fresh_not_mem_augmentString G r.2

/-- A surviving occurrence of the fresh initial nonterminal can only be the
untouched root configuration. -/
public theorem fresh_prehandle_eq_root (G : CF_grammar T)
    {p : List (symbol T G.augment.nt)} {s : List T}
    (h : G.augment.DerivesRightmost
      [symbol.nonterminal G.augment.initial]
      (p ++ [symbol.nonterminal none] ++ s.map symbol.terminal)) :
    p = [] ∧ s = [] := by
  rcases CF_grammar.derivesRightmost_nonterminal_ancestry G.augment h with
    hroot | hparent
  · exact ⟨hroot.1, hroot.2.2⟩
  · rcases hparent with
      ⟨r, hr, p₀, alpha, beta, t, z, hrhs, _, _, _, _⟩
    have hmem : symbol.nonterminal none ∈ r.2 := by
      rw [hrhs]
      simp
    exact False.elim (fresh_not_mem_rule_rhs G hr hmem)

/-- A displayed rightmost prehandle exposes its production as a reduction in
the canonical state at the completed handle boundary. -/
public theorem stateReduction_of_prehandle (G : CF_grammar T) (k : ℕ)
    {r : RuleIndex G.augment} {p : List (symbol T G.augment.nt)} {s : List T}
    (hpre : G.augment.DerivesRightmost
      [symbol.nonterminal G.augment.initial]
      (p ++ [symbol.nonterminal (ruleAt G.augment r).1] ++
        s.map symbol.terminal)) :
    StateReduction G k (p ++ (ruleAt G.augment r).2) (observe k s)
      (ruleAt G.augment r) := by
  let i := completedItem G k r (observe k s)
  refine ⟨i, ?_, completedItem_complete G k r _, rfl, rfl⟩
  rw [mem_itemState_iff_valid]
  exact ⟨p, s, hpre, by simp [i], rfl⟩

/-- Before a later displayed handle boundary, LR(k) conflict freedom forces
the total table's default shift. -/
public theorem tableAction_shift_before_handle (G : CF_grammar T) (k : ℕ)
    (hk : 0 < k) (hLR : G.IsLRk k)
    {r : RuleIndex G.augment} {p gamma : List (symbol T G.augment.nt)}
    {s x : List T} {a : T}
    (hpre : G.augment.DerivesRightmost
      [symbol.nonterminal G.augment.initial]
      (p ++ [symbol.nonterminal (ruleAt G.augment r).1] ++
        s.map symbol.terminal))
    (hboundary : p ++ (ruleAt G.augment r).2 =
      gamma ++ symbol.terminal a :: x.map symbol.terminal) :
    tableAction G k (scanKernel G k gamma)
      (observe k (a :: x ++ s)) = .shift := by
  have hlater : LaterHandleCandidate G.augment k gamma
      (observe k (a :: x ++ s)) := by
    refine ⟨ruleAt G.augment r, ruleAt_mem G.augment r,
      p, s, a :: x ++ s, a, x.map symbol.terminal,
      hpre, hboundary, ?_, rfl⟩
    rw [hboundary]
    simp [List.map_append, List.append_assoc]
  have hnone : reductionItem? G k (scanKernel G k gamma)
      (observe k (a :: x ++ s)) = none := by
    by_contra hne
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
    have hcand := reductionItem?_reductionCandidate G k hi
    exact CoreIsLRk.not_reductionCandidate_and_laterHandleCandidate
      (G := G.augment) hLR hcand hlater
  exact tableAction_shift_of_none G k _ _ hnone
    (lookaheadHead_observe_cons k hk a (x ++ s))

/-- A block of terminals before a displayed handle can be shifted without the
table skipping an earlier reduction. -/
public theorem shifts_to_handle (G : CF_grammar T) (k : ℕ) (hk : 0 < k)
    (hLR : G.IsLRk k)
    {r : RuleIndex G.augment} {p gamma : List (symbol T G.augment.nt)}
    {s x : List T}
    (hpre : G.augment.DerivesRightmost
      [symbol.nonterminal G.augment.initial]
      (p ++ [symbol.nonterminal (ruleAt G.augment r).1] ++
        s.map symbol.terminal))
    (hboundary : p ++ (ruleAt G.augment r).2 =
      gamma ++ x.map symbol.terminal) :
    Reaches G k ⟨gamma, x ++ s⟩
      ⟨p ++ (ruleAt G.augment r).2, s⟩ := by
  induction x generalizing gamma with
  | nil =>
      simp at hboundary
      subst gamma
      exact Relation.ReflTransGen.refl
  | cons a x ih =>
      have hboundary' : p ++ (ruleAt G.augment r).2 =
          (gamma ++ [symbol.terminal a]) ++ x.map symbol.terminal := by
        simpa [List.append_assoc] using hboundary
      have hshift := tableAction_shift_before_handle G k hk hLR hpre hboundary
      apply Relation.ReflTransGen.head (Step.shift hshift)
      simpa [List.append_assoc] using ih hboundary'

/-- Prefix/terminal-suffix comparison at a rightmost handle boundary. -/
public theorem split_at_handle_boundary
    {N : Type} {gamma B : List (symbol T N)} {input s : List T}
    (hend : gamma = [] ∨ ∃ p A, gamma = p ++ [symbol.nonterminal A])
    (heq : gamma ++ input.map symbol.terminal =
      B ++ s.map symbol.terminal) :
    ∃ x : List T, B = gamma ++ x.map symbol.terminal ∧ input = x ++ s := by
  rw [List.append_eq_append_iff] at heq
  rcases heq with ⟨as, hB, hinput⟩ | ⟨bs, hgamma, hs⟩
  · have hsplit := (List.append_eq_map_iff.mp hinput.symm)
    rcases hsplit with ⟨x, s', hxs, hx, hs'⟩
    have hsEq : s' = s :=
      (List.map_injective_iff.mpr fun _ _ h => symbol.terminal.inj h) hs'
    subst s'
    exact ⟨x, by simpa [hx] using hB, hxs⟩
  · have hsplit := (List.map_eq_append_iff.mp hs)
    rcases hsplit with ⟨z, input', hzs, hz, hinput'⟩
    have hinputEq : input' = input :=
      (List.map_injective_iff.mpr fun _ _ h => symbol.terminal.inj h) hinput'
    subst input'
    have hzNil : z = [] := by
      rcases hend with rfl | ⟨q, A, hq⟩
      · simp at hgamma
        simpa [hgamma] using hz
      · by_contra hzne
        rcases List.eq_nil_or_concat z with hz0 | ⟨z', b, hzb⟩
        · exact hzne hz0
        · have hlast :
              q ++ [symbol.nonterminal A] =
                (B ++ z'.map symbol.terminal) ++ [symbol.terminal b] := by
            calc
              q ++ [symbol.nonterminal A] = gamma := hq.symm
              _ = B ++ bs := hgamma
              _ = B ++ z.map symbol.terminal := by rw [hz]
              _ = (B ++ z'.map symbol.terminal) ++
                  [symbol.terminal b] := by
                rw [hzb]
                simp [List.map_append, List.append_assoc]
          have hrev := congrArg List.reverse hlast
          simp [List.reverse_append] at hrev
    subst z
    simp at hz hgamma hzs
    subst bs
    exact ⟨[], by simpa using hgamma.symm, by simpa using hzs.symm⟩

/-- The only terminal-suffix split of the one-symbol fresh root whose prefix is
empty or ends in a nonterminal is the root itself with empty suffix. -/
public theorem split_fresh_root (G : CF_grammar T)
    {gamma : List (symbol T (Option G.nt))} {input : List T}
    (hend : gamma = [] ∨ ∃ p A, gamma = p ++ [symbol.nonterminal A])
    (heq : gamma ++ input.map symbol.terminal = [symbol.nonterminal none]) :
    gamma = [symbol.nonterminal none] ∧ input = [] := by
  obtain ⟨x, hroot, hinput⟩ :=
    split_at_handle_boundary hend heq
      (B := [symbol.nonterminal none]) (s := [])
  rcases hend with hnil | ⟨p, A, hp⟩
  · subst gamma
    cases x <;> simp at hroot
  · have hgammaPos : 0 < gamma.length := by simp [hp]
    have hlen := congrArg List.length hroot
    have hx : x = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp at hlen
      omega
    subst x
    exact ⟨by simpa using hroot.symm, by simpa using hinput⟩

/-- Result of pruning a counted rightmost derivation: either the table has
accepted, or the degenerate zero-step derivation has reached the fresh root. -/
@[expose]
public def BackOutcome (G : CF_grammar T) (k : ℕ) (c : Config T G) : Prop :=
  ∃ d, Reaches G k c d ∧
    (Accepting G k d ∨
      (d.stack = [symbol.nonterminal none] ∧ d.input = []))

/-- Reverse a counted rightmost derivation by shifting up to each displayed
handle and then taking the unique LR(k) reduction. -/
private theorem parses_back_of_derivesRightmostIn_aux
    (G : CF_grammar T) (k : ℕ) (hk : 0 < k) (hLR : G.IsLRk k)
    {n : ℕ} {u v : List (symbol T G.augment.nt)}
    (h : G.augment.DerivesRightmostIn n u v)
    {gamma : List (symbol T G.augment.nt)} {input : List T}
    (hu : u = [symbol.nonterminal G.augment.initial])
    (hv : v = gamma ++ input.map symbol.terminal)
    (hend : gamma = [] ∨ ∃ p A, gamma = p ++ [symbol.nonterminal A]) :
    BackOutcome G k ⟨gamma, input⟩ := by
  induction h generalizing gamma input with
  | refl =>
      have heq : gamma ++ input.map symbol.terminal =
          [symbol.nonterminal none] := by
        rw [← hv, hu]
        rfl
      have hsplit := split_fresh_root G hend heq
      rcases hsplit with ⟨rfl, rfl⟩
      exact ⟨⟨[symbol.nonterminal none], []⟩,
        Relation.ReflTransGen.refl, Or.inr ⟨rfl, rfl⟩⟩
  | @tail n start middle target hprev hstep ih =>
      rcases hstep with ⟨rule, hrule, p, s, hsource, htarget⟩
      obtain ⟨ri, hri⟩ := List.get_of_mem hrule
      have hri' : ruleAt G.augment ri = rule := hri
      have heq : gamma ++ input.map symbol.terminal =
          (p ++ rule.2) ++ s.map symbol.terminal := by
        rw [← hv]
        exact htarget
      obtain ⟨x, hboundary, hinput⟩ :=
        split_at_handle_boundary hend heq
      have hpre : G.augment.DerivesRightmost
          [symbol.nonterminal G.augment.initial]
          (p ++ [symbol.nonterminal rule.1] ++ s.map symbol.terminal) := by
        rw [← hsource]
        rw [← hu]
        exact hprev.derives
      have hpre' : G.augment.DerivesRightmost
          [symbol.nonterminal G.augment.initial]
          (p ++ [symbol.nonterminal (ruleAt G.augment ri).1] ++
            s.map symbol.terminal) := by
        simpa [hri'] using hpre
      have hshifts : Reaches G k ⟨gamma, input⟩
          ⟨p ++ (ruleAt G.augment ri).2, s⟩ := by
        rw [hinput]
        apply shifts_to_handle G k hk hLR hpre'
        simpa [hri'] using hboundary
      have hstate := stateReduction_of_prehandle G k hpre'
      obtain ⟨chosen, hchosen, hchosenRule⟩ :=
        reductionItem?_rule_eq_of_stateReduction G k hLR hstate
      by_cases hstart : chosen.rule = startRuleIndex G
      · have haction : tableAction G k
            (scanKernel G k (p ++ (ruleAt G.augment ri).2))
            (observe k s) = .accept :=
          (tableAction_accept_iff G k _ _).2 ⟨chosen, hchosen, hstart⟩
        have hhead : (ruleAt G.augment ri).1 = none := by
          rw [← hchosenRule, hstart, ruleAt_startRuleIndex]
          rfl
        have hroot := fresh_prehandle_eq_root G (by simpa [hhead] using hpre')
        rcases hroot with ⟨rfl, rfl⟩
        refine ⟨⟨(ruleAt G.augment ri).2, []⟩, hshifts, Or.inl ?_⟩
        refine ⟨rfl, ?_⟩
        simpa using haction
      · have haction : tableAction G k
            (scanKernel G k (p ++ (ruleAt G.augment ri).2))
            (observe k s) = .reduce chosen.rule :=
          (tableAction_reduce_iff G k _ _ _).2
            ⟨chosen, hchosen, hstart, rfl⟩
        have hreduce : Step G k
            ⟨p ++ (ruleAt G.augment ri).2, s⟩
            ⟨p ++ [symbol.nonterminal (ruleAt G.augment ri).1], s⟩ := by
          have hvalue : ruleAt G.augment chosen.rule = ruleAt G.augment ri :=
            hchosenRule
          have hredChosen : Step G k
              ⟨p ++ (ruleAt G.augment ri).2, s⟩
              ⟨p ++ [symbol.nonterminal
                (ruleAt G.augment chosen.rule).1], s⟩ :=
            Step.reduce (G := G) (k := k) haction
              (p := p) (r := chosen.rule) (by rw [hvalue])
          simpa only [hvalue] using hredChosen
        have htoSource : Reaches G k ⟨gamma, input⟩
            ⟨p ++ [symbol.nonterminal (ruleAt G.augment ri).1], s⟩ :=
          hshifts.tail hreduce
        have hmiddle : middle =
            (p ++ [symbol.nonterminal (ruleAt G.augment ri).1]) ++
              s.map symbol.terminal := by
          simpa [hri'] using hsource
        have hout := ih (gamma := p ++
            [symbol.nonterminal (ruleAt G.augment ri).1])
          (input := s) hu hmiddle
          (Or.inr ⟨p, _, rfl⟩)
        rcases hout with ⟨d, hd, hout⟩
        exact ⟨d, htoSource.trans hd, hout⟩

/-- Reverse a counted rightmost derivation by shifting up to each displayed
handle and then taking the unique LR(k) reduction. -/
public theorem parses_back_of_derivesRightmostIn
    (G : CF_grammar T) (k : ℕ) (hk : 0 < k) (hLR : G.IsLRk k)
    {n : ℕ} {gamma : List (symbol T G.augment.nt)} {input : List T}
    (h : G.augment.DerivesRightmostIn n
      [symbol.nonterminal G.augment.initial]
      (gamma ++ input.map symbol.terminal))
    (hend : gamma = [] ∨ ∃ p A, gamma = p ++ [symbol.nonterminal A]) :
    BackOutcome G k ⟨gamma, input⟩ :=
  parses_back_of_derivesRightmostIn_aux G k hk hLR h rfl rfl hend

/-- The parser stack never contains the fresh augmented start nonterminal.
That symbol is recognized by the accept action rather than pushed by a
reduction. -/
@[expose]
public def FreshFree (c : Config T G) : Prop :=
  symbol.nonterminal none ∉ c.stack

public theorem Step.freshFree {G : CF_grammar T} {k : ℕ}
    {c d : Config T G} (h : Step G k c d) (hc : FreshFree c) :
    FreshFree d := by
  cases h with
  | @shift gamma a w _ =>
      simp only [FreshFree, List.mem_append, List.mem_singleton] at hc ⊢
      rintro (hmem | heq)
      · exact hc hmem
      · cases heq
  | @reduce gamma p w r haction hgamma =>
      obtain ⟨i, _, hnotStart, hir⟩ :=
        (tableAction_reduce_iff G k (scanKernel G k gamma)
          (observe k w) r).mp haction
      have hrNotFresh : (ruleAt G.augment r).1 ≠ none := by
        intro hfresh
        have hiStart : i.rule = startRuleIndex G := by
          apply augment_ruleIndex_eq_start_of_fst_eq_none G
          rw [hir]
          exact hfresh
        exact hnotStart hiStart
      have hp : symbol.nonterminal none ∉ p := by
        intro hmem
        apply hc
        rw [hgamma]
        exact List.mem_append_left _ hmem
      simp only [FreshFree, List.mem_append, List.mem_singleton,
        symbol.nonterminal.injEq]
      exact fun hmem => hmem.elim hp (fun heq => hrNotFresh heq.symm)

public theorem Reaches.freshFree {G : CF_grammar T} {k : ℕ}
    {c d : Config T G} (h : Reaches G k c d) (hc : FreshFree c) :
    FreshFree d := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih => exact hstep.freshFree ih

/-- Every word generated by an LR(k) grammar is accepted by its canonical
table (for positive lookahead). -/
public theorem accepts_complete (G : CF_grammar T) (k : ℕ) (hk : 0 < k)
    (hLR : G.IsLRk k) {w : List T} (hw : w ∈ CF_language G) :
    Accepts G k w := by
  change CF_derives G [symbol.nonterminal G.initial]
    (w.map symbol.terminal) at hw
  have hright := CF_grammar.derivesRightmost_of_derives hw
  have haug := CF_grammar.augment_derivesRightmost G hright
  obtain ⟨n, hn⟩ :=
    CF_grammar.exists_derivesRightmostIn_of_derivesRightmost haug
  have hn' : G.augment.DerivesRightmostIn n
      [symbol.nonterminal G.augment.initial]
      ([] ++ w.map (symbol.terminal (N := G.augment.nt))) := by
    simpa [CF_grammar.augmentString] using hn
  have hout := parses_back_of_derivesRightmostIn G k hk hLR hn' (Or.inl rfl)
  rcases hout with ⟨d, hreach, haccept | hroot⟩
  · exact ⟨d, hreach, haccept⟩
  · have hfree : FreshFree d :=
      hreach.freshFree (by simp [FreshFree, initialConfig])
    rcases hroot with ⟨hstack, _⟩
    rw [FreshFree, hstack] at hfree
    simp at hfree

end CF_grammar.LRk.CanonicalParser
