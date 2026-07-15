module

public import Langlib.Grammars.LR.Equivalence.Candidates
public import Langlib.Grammars.LR.Rightmost

@[expose]
public section

/-!
# Reverse viable-prefix lemmas

The soundness development follows item edges forward.  Completeness needs the
converse structural fact.  The first such fact is proved here: a valid item at
dot position zero is either the untouched start configuration, or is obtained
by one closure edge from a valid parent item.  It is a direct item-level form
of `CF_grammar.derivesRightmost_nonterminal_ancestry`.
-/

open Language

namespace CF_grammar.LRk

variable {T : Type}

/-- Semantic item validity with an exact count of the rightmost derivation
steps reaching the item's prehandle. -/
@[expose]
public def ValidIn (G : CF_grammar T) (k n : ℕ)
    (gamma : List (symbol T G.nt)) (i : Item G k) : Prop :=
  ∃ (p : List (symbol T G.nt)) (s : List T),
    G.DerivesRightmostIn n [symbol.nonterminal G.initial]
      (p ++ [symbol.nonterminal (ruleAt G i.rule).1] ++
        s.map symbol.terminal) ∧
    gamma = p ++ i.before ∧
    observe k s = i.lookahead

public theorem ValidIn.valid {G : CF_grammar T} {k n : ℕ}
    {gamma : List (symbol T G.nt)} {i : Item G k}
    (h : ValidIn G k n gamma i) : Valid G k gamma i := by
  rcases h with ⟨p, s, hder, hgamma, hlook⟩
  exact ⟨p, s, hder.derives, hgamma, hlook⟩

public theorem Valid.exists_validIn {G : CF_grammar T} {k : ℕ}
    {gamma : List (symbol T G.nt)} {i : Item G k}
    (h : Valid G k gamma i) : ∃ n, ValidIn G k n gamma i := by
  rcases h with ⟨p, s, hder, hgamma, hlook⟩
  obtain ⟨n, hn⟩ := CF_grammar.exists_derivesRightmostIn_of_derivesRightmost hder
  exact ⟨n, p, s, hn, hgamma, hlook⟩

/-- Extensionality for dependent canonical items, stated through their public
projections. -/
public theorem Item.ext_of_rule_position_lookahead {G : CF_grammar T} {k : ℕ}
    {i j : Item G k} (hrule : i.rule = j.rule)
    (hposition : i.position.val = j.position.val)
    (hlookahead : i.lookahead = j.lookahead) : i = j := by
  rcases i with ⟨ir, ip, ilook⟩
  rcases j with ⟨jr, jp, jlook⟩
  change ir = jr at hrule
  subst jr
  change ip.val = jp.val at hposition
  have hip : ip = jp := Fin.ext hposition
  subst jp
  change ilook = jlook at hlookahead
  subst jlook
  rfl

/-- The distinguished start rule is the only augmented rule headed by the
fresh nonterminal. -/
public theorem augment_ruleIndex_eq_start_of_fst_eq_none (G : CF_grammar T)
    (i : RuleIndex G.augment) (h : (ruleAt G.augment i).1 = none) :
    i = startRuleIndex G := by
  apply Fin.ext
  change i.val = 0
  by_contra hne
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hget : G.augment.rules[i.val]? = some (ruleAt G.augment i) := by
    apply List.getElem?_eq_some_iff.mpr
    refine ⟨i.isLt, ?_⟩
    exact (List.get_eq_getElem (l := G.augment.rules) (i := i)).symm
  have hfst := congrArg (Option.map Prod.fst) hget
  rw [hn] at hfst
  simp [CF_grammar.augment, CF_grammar.augmentRule] at hfst
  rcases hfst with ⟨a, _, ha⟩
  change some a = (ruleAt G.augment i).1 at ha
  rw [h] at ha
  simp at ha

/-- An augmented item at the untouched fresh-start configuration is exactly
the distinguished start item. -/
public theorem Item.eq_startItem_of_root (G : CF_grammar T) (k : ℕ)
    {i : Item G.augment k} (hposition : i.position.val = 0)
    (hhead : (ruleAt G.augment i.rule).1 = none)
    (hlook : i.lookahead = eofLookahead T k) :
    i = startItem G k := by
  apply Item.ext_of_rule_position_lookahead
  · exact augment_ruleIndex_eq_start_of_fst_eq_none G i.rule hhead
  · simpa using hposition
  · simpa using hlook

/-- A valid item with a positive dot position is obtained by one goto
advancement from a valid item at the prefix with its final symbol removed. -/
public theorem Valid.positive_position_predecessor {G : CF_grammar T} {k : ℕ}
    {gamma : List (symbol T G.nt)} {j : Item G k}
    (hj : Valid G k gamma j) (hpositive : 0 < j.position.val) :
    ∃ (delta : List (symbol T G.nt)) (X : symbol T G.nt) (i : Item G k),
      gamma = delta ++ [X] ∧ Valid G k delta i ∧ Advances i X j := by
  rcases hj with ⟨p, s, hder, hgamma, hlook⟩
  have hle : j.position.val ≤ (ruleAt G j.rule).2.length := by
    omega
  have hprevLt : j.position.val - 1 < (ruleAt G j.rule).2.length := by
    omega
  let X : symbol T G.nt :=
    (ruleAt G j.rule).2[j.position.val - 1]
  have ipos : j.position.val - 1 < (ruleAt G j.rule).2.length + 1 := by
    omega
  let i : Item G k :=
    ⟨j.rule, ⟨⟨j.position.val - 1, ipos⟩, j.lookahead⟩⟩
  have hinext : i.next? = some X := by
    change (ruleAt G j.rule).2[j.position.val - 1]? = some X
    exact List.getElem?_eq_some_iff.mpr ⟨hprevLt, rfl⟩
  have hadv : Advances i X j := by
    refine ⟨rfl, ?_, hinext, rfl⟩
    change j.position.val = (j.position.val - 1) + 1
    omega
  refine ⟨p ++ i.before, X, i, ?_, ?_, hadv⟩
  · rw [hgamma, before_eq_of_advances hadv]
    simp [List.append_assoc]
  · refine ⟨p, s, ?_, rfl, ?_⟩
    · change G.DerivesRightmost [symbol.nonterminal G.initial]
        (p ++ [symbol.nonterminal (ruleAt G j.rule).1] ++
          s.map symbol.terminal)
      exact hder
    · change observe k s = j.lookahead
      exact hlook

/-- Counted form of `Valid.positive_position_predecessor`; reversing a goto
keeps the derivation count unchanged and shortens the scanned prefix. -/
public theorem ValidIn.positive_position_predecessor
    {G : CF_grammar T} {k n : ℕ}
    {gamma : List (symbol T G.nt)} {j : Item G k}
    (hj : ValidIn G k n gamma j) (hpositive : 0 < j.position.val) :
    ∃ (delta : List (symbol T G.nt)) (X : symbol T G.nt) (i : Item G k),
      gamma = delta ++ [X] ∧ ValidIn G k n delta i ∧ Advances i X j := by
  rcases hj with ⟨p, s, hder, hgamma, hlook⟩
  have hprevLt : j.position.val - 1 < (ruleAt G j.rule).2.length := by
    have := j.position.isLt
    omega
  let X : symbol T G.nt :=
    (ruleAt G j.rule).2[j.position.val - 1]
  have ipos : j.position.val - 1 < (ruleAt G j.rule).2.length + 1 := by
    omega
  let i : Item G k :=
    ⟨j.rule, ⟨⟨j.position.val - 1, ipos⟩, j.lookahead⟩⟩
  have hinext : i.next? = some X := by
    change (ruleAt G j.rule).2[j.position.val - 1]? = some X
    exact List.getElem?_eq_some_iff.mpr ⟨hprevLt, rfl⟩
  have hadv : Advances i X j := by
    refine ⟨rfl, ?_, hinext, rfl⟩
    change j.position.val = (j.position.val - 1) + 1
    omega
  refine ⟨p ++ i.before, X, i, ?_, ?_, hadv⟩
  · rw [hgamma, before_eq_of_advances hadv]
    simp [List.append_assoc]
  · refine ⟨p, s, ?_, rfl, ?_⟩
    · change G.DerivesRightmostIn n [symbol.nonterminal G.initial]
        (p ++ [symbol.nonterminal (ruleAt G j.rule).1] ++
          s.map symbol.terminal)
      exact hder
    · change observe k s = j.lookahead
      exact hlook

/-- A valid zero-dot item is either rooted at the untouched initial
nonterminal, or has a valid parent connected by one canonical closure edge. -/
public theorem Valid.zero_position_ancestry {G : CF_grammar T} {k : ℕ}
    {gamma : List (symbol T G.nt)} {j : Item G k}
    (hj : Valid G k gamma j) (hzero : j.position.val = 0) :
    (gamma = [] ∧ (ruleAt G j.rule).1 = G.initial ∧
      j.lookahead = eofLookahead T k) ∨
    ∃ i : Item G k, Valid G k gamma i ∧ ClosureStep G k i j := by
  rcases hj with ⟨p, s, hder, hgamma, hlook⟩
  have hjbefore : j.before = [] := by
    unfold Item.before
    rw [hzero]
    rfl
  have hgammaP : gamma = p := by
    simpa [hjbefore] using hgamma
  rcases CF_grammar.derivesRightmost_nonterminal_ancestry G hder with
    hbase | hparent
  · rcases hbase with ⟨hp, hA, hs⟩
    left
    refine ⟨hgammaP.trans hp, hA, ?_⟩
    rw [← hlook, hs]
    exact observe_nil k
  · rcases hparent with
      ⟨r, hr, p₀, alpha, beta, t, z,
        hrhs, hp, hs, hparentDer, hbeta⟩
    obtain ⟨ri, hri⟩ := List.get_of_mem hr
    have hri' : ruleAt G ri = r := hri
    have hpos : alpha.length < (ruleAt G ri).2.length + 1 := by
      rw [hri', hrhs]
      simp
    let i : Item G k :=
      ⟨ri, ⟨⟨alpha.length, hpos⟩, observe k t⟩⟩
    have ibefore : i.before = alpha := by
      change (ruleAt G ri).2.take alpha.length = alpha
      rw [hri', hrhs]
      simp
    have inext : i.next? =
        some (symbol.nonterminal (ruleAt G j.rule).1) := by
      change (ruleAt G ri).2[alpha.length]? =
        some (symbol.nonterminal (ruleAt G j.rule).1)
      rw [hri', hrhs]
      simp
    have iafter : i.afterNext = beta := by
      change ((ruleAt G ri).2.drop alpha.length).drop 1 = beta
      rw [hri', hrhs]
      simp
    right
    refine ⟨i, ?_, ?_⟩
    · refine ⟨p₀, t, ?_, ?_, rfl⟩
      · change G.DerivesRightmost [symbol.nonterminal G.initial]
          (p₀ ++ [symbol.nonterminal (ruleAt G ri).1] ++
            t.map symbol.terminal)
        rw [hri']
        exact hparentDer
      rw [hgammaP, hp, ibefore]
    · refine ⟨inext, hzero, ?_⟩
      refine ⟨z, ?_, ?_⟩
      · simpa [iafter] using hbeta
      · rw [← hlook, hs, observe_append]
        rfl

/-- Counted zero-dot ancestry.  In the non-root case the valid parent is
reached in strictly fewer rightmost steps. -/
public theorem ValidIn.zero_position_ancestry {G : CF_grammar T} {k n : ℕ}
    {gamma : List (symbol T G.nt)} {j : Item G k}
    (hj : ValidIn G k n gamma j) (hzero : j.position.val = 0) :
    (gamma = [] ∧ (ruleAt G j.rule).1 = G.initial ∧
      j.lookahead = eofLookahead T k) ∨
    ∃ (m : ℕ) (i : Item G k), m < n ∧
      ValidIn G k m gamma i ∧ ClosureStep G k i j := by
  rcases hj with ⟨p, s, hder, hgamma, hlook⟩
  have hjbefore : j.before = [] := by
    unfold Item.before
    rw [hzero]
    rfl
  have hgammaP : gamma = p := by
    simpa [hjbefore] using hgamma
  rcases CF_grammar.derivesRightmostIn_nonterminal_ancestry G hder with
    hbase | hparent
  · rcases hbase with ⟨hp, hA, hs⟩
    left
    refine ⟨hgammaP.trans hp, hA, ?_⟩
    rw [← hlook, hs]
    exact observe_nil k
  · rcases hparent with
      ⟨m, r, hr, p₀, alpha, beta, t, z, hmn,
        hrhs, hp, hs, hparentDer, hbeta⟩
    obtain ⟨ri, hri⟩ := List.get_of_mem hr
    have hri' : ruleAt G ri = r := hri
    have hpos : alpha.length < (ruleAt G ri).2.length + 1 := by
      rw [hri', hrhs]
      simp
    let i : Item G k :=
      ⟨ri, ⟨⟨alpha.length, hpos⟩, observe k t⟩⟩
    have ibefore : i.before = alpha := by
      change (ruleAt G ri).2.take alpha.length = alpha
      rw [hri', hrhs]
      simp
    have inext : i.next? =
        some (symbol.nonterminal (ruleAt G j.rule).1) := by
      change (ruleAt G ri).2[alpha.length]? =
        some (symbol.nonterminal (ruleAt G j.rule).1)
      rw [hri', hrhs]
      simp
    have iafter : i.afterNext = beta := by
      change ((ruleAt G ri).2.drop alpha.length).drop 1 = beta
      rw [hri', hrhs]
      simp
    right
    refine ⟨m, i, hmn, ?_, ?_⟩
    · refine ⟨p₀, t, ?_, ?_, rfl⟩
      · change G.DerivesRightmostIn m [symbol.nonterminal G.initial]
          (p₀ ++ [symbol.nonterminal (ruleAt G ri).1] ++
            t.map symbol.terminal)
        rw [hri']
        exact hparentDer
      · rw [hgammaP, hp, ibefore]
    · refine ⟨inext, hzero, ?_⟩
      refine ⟨z, ?_, ?_⟩
      · simpa [iafter] using hbeta
      · rw [← hlook, hs, observe_append]
        rfl

/-- Full viable-prefix completeness for the augmented canonical item
automaton, with an exact derivation witness. -/
public theorem validIn_mem_itemState [Fintype T] (G : CF_grammar T) (k : ℕ)
    {n : ℕ} {gamma : List (symbol T G.augment.nt)} {i : Item G.augment k}
    (hi : ValidIn G.augment k n gamma i) : i ∈ itemState G k gamma := by
  let motive := fun measure =>
    ∀ (n : ℕ) (gamma : List (symbol T G.augment.nt))
        (i : Item G.augment k),
      n + gamma.length = measure →
      ValidIn G.augment k n gamma i → i ∈ itemState G k gamma
  apply (Nat.strong_induction_on (p := motive) (n + gamma.length) ?_)
    n gamma i rfl hi
  intro measure ih n gamma i hmeasure hi
  dsimp only [motive] at ih ⊢
  by_cases hzero : i.position.val = 0
  · rcases hi.zero_position_ancestry hzero with hroot | hparent
    · rcases hroot with ⟨hgamma, hhead, hlook⟩
      have hiStart : i = startItem G k :=
        Item.eq_startItem_of_root G k hzero hhead hlook
      subst gamma
      subst i
      exact subset_closure G.augment k (startKernel G k)
        (Finset.mem_singleton_self (startItem G k))
    · rcases hparent with ⟨m, j, hmn, hj, hstep⟩
      have hmeasure : m + gamma.length < n + gamma.length := by omega
      have hjmem : j ∈ itemState G k gamma :=
        ih (m + gamma.length) (by omega) m gamma j rfl hj
      obtain ⟨seed, hseed, hreach⟩ :=
        (mem_closure G.augment k (scanKernel G k gamma) j).1 hjmem
      exact (mem_closure G.augment k (scanKernel G k gamma) i).2
        ⟨seed, hseed, hreach.tail hstep⟩
  · have hpositive : 0 < i.position.val := Nat.pos_of_ne_zero hzero
    rcases hi.positive_position_predecessor hpositive with
      ⟨delta, X, j, hgamma, hj, hadv⟩
    have hlen : delta.length < gamma.length := by
      rw [hgamma]
      simp
    have hmeasure : n + delta.length < n + gamma.length := by omega
    have hjmem : j ∈ itemState G k delta :=
      ih (n + delta.length) (by omega) n delta j rfl hj
    subst gamma
    change i ∈ closure G.augment k (scanKernel G k (delta ++ [X]))
    rw [scanKernel_append_singleton]
    apply subset_closure G.augment k
    exact (mem_goto G.augment k (scanKernel G k delta) X i).2
      ⟨j, hjmem, hadv⟩

/-- Semantic validity and membership in the finite canonical state coincide. -/
public theorem mem_itemState_iff_valid [Fintype T] (G : CF_grammar T) (k : ℕ)
    (gamma : List (symbol T G.augment.nt)) (i : Item G.augment k) :
    i ∈ itemState G k gamma ↔ Valid G.augment k gamma i := by
  constructor
  · exact itemState_valid G k gamma
  · intro hi
    obtain ⟨n, hn⟩ := hi.exists_validIn
    exact validIn_mem_itemState G k hn

end CF_grammar.LRk
