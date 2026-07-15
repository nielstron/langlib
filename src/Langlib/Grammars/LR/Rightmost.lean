module

public import Langlib.Grammars.LR.Definition

@[expose]
public section

/-!
# Rightmost derivations

This file supplies the structural facts about rightmost derivations which are
independent of the LR conflict condition.  In particular, an ordinary
context-free derivation whose result is a terminal word can always be
scheduled rightmost.
-/

open Language

namespace CF_grammar

variable {T : Type} {G : CF_grammar T}

/-! ## Counted rightmost derivations -/

/-- A rightmost derivation using exactly `n` production steps.  Unlike
`DerivesRightmost`, this relation retains the measure needed for well-founded
arguments which trace a surviving nonterminal back through its ancestors. -/
public inductive DerivesRightmostIn (G : CF_grammar T) :
    ℕ → List (symbol T G.nt) → List (symbol T G.nt) → Prop
  | refl (w) : DerivesRightmostIn G 0 w w
  | tail {n u v w} :
      DerivesRightmostIn G n u v → G.ProducesRightmost v w →
        DerivesRightmostIn G (n + 1) u w

public theorem DerivesRightmostIn.derives {n : ℕ}
    {u v : List (symbol T G.nt)} (h : G.DerivesRightmostIn n u v) :
    G.DerivesRightmost u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep

public theorem exists_derivesRightmostIn_of_derivesRightmost
    {u v : List (symbol T G.nt)} (h : G.DerivesRightmost u v) :
    ∃ n, G.DerivesRightmostIn n u v := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, .tail hn hstep⟩

public theorem derivesRightmost_iff_exists_derivesRightmostIn
    {u v : List (symbol T G.nt)} :
    G.DerivesRightmost u v ↔ ∃ n, G.DerivesRightmostIn n u v :=
  ⟨exists_derivesRightmostIn_of_derivesRightmost,
    fun ⟨_, h⟩ => h.derives⟩

public theorem ProducesRightmost.derivesRightmostIn_one
    {u v : List (symbol T G.nt)} (h : G.ProducesRightmost u v) :
    G.DerivesRightmostIn 1 u v :=
  .tail (.refl u) h

public theorem DerivesRightmostIn.trans {m n : ℕ}
    {u v w : List (symbol T G.nt)}
    (huv : G.DerivesRightmostIn m u v)
    (hvw : G.DerivesRightmostIn n v w) :
    G.DerivesRightmostIn (m + n) u w := by
  induction hvw generalizing u with
  | refl => simpa using huv
  | tail _ hstep ih =>
      simpa [Nat.add_assoc] using DerivesRightmostIn.tail (ih huv) hstep

/-! ## Context closure -/

public theorem RewritesRightmost.append_left {N : Type}
    {r : N × List (symbol T N)} {u v : List (symbol T N)}
    (h : RewritesRightmost r u v) (pre : List (symbol T N)) :
    RewritesRightmost r (pre ++ u) (pre ++ v) := by
  rcases h with ⟨p, s, hu, hv⟩
  refine ⟨pre ++ p, s, ?_, ?_⟩ <;>
    simp [hu, hv, List.append_assoc]

public theorem RewritesRightmost.append_terminals_right {N : Type}
    {r : N × List (symbol T N)} {u v : List (symbol T N)}
    (h : RewritesRightmost r u v) (suf : List T) :
    RewritesRightmost r
      (u ++ suf.map symbol.terminal)
      (v ++ suf.map symbol.terminal) := by
  rcases h with ⟨p, s, hu, hv⟩
  refine ⟨p, s ++ suf, ?_, ?_⟩ <;>
    simp [hu, hv, List.map_append, List.append_assoc]

public theorem ProducesRightmost.single {u v : List (symbol T G.nt)}
    (h : G.ProducesRightmost u v) : G.DerivesRightmost u v :=
  Relation.ReflTransGen.single h

public theorem ProducesRightmost.append_left {u v : List (symbol T G.nt)}
    (h : G.ProducesRightmost u v) (pre : List (symbol T G.nt)) :
    G.ProducesRightmost (pre ++ u) (pre ++ v) := by
  rcases h with ⟨r, hr, hrewrite⟩
  exact ⟨r, hr, hrewrite.append_left pre⟩

public theorem ProducesRightmost.append_terminals_right
    {u v : List (symbol T G.nt)} (h : G.ProducesRightmost u v)
    (suf : List T) :
    G.ProducesRightmost
      (u ++ suf.map symbol.terminal)
      (v ++ suf.map symbol.terminal) := by
  rcases h with ⟨r, hr, hrewrite⟩
  exact ⟨r, hr, hrewrite.append_terminals_right suf⟩

public theorem DerivesRightmost.append_left {u v : List (symbol T G.nt)}
    (h : G.DerivesRightmost u v) (pre : List (symbol T G.nt)) :
    G.DerivesRightmost (pre ++ u) (pre ++ v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.append_left pre)

public theorem DerivesRightmost.append_terminals_right
    {u v : List (symbol T G.nt)} (h : G.DerivesRightmost u v)
    (suf : List T) :
    G.DerivesRightmost
      (u ++ suf.map symbol.terminal)
      (v ++ suf.map symbol.terminal) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.append_terminals_right suf)

/-- Rightmost derivations of adjacent pieces can be scheduled from right to
left.  This is the basic commutation principle used below. -/
public theorem DerivesRightmost.append_to_terminals
    {u v : List (symbol T G.nt)} {wu wv : List T}
    (hu : G.DerivesRightmost u (wu.map symbol.terminal))
    (hv : G.DerivesRightmost v (wv.map symbol.terminal)) :
    G.DerivesRightmost (u ++ v) ((wu ++ wv).map symbol.terminal) := by
  have hright := hv.append_left u
  have hleft := hu.append_terminals_right wv
  simpa [List.map_append] using hright.trans hleft

/-! ## Terminal sentential forms -/

private theorem append_eq_map_terminal_split
    {u v : List (symbol T G.nt)} {w : List T}
    (h : u ++ v = w.map symbol.terminal) :
    ∃ wu wv, w = wu ++ wv ∧
      u = wu.map symbol.terminal ∧ v = wv.map symbol.terminal := by
  induction u generalizing w with
  | nil => exact ⟨[], w, by simp, rfl, by simpa using h⟩
  | cons a u ih =>
      cases w with
      | nil => simp at h
      | cons b w =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, ht⟩ := h
          obtain ⟨wu, wv, hw, hu, hv⟩ := ih ht
          exact ⟨b :: wu, wv, by simp [hw], by simp [hu], hv⟩

public theorem not_producesRightmost_map_terminal
    {w : List T} {v : List (symbol T G.nt)} :
    ¬ G.ProducesRightmost (w.map symbol.terminal) v := by
  rintro ⟨r, _, p, s, hsource, _⟩
  have hmem : symbol.nonterminal r.1 ∈ w.map symbol.terminal := by
    rw [hsource]
    simp
  simp at hmem

public theorem DerivesRightmost.eq_of_map_terminal_source
    {w : List T} {v : List (symbol T G.nt)}
    (h : G.DerivesRightmost (w.map symbol.terminal) v) :
    v = w.map symbol.terminal := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rw [ih] at hstep
      exact False.elim (not_producesRightmost_map_terminal hstep)

/-! ## Splitting rightmost derivations -/

/-- A rightmost step in an append either occurs in the right component, or it
occurs in the left component after the right component is already terminal. -/
public theorem ProducesRightmost.append_cases
    {u v x : List (symbol T G.nt)}
    (h : G.ProducesRightmost (u ++ v) x) :
    (∃ (u' : List (symbol T G.nt)) (wv : List T),
        v = wv.map symbol.terminal ∧ x = u' ++ v ∧
          G.ProducesRightmost u u') ∨
      (∃ v', x = u ++ v' ∧ G.ProducesRightmost v v') := by
  rcases h with ⟨r, hr, p, s, hsource, rfl⟩
  have hsource' : u ++ v = p ++ ([symbol.nonterminal r.1] ++
      s.map symbol.terminal) := by
    simpa [List.append_assoc] using hsource
  rw [List.append_eq_append_iff] at hsource'
  rcases hsource' with ⟨as, hp, hv⟩ | ⟨bs, hu, hrest⟩
  · right
    refine ⟨as ++ r.2 ++ s.map symbol.terminal, ?_, ?_⟩
    · simp [hp, List.append_assoc]
    · exact ⟨r, hr, as, s,
        by simpa [List.append_assoc] using hv, rfl⟩
  · cases bs with
    | nil =>
        simp only [List.append_nil, List.nil_append] at hu hrest
        right
        refine ⟨r.2 ++ s.map symbol.terminal, ?_, ?_⟩
        · simp [hu]
        · exact ⟨r, hr, [], s, hrest.symm, rfl⟩
    | cons b bs =>
        simp only [List.cons_append, List.cons.injEq] at hrest
        obtain ⟨rfl, hs⟩ := hrest
        have hs' : s.map (symbol.terminal (N := G.nt)) = bs ++ v := by
          simpa using hs
        obtain ⟨ws, wv, rfl, hbs, hv⟩ :=
          append_eq_map_terminal_split hs'.symm
        left
        refine ⟨p ++ r.2 ++ ws.map symbol.terminal, wv, hv, ?_, ?_⟩
        · simp [List.append_assoc, hv]
        · exact ⟨r, hr, p, ws,
            by simpa [hbs, List.append_assoc] using hu, rfl⟩

/-- Trace a nonterminal in the result of one rightmost step.  It was either
already to the left of the rewritten (rightmost) nonterminal, or it occurs in
the right-hand side of the rule used by the step. -/
public theorem ProducesRightmost.preimage_nonterminal
    {y p q : List (symbol T G.nt)} {A : G.nt}
    (h : G.ProducesRightmost y
      (p ++ [symbol.nonterminal A] ++ q)) :
    (∃ q₀, y = p ++ [symbol.nonterminal A] ++ q₀ ∧
      G.ProducesRightmost q₀ q) ∨
    (∃ r ∈ G.rules,
      ∃ (p₀ α β : List (symbol T G.nt)) (t : List T),
        r.2 = α ++ [symbol.nonterminal A] ++ β ∧
        p = p₀ ++ α ∧ q = β ++ t.map symbol.terminal ∧
        y = p₀ ++ [symbol.nonterminal r.1] ++
          t.map symbol.terminal) := by
  rcases h with ⟨r, hr, pre, t, hsource, htarget⟩
  have htarget' : p ++ ([symbol.nonterminal A] ++ q) =
      pre ++ (r.2 ++ t.map symbol.terminal) := by
    simpa [List.append_assoc] using htarget
  rw [List.append_eq_append_iff] at htarget'
  rcases htarget' with ⟨as, hpre, htail⟩ | ⟨bs, hp, htail⟩
  · cases as with
    | nil =>
        simp only [List.append_nil, List.nil_append] at hpre htail
        have hloc : r.2 ++ t.map symbol.terminal =
            [] ++ ([symbol.nonterminal A] ++ q) := by
          simpa using htail.symm
        rw [List.append_eq_append_iff] at hloc
        rcases hloc with ⟨cs, _, hterm⟩ | ⟨cs, hrhs, hrest⟩
        · have hmem : symbol.nonterminal A ∈
              t.map (symbol.terminal (N := G.nt)) := by
            rw [hterm]
            simp
          simp at hmem
        · cases cs with
          | nil =>
              simp only [List.append_nil, List.nil_append] at hrhs hrest
              have hmem : symbol.nonterminal A ∈
                  t.map (symbol.terminal (N := G.nt)) := by
                rw [← hrest]
                simp
              simp at hmem
          | cons c cs =>
              simp only [List.cons_append, List.cons.injEq] at hrest
              obtain ⟨rfl, hq⟩ := hrest
              right
              refine ⟨r, hr, pre, [], cs, t, ?_, ?_, ?_, hsource⟩
              · simpa using hrhs
              · simp [hpre]
              · simpa using hq
    | cons c cs =>
        simp only [List.cons_append, List.cons.injEq] at htail
        obtain ⟨rfl, hq⟩ := htail
        left
        refine ⟨cs ++ [symbol.nonterminal r.1] ++
          t.map symbol.terminal, ?_, ?_⟩
        · rw [hsource, hpre]
          simp [List.append_assoc]
        · exact ⟨r, hr, cs, t, rfl,
            by simpa [List.append_assoc] using hq⟩
  · have hloc : r.2 ++ t.map symbol.terminal =
        bs ++ ([symbol.nonterminal A] ++ q) := by
      simpa [List.append_assoc] using htail
    rw [List.append_eq_append_iff] at hloc
    rcases hloc with ⟨cs, _, hterm⟩ | ⟨cs, hrhs, hrest⟩
    · have hmem : symbol.nonterminal A ∈
          t.map (symbol.terminal (N := G.nt)) := by
        rw [hterm]
        simp
      simp at hmem
    · cases cs with
      | nil =>
          simp only [List.append_nil, List.nil_append] at hrhs hrest
          have hmem : symbol.nonterminal A ∈
              t.map (symbol.terminal (N := G.nt)) := by
            rw [← hrest]
            simp
          simp at hmem
      | cons c cs =>
          simp only [List.cons_append, List.cons.injEq] at hrest
          obtain ⟨rfl, hq⟩ := hrest
          right
          refine ⟨r, hr, pre, bs, cs, t, ?_, ?_, ?_, hsource⟩
          · simpa [List.append_assoc] using hrhs
          · exact hp
          · simpa using hq

/-- A derivation of an append to a terminal word uniquely separates into
rightmost derivations of its two components. -/
public theorem DerivesRightmost.append_to_terminals_split
    {u v : List (symbol T G.nt)} {w : List T}
    (h : G.DerivesRightmost (u ++ v) (w.map symbol.terminal)) :
    ∃ wu wv, w = wu ++ wv ∧
      G.DerivesRightmost u (wu.map symbol.terminal) ∧
      G.DerivesRightmost v (wv.map symbol.terminal) := by
  have aux : ∀ {x : List (symbol T G.nt)},
      G.DerivesRightmost x (w.map symbol.terminal) →
      ∀ {u v : List (symbol T G.nt)}, x = u ++ v →
      ∃ wu wv, w = wu ++ wv ∧
        G.DerivesRightmost u (wu.map symbol.terminal) ∧
        G.DerivesRightmost v (wv.map symbol.terminal) := by
    intro x hx
    induction hx using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro u v huv
        obtain ⟨wu, wv, hw, hu, hv⟩ :=
          append_eq_map_terminal_split huv.symm
        subst u
        subst v
        exact ⟨wu, wv, hw, Relation.ReflTransGen.refl,
          Relation.ReflTransGen.refl⟩
    | @head a b hstep hrest ih =>
        intro u v huv
        subst a
        rcases hstep.append_cases with hleft | hright
        · rcases hleft with ⟨u', wv₀, hvterm, hb, hustep⟩
          obtain ⟨wu, wv, hw, huder, hvder⟩ := ih hb
          have hvder' : G.DerivesRightmost
              (wv₀.map symbol.terminal) (wv.map symbol.terminal) := by
            simpa [hvterm] using hvder
          have hmaps : wv.map symbol.terminal =
              wv₀.map (symbol.terminal (N := G.nt)) :=
            hvder'.eq_of_map_terminal_source
          have hwv : wv = wv₀ := by
            exact (List.map_injective_iff.mpr fun _ _ h =>
              symbol.terminal.inj h) hmaps
          subst wv
          exact ⟨wu, wv₀, hw,
            hustep.single.trans huder, hvder⟩
        · rcases hright with ⟨v', hb, hvstep⟩
          obtain ⟨wu, wv, hw, huder, hvder⟩ := ih hb
          exact ⟨wu, wv, hw, huder, hvstep.single.trans hvder⟩
  exact aux h rfl

/-! ## Ancestry of a surviving nonterminal -/

private theorem derivesRightmost_nonterminal_ancestry_aux
    {x : List (symbol T G.nt)}
    (h : G.DerivesRightmost [symbol.nonterminal G.initial] x) :
    ∀ (p : List (symbol T G.nt)) (A : G.nt)
        (q : List (symbol T G.nt)) (s : List T),
      x = p ++ [symbol.nonterminal A] ++ q →
      G.DerivesRightmost q (s.map symbol.terminal) →
      (p = [] ∧ A = G.initial ∧ s = []) ∨
      ∃ r ∈ G.rules,
        ∃ (p₀ α β : List (symbol T G.nt)) (t z : List T),
          r.2 = α ++ [symbol.nonterminal A] ++ β ∧
          p = p₀ ++ α ∧ s = z ++ t ∧
          G.DerivesRightmost [symbol.nonterminal G.initial]
            (p₀ ++ [symbol.nonterminal r.1] ++
              t.map symbol.terminal) ∧
          G.DerivesRightmost β (z.map symbol.terminal) := by
  induction h with
  | refl =>
      intro p A q s hshape hq
      cases p with
      | nil =>
          simp at hshape
          rcases hshape with ⟨rfl, rfl⟩
          have hq' : G.DerivesRightmost
              (([] : List T).map symbol.terminal)
              (s.map symbol.terminal) := by
            simpa using hq
          have hsmap := hq'.eq_of_map_terminal_source
          have hs : s = [] := by
            have hinj : Function.Injective
                (symbol.terminal (T := T) (N := G.nt)) :=
              fun _ _ h => symbol.terminal.inj h
            exact (List.map_injective_iff.mpr hinj) (by simpa using hsmap)
          exact Or.inl ⟨rfl, rfl, hs⟩
      | cons a p =>
          simp at hshape
  | @tail b c hprev hstep ih =>
      intro p A q s hshape hq
      have hstep' : G.ProducesRightmost b
          (p ++ [symbol.nonterminal A] ++ q) := by
        rw [← hshape]
        exact hstep
      rcases hstep'.preimage_nonterminal with hbefore | hintroduced
      · rcases hbefore with ⟨q₀, hb, hqstep⟩
        exact ih p A q₀ s hb (hqstep.single.trans hq)
      · rcases hintroduced with
          ⟨r, hr, p₀, α, β, t, hrhs, hp, hqshape, hb⟩
        have hfinish : G.DerivesRightmost
            (β ++ t.map symbol.terminal) (s.map symbol.terminal) := by
          rw [← hqshape]
          exact hq
        obtain ⟨z, t', hs, hbeta, ht⟩ :=
          hfinish.append_to_terminals_split
        have htmap : t'.map symbol.terminal =
            t.map (symbol.terminal (N := G.nt)) :=
          ht.eq_of_map_terminal_source
        have htt : t' = t :=
          (List.map_injective_iff.mpr fun _ _ h =>
            symbol.terminal.inj h) htmap
        subst t'
        right
        refine ⟨r, hr, p₀, α, β, t, z, hrhs, hp, hs, ?_, hbeta⟩
        rw [← hb]
        exact hprev

/-- A nonterminal surviving in a right-sentential form is either the untouched
start symbol, or descends from a concrete occurrence in the right-hand side of
a rule.  The rule's suffix derives exactly the terminal segment immediately
following that occurrence; the remaining terminal suffix was already present
when the rule was applied. -/
public theorem derivesRightmost_nonterminal_ancestry
    (G : CF_grammar T) {p : List (symbol T G.nt)} {A : G.nt}
    {s : List T}
    (h : G.DerivesRightmost [symbol.nonterminal G.initial]
      (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal)) :
    (p = [] ∧ A = G.initial ∧ s = []) ∨
    ∃ r ∈ G.rules,
      ∃ (p₀ α β : List (symbol T G.nt)) (t z : List T),
        r.2 = α ++ [symbol.nonterminal A] ++ β ∧
        p = p₀ ++ α ∧ s = z ++ t ∧
        G.DerivesRightmost [symbol.nonterminal G.initial]
          (p₀ ++ [symbol.nonterminal r.1] ++ t.map symbol.terminal) ∧
        G.DerivesRightmost β (z.map symbol.terminal) := by
  exact derivesRightmost_nonterminal_ancestry_aux h
    p A (s.map symbol.terminal) s rfl Relation.ReflTransGen.refl

private theorem derivesRightmostIn_nonterminal_ancestry_aux
    {n : ℕ} {x : List (symbol T G.nt)}
    (h : G.DerivesRightmostIn n
      [symbol.nonterminal G.initial] x) :
    ∀ (p : List (symbol T G.nt)) (A : G.nt)
        (q : List (symbol T G.nt)) (s : List T),
      x = p ++ [symbol.nonterminal A] ++ q →
      G.DerivesRightmost q (s.map symbol.terminal) →
      (p = [] ∧ A = G.initial ∧ s = []) ∨
      ∃ (m : ℕ) (r : G.nt × List (symbol T G.nt)), r ∈ G.rules ∧
        ∃ (p₀ α β : List (symbol T G.nt)) (t z : List T),
          m < n ∧
          r.2 = α ++ [symbol.nonterminal A] ++ β ∧
          p = p₀ ++ α ∧ s = z ++ t ∧
          G.DerivesRightmostIn m [symbol.nonterminal G.initial]
            (p₀ ++ [symbol.nonterminal r.1] ++
              t.map symbol.terminal) ∧
          G.DerivesRightmost β (z.map symbol.terminal) := by
  generalize hstart : [symbol.nonterminal G.initial] = start at h
  induction h with
  | refl =>
      intro p A q s hshape hq
      have hshape' : [symbol.nonterminal G.initial] =
          p ++ [symbol.nonterminal A] ++ q := hstart.trans hshape
      cases p with
      | nil =>
          simp at hshape'
          rcases hshape' with ⟨rfl, rfl⟩
          have hq' : G.DerivesRightmost
              (([] : List T).map symbol.terminal)
              (s.map symbol.terminal) := by
            simpa using hq
          have hsmap := hq'.eq_of_map_terminal_source
          have hs : s = [] := by
            have hinj : Function.Injective
                (symbol.terminal (T := T) (N := G.nt)) :=
              fun _ _ h => symbol.terminal.inj h
            exact (List.map_injective_iff.mpr hinj) (by simpa using hsmap)
          exact Or.inl ⟨rfl, rfl, hs⟩
      | cons a p =>
          simp at hshape'
  | @tail n start b c hprev hstep ih =>
      intro p A q s hshape hq
      have hstep' : G.ProducesRightmost b
          (p ++ [symbol.nonterminal A] ++ q) := by
        rw [← hshape]
        exact hstep
      rcases hstep'.preimage_nonterminal with hbefore | hintroduced
      · rcases hbefore with ⟨q₀, hb, hqstep⟩
        rcases ih hstart p A q₀ s hb (hqstep.single.trans hq) with
          hbase | ⟨m, r, hr, p₀, α, β, t, z, hm, hrhs, hp, hs,
            hparent, hbeta⟩
        · exact Or.inl hbase
        · right
          exact ⟨m, r, hr, p₀, α, β, t, z, by omega,
            hrhs, hp, hs, hparent, hbeta⟩
      · rcases hintroduced with
          ⟨r, hr, p₀, α, β, t, hrhs, hp, hqshape, hb⟩
        have hfinish : G.DerivesRightmost
            (β ++ t.map symbol.terminal) (s.map symbol.terminal) := by
          rw [← hqshape]
          exact hq
        obtain ⟨z, t', hs, hbeta, ht⟩ :=
          hfinish.append_to_terminals_split
        have htmap : t'.map symbol.terminal =
            t.map (symbol.terminal (N := G.nt)) :=
          ht.eq_of_map_terminal_source
        have htt : t' = t :=
          (List.map_injective_iff.mpr fun _ _ h =>
            symbol.terminal.inj h) htmap
        subst t'
        right
        refine ⟨n, r, hr, p₀, α, β, t, z, by omega,
          hrhs, hp, hs, ?_, hbeta⟩
        rw [← hb]
        exact hprev

/-- Counted form of `derivesRightmost_nonterminal_ancestry`.  In the non-base
case the parent prehandle is reached in strictly fewer steps than the displayed
surviving configuration.  This strict measure supports terminating reverse
item-closure and ancestry arguments even when the grammar contains cycles. -/
public theorem derivesRightmostIn_nonterminal_ancestry
    (G : CF_grammar T) {n : ℕ}
    {p : List (symbol T G.nt)} {A : G.nt} {s : List T}
    (h : G.DerivesRightmostIn n [symbol.nonterminal G.initial]
      (p ++ [symbol.nonterminal A] ++ s.map symbol.terminal)) :
    (p = [] ∧ A = G.initial ∧ s = []) ∨
    ∃ (m : ℕ) (r : G.nt × List (symbol T G.nt)), r ∈ G.rules ∧
      ∃ (p₀ α β : List (symbol T G.nt)) (t z : List T),
        m < n ∧
        r.2 = α ++ [symbol.nonterminal A] ++ β ∧
        p = p₀ ++ α ∧ s = z ++ t ∧
        G.DerivesRightmostIn m [symbol.nonterminal G.initial]
          (p₀ ++ [symbol.nonterminal r.1] ++ t.map symbol.terminal) ∧
        G.DerivesRightmost β (z.map symbol.terminal) := by
  exact derivesRightmostIn_nonterminal_ancestry_aux h
    p A (s.map symbol.terminal) s rfl Relation.ReflTransGen.refl

/-! ## Equivalence with unrestricted scheduling on terminal results -/

public theorem transforms_of_producesRightmost
    {u v : List (symbol T G.nt)}
    (h : G.ProducesRightmost u v) : CF_transforms G u v := by
  rcases h with ⟨r, hr, p, s, hu, hv⟩
  exact ⟨r, p, s.map symbol.terminal, hr, hu, hv⟩

public theorem derives_of_derivesRightmost
    {u v : List (symbol T G.nt)}
    (h : G.DerivesRightmost u v) : CF_derives G u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (transforms_of_producesRightmost hstep)

/-- Every context-free derivation ending in terminals has a rightmost
scheduling. -/
public theorem derivesRightmost_of_derives
    {u : List (symbol T G.nt)} {w : List T}
    (h : CF_derives G u (w.map symbol.terminal)) :
    G.DerivesRightmost u (w.map symbol.terminal) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hstep hrest ih =>
      rcases hstep with ⟨r, p, q, hr, hsource, htarget⟩
      have ih' : G.DerivesRightmost
          (p ++ r.2 ++ q) (w.map symbol.terminal) := by
        rw [← htarget]
        exact ih
      obtain ⟨wp, wq, hw, hp, hq⟩ :=
        DerivesRightmost.append_to_terminals_split
          (u := p ++ r.2) (v := q) (by
            simpa [List.append_assoc] using ih')
      have hq' := hq.append_left (p ++ [symbol.nonterminal r.1])
      have hreduce : G.ProducesRightmost
          (p ++ [symbol.nonterminal r.1] ++ wq.map symbol.terminal)
          (p ++ r.2 ++ wq.map symbol.terminal) :=
        ⟨r, hr, p, wq, rfl, rfl⟩
      have hp' := hp.append_terminals_right wq
      rw [hsource, hw, List.map_append]
      have hq'' : G.DerivesRightmost
          (p ++ [symbol.nonterminal r.1] ++ q)
          (p ++ [symbol.nonterminal r.1] ++ wq.map symbol.terminal) := by
        simpa [List.append_assoc] using hq'
      have hp'' : G.DerivesRightmost
          (p ++ r.2 ++ wq.map symbol.terminal)
          (wp.map symbol.terminal ++ wq.map symbol.terminal) := by
        simpa [List.append_assoc] using hp'
      exact hq''.trans (hreduce.single.trans hp'')

public theorem derivesRightmost_iff
    {u : List (symbol T G.nt)} {w : List T} :
    G.DerivesRightmost u (w.map symbol.terminal) ↔
      CF_derives G u (w.map symbol.terminal) :=
  ⟨derives_of_derivesRightmost, derivesRightmost_of_derives⟩

end CF_grammar
