module

/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Linear.Pumping.Spine
public import Langlib.Classes.ContextFree.Pumping.Utils
@[expose]
public section



/-! # The pumping lemma for linear languages

A linear language `L` has a constant `p` such that every `w ∈ L` with `|w| ≥ p`
can be written `w = u v x y z` with `v y` nonempty, `|u v y z| ≤ p` (the pumped
pieces and outer pieces are confined to the two ends), and `u vⁱ x yⁱ z ∈ L`
for all `i`.

The decisive difference from the context-free pumping lemma is the bound: here
the **outer** material `u v y z` is bounded, forcing `v` to lie near the start of
`w` and `y` near its end.
-/

open Relation

variable {T : Type}

/-- Pigeonhole core. Given a "root" colouring landing in a finite set `S`, a
monotone "count" with bounded increments starting at `0`, and a depth `N` whose
count is at least `S.card * (c+1)`, there are two depths `i < j` with the same
root, strictly increasing count, and `cnt j ≤ (S.card + 1) * (c + 1)`. -/
public lemma exists_pump_indices {α : Type*} [DecidableEq α] (S : Finset α)
    (root : ℕ → α) (cnt : ℕ → ℕ) (c : ℕ)
    (hroot : ∀ k, root k ∈ S)
    (hmono : Monotone cnt)
    (hstep : ∀ k, cnt (k + 1) ≤ cnt k + c)
    (h0 : cnt 0 = 0)
    (N : ℕ) (hN : S.card * (c + 1) ≤ cnt N) :
    ∃ i j, i < j ∧ root i = root j ∧ cnt i < cnt j ∧ cnt j ≤ (S.card + 1) * (c + 1) := by
  classical
  set r := S.card with hr
  -- For each `b ≤ r`, there is a depth whose count reaches the threshold `b*(c+1)`.
  have hex : ∀ b : Fin (r + 1), ∃ k, (b : ℕ) * (c + 1) ≤ cnt k := fun b =>
    ⟨N, le_trans (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ b.isLt)) hN⟩
  -- Lower and upper bounds on the count at each threshold depth.
  have hlb : ∀ b : Fin (r + 1), (b : ℕ) * (c + 1) ≤ cnt (Nat.find (hex b)) :=
    fun b => Nat.find_spec (hex b)
  have hub : ∀ b : Fin (r + 1), cnt (Nat.find (hex b)) ≤ (b : ℕ) * (c + 1) + c := by
    intro b
    rcases Nat.eq_zero_or_pos (Nat.find (hex b)) with h0t | hpos
    · rw [h0t, h0]; exact Nat.zero_le _
    · have hmin : ¬ (b : ℕ) * (c + 1) ≤ cnt (Nat.find (hex b) - 1) :=
        Nat.find_min (hex b) (Nat.sub_lt hpos Nat.one_pos)
      have hs := hstep (Nat.find (hex b) - 1)
      have heq : Nat.find (hex b) - 1 + 1 = Nat.find (hex b) := by omega
      rw [heq] at hs
      omega
  -- Pigeonhole: r+1 thresholds, r colours.
  have hmaps : ∀ b ∈ (Finset.univ : Finset (Fin (r + 1))), root (Nat.find (hex b)) ∈ S :=
    fun b _ => hroot _
  have hcard : S.card < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨a, -, b, -, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  -- Order the two by value; the smaller-threshold one has strictly smaller count.
  have key : ∀ p q : Fin (r + 1), (p : ℕ) < (q : ℕ) →
      root (Nat.find (hex p)) = root (Nat.find (hex q)) →
      ∃ i j, i < j ∧ root i = root j ∧ cnt i < cnt j ∧ cnt j ≤ (r + 1) * (c + 1) := by
    intro p q hpq hrr
    have hcnt : cnt (Nat.find (hex p)) < cnt (Nat.find (hex q)) := by
      have h1 := hub p
      have h2 := hlb q
      have hmul : ((p : ℕ) + 1) * (c + 1) ≤ (q : ℕ) * (c + 1) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hpq)
      have hexp : ((p : ℕ) + 1) * (c + 1) = (p : ℕ) * (c + 1) + (c + 1) := Nat.succ_mul _ _
      omega
    have hij : Nat.find (hex p) < Nat.find (hex q) := by
      by_contra hcon
      push_neg at hcon
      exact absurd (hmono hcon) (by omega)
    refine ⟨_, _, hij, hrr, hcnt, ?_⟩
    have hqb := hub q
    have hmul : (q : ℕ) * (c + 1) ≤ r * (c + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt_succ q.isLt)
    have hexp : (r + 1) * (c + 1) = r * (c + 1) + (c + 1) := Nat.succ_mul _ _
    omega
  rcases lt_or_gt_of_ne (fun h => hab (Fin.ext h)) with h | h
  · exact key a b h hfab
  · exact key b a h hfab.symm

/-- A derivation `C ⇒* β` can be performed inside a terminal context `p · q`. -/
public lemma deri_ctx {g : grammar T} {C : g.nt} {β p q : List (symbol T g.nt)}
    (h : grammar_derives g [symbol.nonterminal C] β) :
    grammar_derives g (p ++ [symbol.nonterminal C] ++ q) (p ++ β ++ q) := by
  have := grammar_deri_with_prefix p (grammar_deri_with_postfix q h)
  simpa [List.append_assoc] using this

/-- Iterating a self-embedding derivation `C ⇒* v · C · x` pumps both ends. -/
public lemma pump_derives {g : grammar T} {C : g.nt} {v x : List T}
    (h : grammar_derives g [symbol.nonterminal C]
      (List.map symbol.terminal v ++ [symbol.nonterminal C] ++ List.map symbol.terminal x)) :
    ∀ n, grammar_derives g [symbol.nonterminal C]
      (List.map symbol.terminal (v ^+^ n) ++ [symbol.nonterminal C]
        ++ List.map symbol.terminal (x ^+^ n))
  | 0 => by
      simpa [nTimes] using grammar_deri_self (g := g) (w := [symbol.nonterminal C])
  | n + 1 => by
      have ih := pump_derives h n
      have mid := deri_ctx (p := List.map symbol.terminal v) (q := List.map symbol.terminal x) ih
      have step := grammar_deri_of_deri_deri h mid
      rw [show (v : List T) ^+^ (n + 1) = v ++ v ^+^ n from nTimes_succ_l,
          show (x : List T) ^+^ (n + 1) = x ^+^ n ++ x from nTimes_succ_r]
      simpa [List.map_append, List.append_assoc] using step

/-- **Pumping lemma for linear languages.** Every linear language `L` has a constant
`p` such that any `w ∈ L` with `|w| ≥ p` factors as `w = u v x y z` with `v y`
nonempty, the outer material `u v y z` bounded by `p`, and `u vⁱ x yⁱ z ∈ L` for all `i`. -/
public theorem is_Linear.pumping {L : Language T} (hL : is_Linear L) :
    ∃ p : ℕ, ∀ w ∈ L, w.length ≥ p → ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      (v ++ y).length > 0 ∧
      (u ++ v ++ y ++ z).length ≤ p ∧
      ∀ n : ℕ, u ++ v ^+^ n ++ x ++ y ^+^ n ++ z ∈ L := by
  obtain ⟨g, hg, rfl⟩ := hL
  classical
  set S : Finset g.nt := (g.rules.map (·.input_N)).toFinset with hS
  set c : ℕ := maxRuleLen g with hc
  refine ⟨(S.card + 1) * (c + 1), ?_⟩
  intro w hw hwlen
  have hgen : grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w) := hw
  obtain ⟨s⟩ := exists_spine hg hgen
  -- the colouring lands in the finite set of rule nonterminals
  have hroot : ∀ k, (Spine.splitAt s k).C ∈ S := by
    intro k
    rw [hS, List.mem_toFinset]
    exact Spine.root_mem (Spine.splitAt s k).inner
  -- the word is long enough to force the count past the pigeonhole threshold
  have hN : S.card * (c + 1) ≤ Spine.cnt s s.length := by
    have h1 := Spine.cnt_length_ge s
    have hexp : (S.card + 1) * (c + 1) = S.card * (c + 1) + (c + 1) := Nat.succ_mul _ _
    omega
  obtain ⟨i, j, hij, hrooteq, hcntlt, hbound⟩ :=
    exists_pump_indices S (fun k => (Spine.splitAt s k).C) (Spine.cnt s) c
      hroot (Spine.cnt_mono s) (Spine.cnt_step s) (Spine.cnt_zero s) s.length hN
  -- name the two splits
  set P1 := Spine.splitAt s i with hP1
  set P2 := Spine.splitAt P1.inner (j - i) with hP2
  have hji : i + (j - i) = j := by omega
  -- the repeated nonterminal
  have hC : P2.C = P1.C := by
    have hadd := Spine.splitAt_add_C s i (j - i)
    rw [hji] at hadd
    exact (hrooteq.trans hadd).symm
  -- arithmetic facts about the counts
  have hcadd : Spine.cnt s j = Spine.cnt s i + Spine.cnt P1.inner (j - i) := by
    have := Spine.cnt_add s i (j - i); rwa [hji] at this
  have hP2len : Spine.cnt P1.inner (j - i) = P2.u.length + P2.y.length := rfl
  have hcnti : Spine.cnt s i = P1.u.length + P1.y.length := rfl
  refine ⟨P1.u, P2.u, P2.wc, P2.y, P1.y, ?_, ?_, ?_, ?_⟩
  · -- w = u v x y z, via value-level transitivity (the indices forbid rewriting `w`)
    have := P1.hword.trans (congrArg (fun t => P1.u ++ t ++ P1.y) P2.hword)
    simpa [List.append_assoc] using this
  · -- v y nonempty
    rw [List.length_append]; omega
  · -- bound on the outer pieces
    simp only [List.length_append]; omega
  · -- pumping closure
    intro n
    have hpumpbase : grammar_derives g [symbol.nonterminal P1.C]
        (List.map symbol.terminal P2.u ++ [symbol.nonterminal P1.C]
          ++ List.map symbol.terminal P2.y) := by
      have h := P2.hderiv; rw [hC] at h; exact h
    have hpump := pump_derives hpumpbase n
    have hcore : grammar_derives g [symbol.nonterminal P1.C] (List.map symbol.terminal P2.wc) := by
      have h := P2.inner.derives; rw [hC] at h; exact h
    have inner := grammar_deri_of_deri_deri hpump
      (deri_ctx (p := List.map symbol.terminal (P2.u ^+^ n))
        (q := List.map symbol.terminal (P2.y ^+^ n)) hcore)
    have full := grammar_deri_of_deri_deri P1.hderiv
      (deri_ctx (p := List.map symbol.terminal P1.u)
        (q := List.map symbol.terminal P1.y) inner)
    show grammar_derives g [symbol.nonterminal g.initial]
      (List.map symbol.terminal (P1.u ++ P2.u ^+^ n ++ P2.wc ++ P2.y ^+^ n ++ P1.y))
    simpa [List.map_append, List.append_assoc] using full
