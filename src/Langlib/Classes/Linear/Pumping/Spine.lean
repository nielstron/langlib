module

/-
Copyright (c) 2026 Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Langlib.Classes.Linear.Definition
public import Langlib.Grammars.Unrestricted.Toolbox
@[expose]
public section



/-! # Spines of linear derivations

A linear grammar derives a terminal word from a single nonterminal along a
single "spine": every sentential form has the shape
`map terminal p ++ [nonterminal C] ++ map terminal s`, until a terminal rule is
applied. This file reifies that spine as an inductive `Spine`, proves it sound
and complete with respect to `grammar_derives`, and equips it with the
bookkeeping (length, list of visited nonterminals, accumulated terminal counts)
needed for the linear pumping lemma.

## Main declarations

- `Spine`                — the caterpillar derivation from a nonterminal to a word.
- `Spine.derives`        — soundness: a spine yields a `grammar_derives`.
- `exists_spine`         — completeness: a linear derivation yields a spine.
-/

open Relation

variable {T : Type} {g : grammar T}

/-- A `Spine g B w` witnesses, for a linear grammar `g`, a derivation of the
terminal word `w` from the single nonterminal `B`, recorded as the chain of
rules applied along the unique nonterminal. -/
public inductive Spine {T : Type} (g : grammar T) : g.nt → List T → Type
  /-- The final step: a purely terminal rule `B → m`. -/
  | last (B : g.nt) (m : List T)
      (h : (⟨[], B, [], List.map symbol.terminal m⟩ : grule T g.nt) ∈ g.rules) :
      Spine g B m
  /-- A spine step: a rule `B → u C v` with `u, v` terminal, then continue from `C`. -/
  | cons (B C : g.nt) (u v : List T) (m : List T)
      (h : (⟨[], B, [], List.map symbol.terminal u ++ [symbol.nonterminal C] ++
              List.map symbol.terminal v⟩ : grule T g.nt) ∈ g.rules)
      (rest : Spine g C m) :
      Spine g B (u ++ m ++ v)

namespace Spine

/-- Soundness: a spine gives an actual derivation `B ⇒* w`. -/
public def derives : {B : g.nt} → {w : List T} → Spine g B w →
    grammar_derives g [symbol.nonterminal B] (List.map symbol.terminal w)
  | _, _, last B m h =>
      grammar_deri_of_tran ⟨_, h, [], [], by simp, by simp⟩
  | _, _, cons B C u v m h rest => by
      have step1 : grammar_derives g [symbol.nonterminal B]
          (List.map symbol.terminal u ++ [symbol.nonterminal C] ++ List.map symbol.terminal v) :=
        grammar_deri_of_tran ⟨_, h, [], [], by simp, by simp⟩
      have hpost := grammar_deri_with_postfix (List.map symbol.terminal v) rest.derives
      have hpre := grammar_deri_with_prefix (List.map symbol.terminal u) hpost
      have step2 : grammar_derives g
          (List.map symbol.terminal u ++ [symbol.nonterminal C] ++ List.map symbol.terminal v)
          (List.map symbol.terminal (u ++ m ++ v)) := by
        simpa [List.map_append, List.append_assoc] using hpre
      exact grammar_deri_of_deri_deri step1 step2

/-- The number of rule applications recorded by the spine. -/
public def length : {B : g.nt} → {w : List T} → Spine g B w → ℕ
  | _, _, last _ _ _ => 1
  | _, _, cons _ _ _ _ _ _ rest => rest.length + 1

/-- The list of nonterminals visited along the spine, from top to bottom. -/
public def nts : {B : g.nt} → {w : List T} → Spine g B w → List g.nt
  | _, _, last B _ _ => [B]
  | _, _, cons B _ _ _ _ _ rest => B :: rest.nts

end Spine

/-! ## Completeness: every linear derivation is a spine -/

/-- A terminal-only sentential form admits no transformation step. -/
public lemma not_transforms_map_terminal {a : List T} {z : List (symbol T g.nt)} :
    ¬ grammar_transforms g (List.map symbol.terminal a) z := by
  rintro ⟨r, _, u, v, hbef, _⟩
  have hmem : symbol.nonterminal r.input_N ∈ List.map symbol.terminal a := by
    rw [hbef]; simp
  simp [List.mem_map] at hmem

/-- From a terminal-only form, any derivation reaches only that same form. -/
public lemma eq_of_deri_from_terminals {a : List T} {z : List (symbol T g.nt)}
    (h : grammar_derives g (List.map symbol.terminal a) z) :
    z = List.map symbol.terminal a := by
  rcases grammar_tran_or_id_of_deri h with heq | ⟨v, htr, -⟩
  · exact heq.symm
  · exact absurd htr not_transforms_map_terminal

/-- A symbol list whose every element is a terminal is the image of a terminal word. -/
public lemma eq_map_terminal_of_all_terminal {l : List (symbol T g.nt)}
    (h : ∀ x ∈ l, ∃ t, x = symbol.terminal t) :
    ∃ o : List T, l = List.map symbol.terminal o := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      obtain ⟨t, rfl⟩ := h x (List.mem_cons_self ..)
      obtain ⟨o, ho⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      exact ⟨t :: o, by simp [ho]⟩

/-- In a terminal sandwich `map p ++ [nt C] ++ map s = u ++ [nt N'] ++ v`, the
nonterminal is forced to line up: `u = map p`, `N' = C`, `v = map s`. -/
public lemma eq_of_terminal_sandwich {p s : List T} {C N' : g.nt}
    {u v : List (symbol T g.nt)}
    (h : List.map symbol.terminal p ++ [symbol.nonterminal C] ++ List.map symbol.terminal s
       = u ++ [symbol.nonterminal N'] ++ v) :
    u = List.map symbol.terminal p ∧ N' = C ∧ v = List.map symbol.terminal s := by
  rw [List.append_assoc, List.append_assoc] at h
  rcases (List.append_eq_append_iff.1 h) with ⟨a, hu, htail⟩ | ⟨c, hp, htail⟩
  · -- u = map p ++ a  and  [nt C] ++ map s = a ++ ([nt N'] ++ v)
    cases a with
    | nil =>
        simp only [List.nil_append, List.append_nil, List.cons_append] at hu htail
        refine ⟨hu, ?_, ?_⟩ <;> simp_all
    | cons hd tl =>
        exfalso
        simp only [List.nil_append, List.cons_append] at htail
        injection htail with _ htl
        have hmem : symbol.nonterminal N' ∈ List.map symbol.terminal s := by
          rw [htl]; simp
        simp [List.mem_map] at hmem
  · -- map p = u ++ c  and  c ++ ([nt C] ++ map s) = [nt N'] ++ v
    cases c with
    | nil =>
        simp only [List.nil_append, List.append_nil, List.cons_append] at hp htail
        refine ⟨hp.symm, ?_, ?_⟩ <;> simp_all
    | cons hd tl =>
        exfalso
        have hmem : hd ∈ List.map symbol.terminal p := by rw [hp]; simp
        simp only [List.nil_append, List.cons_append] at htail
        injection htail with hhd _
        rw [← hhd] at hmem
        simp [List.mem_map] at hmem

/-- In a linear grammar, a transformation step from a terminal sandwich
`map p ++ [nt C] ++ map s` rewrites exactly the nonterminal `C` in place. -/
public lemma linear_transforms_at_nt (hg : grammar_linear g) {p s : List T} {C : g.nt}
    {x' : List (symbol T g.nt)}
    (h : grammar_transforms g
          (List.map symbol.terminal p ++ [symbol.nonterminal C] ++ List.map symbol.terminal s) x') :
    ∃ out : List (symbol T g.nt),
      (⟨[], C, [], out⟩ : grule T g.nt) ∈ g.rules ∧
      x' = List.map symbol.terminal p ++ out ++ List.map symbol.terminal s := by
  obtain ⟨r, hr, u, v, hbef, haft⟩ := h
  obtain ⟨hL, hR, -⟩ := hg r hr
  rw [hL, hR] at hbef
  simp only [List.append_nil] at hbef
  obtain ⟨hu, hN, hv⟩ := eq_of_terminal_sandwich hbef
  refine ⟨r.output_string, ?_, ?_⟩
  · subst hN; cases r with | mk iL iN iR os => simp_all
  · rw [haft, hu, hv]

/-- Completeness (general form): a linear derivation from a terminal sandwich
`map p ++ [nt C] ++ map s` to a terminal word `map w` factors through `C`. -/
public lemma spine_of_deri (hg : grammar_linear g) {w : List T} :
    ∀ {x : List (symbol T g.nt)}, grammar_derives g x (List.map symbol.terminal w) →
      ∀ {p s : List T} {C : g.nt},
        x = List.map symbol.terminal p ++ [symbol.nonterminal C] ++ List.map symbol.terminal s →
        ∃ m : List T, w = p ++ m ++ s ∧ Nonempty (Spine g C m) := by
  intro x h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro p s C hx
      exfalso
      have hmem : symbol.nonterminal C ∈ List.map symbol.terminal w := by rw [hx]; simp
      simp [List.mem_map] at hmem
  | @head x x' hstep hrest ih =>
      intro p s C hx
      subst hx
      obtain ⟨out, hout_mem, hx'⟩ := linear_transforms_at_nt hg hstep
      rcases (hg _ hout_mem).2.2 with hterm | ⟨o₁, C₁, o₂, hout⟩
      · -- terminal output: the derivation must already be finished
        obtain ⟨o, rfl⟩ := eq_map_terminal_of_all_terminal hterm
        have hx'' : x' = List.map symbol.terminal (p ++ o ++ s) := by
          rw [hx']; simp [List.map_append, List.append_assoc]
        have hwe : List.map symbol.terminal w = List.map symbol.terminal (p ++ o ++ s) :=
          eq_of_deri_from_terminals (hx'' ▸ hrest)
        have hinj : Function.Injective (symbol.terminal (T := T) (N := g.nt)) := by
          intro a b hab; cases hab; rfl
        have hw : w = p ++ o ++ s := hinj.list_map hwe
        exact ⟨o, by rw [hw], ⟨Spine.last C o hout_mem⟩⟩
      · -- single-nonterminal output: recurse on the smaller derivation
        subst hout
        have hx'' : x' = List.map symbol.terminal (p ++ o₁) ++ [symbol.nonterminal C₁]
              ++ List.map symbol.terminal (o₂ ++ s) := by
          rw [hx']; simp [List.map_append, List.append_assoc]
        obtain ⟨m', hw', ⟨sp⟩⟩ := ih hx''
        exact ⟨o₁ ++ m' ++ o₂, by rw [hw']; simp [List.append_assoc],
          ⟨Spine.cons C C₁ o₁ o₂ m' hout_mem sp⟩⟩

/-- Completeness: every linear derivation of a terminal word from a single
nonterminal `B` is witnessed by a spine. -/
public lemma exists_spine (hg : grammar_linear g) {B : g.nt} {w : List T}
    (h : grammar_derives g [symbol.nonterminal B] (List.map symbol.terminal w)) :
    Nonempty (Spine g B w) := by
  obtain ⟨m, hw, hsp⟩ := spine_of_deri hg (p := []) (s := []) (C := B) h (by simp)
  have hwm : w = m := by simpa using hw
  rw [hwm]; exact hsp

/-! ## Splitting a spine -/

/-- An upper bound on the number of terminals a single rule application produces. -/
public def maxRuleLen (g : grammar T) : ℕ :=
  (g.rules.map (fun r => r.output_string.length)).foldr max 0

/-- Every rule's output is no longer than `maxRuleLen`. -/
public lemma output_length_le_maxRuleLen {r : grule T g.nt} (hr : r ∈ g.rules) :
    r.output_string.length ≤ maxRuleLen g := by
  have key : ∀ (L : List (grule T g.nt)), r ∈ L →
      r.output_string.length ≤ (L.map (fun r => r.output_string.length)).foldr max 0 := by
    intro L hL
    induction L with
    | nil => simp at hL
    | cons hd tl ih =>
        simp only [List.map_cons, List.foldr_cons]
        rcases List.mem_cons.1 hL with rfl | hmem
        · exact le_max_left _ _
        · exact le_trans (ih hmem) (le_max_right _ _)
  exact key g.rules hr

/-- The result of splitting a spine `B ⇒* w` at a given depth: a top derivation
`B ⇒* u·C·y` and an inner spine `C ⇒* wc`, with `w = u ++ wc ++ y`. -/
public structure SplitResult (g : grammar T) (B : g.nt) (w : List T) where
  C : g.nt
  u : List T
  y : List T
  wc : List T
  inner : Spine g C wc
  hword : w = u ++ wc ++ y
  hderiv : grammar_derives g [symbol.nonterminal B]
            (List.map symbol.terminal u ++ [symbol.nonterminal C] ++ List.map symbol.terminal y)

namespace Spine

/-- Split a spine at depth `k`, peeling off the first `k` rule applications. -/
public def splitAt : {B : g.nt} → {w : List T} → Spine g B w → ℕ → SplitResult g B w
  | B, w, s, 0 =>
      ⟨B, [], [], w, s, by simp, by simpa using grammar_deri_self (g := g) (w := [symbol.nonterminal B])⟩
  | _, _, last B m h, _ + 1 =>
      ⟨B, [], [], m, last B m h, by simp,
        by simpa using grammar_deri_self (g := g) (w := [symbol.nonterminal B])⟩
  | _, _, cons B C u0 v0 m h rest, k + 1 =>
      match splitAt rest k with
      | ⟨rC, ru, ry, rwc, rinner, rhword, rhderiv⟩ =>
        ⟨ rC, u0 ++ ru, ry ++ v0, rwc, rinner,
          by rw [rhword]; simp [List.append_assoc],
          by
            have step1 : grammar_derives g [symbol.nonterminal B]
                (List.map symbol.terminal u0 ++ [symbol.nonterminal C] ++ List.map symbol.terminal v0) :=
              grammar_deri_of_tran ⟨_, h, [], [], by simp, by simp⟩
            have hpost := grammar_deri_with_postfix (List.map symbol.terminal v0) rhderiv
            have hpre := grammar_deri_with_prefix (List.map symbol.terminal u0) hpost
            have step2 : grammar_derives g
                (List.map symbol.terminal u0 ++ [symbol.nonterminal C] ++ List.map symbol.terminal v0)
                (List.map symbol.terminal (u0 ++ ru) ++ [symbol.nonterminal rC]
                  ++ List.map symbol.terminal (ry ++ v0)) := by
              simpa [List.map_append, List.append_assoc] using hpre
            exact grammar_deri_of_deri_deri step1 step2 ⟩

@[simp] public lemma splitAt_zero_C (s : Spine g B w) : (splitAt s 0).C = B := by cases s <;> rfl
@[simp] public lemma splitAt_zero_u (s : Spine g B w) : (splitAt s 0).u = [] := by cases s <;> rfl
@[simp] public lemma splitAt_zero_y (s : Spine g B w) : (splitAt s 0).y = [] := by cases s <;> rfl
@[simp] public lemma splitAt_zero_wc (s : Spine g B w) : (splitAt s 0).wc = w := by cases s <;> rfl

@[simp] public lemma splitAt_last_C (B m h k) :
    (splitAt (Spine.last (g := g) B m h) k).C = B := by cases k <;> rfl
@[simp] public lemma splitAt_last_u (B m h k) :
    (splitAt (Spine.last (g := g) B m h) k).u = [] := by cases k <;> rfl
@[simp] public lemma splitAt_last_y (B m h k) :
    (splitAt (Spine.last (g := g) B m h) k).y = [] := by cases k <;> rfl
@[simp] public lemma splitAt_last_wc (B m h k) :
    (splitAt (Spine.last (g := g) B m h) k).wc = m := by cases k <;> rfl

@[simp] public lemma splitAt_cons_succ_C (B C u0 v0 m h rest k) :
    (splitAt (Spine.cons (g := g) B C u0 v0 m h rest) (k + 1)).C = (splitAt rest k).C := rfl
@[simp] public lemma splitAt_cons_succ_u (B C u0 v0 m h rest k) :
    (splitAt (Spine.cons (g := g) B C u0 v0 m h rest) (k + 1)).u = u0 ++ (splitAt rest k).u := rfl
@[simp] public lemma splitAt_cons_succ_y (B C u0 v0 m h rest k) :
    (splitAt (Spine.cons (g := g) B C u0 v0 m h rest) (k + 1)).y = (splitAt rest k).y ++ v0 := rfl
@[simp] public lemma splitAt_cons_succ_wc (B C u0 v0 m h rest k) :
    (splitAt (Spine.cons (g := g) B C u0 v0 m h rest) (k + 1)).wc = (splitAt rest k).wc := rfl
@[simp] public lemma splitAt_cons_succ_inner (B C u0 v0 m h rest k) :
    (splitAt (Spine.cons (g := g) B C u0 v0 m h rest) (k + 1)).inner = (splitAt rest k).inner := rfl

/-- Composition of splits: splitting at depth `i + d` is splitting at `i`, then
splitting the inner spine at depth `d`. -/
public lemma splitAt_add : ∀ (i d : ℕ) {B : g.nt} {w : List T} (s : Spine g B w),
    (splitAt s (i + d)).C = (splitAt (splitAt s i).inner d).C ∧
    (splitAt s (i + d)).u = (splitAt s i).u ++ (splitAt (splitAt s i).inner d).u ∧
    (splitAt s (i + d)).y = (splitAt (splitAt s i).inner d).y ++ (splitAt s i).y := by
  intro i
  induction i with
  | zero =>
      intro d B w s
      cases s <;> (rw [Nat.zero_add]; exact ⟨rfl, rfl, (List.append_nil _).symm⟩)
  | succ i ih =>
      intro d B w s
      cases s with
      | last _ _ h =>
          have e : ((Spine.last (g := g) B w h).splitAt (i + 1)).inner = Spine.last B w h := rfl
          rw [e]; simp [Spine.splitAt]
      | cons B C u0 v0 m h rest =>
          obtain ⟨ihC, ihu, ihy⟩ := ih d rest
          rw [show (i + 1) + d = (i + d) + 1 from by omega]
          simp only [splitAt_cons_succ_C, splitAt_cons_succ_u, splitAt_cons_succ_y,
            splitAt_cons_succ_inner]
          refine ⟨ihC, ?_, ?_⟩
          · rw [ihu, List.append_assoc]
          · rw [ihy, List.append_assoc]

/-- The root nonterminal of any spine is the input nonterminal of one of its rules. -/
public lemma root_mem {B : g.nt} {w : List T} (s : Spine g B w) :
    B ∈ g.rules.map (·.input_N) := by
  cases s with
  | last B m h => exact List.mem_map.2 ⟨_, h, rfl⟩
  | cons B C u0 v0 m h rest => exact List.mem_map.2 ⟨_, h, rfl⟩

/-- The number of terminals produced in the first `k` rule applications of the spine. -/
public def cnt {B : g.nt} {w : List T} (s : Spine g B w) (k : ℕ) : ℕ :=
  (splitAt s k).u.length + (splitAt s k).y.length

/-- `cnt` decomposes additively along `splitAt_add`. -/
public lemma cnt_add {B : g.nt} {w : List T} (s : Spine g B w) (i d : ℕ) :
    cnt s (i + d) = cnt s i + cnt (splitAt s i).inner d := by
  obtain ⟨_, hu, hy⟩ := splitAt_add i d s
  simp only [cnt, hu, hy, List.length_append]
  omega

@[simp] public lemma cnt_zero {B : g.nt} {w : List T} (s : Spine g B w) : cnt s 0 = 0 := by
  simp [cnt]

/-- The root nonterminal reached at depth `i + d` is the one reached by splitting the inner
spine at depth `d`. -/
public lemma splitAt_add_C {B : g.nt} {w : List T} (s : Spine g B w) (i d : ℕ) :
    (splitAt s (i + d)).C = (splitAt (splitAt s i).inner d).C := (splitAt_add i d s).1

/-- One rule application produces at most `maxRuleLen` terminals. -/
public lemma cnt_one_le {B : g.nt} {w : List T} (s : Spine g B w) :
    cnt s 1 ≤ maxRuleLen g := by
  cases s with
  | last B m h => simp [cnt]
  | cons B C u0 v0 m h rest =>
      have hb := output_length_le_maxRuleLen h
      simp only [cnt, splitAt_cons_succ_u, splitAt_cons_succ_y, splitAt_zero_u, splitAt_zero_y,
        List.append_nil, List.nil_append, List.length_append] at hb ⊢
      simp only [List.length_map, List.length_cons] at hb
      omega

/-- Each additional step adds at most `maxRuleLen` terminals. -/
public lemma cnt_step {B : g.nt} {w : List T} (s : Spine g B w) (k : ℕ) :
    cnt s (k + 1) ≤ cnt s k + maxRuleLen g := by
  rw [cnt_add s k 1]
  exact Nat.add_le_add_left (cnt_one_le _) _

/-- `cnt` is monotone in the depth. -/
public lemma cnt_mono {B : g.nt} {w : List T} (s : Spine g B w) : Monotone (cnt s) := by
  intro i j hij
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [cnt_add]
  exact Nat.le_add_right _ _

/-- The terminals produced plus the remaining inner word recover the whole word. -/
public lemma cnt_add_wc {B : g.nt} {w : List T} (s : Spine g B w) (k : ℕ) :
    cnt s k + (splitAt s k).wc.length = w.length := by
  have hw := (splitAt s k).hword
  conv_rhs => rw [hw]
  simp only [cnt, List.length_append]
  omega

/-- The remaining inner word after fully splitting is a single rule output, hence short. -/
public lemma splitAt_length_wc_le : ∀ {B : g.nt} {w : List T} (s : Spine g B w),
    (splitAt s s.length).wc.length ≤ maxRuleLen g := by
  intro B w s
  induction s with
  | last B m h =>
      show (splitAt (Spine.last B m h) 1).wc.length ≤ maxRuleLen g
      rw [splitAt_last_wc]
      have := output_length_le_maxRuleLen h
      simpa using this
  | cons B C u0 v0 m h rest ih =>
      show (splitAt (Spine.cons B C u0 v0 m h rest) (rest.length + 1)).wc.length ≤ maxRuleLen g
      rw [splitAt_cons_succ_wc]
      exact ih

/-- At full depth, `cnt` accounts for all but at most `maxRuleLen` symbols of the word. -/
public lemma cnt_length_ge {B : g.nt} {w : List T} (s : Spine g B w) :
    w.length - maxRuleLen g ≤ cnt s s.length := by
  have h1 := cnt_add_wc s s.length
  have h2 := splitAt_length_wc_le s
  omega

end Spine
