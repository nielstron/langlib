import Mathlib
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Classes.ContextFree.Closure.Bijection
import Langlib.Classes.ContextFree.Closure.Intersection
import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.DeterministicContextFree.Inclusion.ContextFree
import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
import Langlib.Classes.RecursivelyEnumerable.Closure.Union
import Langlib.Classes.ContextFree.Definition

/-! # `a^n b^n c^n` as an RE Language

This file constructs an unrestricted grammar for `{a^n b^n c^n}` and proves that
the language is recursively enumerable.
-/

open Language List

/-- Unrestricted grammar for `{aⁿbⁿcⁿ | n ≥ 1}` over `Fin 3`.

Nonterminals: `Fin 2` where `0 = S`, `1 = B`.

Rules:
1. S → a B c
2. S → a S B c
3. c B → B c  (bubble sort)
4. a B → a b  (context-sensitive conversion)
5. b B → b b  (context-sensitive conversion)
-/
@[reducible] def grammar_anbncn : grammar (Fin 3) where
  nt := Fin 2
  initial := 0
  rules := [
    ⟨[], 0, [], [symbol.terminal 0, symbol.nonterminal 1, symbol.terminal 2]⟩,
    ⟨[], 0, [], [symbol.terminal 0, symbol.nonterminal 0,
                  symbol.nonterminal 1, symbol.terminal 2]⟩,
    ⟨[symbol.terminal 2], 1, [], [symbol.nonterminal 1, symbol.terminal 2]⟩,
    ⟨[symbol.terminal 0], 1, [], [symbol.terminal 0, symbol.terminal 1]⟩,
    ⟨[symbol.terminal 1], 1, [], [symbol.terminal 1, symbol.terminal 1]⟩
  ]

private abbrev gS : symbol (Fin 3) grammar_anbncn.nt := symbol.nonterminal grammar_anbncn.initial
private abbrev gB : symbol (Fin 3) grammar_anbncn.nt := symbol.nonterminal ⟨1, by omega⟩
private abbrev ga : symbol (Fin 3) grammar_anbncn.nt := symbol.terminal 0
private abbrev gb : symbol (Fin 3) grammar_anbncn.nt := symbol.terminal 1
private abbrev gc : symbol (Fin 3) grammar_anbncn.nt := symbol.terminal 2

private def lang_eq_eq_pos : Language (Fin 3) :=
  fun w => ∃ n : ℕ, w = List.replicate (n + 1) 0 ++
    List.replicate (n + 1) 1 ++ List.replicate (n + 1) 2

private def lang_epsilon : Language (Fin 3) :=
  fun w => w = []

-- Single-step lemmas

private lemma anbncn_step_base (u v : List (symbol (Fin 3) grammar_anbncn.nt)) :
    grammar_transforms grammar_anbncn (u ++ [gS] ++ v) (u ++ [ga, gB, gc] ++ v) := by
  exact ⟨⟨[], grammar_anbncn.initial, [], [ga, gB, gc]⟩, by simp [grammar_anbncn],
         u, v, by simp, by simp⟩

private lemma anbncn_step_expand (u v : List (symbol (Fin 3) grammar_anbncn.nt)) :
    grammar_transforms grammar_anbncn
      (u ++ [gS] ++ v) (u ++ [ga, gS, gB, gc] ++ v) := by
  exact ⟨⟨[], grammar_anbncn.initial, [], [ga, gS, gB, gc]⟩, by simp [grammar_anbncn],
         u, v, by simp, by simp⟩

private lemma anbncn_step_swap (u v : List (symbol (Fin 3) grammar_anbncn.nt)) :
    grammar_transforms grammar_anbncn
      (u ++ [gc, gB] ++ v) (u ++ [gB, gc] ++ v) := by
  exact ⟨⟨[gc], ⟨1, by omega⟩, [], [gB, gc]⟩, by simp [grammar_anbncn],
         u, v, by simp, by simp⟩

private lemma anbncn_step_convert_a (u v : List (symbol (Fin 3) grammar_anbncn.nt)) :
    grammar_transforms grammar_anbncn
      (u ++ [ga, gB] ++ v) (u ++ [ga, gb] ++ v) := by
  exact ⟨⟨[ga], ⟨1, by omega⟩, [], [ga, gb]⟩, by simp [grammar_anbncn],
         u, v, by simp, by simp⟩

private lemma anbncn_step_convert_b (u v : List (symbol (Fin 3) grammar_anbncn.nt)) :
    grammar_transforms grammar_anbncn
      (u ++ [gb, gB] ++ v) (u ++ [gb, gb] ++ v) := by
  exact ⟨⟨[gb], ⟨1, by omega⟩, [], [gb, gb]⟩, by simp [grammar_anbncn],
         u, v, by simp, by simp⟩

-- Phase 1: expansion

private lemma anbncn_phase1 (n : ℕ) :
    grammar_derives grammar_anbncn [gS]
      (List.replicate n ga ++ [gS] ++ (List.replicate n [gB, gc]).flatten) := by
        induction' n with n ih;
        · constructor;
        · convert grammar_deri_of_deri_tran ih _ using 1;
          convert anbncn_step_expand _ _ using 1 ; simp +decide [ List.replicate_add ];
          exact Nat.recOn n ( by rfl ) fun n ihn => by simp +decide [ List.replicate ] at * ; aesop;

private lemma anbncn_after_expansion (n : ℕ) :
    grammar_derives grammar_anbncn [gS]
      (List.replicate n ga ++ ga :: gB :: gc :: (List.replicate n [gB, gc]).flatten) := by
  have hbase := anbncn_step_base (List.replicate n ga) ((List.replicate n [gB, gc]).flatten)
  exact grammar_deri_of_deri_tran (anbncn_phase1 n) (by simpa [List.append_assoc] using hbase)

-- Phase 2: sorting

private lemma anbncn_sort (n : ℕ) :
    grammar_derives grammar_anbncn
      ((List.replicate n [gB, gc]).flatten)
      (List.replicate n gB ++ List.replicate n gc) := by
        simp +decide [ List.replicate_add ];
        have h_swap : ∀ m : ℕ, ∀ s₁ s₂ : List (symbol (Fin 3) grammar_anbncn.nt), grammar_derives grammar_anbncn (s₁ ++ [gc] ++ List.replicate m gB ++ s₂) (s₁ ++ List.replicate m gB ++ [gc] ++ s₂) := by
          intro m s₁ s₂; induction' m with m ih generalizing s₁ s₂ <;> simp_all +decide [ List.replicate ] ;
          · constructor;
          · have h_swap : grammar_derives grammar_anbncn (s₁ ++ gc :: gB :: (replicate m gB ++ s₂)) (s₁ ++ gB :: gc :: (replicate m gB ++ s₂)) := by
              apply_rules [ grammar_deri_of_tran, anbncn_step_swap ];
              convert anbncn_step_swap s₁ ( replicate m gB ++ s₂ ) using 1;
              · simp +decide [ List.append_assoc ];
              · simp +decide [ List.append_assoc ];
            exact h_swap.trans ( by simpa [ List.replicate ] using ih ( s₁ ++ [ gB ] ) s₂ );
        induction' n with n ih;
        · constructor;
        · have h_swap_step : grammar_derives grammar_anbncn ([gB, gc] ++ (replicate n [gB, gc]).flatten) ([gB] ++ (replicate n gB) ++ [gc] ++ (replicate n gc)) := by
            convert grammar_deri_of_deri_deri _ _ using 1;
            exact [ gB, gc ] ++ replicate n gB ++ replicate n gc;
            · convert grammar_deri_with_prefix [ gB, gc ] ih using 1;
            · convert h_swap n [ gB ] ( replicate n gc ) using 1;
          grind +revert

-- Phase 3: conversion (left-to-right, using context-sensitive rules)

/-- Convert `n` consecutive `B`'s to `b`'s, given that the block is preceded by
    either `a` or `b` (the `trigger` symbol). -/
private lemma anbncn_convert_chain
    (trigger : symbol (Fin 3) grammar_anbncn.nt) (h_trigger : trigger = ga ∨ trigger = gb)
    (n : ℕ) (u v : List (symbol (Fin 3) grammar_anbncn.nt)) :
    grammar_derives grammar_anbncn
      (u ++ [trigger] ++ List.replicate n gB ++ v)
      (u ++ [trigger] ++ List.replicate n gb ++ v) := by
  induction n generalizing trigger u with
  | zero => simp; constructor
  | succ n ih =>
    have step1 : grammar_transforms grammar_anbncn
        (u ++ [trigger] ++ gB :: replicate n gB ++ v)
        (u ++ [trigger] ++ gb :: replicate n gB ++ v) := by
      rcases h_trigger with rfl | rfl
      · convert anbncn_step_convert_a u (replicate n gB ++ v) using 1 <;> simp
      · convert anbncn_step_convert_b u (replicate n gB ++ v) using 1 <;> simp
    have step2 : grammar_derives grammar_anbncn
        ((u ++ [trigger]) ++ [gb] ++ replicate n gB ++ v)
        ((u ++ [trigger]) ++ [gb] ++ replicate n gb ++ v) :=
      ih gb (Or.inr rfl) (u ++ [trigger])
    have h1 : u ++ [trigger] ++ replicate (n + 1) gB ++ v =
        u ++ [trigger] ++ gB :: replicate n gB ++ v := by simp [List.replicate_succ]
    have h2 : u ++ [trigger] ++ replicate (n + 1) gb ++ v =
        (u ++ [trigger]) ++ [gb] ++ replicate n gb ++ v := by simp [List.replicate_succ]
    rw [h1, h2]
    exact grammar_deri_of_tran_deri step1 (by convert step2 using 1 <;> simp)

/-- Convert all B's in `a^n B^n c^n` to b's. -/
private lemma anbncn_convert_Bs (n : ℕ) :
    grammar_derives grammar_anbncn
      (List.replicate (n + 1) ga ++ List.replicate (n + 1) gB ++ List.replicate (n + 1) gc)
      (List.replicate (n + 1) ga ++ List.replicate (n + 1) gb ++ List.replicate (n + 1) gc) := by
  have h := anbncn_convert_chain ga (Or.inl rfl) (n + 1)
    (List.replicate n ga) (List.replicate (n + 1) gc)
  convert h using 1 <;> simp [List.replicate_succ']

-- Backward direction

private lemma anbncn_derivable (n : ℕ) :
    List.replicate (n + 1) (0 : Fin 3) ++ List.replicate (n + 1) 1 ++ List.replicate (n + 1) 2 ∈
      grammar_language grammar_anbncn := by
  show grammar_generates grammar_anbncn _
  unfold grammar_generates
  apply grammar_deri_of_deri_deri (anbncn_after_expansion n)
  have hsort : grammar_derives grammar_anbncn
      (List.replicate n ga ++ ga :: gB :: gc :: (List.replicate n [gB, gc]).flatten)
      (List.replicate (n + 1) ga ++ List.replicate (n + 1) gB ++ List.replicate (n + 1) gc) := by
    have hsort0 := grammar_deri_with_prefix (List.replicate n ga ++ [ga]) (anbncn_sort (n + 1))
    have key : ∀ {α : Type} (a : α) (n : ℕ) (rest : List α),
        a :: (List.replicate n a ++ rest) = List.replicate n a ++ a :: rest := by
      intros; induction ‹ℕ› with | zero => simp | succ n ih => simp [List.replicate_succ, ih]
    convert hsort0 using 1 <;> simp [List.replicate_succ, List.append_assoc, key]
  apply grammar_deri_of_deri_deri hsort
  have hconv := anbncn_convert_Bs n
  convert hconv using 1 <;> simp [List.map_replicate]

/- Forward direction: counting invariants -/
private lemma count_a_eq_Bb_step
    (w₁ w₂ : List (symbol (Fin 3) grammar_anbncn.nt))
    (ht : grammar_transforms grammar_anbncn w₁ w₂)
    (hinv : w₁.count ga = w₁.count gB + w₁.count gb) :
    w₂.count ga = w₂.count gB + w₂.count gb := by
      rcases ht with ⟨ u, v, r, hr, hw₁, hw₂ ⟩;
      simp_all +decide [ count ];
      rcases v with ( rfl | rfl | rfl | rfl | rfl ) <;> simp_all +arith +decide

private lemma count_a_eq_c_step
    (w₁ w₂ : List (symbol (Fin 3) grammar_anbncn.nt))
    (ht : grammar_transforms grammar_anbncn w₁ w₂)
    (hinv : w₁.count ga = w₁.count gc) :
    w₂.count ga = w₂.count gc := by
      obtain ⟨ u, v, p, r, h, hw₁, hw₂ ⟩ := ht;
      unfold grammar_anbncn at v; simp_all +decide [ Fin.forall_fin_succ ] ;
      rcases v with ( rfl | rfl | rfl | rfl | rfl ) <;> simp_all +decide <;> omega

private lemma count_a_eq_Bb_of_derives
    (w : List (symbol (Fin 3) grammar_anbncn.nt))
    (hd : grammar_derives grammar_anbncn [gS] w) :
    w.count ga = w.count gB + w.count gb := by
      induction hd with
      | refl => rfl
      | tail _ h₂ ih => exact count_a_eq_Bb_step _ _ h₂ ih

private lemma count_a_eq_c_of_derives
    (w : List (symbol (Fin 3) grammar_anbncn.nt))
    (hd : grammar_derives grammar_anbncn [gS] w) :
    w.count ga = w.count gc := by
      induction hd with
      | refl => rfl
      | tail _ h₂ ih => exact count_a_eq_c_step _ _ h₂ ih

private lemma count_a_or_S_pos_step
    (w₁ w₂ : List (symbol (Fin 3) grammar_anbncn.nt))
    (ht : grammar_transforms grammar_anbncn w₁ w₂)
    (hpos : 0 < w₁.count ga + w₁.count gS) :
    0 < w₂.count ga + w₂.count gS := by
      rcases ht with ⟨r, hr, u, v, hw₁, hw₂⟩
      simp [grammar_anbncn] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp_all +arith +decide [List.count]

private lemma count_a_or_S_pos_of_derives
    (w : List (symbol (Fin 3) grammar_anbncn.nt))
    (hd : grammar_derives grammar_anbncn [gS] w) :
    0 < w.count ga + w.count gS := by
  induction hd with
  | refl => simp
  | tail _ h₂ ih => exact count_a_or_S_pos_step _ _ h₂ ih

-- Forward direction: weight invariants

/-- Weight function 1: ga has weight 0, everything else has weight 1.
    Invariant: all a's appear before all other symbols. -/
private def wa (x : symbol (Fin 3) grammar_anbncn.nt) : Fin 2 :=
  if x = ga then 0 else 1

/-- Weight function 2: ga, gS, gb have weight 0; gB, gc have weight 1.
    Invariant: all {a, S, b}'s appear before all {B, c}'s. -/
private def wb (x : symbol (Fin 3) grammar_anbncn.nt) : Fin 2 :=
  if x = gB ∨ x = gc then 1 else 0

/-- Combined structural invariant for sentential forms derivable from [gS].
    - wa-sorted: all ga's come before all other symbols
    - wb-sorted: all {ga,gS,gb} come before all {gB,gc}
    - no_coexist: gS and gb cannot both be in the word
    - ga_prefix: everything before gS consists of ga's -/
private def grammar_inv (w : List (symbol (Fin 3) grammar_anbncn.nt)) : Prop :=
  (w.map wa).Pairwise (· ≤ ·) ∧
  (w.map wb).Pairwise (· ≤ ·) ∧
  (gS ∈ w → gb ∉ w) ∧
  (∀ (u v : List (symbol (Fin 3) grammar_anbncn.nt)),
    w = u ++ [gS] ++ v → ∀ x ∈ u, x = ga)

private lemma grammar_inv_initial : grammar_inv [gS] := by
  constructor
  · simp [wa, gS, ga]
  constructor
  · simp [wb, gS, ga]
  constructor
  · simp [gS, gb]
  · intro u v h
    have : u = [] := by
      rcases u with _ | ⟨x, u⟩
      · rfl
      · simp at h
    subst this; simp

set_option maxHeartbeats 800000 in
private lemma grammar_inv_step_base (u v : List (symbol (Fin 3) grammar_anbncn.nt))
    (hinv : grammar_inv (u ++ [gS] ++ v)) :
    grammar_inv (u ++ [ga, gB, gc] ++ v) := by
      have hv_wb : ∀ x ∈ v, x ≠ ga ∧ x ≠ gS ∧ x ≠ gb := by
        intros x hx
        have h_not_ga : x ≠ ga := by
          contrapose! hinv
          simp_all +decide [grammar_inv]
          intro h₁ h₂ h₃ h₄
          use u ++ [gS]
          simp_all +decide [List.pairwise_append]
          exact absurd (h₁.2.1.1 _ hx) (by simp +decide [wa])
        have h_not_gS : x ≠ gS := by
          have := hinv.2.2.2
          simp_all +decide [grammar_inv]
          contrapose! this
          use u ++ [gS] ++ List.takeWhile (fun y => y ≠ gS) v,
            List.dropWhile (fun y => y ≠ gS) v |> List.tail!
          simp_all +decide [List.takeWhile, List.dropWhile]
          have h_take_drop : ∀ {l : List (symbol (Fin 3) grammar_anbncn.nt)}, gS ∈ l →
              l = takeWhile (fun y => !decide (y = gS)) l ++
                gS :: (dropWhile (fun y => !decide (y = gS)) l).tail! := by
            intros l hl
            induction' l with hd tl ih <;> simp_all +decide [List.takeWhile, List.dropWhile]
            by_cases h : hd = gS <;> simp +decide [h] at hl ⊢
            tauto
          exact ⟨h_take_drop hx, gS, by simp +decide⟩
        have h_not_gb : x ≠ gb := by
          exact fun h => hinv.2.2.1 (by aesop) (by aesop)
        exact ⟨h_not_ga, h_not_gS, h_not_gb⟩
      unfold grammar_inv at *
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold wa at *
        simp +zetaDelta at *
        grind
      · simp +decide [List.pairwise_append, List.pairwise_map] at *
        simp_all +decide [wb]
        intro x hx
        specialize hv_wb x hx
        cases x with
        | terminal t =>
            fin_cases t <;> simp_all +decide
        | nonterminal n =>
            fin_cases n <;> simp_all +decide
      · intro hgS
        have hnogb := hinv.2.2.1 (by simp)
        simpa [List.mem_append] using hnogb
      · intro u' v' h
        have : gS ∈ (u ++ [ga, gB, gc] ++ v) := by
          rw [h]
          simp
        have hu_not : gS ∉ u := by
          intro hx
          have hprefix := hinv.2.2.2 u v rfl gS hx
          simp [ga, gS] at hprefix
        have hv_not : gS ∉ v := by
          intro hx
          exact (hv_wb gS hx).2.1 rfl
        simp [List.mem_append, hu_not, hv_not] at this

set_option maxHeartbeats 800000 in
private lemma grammar_inv_step_expand (u v : List (symbol (Fin 3) grammar_anbncn.nt))
    (hinv : grammar_inv (u ++ [gS] ++ v)) :
    grammar_inv (u ++ [ga, gS, gB, gc] ++ v) := by
      have hv_wb : ∀ x ∈ v, x ≠ ga ∧ x ≠ gS ∧ x ≠ gb := by
        intros x hx
        have h_not_ga : x ≠ ga := by
          contrapose! hinv; simp_all +decide [ grammar_inv ] ;
          intro h₁ h₂ h₃ h₄; use u ++ [gS]; simp_all +decide [ List.pairwise_append ] ;
          exact absurd ( h₁.2.1.1 _ hx ) ( by simp +decide [ wa ] )
        have h_not_gS : x ≠ gS := by
          have := hinv.2.2.2; simp_all +decide [ grammar_inv ] ;
          contrapose! this;
          use u ++ [gS] ++ List.takeWhile (fun y => y ≠ gS) v, List.dropWhile (fun y => y ≠ gS) v |> List.tail!; simp_all +decide [ List.takeWhile, List.dropWhile ] ;
          have h_take_drop : ∀ {l : List (symbol (Fin 3) grammar_anbncn.nt)}, gS ∈ l → l = takeWhile (fun y => !decide (y = gS)) l ++ gS :: (dropWhile (fun y => !decide (y = gS)) l).tail! := by
            intros l hl; induction' l with hd tl ih <;> simp_all +decide [ List.takeWhile, List.dropWhile ] ;
            by_cases h : hd = gS <;> simp +decide [ h ] at hl ⊢ ; tauto;
          exact ⟨ h_take_drop hx, gS, by simp +decide ⟩
        have h_not_gb : x ≠ gb := by
          exact fun h => hinv.2.2.1 ( by aesop ) ( by aesop )
        exact ⟨h_not_ga, h_not_gS, h_not_gb⟩;
      unfold grammar_inv at *;
      refine' ⟨ _, _, _, _ ⟩;
      · unfold wa at *;
        simp +zetaDelta at *;
        grind;
      · simp +decide [ List.pairwise_append, List.pairwise_map ] at *;
        simp_all +decide [ wb ];
        intro x hx; specialize hv_wb x hx; rcases x with ( _ | _ | _ | x ) <;> simp_all +decide ;
        · rename_i k; fin_cases k <;> trivial;
        · linarith;
      · grind;
      · intro u_1 v_1 huv_1 x hx; have := huv_1; simp_all +decide [ List.append_assoc ] ;
        rw [ List.append_eq_append_iff ] at this;
        rcases this with ( ⟨ as, rfl, h ⟩ | ⟨ bs, rfl, h ⟩ ) <;> simp_all +decide [ List.append_assoc ];
        · rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          rcases as with ( _ | ⟨ b, as ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          · grind;
          · grind;
        · cases bs <;> aesop

set_option maxHeartbeats 800000 in
private lemma grammar_inv_step_swap (u v : List (symbol (Fin 3) grammar_anbncn.nt))
    (hinv : grammar_inv (u ++ [gc, gB] ++ v)) :
    grammar_inv (u ++ [gB, gc] ++ v) := by
      unfold grammar_inv at *; simp_all +decide [ List.pairwise_append ] ;
      intro u_1 v_1 huv x hx;
      contrapose! hinv;
      intro h1 h2 h3;
      rcases List.append_eq_append_iff.mp huv with ( ⟨ u', hu' ⟩ | ⟨ u', hu' ⟩ ) <;> simp_all +decide [ List.append_assoc ];
      · rcases u' with ( _ | ⟨ x, u' ⟩ ) <;> simp_all +decide [ List.append_assoc ];
        rcases u' with ( _ | ⟨ y, u' ⟩ ) <;> simp_all +decide [ List.append_assoc ];
        use u ++ [y, x] ++ u';
        exact ⟨ ⟨ v_1, by simp +decide [ List.append_assoc ] ⟩, y, by simp +decide [ List.append_assoc ], by aesop ⟩;
      · rcases u' with ( _ | ⟨ a, u' ⟩ ) <;> simp_all +decide [ List.map ];
        exact ⟨ u_1, ⟨ u' ++ gc :: gB :: v, by simp +decide [ List.append_assoc ] ⟩, x, hx, hinv ⟩

set_option maxHeartbeats 800000 in
private lemma grammar_inv_step_conv_a (u v : List (symbol (Fin 3) grammar_anbncn.nt))
    (hinv : grammar_inv (u ++ [ga, gB] ++ v)) :
    grammar_inv (u ++ [ga, gb] ++ v) := by
      unfold grammar_inv at *; simp_all +decide [ List.pairwise_append ] ;
      unfold wa wb at *;
      refine' ⟨ _, _, _, _ ⟩;
      · grind;
      · grind;
      · grind;
      · intro u_1 v_1 h x hx; replace h := congr_arg List.toFinset h; simp_all +decide [ Finset.ext_iff ] ;
        grind

set_option maxHeartbeats 800000 in
private lemma grammar_inv_step_conv_b (u v : List (symbol (Fin 3) grammar_anbncn.nt))
    (hinv : grammar_inv (u ++ [gb, gB] ++ v)) :
    grammar_inv (u ++ [gb, gb] ++ v) := by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hinv;
      refine' ⟨ _, _, _, _ ⟩;
      · simp_all +decide [ List.pairwise_append ];
      · simp_all +decide [ List.pairwise_append, List.pairwise_map ];
      · simp_all +decide [ List.pairwise_append ];
      · contrapose! h₄;
        obtain ⟨ u, v, h₁, x, hx, hx' ⟩ := h₄; use u, v; simp_all +decide [ List.map ] ;
        replace h₁ := congr_arg ( fun z => z.count gS ) h₁ ; simp_all +decide [ List.count_cons ];
        simp_all +decide [ List.count_eq_zero_of_not_mem ];
        omega

private lemma grammar_inv_step
    (w₁ w₂ : List (symbol (Fin 3) grammar_anbncn.nt))
    (ht : grammar_transforms grammar_anbncn w₁ w₂)
    (hinv : grammar_inv w₁) :
    grammar_inv w₂ := by
  obtain ⟨r, hr, u, v, rfl, rfl⟩ := ht
  simp [grammar_anbncn] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    (try { show grammar_inv _; convert grammar_inv_step_base u v (by convert hinv using 2 <;> simp)
           using 2 <;> simp; done }) <;>
    (try { show grammar_inv _; convert grammar_inv_step_expand u v (by convert hinv using 2 <;> simp)
           using 2 <;> simp; done }) <;>
    (try { show grammar_inv _; convert grammar_inv_step_swap u v (by convert hinv using 2 <;> simp)
           using 2 <;> simp; done }) <;>
    (try { show grammar_inv _; convert grammar_inv_step_conv_a u v (by convert hinv using 2 <;> simp)
           using 2 <;> simp; done }) <;>
    (try { show grammar_inv _; convert grammar_inv_step_conv_b u v (by convert hinv using 2 <;> simp)
           using 2 <;> simp; done })

private lemma grammar_inv_of_derives
    (w : List (symbol (Fin 3) grammar_anbncn.nt))
    (hd : grammar_derives grammar_anbncn [gS] w) :
    grammar_inv w := by
  induction hd with
  | refl => exact grammar_inv_initial
  | tail _ h₂ ih => exact grammar_inv_step _ _ h₂ ih

/- Any fully terminal word derivable from `[gS]` is sorted. -/
private lemma terminal_sorted_of_derives
    (w : List (Fin 3))
    (hd : grammar_derives grammar_anbncn [gS] (w.map symbol.terminal)) :
    w.Pairwise (· ≤ ·) := by
      have := grammar_inv_of_derives _ hd;
      unfold grammar_inv at this;
      simp_all +decide [ List.pairwise_map ];
      simp_all +decide [ wa, wb, List.pairwise_iff_get ];
      grind

private lemma sorted_fin3_decomp {w : List (Fin 3)} (hw : w.Pairwise (· ≤ ·)) :
    ∃ a_ b_ c_, w = replicate a_ 0 ++ replicate b_ 1 ++ replicate c_ 2 := by
  induction w with
  | nil => exact ⟨0, 0, 0, rfl⟩
  | cons x w ih =>
    obtain ⟨n, m, k, rfl⟩ := ih (List.pairwise_cons.mp hw).2
    fin_cases x <;> simp +decide [List.pairwise_cons] at hw ⊢
    · exact ⟨n + 1, m, k, by simp [List.replicate]⟩
    · rcases n with _ | n
      · exact ⟨0, m + 1, k, by simp [List.replicate]⟩
      · simp_all +decide [List.replicate]
    · rcases n with _ | n
      · rcases m with _ | m
        · exact ⟨0, 0, k + 1, by simp [List.replicate]⟩
        · simp_all +decide
      · simp_all +decide

private lemma grammar_anbncn_sub_lang_eq_eq :
    ∀ w, w ∈ grammar_language grammar_anbncn → w ∈ lang_eq_eq_pos := by
      intro w hw
      change grammar_generates grammar_anbncn w at hw
      have hw_derives : grammar_derives grammar_anbncn [gS] (w.map symbol.terminal) := hw
      have hw_sorted : w.Pairwise (· ≤ ·) := terminal_sorted_of_derives _ hw_derives
      obtain ⟨a_, b_, c_, hw_form⟩ := sorted_fin3_decomp hw_sorted
      subst hw_form
      have h1 := count_a_eq_Bb_of_derives _ hw_derives
      have h2 := count_a_eq_c_of_derives _ hw_derives
      have hpos := count_a_or_S_pos_of_derives _ hw_derives
      have hapos : 0 < a_ := by
        unfold ga gS at hpos
        simp_all +decide [List.count_replicate]
      cases a_ with
      | zero => cases Nat.lt_irrefl 0 hapos
      | succ n =>
          exact ⟨n, by
            unfold ga gc at *
            simp_all +decide [List.count_replicate]
          ⟩

/-- The grammar `grammar_anbncn` generates exactly `{aⁿbⁿcⁿ | n ≥ 1}`. -/
theorem grammar_anbncn_language : grammar_language grammar_anbncn = lang_eq_eq_pos := by
  ext w
  exact ⟨grammar_anbncn_sub_lang_eq_eq w, fun ⟨n, hw⟩ => hw ▸ anbncn_derivable n⟩

private def grammar_epsilon : grammar (Fin 3) where
  nt := Unit
  initial := ()
  rules := [⟨[], (), [], []⟩]

private lemma grammar_epsilon_language : grammar_language grammar_epsilon = lang_epsilon := by
  ext w
  constructor
  · intro hw
    change grammar_generates grammar_epsilon w at hw
    have h := grammar_tran_or_id_of_deri hw
    rcases h with h | ⟨v, hv, hd⟩
    · cases w <;> simp at h
    · rcases hv with ⟨r, hr, u, v', hw₁, hw₂⟩
      simp [grammar_epsilon] at hr
      rcases hr with rfl
      cases u <;> cases v' <;> simp at hw₁ hw₂
      subst v
      have h' := grammar_tran_or_id_of_deri hd
      rcases h' with h' | ⟨v'', hv'', _⟩
      · simpa [lang_epsilon] using h'
      · rcases hv'' with ⟨r, hr, u, v', hw₁, _⟩
        simp [grammar_epsilon] at hr
        rcases hr with rfl
        simp at hw₁
  · intro hw
    change grammar_generates grammar_epsilon w
    unfold lang_epsilon at hw
    subst w
    exact grammar_deri_of_tran (by
      refine ⟨⟨[], grammar_epsilon.initial, [], []⟩, by simp [grammar_epsilon], [], [], ?_, ?_⟩ <;> simp)

private lemma lang_eq_eq_pos_union_epsilon : lang_eq_eq_pos + lang_epsilon = lang_eq_eq := by
  ext w
  constructor
  · intro hw
    rw [Language.mem_add] at hw
    rcases hw with hw | hw
    · rcases hw with ⟨n, rfl⟩
      exact ⟨n + 1, by simp [a_, b_, c_, List.replicate_add, List.append_assoc]⟩
    · cases hw
      exact ⟨0, by simp [a_, b_, c_]⟩
  · intro hw
    rw [Language.mem_add]
    rcases hw with ⟨n, rfl⟩
    cases n with
    | zero =>
        right
        exact rfl
    | succ n =>
        left
        exact ⟨n, rfl⟩

/-- The language `{aⁿbⁿcⁿ}` is recursively enumerable. -/
theorem lang_eq_eq_is_RE : is_RE lang_eq_eq := by
  have hpos : is_RE lang_eq_eq_pos := ⟨grammar_anbncn, grammar_anbncn_language⟩
  have heps : is_RE lang_epsilon := ⟨grammar_epsilon, grammar_epsilon_language⟩
  rw [← lang_eq_eq_pos_union_epsilon]
  exact RE_of_RE_u_RE _ _ ⟨hpos, heps⟩
