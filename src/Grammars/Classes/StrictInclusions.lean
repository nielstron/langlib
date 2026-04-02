import Mathlib
import Grammars.Classes.ContextFree.Basics.Inclusion
import Grammars.Classes.ContextFree.ClosureProperties.Intersection
import Grammars.Classes.ContextSensitive.Basics.Inclusion
import Grammars.Classes.Regular.Basics.NonRegular
import Grammars.Classes.DetContextFree.Basics.Inclusion

/-! # Strict Inclusions in the Chomsky Hierarchy

This file proves strict subset relationships between the language classes
in the Chomsky hierarchy, using results already established elsewhere in
the project.

## Main results

- `anbn_is_CF` — The language `{aⁿbⁿ}` is context-free.
- `exists_CF_not_regular` — There exists a CF language that is not regular.
- `lang_eq_eq_is_RE` — The language `{aⁿbⁿcⁿ}` is recursively enumerable.
- `CF_strictSubclass_RE` — The class CF is a strict subclass of RE.
-/

open Language List

-- ============================================================================
-- Section 1: anbn is context-free
-- ============================================================================

/-- Context-free grammar for the language `{aⁿbⁿ | n ∈ ℕ}` over `Bool`. -/
def cfg_anbn : CF_grammar Bool where
  nt := Unit
  initial := ()
  rules := [
    ((), [symbol.terminal false, symbol.nonterminal (), symbol.terminal true]),
    ((), [])
  ]

private def sentential_form (w : List (symbol Bool Unit)) : Prop :=
  (∃ n : ℕ, w = List.map symbol.terminal (List.replicate n false) ++
    [symbol.nonterminal ()] ++
    List.map symbol.terminal (List.replicate n true)) ∨
  (∃ n : ℕ, w = List.map symbol.terminal (List.replicate n false ++ List.replicate n true))

private lemma sentential_form_step (w w' : List (symbol Bool Unit))
    (hw : sentential_form w) (ht : CF_transforms cfg_anbn w w') :
    sentential_form w' := by
      rcases hw with ⟨ n, rfl ⟩ | ⟨ n, rfl ⟩ <;> simp_all +decide [ CF_transforms, cfg_anbn ];
      · rcases ht with ( ⟨ x, y, hxy, rfl ⟩ | ⟨ x, y, hxy, rfl ⟩ ) <;> simp_all +decide [ sentential_form ];
        · rw [ List.append_eq_append_iff ] at hxy;
          rcases hxy with ( ⟨ as, rfl, h ⟩ | ⟨ bs, h, h' ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
          · rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.replicate ];
            · refine' Or.inl ⟨ n + 1, Or.inl ⟨ [ symbol.terminal false ], _, _ ⟩ ⟩ <;> simp +decide [ List.replicate ];
              · exact Nat.recOn n ( by rfl ) fun n ih => by simp +decide [ List.replicate ] at * ; aesop;
              · exact h.symm;
            · replace h := congr_arg List.toFinset h.2; rw [ Finset.ext_iff ] at h; specialize h ( symbol.nonterminal () ) ; aesop;
          · rcases bs with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
            · refine Or.inl ⟨ n + 1, ?_ ⟩ ; simp_all +decide [ List.replicate ];
              exact Or.inl ⟨ [ symbol.terminal false ], by rw [ ← h ] ; exact Nat.recOn n ( by simp +decide ) fun n ihn => by simp +decide [ List.replicate ] at ihn ⊢; aesop ⟩;
            · replace h := congr_arg List.toFinset h; rw [ Finset.ext_iff ] at h; specialize h ( symbol.nonterminal () ) ; aesop;
        · rw [ List.append_eq_append_iff ] at hxy;
          rcases hxy with ( ⟨ as, rfl, h ⟩ | ⟨ bs, h, h' ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
          · rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.replicate ];
            · exact Or.inr ⟨ n, Or.inl ⟨ [ ], by aesop ⟩ ⟩;
            · replace h := congr_arg List.toFinset h.2; rw [ Finset.ext_iff ] at h; specialize h ( symbol.nonterminal () ) ; aesop;
          · rcases bs with ( _ | ⟨ a, bs ⟩ ) <;> simp_all +decide [ List.append_assoc ];
            · exact Or.inr ⟨ n, Or.inl ⟨ [ ], by aesop ⟩ ⟩;
            · replace h := congr_arg List.toFinset h; rw [ Finset.ext_iff ] at h; specialize h a; aesop;
      · rcases ht with ( ⟨ x, y, hxy, rfl ⟩ | ⟨ x, y, hxy, rfl ⟩ );
        · replace hxy := congr_arg List.toFinset hxy ; rw [ Finset.ext_iff ] at hxy ; specialize hxy ( symbol.nonterminal () ) ; aesop;
        · replace hxy := congr_arg List.toFinset hxy ; simp_all +decide [ Finset.ext_iff ];
          have := hxy ( symbol.nonterminal () ) ; have := hxy ( symbol.terminal false ) ; have := hxy ( symbol.terminal true ) ; aesop;

private lemma sentential_form_of_derives (w : List (symbol Bool Unit))
    (hd : CF_derives cfg_anbn [symbol.nonterminal ()] w) :
    sentential_form w := by
  induction hd with
  | refl => exact Or.inl ⟨0, by simp⟩
  | tail _ ht ih => exact sentential_form_step _ _ ih ht

private lemma CF_language_cfg_anbn_sub_anbn :
    ∀ w, w ∈ CF_language cfg_anbn → w ∈ anbn := by
  intro w hw
  have hsf : sentential_form (List.map symbol.terminal w) :=
    sentential_form_of_derives _ hw
  rcases hsf with ⟨n, hn⟩ | ⟨n, hn⟩
  · exfalso
    have hmem : symbol.nonterminal () ∈ List.map symbol.terminal w := by
      rw [hn]; simp
    simp at hmem
  · have hinj : Function.Injective (symbol.terminal (T := Bool) (N := Unit)) := by
      intro a b h; cases h; rfl
    exact ⟨n, hinj.list_map hn⟩

private lemma anbn_sub_CF_language_cfg_anbn :
    ∀ w, w ∈ anbn → w ∈ CF_language cfg_anbn := by
      intro w hw
      obtain ⟨n, rfl⟩ := hw;
      have h_deriv : ∀ n : ℕ, CF_derives cfg_anbn [symbol.nonterminal ()] (List.replicate n (symbol.terminal false) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal true)) := by
        intro n
        induction' n with n ih;
        · constructor;
        · have h_step : CF_derives cfg_anbn (List.replicate n (symbol.terminal false) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal true)) (List.replicate n (symbol.terminal false) ++ [symbol.terminal false, symbol.nonterminal (), symbol.terminal true] ++ List.replicate n (symbol.terminal true)) := by
            apply_rules [ CF_deri_of_tran, CF_deri_with_prefix_and_postfix ];
            use ((), [symbol.terminal false, symbol.nonterminal (), symbol.terminal true]);
            exact ⟨ replicate n ( symbol.terminal false ), replicate n ( symbol.terminal true ), by simp +decide [ cfg_anbn ], by simp +decide, by simp +decide ⟩;
          convert ih.trans h_step using 1 ; simp +decide [ List.replicate_add ];
          exact Nat.recOn n rfl fun n ih => by rw [ replicate_succ' ] ; aesop;
      have h_final : CF_derives cfg_anbn (List.replicate n (symbol.terminal false) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal true)) (List.replicate n (symbol.terminal false) ++ List.replicate n (symbol.terminal true)) := by
        apply_rules [ CF_deri_of_tran, CF_deri_with_prefix_and_postfix ];
        use ((), []);
        exact ⟨ replicate n ( symbol.terminal false ), replicate n ( symbol.terminal true ), by simp +decide [ cfg_anbn ], by simp +decide, by simp +decide ⟩;
      apply_rules [ CF_deri_of_deri_deri, h_deriv ];
      any_goals tauto;
      convert CF_deri_self using 1 ; aesop

theorem CF_language_cfg_anbn : CF_language cfg_anbn = anbn := by
  ext w; exact ⟨CF_language_cfg_anbn_sub_anbn w, anbn_sub_CF_language_cfg_anbn w⟩

/-- The language `{aⁿbⁿ}` is context-free. -/
theorem anbn_is_CF : is_CF anbn :=
  ⟨cfg_anbn, CF_language_cfg_anbn⟩

/-- There exists a context-free language that is not regular. -/
theorem exists_CF_not_regular : ∃ L : Language Bool, is_CF L ∧ ¬ L.IsRegular :=
  ⟨anbn, anbn_is_CF, anbn_not_isRegular⟩

-- ============================================================================
-- Section 2: lang_eq_eq ({aⁿbⁿcⁿ}) is recursively enumerable
-- ============================================================================

/-- Unrestricted grammar for `{aⁿbⁿcⁿ | n ∈ ℕ}` over `Fin 3`.

Nonterminals: `Fin 2` where `0 = S`, `1 = B`.

Rules:
1. S → ε
2. S → a S B c
3. c B → B c  (bubble sort)
4. a B → a b  (context-sensitive conversion)
5. b B → b b  (context-sensitive conversion)
-/
@[reducible] def grammar_anbncn : grammar (Fin 3) where
  nt := Fin 2
  initial := 0
  rules := [
    ⟨[], 0, [], []⟩,
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

-- Single-step lemmas

private lemma anbncn_step_eps (u v : List (symbol (Fin 3) grammar_anbncn.nt)) :
    grammar_transforms grammar_anbncn (u ++ [gS] ++ v) (u ++ v) := by
  exact ⟨⟨[], grammar_anbncn.initial, [], []⟩, by simp [grammar_anbncn],
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
      (List.replicate n ga ++ (List.replicate n [gB, gc]).flatten) := by
        convert anbncn_phase1 n |> fun h => h.trans _ using 1;
        convert Relation.ReflTransGen.single ( anbncn_step_eps _ _ ) using 1

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
      (List.replicate n ga ++ List.replicate n gB ++ List.replicate n gc)
      (List.replicate n ga ++ List.replicate n gb ++ List.replicate n gc) := by
  cases n with
  | zero => simp; constructor
  | succ m =>
    have h := anbncn_convert_chain ga (Or.inl rfl) (m + 1)
      (List.replicate m ga) (List.replicate (m + 1) gc)
    convert h using 1 <;> simp [List.replicate_succ']

-- Backward direction

private lemma anbncn_derivable (n : ℕ) :
    List.replicate n (0 : Fin 3) ++ List.replicate n 1 ++ List.replicate n 2 ∈
      grammar_language grammar_anbncn := by
  show grammar_generates grammar_anbncn _
  unfold grammar_generates
  apply grammar_deri_of_deri_deri (anbncn_after_expansion n)
  have hsort := grammar_deri_with_prefix (List.replicate n ga) (anbncn_sort n)
  apply grammar_deri_of_deri_deri hsort
  have hconv := anbncn_convert_Bs n
  convert hconv using 1 <;> simp [List.map_replicate]

/-
Forward direction: counting invariants
-/
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
      rcases v with ( rfl | rfl | rfl | rfl | rfl ) <;> simp_all +decide;
      linarith

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

private lemma grammar_inv_step_eps (u v : List (symbol (Fin 3) grammar_anbncn.nt))
    (hinv : grammar_inv (u ++ [gS] ++ v)) :
    grammar_inv (u ++ v) := by
      refine' ⟨ _, _, _, _ ⟩;
      · have := hinv.1; simp_all +decide [ List.pairwise_append ] ;
      · have := hinv.2.1; simp_all +decide [ List.pairwise_append ] ;
      · cases hinv ; aesop;
      · intro u' v' h;
        cases' List.append_eq_append_iff.mp h with h h <;> simp_all +decide [ List.append_eq_append_iff ];
        · rcases h with ⟨ as, ⟨ ⟨ as', rfl, h ⟩ | ⟨ bs, rfl, h ⟩, rfl ⟩ ⟩ <;> simp_all +decide [ List.append_eq_append_iff ];
          · cases as' <;> cases as <;> simp_all +decide [ List.append_eq_append_iff ];
            · have := hinv.2.2.2; aesop;
            · cases hinv ; aesop;
          · have := hinv.2.2.2;
            specialize this ( u ++ [ gS ] ++ bs ) v' ; aesop;
        · cases hinv ; aesop

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
    (try { show grammar_inv _; convert grammar_inv_step_eps u v (by convert hinv using 2 <;> simp)
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

/-
Any fully terminal word derivable from [gS] is sorted.
    Follows from the two weight invariants: wa-sorted gives a's first,
    wb-sorted gives b's before c's.
-/
private lemma terminal_sorted_of_derives
    (w : List (Fin 3))
    (hd : grammar_derives grammar_anbncn [gS] (w.map symbol.terminal)) :
    w.Pairwise (· ≤ ·) := by
      have := grammar_inv_of_derives _ hd;
      unfold grammar_inv at this;
      simp_all +decide [ List.pairwise_map ];
      simp_all +decide [ wa, wb, List.pairwise_iff_get ];
      grind

-- Combining forward direction

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
    ∀ w, w ∈ grammar_language grammar_anbncn → w ∈ lang_eq_eq := by
      intro w hw
      change grammar_generates grammar_anbncn w at hw
      have hw_derives : grammar_derives grammar_anbncn [gS] (w.map symbol.terminal) := hw
      have hw_sorted : w.Pairwise (· ≤ ·) := terminal_sorted_of_derives _ hw_derives
      obtain ⟨a_, b_, c_, hw_form⟩ := sorted_fin3_decomp hw_sorted
      subst hw_form
      have h1 := count_a_eq_Bb_of_derives _ hw_derives
      have h2 := count_a_eq_c_of_derives _ hw_derives
      -- Extract a_ = b_ = c_ from counting invariants
      exact ⟨a_, by
        unfold ga gc at *; simp_all +decide [ List.count_replicate ] ;
        rfl⟩

-- Main results

theorem grammar_anbncn_language : grammar_language grammar_anbncn = lang_eq_eq := by
  ext w
  exact ⟨grammar_anbncn_sub_lang_eq_eq w, fun ⟨n, hw⟩ => hw ▸ anbncn_derivable n⟩

/-- The language `{aⁿbⁿcⁿ}` is recursively enumerable. -/
theorem lang_eq_eq_is_RE : is_RE lang_eq_eq :=
  ⟨grammar_anbncn, grammar_anbncn_language⟩

-- ============================================================================
-- Section 3: Strict inclusion CF ⊊ RE
-- ============================================================================

/-- The class of context-free languages is a strict subclass of the class
    of recursively enumerable languages: every CF language is RE,
    but there exists an RE language that is not CF. -/
theorem CF_strictSubclass_RE :
    (∀ (T : Type) (L : Language T), is_CF L → is_RE L) ∧
    (∃ (T : Type) (L : Language T), is_RE L ∧ ¬ is_CF L) :=
  ⟨fun _ _ => CF_subclass_RE, ⟨Fin 3, lang_eq_eq, lang_eq_eq_is_RE, notCF_lang_eq_eq⟩⟩

-- ============================================================================
-- Section 4: Additional inclusions and chain
-- ============================================================================

/-- Every DCFL is RE (by transitivity: DCFL ⊆ CF ⊆ RE). -/
theorem DCFL_subclass_RE {T : Type} [Fintype T] {L : Language T}
    (h : is_DCFL L) : is_RE L :=
  CF_subclass_RE (is_CF_of_is_DCFL h)

/-- The Chomsky hierarchy inclusion chain: DCFL ⊆ CF ⊆ RE.
    Moreover, the inclusion CF ⊆ RE is strict. -/
theorem chomsky_hierarchy_chain :
    -- (1) DCFL ⊆ CF
    (∀ (T : Type) [Fintype T] (L : Language T), is_DCFL L → is_CF L) ∧
    -- (2) CF ⊆ RE
    (∀ (T : Type) (L : Language T), is_CF L → is_RE L) ∧
    -- (3) CF ⊊ RE (strict)
    (∃ (T : Type) (L : Language T), is_RE L ∧ ¬ is_CF L) ∧
    -- (4) Regular ⊂ CF is non-trivial: ∃ CF language that is not regular
    (∃ (L : Language Bool), is_CF L ∧ ¬ L.IsRegular) :=
  ⟨fun _ _ _ => is_CF_of_is_DCFL,
   fun _ _ => CF_subclass_RE,
   ⟨Fin 3, lang_eq_eq, lang_eq_eq_is_RE, notCF_lang_eq_eq⟩,
   exists_CF_not_regular⟩