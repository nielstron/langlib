import Langlib.Classes.ContextFree.Basics.Lifting
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Inclusion.ContextSensitive
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization

/-! # Context-Free Union Bonus Construction

This file records the older direct grammar construction for context-free closure under union.

## Main declarations

- `bonus_CF_of_CF_u_CF`
-/

variable {T : Type}

private def union_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (Option (g₁.nt ⊕ g₂.nt)) none (
  (none, [symbol.nonterminal (some (Sum.inl (g₁.initial)))]) ::
  (none, [symbol.nonterminal (some (Sum.inr (g₂.initial)))]) ::
  ((List.map rule_of_rule₁ g₁.rules) ++ (List.map rule_of_rule₂ g₂.rules))
)


variable {g₁ g₂ : CF_grammar T}

section lifted_grammars

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (Option g₁.nt)
| none => none
| (some (Sum.inl nonte)) => some nonte
| (some (Sum.inr _)) => none

private def oN₂_of_N : (union_grammar g₁ g₂).nt → (Option g₂.nt)
| none => none
| (some (Sum.inl _)) => none
| (some (Sum.inr nonte)) => some nonte



private def g₁g : @lifted_grammar T :=
lifted_grammar.mk g₁ (union_grammar g₁ g₂) (some ∘ Sum.inl)
  (by intro x y h; cases h; rfl)
  (by
    intros r h
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    rw [List.mem_map]
    refine ⟨r, h, ?_⟩
    unfold rule_of_rule₁ lift_rule
    norm_num
    unfold lift_string lsTN_of_lsTN₁
    five_steps
  )
  oN₁_of_N
  (by
    intro x y ass
    match x with
    | none => right; rfl
    | some (Sum.inl _) =>
        match y with
        | none => right; simp [oN₁_of_N] at ass
        | some (Sum.inl _) => left; simp [oN₁_of_N] at ass; cases ass; rfl
        | some (Sum.inr _) => simp [oN₁_of_N] at ass
    | some (Sum.inr _) => right; rfl
  )
  (by
    intros r
    rintro ⟨r_in, r_ntype⟩
    rcases List.mem_cons.1 r_in with rfl | r_in
    · exfalso; obtain ⟨n₀, imposs⟩ := r_ntype; simp [Function.comp] at imposs
    rcases List.mem_cons.1 r_in with rfl | r_in
    · exfalso; obtain ⟨n₀, imposs⟩ := r_ntype; simp [Function.comp] at imposs
    rw [List.mem_append] at r_in
    cases r_in with
    | inl r_in =>
        rcases List.mem_map.1 r_in with ⟨r₁, r₁_in, r₁_convert_r⟩
        refine ⟨r₁, r₁_in, ?_⟩
        rw [←r₁_convert_r]
        simp [lift_rule, rule_of_rule₁, lsTN_of_lsTN₁, Prod.mk.injEq, true_and]
        unfold lift_string
        five_steps
    | inr r_in =>
        exfalso
        rcases List.mem_map.1 r_in with ⟨r₂, _, rfl⟩
        obtain ⟨n₁, contr⟩ := r_ntype
        unfold rule_of_rule₂ at contr; cases contr
  )
  (by intro; rfl)

private def g₂g : @lifted_grammar T :=
lifted_grammar.mk g₂ (union_grammar g₁ g₂) (some ∘ Sum.inr)
  (by intro x y h; cases h; rfl)
  (by
    intro r h
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    rw [List.mem_map]
    refine ⟨r, h, ?_⟩
    unfold rule_of_rule₂ lift_rule
    norm_num
    unfold lift_string lsTN_of_lsTN₂
    five_steps
  )
  oN₂_of_N
  (by
    intro x y ass
    match x with
    | none => right; rfl
    | some (Sum.inl _) => right; rfl
    | some (Sum.inr _) =>
        match y with
        | none => right; cases ass
        | some (Sum.inl _) => simp [oN₂_of_N] at ass
        | some (Sum.inr _) => left; simp [oN₂_of_N] at ass; cases ass; rfl
  )
  (by
    intro r
    rintro ⟨r_in, r_ntype⟩
    rcases List.mem_cons.1 r_in with rfl | r_in
    · exfalso; obtain ⟨n₀, imposs⟩ := r_ntype; cases imposs
    rcases List.mem_cons.1 r_in with rfl | r_in
    · exfalso; obtain ⟨n₀, imposs⟩ := r_ntype; cases imposs
    rw [List.mem_append] at r_in
    cases r_in with
    | inl r_in =>
        exfalso
        rcases List.mem_map.1 r_in with ⟨r₁, _, rfl⟩
        obtain ⟨n₂, contr⟩ := r_ntype
        unfold rule_of_rule₁ at contr; cases contr
    | inr r_in =>
        rcases List.mem_map.1 r_in with ⟨r₂, r₂_in, rfl⟩
        refine ⟨r₂, r₂_in, ?_⟩
        unfold rule_of_rule₂ lift_rule lift_string lsTN_of_lsTN₂
        simp only [Prod.mk.injEq]
        exact ⟨rfl, by five_steps⟩
  )
  (by intro; rfl)

end lifted_grammars


section lemmata_subset

private lemma deri₁_more (w : List (symbol T g₁.nt)) :
  CF_derives g₁ [symbol.nonterminal g₁.initial] w →
    CF_derives
      (union_grammar g₁ g₂)
      (lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial])
      (lsTN_of_lsTN₁ w) :=
by
  intro ass
  let gg₁ := @g₁g T g₁ g₂
  change CF_derives gg₁.g (lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial]) (lsTN_of_lsTN₁ w)
  have techni : lsTN_of_lsTN₁ = lift_string gg₁.lift_nt := by
    unfold lsTN_of_lsTN₁ lift_string; ext1 w
    five_steps
  rw [techni]
  exact lift_deri ass

private lemma deri₂_more (w : List (symbol T g₂.nt)) :
  CF_derives g₂ [symbol.nonterminal g₂.initial] w →
    CF_derives
      (union_grammar g₁ g₂)
      (lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial])
      (lsTN_of_lsTN₂ w) :=
by
  intro ass
  let gg₂ := @g₂g T g₁ g₂
  change CF_derives gg₂.g (lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial]) (lsTN_of_lsTN₂ w)
  have techni : lsTN_of_lsTN₂ = lift_string gg₂.lift_nt := by
    unfold lsTN_of_lsTN₂ lift_string; ext1 w
    five_steps
  rw [techni]
  exact lift_deri ass

private lemma in_union_of_in_first (w : List T) :
  w ∈ CF_language g₁  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
by
  intro assum
  have deri_start :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal none]
      [symbol.nonterminal (some (Sum.inl g₁.initial))]
  := by
    apply CF_deri_of_tran
    refine ⟨(none, [symbol.nonterminal (some (Sum.inl (g₁.initial)))]), ?_, ?_, ?_⟩
    · exact []
    · exact []
    constructor
    · simp [union_grammar]
    constructor <;> simp
  have deri_rest :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal (some (Sum.inl g₁.initial))]
      (List.map symbol.terminal w) := by
    have beginning :
      [symbol.nonterminal (some (Sum.inl g₁.initial))] =
      lsTN_of_lsTN₁ (g₁ := g₁) (g₂ := g₂) [symbol.nonterminal g₁.initial] := by
      simp [lsTN_of_lsTN₁, sTN_of_sTN₁]
    rw [beginning, (lsTN_of_lsTN₁_map_terminal w).symm]
    exact deri₁_more (List.map symbol.terminal w) assum
  exact CF_deri_of_deri_deri deri_start deri_rest

private lemma in_union_of_in_second (w : List T) :
  w ∈ CF_language g₂  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
by
  intro assum
  have deri_start :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal none]
      [symbol.nonterminal (some (Sum.inr g₂.initial))]
  := by
    apply CF_deri_of_tran
    refine ⟨(none, [symbol.nonterminal (some (Sum.inr (g₂.initial)))]), ?_, ?_, ?_⟩
    · exact []
    · exact []
    constructor
    · simp [union_grammar]
    constructor <;> simp
  have deri_rest :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal (some (Sum.inr g₂.initial))]
      (List.map symbol.terminal w) := by
    have beginning :
      [symbol.nonterminal (some (Sum.inr g₂.initial))] =
      lsTN_of_lsTN₂ (g₁ := g₁) (g₂ := g₂) [symbol.nonterminal g₂.initial] := by
      simp [lsTN_of_lsTN₂, sTN_of_sTN₂]
    rw [beginning, (lsTN_of_lsTN₂_map_terminal w).symm]
    exact deri₂_more (List.map symbol.terminal w) assum
  exact CF_deri_of_deri_deri deri_start deri_rest

end lemmata_subset


section lemmata_supset

macro "good_singleton" : tactic =>
  `(tactic|
    (--
    unfold good_string
    intro a in_singleton
    rw [List.mem_singleton] at in_singleton
    rw [in_singleton]
    unfold good_letter
  ))

private lemma in_language_left_case_of_union {w : List T}
    (hypo : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal (some (Sum.inl g₁.initial))]
      (List.map symbol.terminal w)) :
  w ∈ CF_language g₁ :=
by
  change CF_derives g₁ [symbol.nonterminal g₁.initial] (List.map symbol.terminal w)
  let gg₁ := @g₁g T g₁ g₂
  have bar :
    [symbol.nonterminal g₁.initial] =
    (sink_string gg₁.sink_nt (T := T) [symbol.nonterminal (some (Sum.inl g₁.initial))]) := by
    unfold sink_string; rfl
  rw [bar, ← sink_string_map_terminal gg₁]
  exact (sink_deri gg₁ _ _ hypo (by good_singleton; exact ⟨g₁.initial, rfl⟩)).left

private lemma in_language_right_case_of_union {w : List T}
    (hypo : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal (some (Sum.inr g₂.initial))]
      (List.map symbol.terminal w)) :
  w ∈ CF_language g₂ :=
by
  change CF_derives g₂ [symbol.nonterminal g₂.initial] (List.map symbol.terminal w)
  let gg₂ := @g₂g T g₁ g₂
  have bar :
    [symbol.nonterminal g₂.initial] =
    (sink_string gg₂.sink_nt (T:=T) [symbol.nonterminal (some (Sum.inr g₂.initial))]) := by
    unfold sink_string; rfl
  rw [bar, ← sink_string_map_terminal gg₂]
  exact (sink_deri gg₂ _ _ hypo (by good_singleton; exact ⟨g₂.initial, rfl⟩)).left

private lemma both_empty
    (u v: List (symbol T (union_grammar g₁ g₂).nt))
    (a : (symbol T (union_grammar g₁ g₂).nt))
    (bef: [symbol.nonterminal (union_grammar g₁ g₂).initial] = u ++ [a] ++ v) :
  u = []  ∧  v = [] := by
  have len := congr_arg List.length bef
  simp [List.length_append] at len
  constructor <;> (rw [← List.length_eq_zero_iff]; omega)

private lemma in_language_impossible_case_of_union
    (w : List T)
    (r : (union_grammar g₁ g₂).nt × List (symbol T (union_grammar g₁ g₂).nt))
    (u v: List (symbol T (union_grammar g₁ g₂).nt))
    (hu : u = []) (hv : v = [])
    (bef: [symbol.nonterminal (union_grammar g₁ g₂).initial] = u ++ [symbol.nonterminal r.fst] ++ v)
    (sbi : r ∈ (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules)) :
  w ∈ CF_language g₁ ∨ w ∈ CF_language g₂ :=
by
  exfalso
  rw [hu, hv, List.nil_append, List.append_nil] at bef
  have rule_root : r.fst = none :=
    symbol.nonterminal.inj (List.head_eq_of_cons_eq bef).symm
  rcases List.mem_append.1 sbi with sbi | sbi
  · rcases List.mem_map.1 sbi with ⟨_, _, imposs⟩
    rw [←imposs] at rule_root
    unfold rule_of_rule₁ Prod.fst at rule_root
    cases rule_root
  · rcases List.mem_map.1 sbi with ⟨_, _, imposs⟩
    rw [←imposs] at rule_root
    unfold rule_of_rule₂ Prod.fst at rule_root
    cases rule_root

private lemma in_language_of_in_union (w : List T) :
  w ∈ CF_language (union_grammar g₁ g₂)   →   w ∈ CF_language g₁  ∨  w ∈ CF_language g₂   :=
by
  intro ass
  cases CF_tran_or_id_of_deri ass with
  | inl impossible =>
      exfalso
      cases w with
      | nil => cases impossible
      | cons head tail =>
          have zeroth := congr_arg List.head? impossible
          simp at zeroth
  | inr h =>
      rcases h with ⟨S₁, deri_head, deri_tail⟩
      rcases deri_head with ⟨rule, u, v, ruleok, h_bef, h_aft⟩
      rw [h_aft] at deri_tail
      obtain ⟨u_nil, v_nil⟩ := both_empty u v (symbol.nonterminal rule.fst) h_bef
      rcases List.mem_cons.1 ruleok with g₁S | r_rest
      · left
        exact in_language_left_case_of_union (by simpa [g₁S, u_nil, v_nil] using deri_tail)
      rcases List.mem_cons.1 r_rest with g₂S | r_imposs
      · right
        exact in_language_right_case_of_union (by simpa [g₂S, u_nil, v_nil] using deri_tail)
      · exact in_language_impossible_case_of_union w rule u v u_nil v_nil h_bef r_imposs

end lemmata_supset


/-- An explicit grammar construction witnessing closure of context-free languages under union. -/
theorem bonus_CF_of_CF_u_CF {T : Type} (L₁ : Language T) (L₂ : Language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ + L₂)   :=
by
  rintro ⟨h₁, h₂⟩
  obtain ⟨g₁, eq_L₁⟩ := is_CF_implies_is_CF_via_cfg h₁
  obtain ⟨g₂, eq_L₂⟩ := is_CF_implies_is_CF_via_cfg h₂
  apply is_CF_via_cfg_implies_is_CF
  refine ⟨union_grammar g₁ g₂, ?_⟩
  apply Set.eq_of_subset_of_subset
  · intro w hyp
    rw [Language.mem_add, ←eq_L₁, ←eq_L₂]
    exact in_language_of_in_union w hyp
  · intro w hyp
    cases hyp with
    | inl case₁ => rw [←eq_L₁] at case₁; exact in_union_of_in_first w case₁
    | inr case₂ => rw [←eq_L₂] at case₂; exact in_union_of_in_second w case₂
