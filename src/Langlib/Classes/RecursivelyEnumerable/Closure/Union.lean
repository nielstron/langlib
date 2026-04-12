import Langlib.Classes.RecursivelyEnumerable.Basics.Lifting
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Utilities.ListUtils
import Langlib.Utilities.ClosurePredicates


/-! # RE Closure Under Union

This file constructs an unrestricted grammar for the union of two recursively enumerable languages.

## Main declarations

- `union_grammar`
- `in_L₁_or_L₂_of_in_union`
- `in_union_of_in_L₁`
- `in_union_of_in_L₂`
- `RE_of_RE_u_RE`
-/

variable {T : Type}

def union_grammar (g₁ g₂ : grammar T) : grammar T :=
grammar.mk (Option (g₁.nt ⊕ g₂.nt)) none (
  ⟨ [], none, [], [symbol.nonterminal (some (Sum.inl (g₁.initial)))] ⟩ :: (
  ⟨ [], none, [], [symbol.nonterminal (some (Sum.inr (g₂.initial)))] ⟩ :: (
  (List.map (lift_rule_ (some ∘ Sum.inl)) g₁.rules) ++
  (List.map (lift_rule_ (some ∘ Sum.inr)) g₂.rules)
  )))


variable {g₁ g₂ : grammar T}

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (Option g₁.nt)
| none               => none
| (some (Sum.inl n)) => some n
| (some (Sum.inr _)) => none

private def oN₂_of_N : (union_grammar g₁ g₂).nt → (Option g₂.nt)
| none               => none
| (some (Sum.inl _)) => none
| (some (Sum.inr n)) => some n


private def lg₁ : lifted_grammar_ T :=
lifted_grammar_.mk g₁ (union_grammar g₁ g₂) (Option.some ∘ Sum.inl) oN₁_of_N
  (fun _ _ h => Sum.inl_injective (Option.some_injective _ h))
  (by
    intro x y hyp
    match x with
    | none => right; rfl
    | some (Sum.inl x_nt) =>
        match y with
        | none => rw [hyp]; right; rfl
        | some (Sum.inl y_nt) =>
            left
            simp only [oN₁_of_N] at hyp
            exact congrArg (fun nt => some (Sum.inl nt)) (Option.some.inj hyp)
        | some (Sum.inr _) => cases hyp
    | some (Sum.inr _) => right; rfl)
  (fun _ => rfl)
  (by
    intro r hyp
    apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
    exact List.mem_append_left _ (List.mem_map.2 ⟨r, hyp, rfl⟩))
  (by
    rintro r ⟨rin, n₀, rnt⟩
    rcases List.mem_cons.1 rin with rfl | rin
    · cases rnt
    rcases List.mem_cons.1 rin with rfl | rin
    · cases rnt
    rcases List.mem_append.1 rin with rin | rin
    · exact let ⟨r₁, r₁_in, r₁_lift⟩ := List.mem_map.1 rin; ⟨r₁, r₁_in, r₁_lift⟩
    · exfalso
      rcases List.mem_map.1 rin with ⟨_, _, rfl⟩
      simp [lift_rule_] at rnt; cases rnt)

private def lg₂ : lifted_grammar_ T :=
lifted_grammar_.mk g₂ (union_grammar g₁ g₂) (Option.some ∘ Sum.inr) oN₂_of_N
  (fun _ _ h => Sum.inr_injective (Option.some_injective _ h))
  (by
    intro x y hyp
    match x with
    | none => right; rfl
    | some (Sum.inl _) => right; rfl
    | some (Sum.inr x_nt) =>
        match y with
        | none => right; rw [hyp]; rfl
        | some (Sum.inl _) => cases hyp
        | some (Sum.inr y_nt) =>
            left
            simp only [oN₂_of_N] at hyp
            exact congrArg (fun nt => some (Sum.inr nt)) (Option.some.inj hyp))
  (fun _ => rfl)
  (by
    intro r hyp
    apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
    exact List.mem_append_right _ (List.mem_map.2 ⟨r, hyp, rfl⟩))
  (by
    rintro r ⟨rin, n₀, rnt⟩
    rcases List.mem_cons.1 rin with rfl | rin
    · cases rnt
    rcases List.mem_cons.1 rin with rfl | rin
    · cases rnt
    rcases List.mem_append.1 rin with rin | rin
    · exfalso
      rcases List.mem_map.1 rin with ⟨_, _, rfl⟩
      simp [lift_rule_] at rnt; cases rnt
    · exact let ⟨r₂, r₂_in, r₂_lift⟩ := List.mem_map.1 rin; ⟨r₂, r₂_in, r₂_lift⟩)


lemma in_L₁_or_L₂_of_in_union {w : List T} (ass : w ∈ grammar_language (union_grammar g₁ g₂)) :
  w ∈ grammar_language g₁  ∨  w ∈ grammar_language g₂  :=
by
  unfold grammar_language at ass ⊢
  change grammar_generates (union_grammar g₁ g₂) w at ass
  change grammar_generates g₁ w ∨ grammar_generates g₂ w
  unfold grammar_generates at ass ⊢
  cases grammar_tran_or_id_of_deri (g := union_grammar g₁ g₂) ass with
  | inl hyp =>
      exfalso
      cases w with
      | nil => simp at hyp
      | cons head tail =>
          have zeroth := congrArg List.head? hyp
          simp at zeroth
  | inr hyp =>
      rcases hyp with ⟨i, ⟨r, rin, u, v, bef, aft⟩, deri⟩
      -- u and v must be empty since initial is a singleton
      have uv_nil : u = [] ∧ v = [] := by
        have bef_len := congrArg List.length bef
        simp [List.length_append] at bef_len
        constructor <;> (rw [← List.length_eq_zero_iff]; omega)
      rw [uv_nil.1, List.nil_append, uv_nil.2, List.append_nil] at bef aft

      have same_nt : (union_grammar g₁ g₂).initial = r.input_N := by
        have : r.input_L = [] ∧ r.input_R = [] := by
          have bef_len := congr_arg List.length bef
          rw [List.length_append_append, List.length_singleton, List.length_singleton] at bef_len
          constructor
          · rw [← List.length_eq_zero_iff]; omega
          · rw [← List.length_eq_zero_iff]; omega
        rw [this.1, this.2] at bef
        exact symbol.nonterminal.inj (List.head_eq_of_cons_eq bef)

      rcases List.mem_cons.1 rin with rfl | rin
      · -- First rule: initial → g₁.initial
        left; rw [aft] at deri; dsimp only at deri
        convert sink_deri_ lg₁ deri (by
          unfold good_string_; simp only [List.mem_singleton, forall_eq]; exact ⟨g₁.initial, rfl⟩)
        exact (sink_string_map_terminal_ lg₁.sink_nt w).symm
      rcases List.mem_cons.1 rin with rfl | rin
      · -- Second rule: initial → g₂.initial
        right; rw [aft] at deri; dsimp only at deri
        convert sink_deri_ lg₂ deri (by
          unfold good_string_; simp only [List.mem_singleton, forall_eq]; exact ⟨g₂.initial, rfl⟩)
        exact (sink_string_map_terminal_ lg₂.sink_nt w).symm
      · -- Impossible: initial can't match any lifted rule
        exfalso
        rcases List.mem_append.1 rin with rin | rin <;> {
          rcases List.mem_map.1 rin with ⟨_, _, rfl⟩
          simp [lift_rule_] at same_nt; cases same_nt
        }


lemma in_union_of_in_L₁ {w : List T} (ass : w ∈ grammar_language g₁) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
by
  unfold grammar_language at ass ⊢
  change grammar_generates g₁ w at ass
  change grammar_generates (union_grammar g₁ g₂) w
  unfold grammar_generates at ass ⊢
  refine grammar_deri_of_tran_deri (g := union_grammar g₁ g₂)
    (v := [symbol.nonterminal (some (Sum.inl g₁.initial))]) ?_ ?_
  ·
    refine ⟨⟨ [], none, [], [symbol.nonterminal (some (Sum.inl (g₁.initial)))] ⟩, ?_, ?_⟩
    · simp [union_grammar]
    · refine ⟨[], [], ?_, ?_⟩ <;> simp [union_grammar]
  ·
    have lifted := lift_deri_ (@lg₁ _ _ g₂) ass
    rwa [lift_string_map_terminal_] at lifted

lemma in_union_of_in_L₂ {w : List T} (ass : w ∈ grammar_language g₂) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
by
  unfold grammar_language at ass ⊢
  change grammar_generates g₂ w at ass
  change grammar_generates (union_grammar g₁ g₂) w
  unfold grammar_generates at ass ⊢
  refine grammar_deri_of_tran_deri (g := union_grammar g₁ g₂)
    (v := [symbol.nonterminal (some (Sum.inr g₂.initial))]) ?_ ?_
  ·
    refine ⟨⟨ [], none, [], [symbol.nonterminal (some (Sum.inr (g₂.initial)))] ⟩, ?_, ?_⟩
    · simp [union_grammar]
    · refine ⟨[], [], ?_, ?_⟩ <;> simp [union_grammar]
  ·
    have lifted := lift_deri_ (@lg₂ _ g₁ _) ass
    rwa [lift_string_map_terminal_] at lifted


/-- The class of recursively-enumerable languages is closed under union. -/
theorem RE_of_RE_u_RE (L₁ : Language T) (L₂ : Language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ + L₂)   :=
by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  use union_grammar g₁ g₂
  ext w
  constructor
  · intro ass
    rw [Language.mem_add, ←eq_L₁, ←eq_L₂]
    exact in_L₁_or_L₂_of_in_union ass
  · intro ass
    cases ass with
    | inl case₁ => rw [←eq_L₁] at case₁; exact in_union_of_in_L₁ case₁
    | inr case₂ => rw [←eq_L₂] at case₂; exact in_union_of_in_L₂ case₂

/-- The class of recursively enumerable languages is closed under union. -/
theorem RE_closedUnderUnion : ClosedUnderUnion (α := T) is_RE :=
  fun L₁ L₂ h₁ h₂ => RE_of_RE_u_RE L₁ L₂ ⟨h₁, h₂⟩
