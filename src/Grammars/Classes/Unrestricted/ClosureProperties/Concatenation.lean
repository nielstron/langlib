import Grammars.Classes.Unrestricted.Basics.Toolbox
import Grammars.Utilities.ListUtils

/-! # RE Closure Under Concatenation

This file constructs an unrestricted grammar for the concatenation of two recursively enumerable languages.

## Main declarations

- `big_grammar`
- `in_big_of_in_concatenated`
- `in_concatenated_of_in_big`
- `RE_of_RE_c_RE`
-/

-- removed duplicate List.nthLe (already defined in ListUtils)


section list_technicalities
variable {α β : Type}

lemma list_take_one_drop {l : List α} {i : ℕ} (hil : i < l.length) :
  List.take 1 (List.drop i l) = [l.get ⟨i, hil⟩] := by
  simpa [List.take, List.drop] using (List.take_one_drop_eq_of_lt_length (l := l) (n := i) hil)

lemma list_drop_take_succ {l : List α} {i : ℕ} (hil : i < l.length) :
  List.drop i (List.take (i + 1) l) = [l.get ⟨i, hil⟩] := by
  simpa using (List.drop_take_succ_eq_cons_getElem (L := l) (i := i) hil)


lemma list_forall₂_nth_le {R : α → β → Prop} :
  ∀ {x : List α}, ∀ {y : List β}, List.Forall₂ R x y →
    ∀ {i : ℕ}, ∀ i_lt_len_x : i < x.length, ∀ i_lt_len_y : i < y.length,
      R (x.get ⟨i, i_lt_len_x⟩) (y.get ⟨i, i_lt_len_y⟩)
| [], [] => by
    intro hyp i hx
    exact (Nat.not_lt_zero _ hx).elim
| [], (a₂::l₂) => by
    intro hyp
    cases hyp
| (a₁::l₁), [] => by
    intro hyp
    cases hyp
| (a₁::l₁), (a₂::l₂) =>
by
  intro ass i i_lt_len_x i_lt_len_y
  cases ass with
  | cons h_head h_tail =>
      cases i with
      | zero =>
          simpa using h_head
      | succ i =>
          have hx : i < l₁.length := Nat.lt_of_succ_lt_succ i_lt_len_x
          have hy : i < l₂.length := Nat.lt_of_succ_lt_succ i_lt_len_y
          exact list_forall₂_nth_le (x := l₁) (y := l₂) h_tail hx hy

lemma list_filter_map_eq_of_map_eq_map_some {f : α → Option β} :
  ∀ {x : List α}, ∀ {y : List β},
    List.map f x = List.map Option.some y →
      List.filterMap f x = y
| [], [] => by
    intro _
    rfl
| (a₁::l₁), [] => by
    intro hyp
    exact (List.cons_ne_nil _ _ hyp).elim
| [], (a₂::l₂) => by
    intro hyp
    exact (List.cons_ne_nil _ _ hyp.symm).elim
| (a₁::l₁), (a₂::l₂) =>
by
  intro ass
  simp at ass
  rcases ass with ⟨ass_head, ass_tail⟩
  simp [List.filterMap, ass_head, list_filter_map_eq_of_map_eq_map_some ass_tail]

end list_technicalities


-- new nonterminal type
def nnn (T N₁ N₂ : Type) : Type :=
Option (N₁ ⊕ N₂) ⊕ (T ⊕ T)

-- new symbol type
abbrev nst (T N₁ N₂ : Type) : Type :=
symbol T (nnn T N₁ N₂)

variable {T : Type}


section the_construction

def wrap_symbol₁ {N₁ : Type} (N₂ : Type) : symbol T N₁ → nst T N₁ N₂
| (symbol.terminal t)    => symbol.nonterminal (Sum.inr (Sum.inl t))
| (symbol.nonterminal n) => symbol.nonterminal (Sum.inl (some (Sum.inl n)))

def wrap_symbol₂ {N₂ : Type} (N₁ : Type) : symbol T N₂ → nst T N₁ N₂
| (symbol.terminal t)    => symbol.nonterminal (Sum.inr (Sum.inr t))
| (symbol.nonterminal n) => symbol.nonterminal (Sum.inl (some (Sum.inr n)))

private def wrap_grule₁ {N₁ : Type} (N₂ : Type) (r : grule T N₁) : grule T (nnn T N₁ N₂) :=
grule.mk
  (List.map (wrap_symbol₁ N₂) r.input_L)
  (Sum.inl (some (Sum.inl r.input_N)))
  (List.map (wrap_symbol₁ N₂) r.input_R)
  (List.map (wrap_symbol₁ N₂) r.output_string)

private def wrap_grule₂ {N₂ : Type} (N₁ : Type) (r : grule T N₂) : grule T (nnn T N₁ N₂) :=
grule.mk
  (List.map (wrap_symbol₂ N₁) r.input_L)
  (Sum.inl (some (Sum.inr r.input_N)))
  (List.map (wrap_symbol₂ N₁) r.input_R)
  (List.map (wrap_symbol₂ N₁) r.output_string)

def rules_for_terminals₁ (N₂ : Type) (g : grammar T) : List (grule T (nnn T g.nt N₂)) :=
List.map (fun t => grule.mk [] (Sum.inr (Sum.inl t)) [] [symbol.terminal t]) (all_used_terminals g)

def rules_for_terminals₂ (N₁ : Type) (g : grammar T) : List (grule T (nnn T N₁ g.nt)) :=
List.map (fun t => grule.mk [] (Sum.inr (Sum.inr t)) [] [symbol.terminal t]) (all_used_terminals g)

-- the grammar for concatenation of `g₁` and `g₂` languages
def big_grammar (g₁ g₂ : grammar T) : grammar T :=
grammar.mk (nnn T g₁.nt g₂.nt) (Sum.inl none) (
  (grule.mk [] (Sum.inl none) [] [
    symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
    symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))]
  ) :: (
    (List.map (wrap_grule₁ g₂.nt) g₁.rules ++ List.map (wrap_grule₂ g₁.nt) g₂.rules) ++
    (rules_for_terminals₁ g₂.nt g₁ ++ rules_for_terminals₂ g₁.nt g₂)
  )
)

end the_construction


section easy_direction

lemma grammar_generates_only_legit_terminals
    {g : grammar T}
    {w : List (symbol T g.nt)}
    (ass : grammar_derives g [symbol.nonterminal g.initial] w)
    {s : symbol T g.nt}
    (symbol_derived : s ∈ w) :
  (∃ r : grule T g.nt, r ∈ g.rules ∧ s ∈ r.output_string) ∨
  (s = symbol.nonterminal g.initial) :=
by
  induction ass with
  | refl =>
      rw [List.mem_singleton] at symbol_derived
      right
      exact symbol_derived
  | tail _ orig ih =>
      rcases orig with ⟨r, rin, u, v, bef, aft⟩
      rw [aft] at symbol_derived
      rw [List.mem_append] at symbol_derived
      rw [List.mem_append] at symbol_derived
      cases symbol_derived with
      | inl symbol_derived =>
          cases symbol_derived with
          | inl symbol_derived =>
              apply ih
              rw [bef]
              repeat
                rw [List.mem_append]
                left
              exact symbol_derived
          | inr symbol_derived =>
              left
              refine ⟨r, rin, ?_⟩
              exact symbol_derived
      | inr symbol_derived =>
          apply ih
          rw [bef]
          rw [List.mem_append]
          right
          exact symbol_derived

private lemma first_transformation {g₁ g₂ : grammar T} :
  grammar_transforms (big_grammar g₁ g₂) [symbol.nonterminal (big_grammar g₁ g₂).initial] [
      symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
      symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))
    ] :=
by
  have hlen : 0 < (big_grammar g₁ g₂).rules.length := by
    simp [big_grammar]
  refine ⟨(big_grammar g₁ g₂).rules.nthLe 0 hlen, ?_, ?_⟩
  ·
    exact List.nthLe_mem hlen
  ·
    refine ⟨[], [], ?_, ?_⟩ <;> rfl

private lemma substitute_terminals
    {g₁ g₂ : grammar T}
    {side : T → T ⊕ T}
    {w : List T}
    (rule_for_each_terminal : ∀ t ∈ w,
      (grule.mk [] (Sum.inr (side t)) [] [symbol.terminal t]) ∈
        (rules_for_terminals₁ g₂.nt g₁ ++ rules_for_terminals₂ g₁.nt g₂)) :
  grammar_derives (big_grammar g₁ g₂)
    (List.map (symbol.nonterminal ∘ Sum.inr ∘ side) w)
    (List.map symbol.terminal w) :=
by
  induction w with
  | nil =>
      exact grammar_deri_self
  | cons d l ih =>
      simp [List.map]
      have step_head :
        grammar_transforms (big_grammar g₁ g₂)
          ([(symbol.nonterminal ∘ Sum.inr ∘ side) d] ++ List.map (symbol.nonterminal ∘ Sum.inr ∘ side) l)
          ([symbol.terminal d] ++ List.map (symbol.nonterminal ∘ Sum.inr ∘ side) l) := by
        refine ⟨grule.mk [] (Sum.inr (side d)) [] [symbol.terminal d], ?_, ?_⟩
        ·
          change _ ∈ List.cons _ _
          apply List.mem_cons_of_mem
          apply List.mem_append_right
          have : d ∈ d :: l := by simpa using (List.mem_cons_self d l)
          exact rule_for_each_terminal d this
        ·
          refine ⟨[], List.map (symbol.nonterminal ∘ Sum.inr ∘ side) l, ?_, ?_⟩ <;> rfl
      apply grammar_deri_of_tran_deri step_head
      apply grammar_deri_with_prefix
      apply ih
      intro t tin
      exact rule_for_each_terminal t (List.mem_cons_of_mem _ tin)

lemma in_big_of_in_concatenated
    {g₁ g₂ : grammar T}
    {w : List T}
    (ass : w ∈ grammar_language g₁ * grammar_language g₂) :
  w ∈ grammar_language (big_grammar g₁ g₂) :=
by
  sorry
end easy_direction


section hard_direction

section correspondence_for_terminals

private def corresponding_symbols {N₁ N₂ : Type} : nst T N₁ N₂ → nst T N₁ N₂ → Prop
| symbol.terminal t,                               symbol.terminal t'                               => t = t'
| symbol.nonterminal (Sum.inr (Sum.inl a)),        symbol.nonterminal (Sum.inr (Sum.inl a'))        => a = a'
| symbol.nonterminal (Sum.inr (Sum.inr a)),        symbol.nonterminal (Sum.inr (Sum.inr a'))        => a = a'
| symbol.nonterminal (Sum.inr (Sum.inl a)),        symbol.terminal t                                => t = a
| symbol.nonterminal (Sum.inr (Sum.inr a)),        symbol.terminal t                                => t = a
| symbol.nonterminal (Sum.inl (some (Sum.inl n))), symbol.nonterminal (Sum.inl (some (Sum.inl n'))) => n = n'
| symbol.nonterminal (Sum.inl (some (Sum.inr n))), symbol.nonterminal (Sum.inl (some (Sum.inr n'))) => n = n'
| symbol.nonterminal (Sum.inl none),               symbol.nonterminal (Sum.inl none)                => True
| _,                                               _                                                => False

private lemma corresponding_symbols_self {N₁ N₂ : Type} (s : nst T N₁ N₂) : corresponding_symbols s s :=
by
  cases s with
  | terminal t => rfl
  | nonterminal n =>
      cases n with
      | inl o =>
          cases o with
          | none => trivial
          | some s =>
              cases s with
              | inl => rfl
              | inr => rfl
      | inr s =>
          cases s with
          | inl => rfl
          | inr => rfl

private lemma corresponding_symbols_never₁ {N₁ N₂ : Type} {s₁ : symbol T N₁} {s₂ : symbol T N₂} :
  ¬ corresponding_symbols (wrap_symbol₁ N₂ s₁) (wrap_symbol₂ N₁ s₂) :=
by
  cases s₁ <;> cases s₂ <;> simp [wrap_symbol₁, wrap_symbol₂, corresponding_symbols]

private lemma corresponding_symbols_never₂ {N₁ N₂ : Type} {s₁ : symbol T N₁} {s₂ : symbol T N₂} :
  ¬ corresponding_symbols (wrap_symbol₂ N₁ s₂) (wrap_symbol₁ N₂ s₁) :=
by
  cases s₁ <;> cases s₂ <;> simp [wrap_symbol₁, wrap_symbol₂, corresponding_symbols]

private def corresponding_strings {N₁ N₂ : Type} : List (nst T N₁ N₂) → List (nst T N₁ N₂) → Prop :=
List.Forall₂ corresponding_symbols

private lemma corresponding_strings_self {N₁ N₂ : Type} {x : List (nst T N₁ N₂)} :
  corresponding_strings x x :=
by
  induction x with
  | nil =>
      simp [corresponding_strings]
  | cons s xs ih =>
      simp [corresponding_strings, corresponding_symbols_self, ih]

private lemma corresponding_strings_singleton {N₁ N₂ : Type} {s₁ s₂ : nst T N₁ N₂}
    (ass : corresponding_symbols s₁ s₂) :
  corresponding_strings [s₁] [s₂] :=
by
  simp [corresponding_strings, ass]

private lemma corresponding_strings_append {N₁ N₂ : Type} {x₁ x₂ y₁ y₂ : List (nst T N₁ N₂)}
    (ass₁ : corresponding_strings x₁ y₁)
    (ass₂ : corresponding_strings x₂ y₂) :
  corresponding_strings (x₁ ++ x₂) (y₁ ++ y₂) :=
by
  unfold corresponding_strings at *
  exact List.rel_append ass₁ ass₂

private lemma corresponding_strings_length {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (ass : corresponding_strings x y) :
  x.length = y.length :=
by
  unfold corresponding_strings at ass
  exact List.Forall₂.length_eq ass

private lemma corresponding_strings_nth_le {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)} {i : ℕ}
    (i_lt_len_x : i < x.length) (i_lt_len_y : i < y.length)
    (ass : corresponding_strings x y) :
  corresponding_symbols (x.nthLe i i_lt_len_x) (y.nthLe i i_lt_len_y) :=
by
  sorry

private lemma corresponding_strings_reverse {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (ass : corresponding_strings x y) :
  corresponding_strings x.reverse y.reverse :=
by
  unfold corresponding_strings at *
  rw [List.forall₂_reverse_iff]
  exact ass

private lemma corresponding_strings_of_reverse {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (ass : corresponding_strings x.reverse y.reverse) :
  corresponding_strings x y :=
by
  unfold corresponding_strings at *
  rw [List.forall₂_reverse_iff] at ass
  exact ass

private lemma corresponding_strings_take {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (n : ℕ) (ass : corresponding_strings x y) :
  corresponding_strings (List.take n x) (List.take n y) :=
by
  unfold corresponding_strings at *
  exact List.forall₂_take n ass

private lemma corresponding_strings_drop {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (n : ℕ) (ass : corresponding_strings x y) :
  corresponding_strings (List.drop n x) (List.drop n y) :=
by
  unfold corresponding_strings at *
  exact List.forall₂_drop n ass

private lemma corresponding_strings_split {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (n : ℕ) (ass : corresponding_strings x y) :
  corresponding_strings (List.take n x) (List.take n y) ∧
  corresponding_strings (List.drop n x) (List.drop n y) :=
by
  constructor
  · exact corresponding_strings_take n ass
  · exact corresponding_strings_drop n ass

end correspondence_for_terminals


section unwrapping_nst

private def unwrap_symbol₁ {N₁ N₂ : Type} : nst T N₁ N₂ → Option (symbol T N₁)
| (symbol.terminal t)                               => some (symbol.terminal t)
| (symbol.nonterminal (Sum.inr (Sum.inl a)))        => some (symbol.terminal a)
| (symbol.nonterminal (Sum.inr (Sum.inr a)))        => none
| (symbol.nonterminal (Sum.inl (some (Sum.inl n)))) => some (symbol.nonterminal n)
| (symbol.nonterminal (Sum.inl (some (Sum.inr n)))) => none
| (symbol.nonterminal (Sum.inl none))               => none

private def unwrap_symbol₂ {N₁ N₂ : Type} : nst T N₁ N₂ → Option (symbol T N₂)
| (symbol.terminal t)                               => some (symbol.terminal t)
| (symbol.nonterminal (Sum.inr (Sum.inl a)))        => none
| (symbol.nonterminal (Sum.inr (Sum.inr a)))        => some (symbol.terminal a)
| (symbol.nonterminal (Sum.inl (some (Sum.inl n)))) => none
| (symbol.nonterminal (Sum.inl (some (Sum.inr n)))) => some (symbol.nonterminal n)
| (symbol.nonterminal (Sum.inl none))               => none


private lemma unwrap_wrap₁_symbol {N₁ N₂ : Type} : @unwrap_symbol₁ T N₁ N₂ ∘ wrap_symbol₁ N₂ = Option.some :=
by
  ext1 a
  cases a <;> rfl

private lemma unwrap_wrap₂_symbol {N₁ N₂ : Type} : @unwrap_symbol₂ T N₁ N₂ ∘ wrap_symbol₂ N₁ = Option.some :=
by
  ext1 a
  cases a <;> rfl

private lemma unwrap_wrap₁_string {N₁ N₂ : Type} {w : List (symbol T N₁)} :
  List.filterMap unwrap_symbol₁ (List.map (wrap_symbol₁ N₂) w) = w :=
by
  rw [List.filterMap_map]
  rw [unwrap_wrap₁_symbol]
  apply List.filterMap_some

private lemma unwrap_wrap₂_string {N₁ N₂ : Type} {w : List (symbol T N₂)} :
  List.filterMap unwrap_symbol₂ (List.map (wrap_symbol₂ N₁) w) = w :=
by
  rw [List.filterMap_map]
  rw [unwrap_wrap₂_symbol]
  apply List.filterMap_some

private lemma unwrap_eq_some_of_corresponding_symbols₁ {N₁ N₂ : Type} {s₁ : symbol T N₁} {s : nst T N₁ N₂}
    (ass : corresponding_symbols (wrap_symbol₁ N₂ s₁) s) :
  unwrap_symbol₁ s = some s₁ :=
by
  sorry

private lemma unwrap_eq_some_of_corresponding_symbols₂ {N₁ N₂ : Type} {s₂ : symbol T N₂} {s : nst T N₁ N₂}
    (ass : corresponding_symbols (wrap_symbol₂ N₁ s₂) s) :
  unwrap_symbol₂ s = some s₂ :=
by
  sorry

private lemma map_unwrap_eq_map_some_of_corresponding_strings₁ {N₁ N₂ : Type} :
  ∀ {v : List (symbol T N₁)}, ∀ {w : List (nst T N₁ N₂)},
    corresponding_strings (List.map (wrap_symbol₁ N₂) v) w →
      List.map unwrap_symbol₁ w = List.map Option.some v := by
  intro v w ass
  sorry

private lemma map_unwrap_eq_map_some_of_corresponding_strings₂ {N₁ N₂ : Type} :
  ∀ {v : List (symbol T N₂)}, ∀ {w : List (nst T N₁ N₂)},
    corresponding_strings (List.map (wrap_symbol₂ N₁) v) w →
      List.map unwrap_symbol₂ w = List.map Option.some v := by
  intro v w ass
  sorry

private lemma filter_map_unwrap_of_corresponding_strings₁ {N₁ N₂ : Type}
    {v : List (symbol T N₁)} {w : List (nst T N₁ N₂)}
    (ass : corresponding_strings (List.map (wrap_symbol₁ N₂) v) w) :
  List.filterMap unwrap_symbol₁ w = v :=
by
  apply list_filter_map_eq_of_map_eq_map_some
  exact map_unwrap_eq_map_some_of_corresponding_strings₁ ass

private lemma filter_map_unwrap_of_corresponding_strings₂ {N₁ N₂ : Type}
    {v : List (symbol T N₂)} {w : List (nst T N₁ N₂)}
    (ass : corresponding_strings (List.map (wrap_symbol₂ N₁) v) w) :
  List.filterMap unwrap_symbol₂ w = v :=
by
  apply list_filter_map_eq_of_map_eq_map_some
  exact map_unwrap_eq_map_some_of_corresponding_strings₂ ass

private lemma corresponding_string_after_wrap_unwrap_self₁ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (ass : ∃ z : List (symbol T N₁), corresponding_strings (List.map (wrap_symbol₁ N₂) z) w) :
  corresponding_strings (List.map (wrap_symbol₁ N₂) (List.filterMap unwrap_symbol₁ w)) w :=
by
  sorry
private lemma corresponding_string_after_wrap_unwrap_self₂ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (ass : ∃ z : List (symbol T N₂), corresponding_strings (List.map (wrap_symbol₂ N₁) z) w) :
  corresponding_strings (List.map (wrap_symbol₂ N₁) (List.filterMap unwrap_symbol₂ w)) w :=
by
  sorry
end unwrapping_nst


section very_complicated

private lemma induction_step_for_lifted_rule_from_g₁
    {g₁ g₂ : grammar T}
    {a b u v : List (nst T g₁.nt g₂.nt)}
    {x : List (symbol T g₁.nt)}
    {y : List (symbol T g₂.nt)}
    {r : grule T (nnn T g₁.nt g₂.nt)}
    (rin : r ∈ List.map (wrap_grule₁ g₂.nt) g₁.rules)
    (bef : a = u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v)
    (aft : b = u ++ r.output_string ++ v)
    (ih_x : grammar_derives g₁ [symbol.nonterminal g₁.initial] x)
    (ih_y : grammar_derives g₂ [symbol.nonterminal g₂.initial] y)
    (ih_concat :
      corresponding_strings
        (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y)
        a) :
  ∃ (x' : List (symbol T g₁.nt)),
      (grammar_derives g₁ [symbol.nonterminal g₁.initial] x') ∧
      (grammar_derives g₂ [symbol.nonterminal g₂.initial] y) ∧
      (corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x' ++ List.map (wrap_symbol₂ g₁.nt) y) b) :=
by
  sorry
private lemma induction_step_for_lifted_rule_from_g₂
    {g₁ g₂ : grammar T}
    {a b u v : List (nst T g₁.nt g₂.nt)}
    {x : List (symbol T g₁.nt)}
    {y : List (symbol T g₂.nt)}
    {r : grule T (nnn T g₁.nt g₂.nt)}
    (rin : r ∈ List.map (wrap_grule₂ g₁.nt) g₂.rules)
    (bef : a = u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v)
    (aft : b = u ++ r.output_string ++ v)
    (ih_x : grammar_derives g₁ [symbol.nonterminal g₁.initial] x)
    (ih_y : grammar_derives g₂ [symbol.nonterminal g₂.initial] y)
    (ih_concat :
      corresponding_strings
        (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y)
        a) :
  ∃ (y' : List (symbol T g₂.nt)),
      (grammar_derives g₁ [symbol.nonterminal g₁.initial] x) ∧
      (grammar_derives g₂ [symbol.nonterminal g₂.initial] y') ∧
      (corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y') b) :=
by
  sorry
private lemma big_induction
    {g₁ g₂ : grammar T}
    {w : List (nst T g₁.nt g₂.nt)}
    (ass :
      grammar_derives (big_grammar g₁ g₂)
        [symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
         symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))]
        w) :
  ∃ x : List (symbol T g₁.nt),
  ∃ y : List (symbol T g₂.nt),
      (grammar_derives g₁ [symbol.nonterminal g₁.initial] x) ∧
      (grammar_derives g₂ [symbol.nonterminal g₂.initial] y) ∧
      (corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y) w) :=
by
  sorry
lemma in_concatenated_of_in_big
    {g₁ g₂ : grammar T}
    {w : List T}
    (ass : w ∈ grammar_language (big_grammar g₁ g₂)) :
  w ∈ grammar_language g₁ * grammar_language g₂ :=
by
  sorry
end very_complicated

end hard_direction


/-- The class of recursively-enumerable languages is closed under concatenation. -/
theorem RE_of_RE_c_RE (L₁ : Language T) (L₂ : Language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ * L₂)   :=
by
  sorry
