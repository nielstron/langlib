import Mathlib
import Langlib.Grammars.Unrestricted.Toolbox
import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Utilities.ListUtils
import Langlib.Utilities.ClosurePredicates

/-! # RE Closure Under Concatenation

This file constructs an unrestricted grammar for the concatenation of two recursively enumerable languages.

## Main declarations

- `big_grammar`
- `in_big_of_in_concatenated`
- `in_concatenated_of_in_big`
- `RE_of_RE_c_RE`
-/


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

/-
PROVIDED SOLUTION
From ass, extract w₁ and w₂ with w = w₁ ++ w₂, w₁ ∈ grammar_language g₁, w₂ ∈ grammar_language g₂. The proof proceeds by:
1. Apply first_transformation to derive from initial to [wrap(g₁.initial), wrap(g₂.initial)].
2. Lift the derivation of g₁ generating w₁ using wrap_symbol₁, and the derivation of g₂ generating w₂ using wrap_symbol₂. The lifted rules are in big_grammar by construction.
3. Apply substitute_terminals to convert the wrapped terminal symbols to actual terminals.
4. Combine these three phases of derivation using grammar_deri_of_deri_deri.

Key steps: first_transformation gives the initial step. Then grammar_deri_with_postfix and grammar_deri_with_prefix allow combining the two independent derivations. Finally substitute_terminals handles the terminal conversion phase.
-/
lemma in_big_of_in_concatenated
    {g₁ g₂ : grammar T}
    {w : List T}
    (ass : w ∈ grammar_language g₁ * grammar_language g₂) :
  w ∈ grammar_language (big_grammar g₁ g₂) :=
by
  obtain ⟨w₁, w₂, hw₁, hw₂, rfl⟩ : ∃ w₁ w₂, w₁ ∈ grammar_language g₁ ∧ w₂ ∈ grammar_language g₂ ∧ w = w₁ ++ w₂ := by
    cases ass ; aesop;
  -- By definition of big_grammar, we know that if w₁ is generated by g₁ and w₂ is generated by g₂, then w₁ ++ w₂ can be generated by big_grammar.
  have h_derive : grammar_derives (big_grammar g₁ g₂) [symbol.nonterminal (Sum.inl none)] (List.map (wrap_symbol₁ g₂.nt) (List.map symbol.terminal w₁) ++ List.map (wrap_symbol₂ g₁.nt) (List.map symbol.terminal w₂)) := by
    have h_derive : grammar_derives (big_grammar g₁ g₂) [symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))), symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))] (List.map (wrap_symbol₁ g₂.nt) (List.map symbol.terminal w₁) ++ List.map (wrap_symbol₂ g₁.nt) (List.map symbol.terminal w₂)) := by
      have h_derive : ∀ {w : List (symbol T g₁.nt)}, grammar_derives g₁ [symbol.nonterminal g₁.initial] w → grammar_derives (big_grammar g₁ g₂) [symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial)))] (List.map (wrap_symbol₁ g₂.nt) w) := by
        intro w hw
        induction' hw with w' hw' ih;
        · constructor;
        · rename_i h₁ h₂;
          obtain ⟨ r, hr, u, v, rfl, rfl ⟩ := h₁;
          convert h₂.tail _ using 1;
          use wrap_grule₁ g₂.nt r;
          grind +locals;
      have h_derive₂ : ∀ {w : List (symbol T g₂.nt)}, grammar_derives g₂ [symbol.nonterminal g₂.initial] w → grammar_derives (big_grammar g₁ g₂) [symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))] (List.map (wrap_symbol₂ g₁.nt) w) := by
        intro w hw
        induction' hw with w₁ w₂ hw₁ hw₂ ih;
        · constructor;
        · obtain ⟨ r, hr, u, v, rfl, rfl ⟩ := hw₂;
          refine' ih.tail _;
          use grule.mk (List.map (wrap_symbol₂ g₁.nt) r.input_L) (Sum.inl (some (Sum.inr r.input_N))) (List.map (wrap_symbol₂ g₁.nt) r.input_R) (List.map (wrap_symbol₂ g₁.nt) r.output_string);
          unfold big_grammar; aesop;
      convert grammar_deri_with_postfix _ ( h_derive hw₁ ) |> grammar_deri_of_deri_deri <| grammar_deri_with_prefix _ ( h_derive₂ hw₂ ) using 1;
    exact grammar_deri_of_deri_deri ( grammar_deri_of_tran ( first_transformation ) ) h_derive;
  -- Apply the substitute_terminals lemma to convert the wrapped terminal symbols to actual terminals.
  have h_subst : grammar_derives (big_grammar g₁ g₂) (List.map (wrap_symbol₁ g₂.nt) (List.map symbol.terminal w₁) ++ List.map (wrap_symbol₂ g₁.nt) (List.map symbol.terminal w₂)) (List.map symbol.terminal w₁ ++ List.map symbol.terminal w₂) := by
    have h_subst : ∀ t ∈ w₁, (grule.mk [] (Sum.inr (Sum.inl t)) [] [symbol.terminal t]) ∈ (rules_for_terminals₁ g₂.nt g₁ ++ rules_for_terminals₂ g₁.nt g₂) := by
      intro t ht
      have h_term : t ∈ all_used_terminals g₁ := by
        have h_term : ∀ {w : List (symbol T g₁.nt)}, grammar_derives g₁ [symbol.nonterminal g₁.initial] w → ∀ t ∈ w, t = symbol.nonterminal g₁.initial ∨ ∃ r ∈ g₁.rules, t ∈ r.output_string := by
          intros w hw t ht; exact (by
          have := grammar_generates_only_legit_terminals hw ht; aesop;);
        specialize h_term hw₁ (symbol.terminal t);
        unfold all_used_terminals; aesop;
      unfold rules_for_terminals₁; aesop;
    have h_subst : ∀ t ∈ w₂, (grule.mk [] (Sum.inr (Sum.inr t)) [] [symbol.terminal t]) ∈ (rules_for_terminals₁ g₂.nt g₁ ++ rules_for_terminals₂ g₁.nt g₂) := by
      intro t ht
      have h_subst : t ∈ all_used_terminals g₂ := by
        have h_subst : ∀ {w : List (symbol T g₂.nt)}, grammar_derives g₂ [symbol.nonterminal g₂.initial] w → ∀ s ∈ w, s = symbol.terminal t → t ∈ all_used_terminals g₂ := by
          intros w hw s hs hs_eq
          have h_subst : ∃ r : grule T g₂.nt, r ∈ g₂.rules ∧ s ∈ r.output_string := by
            have := grammar_generates_only_legit_terminals hw hs; aesop;
          unfold all_used_terminals; aesop;
        exact h_subst hw₂ _ ( List.mem_map.mpr ⟨ t, ht, rfl ⟩ ) rfl
      simp [rules_for_terminals₂, h_subst];
    convert grammar_deri_with_postfix _ ( substitute_terminals _ ) |> grammar_deri_of_deri_deri <| grammar_deri_with_prefix _ ( substitute_terminals _ ) using 1;
    rotate_left;
    use fun t => Sum.inl t;
    grind +splitIndPred;
    use fun t => Sum.inr t;
    · assumption;
    · unfold wrap_symbol₁ wrap_symbol₂; aesop;
  refine' h_derive.trans h_subst |> fun h => h.trans _;
  grind

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

/-
PROVIDED SOLUTION
This follows directly from list_forall₂_nth_le applied to corresponding_strings (which is just List.Forall₂ corresponding_symbols).
-/
private lemma corresponding_strings_nth_le {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)} {i : ℕ}
    (i_lt_len_x : i < x.length) (i_lt_len_y : i < y.length)
    (ass : corresponding_strings x y) :
  corresponding_symbols (x.nthLe i i_lt_len_x) (y.nthLe i i_lt_len_y) :=
by
  have h_nth : ∀ {x y : List (nst T N₁ N₂)}, List.Forall₂ corresponding_symbols x y → ∀ i i_lt_len_x i_lt_len_y, corresponding_symbols (x.nthLe i i_lt_len_x) (y.nthLe i i_lt_len_y) := by
    intros x y hxy i i_lt_len_x i_lt_len_y; induction' i with i ih generalizing x y;
    · rcases x with ( _ | ⟨ a, _ | ⟨ b, x ⟩ ⟩ ) <;> rcases y with ( _ | ⟨ c, _ | ⟨ d, y ⟩ ⟩ ) <;> simp_all +decide [ List.Forall₂ ];
      · contradiction;
      · exact hxy;
      · exact hxy.1;
    · rcases x with ( _ | ⟨ x, xs ⟩ ) <;> rcases y with ( _ | ⟨ y, ys ⟩ ) <;> norm_num at *;
      · contradiction;
      · contradiction;
      · contradiction;
      · exact ih hxy.2 ( by simpa using i_lt_len_x ) ( by simpa using i_lt_len_y );
  exact h_nth ass i i_lt_len_x i_lt_len_y

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

/-
PROVIDED SOLUTION
Case split on s₁ and s, then use the definition of corresponding_symbols and unwrap_symbol₁/wrap_symbol₁. For each case where corresponding_symbols holds, show that unwrap_symbol₁ gives back the original symbol.
-/
private lemma unwrap_eq_some_of_corresponding_symbols₁ {N₁ N₂ : Type} {s₁ : symbol T N₁} {s : nst T N₁ N₂}
    (ass : corresponding_symbols (wrap_symbol₁ N₂ s₁) s) :
  unwrap_symbol₁ s = some s₁ :=
by
  -- By definition of wrap_symbol₁, if wrap_symbol₁ s₁ is equal to s, then s must be a terminal or a nonterminal that wraps s₁.
  cases' s with s_term s_nonterm;
  · cases s₁ <;> cases ass ; aesop;
  · cases s₁ <;> cases s_nonterm <;> simp_all +decide [ corresponding_symbols ];
    · cases ‹Option ( N₁ ⊕ N₂ ) › <;> tauto;
    · cases ‹T ⊕ T› <;> simp_all +decide [ wrap_symbol₁ ];
      rfl;
    · rename_i n hn;
      rcases hn with ( _ | _ | _ ) <;> simp_all +decide [ wrap_symbol₁ ];
      exact?;
    · cases ‹T ⊕ T› <;> tauto

/-
PROVIDED SOLUTION
Case split on s₂ and s, then use the definition of corresponding_symbols and unwrap_symbol₂/wrap_symbol₂. Analogous to the ₁ version.
-/
private lemma unwrap_eq_some_of_corresponding_symbols₂ {N₁ N₂ : Type} {s₂ : symbol T N₂} {s : nst T N₁ N₂}
    (ass : corresponding_symbols (wrap_symbol₂ N₁ s₂) s) :
  unwrap_symbol₂ s = some s₂ :=
by
  -- By definition of `wrap_symbol₂`, we know that `wrap_symbol₂ N₁ s₂` is the wrapped version of `s₂`.
  cases' s₂ with t n₂;
  · unfold wrap_symbol₂ at ass;
    unfold corresponding_symbols at ass;
    unfold unwrap_symbol₂; aesop;
  · cases' s with t n₁ n₂ ; tauto;
    cases' n₁ with n₁ n₁;
    · cases' n₁ with n₁ n₁;
      · cases ass;
      · cases n₁ <;> cases ass;
        rfl;
    · cases n₁ <;> tauto

/-
PROVIDED SOLUTION
Induction on the Forall₂ relation (corresponding_strings). Base case is trivial. For the cons case, use unwrap_eq_some_of_corresponding_symbols₁ for the head and the inductive hypothesis for the tail.
-/
private lemma map_unwrap_eq_map_some_of_corresponding_strings₁ {N₁ N₂ : Type} :
  ∀ {v : List (symbol T N₁)}, ∀ {w : List (nst T N₁ N₂)},
    corresponding_strings (List.map (wrap_symbol₁ N₂) v) w →
      List.map unwrap_symbol₁ w = List.map Option.some v := by
  intro v w ass
  induction' v with v₁ v ih generalizing w <;> induction' w with w₁ w ihw <;> simp_all +decide [ List.Forall₂ ];
  · cases ass;
  · cases ass;
  · cases ass;
    exact ⟨ by exact? , ih ‹_› ⟩

/-
PROVIDED SOLUTION
Induction on the Forall₂ relation (corresponding_strings). Analogous to the ₁ version, using unwrap_eq_some_of_corresponding_symbols₂.
-/
private lemma map_unwrap_eq_map_some_of_corresponding_strings₂ {N₁ N₂ : Type} :
  ∀ {v : List (symbol T N₂)}, ∀ {w : List (nst T N₁ N₂)},
    corresponding_strings (List.map (wrap_symbol₂ N₁) v) w →
      List.map unwrap_symbol₂ w = List.map Option.some v := by
  intro v w ass
  have h_ind : ∀ {v : List (symbol T N₂)} {w : List (nst T N₁ N₂)}, corresponding_strings (List.map (wrap_symbol₂ N₁) v) w → List.map unwrap_symbol₂ w = List.map Option.some v := by
    intro v w ass
    induction' v with s₂ v ih generalizing w;
    · cases w <;> trivial;
    · rcases w with ( _ | ⟨ s, w ⟩ ) <;> simp_all +decide [ corresponding_strings ];
      grind +suggestions;
  exact h_ind ass

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

/-
PROVIDED SOLUTION
From ass, get z with corresponding_strings (map (wrap_symbol₁ N₂) z) w. Then filter_map_unwrap_of_corresponding_strings₁ gives filterMap unwrap_symbol₁ w = z. Substituting z back and using corresponding_string_after_wrap_unwrap_self₁'s hypothesis, we get the result. More precisely: since corresponding_strings (map (wrap_symbol₁ N₂) z) w, by filter_map_unwrap_of_corresponding_strings₁ we get filterMap unwrap_symbol₁ w = z. So map (wrap_symbol₁ N₂) (filterMap unwrap_symbol₁ w) = map (wrap_symbol₁ N₂) z, and corresponding_strings (map (wrap_symbol₁ N₂) z) w gives us the result.
-/
private lemma corresponding_string_after_wrap_unwrap_self₁ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (ass : ∃ z : List (symbol T N₁), corresponding_strings (List.map (wrap_symbol₁ N₂) z) w) :
  corresponding_strings (List.map (wrap_symbol₁ N₂) (List.filterMap unwrap_symbol₁ w)) w :=
by
  obtain ⟨ z, hz ⟩ := ass; rw [ filter_map_unwrap_of_corresponding_strings₁ hz ] ; exact hz;

/-
PROVIDED SOLUTION
Analogous to ₁ version: from ass get z, use filter_map_unwrap_of_corresponding_strings₂ to get filterMap unwrap_symbol₂ w = z, then substitute back.
-/
private lemma corresponding_string_after_wrap_unwrap_self₂ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (ass : ∃ z : List (symbol T N₂), corresponding_strings (List.map (wrap_symbol₂ N₁) z) w) :
  corresponding_strings (List.map (wrap_symbol₂ N₁) (List.filterMap unwrap_symbol₂ w)) w :=
by
  obtain ⟨ z, hz ⟩ := ass;
  rw [ filter_map_unwrap_of_corresponding_strings₂ hz ];
  assumption

end unwrapping_nst


section helpers_for_induction_steps

variable {N₁ N₂ : Type}

/-
PROVIDED SOLUTION
Cases on s, both give rfl.
-/
private lemma unwrap₁_of_wrap₂_eq_none (s : symbol T N₂) :
    @unwrap_symbol₁ T N₁ N₂ (wrap_symbol₂ N₁ s) = none := by
      cases s <;> rfl

/-
PROVIDED SOLUTION
Cases on s, both give rfl.
-/
private lemma unwrap₂_of_wrap₁_eq_none (s : symbol T N₁) :
    @unwrap_symbol₂ T N₁ N₂ (wrap_symbol₁ N₂ s) = none := by
      cases s <;> rfl

/-
PROVIDED SOLUTION
Induction on w, using unwrap₁_of_wrap₂_eq_none at each step.
-/
private lemma filterMap_unwrap₁_map_wrap₂ (w : List (symbol T N₂)) :
    List.filterMap (@unwrap_symbol₁ T N₁ N₂) (List.map (wrap_symbol₂ N₁) w) = [] := by
      have h_filterMap_none : ∀ s ∈ List.map (wrap_symbol₂ N₁) w, @unwrap_symbol₁ T N₁ N₂ s = none := by
        intro s hs
        obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
        exact (by
        exact?);
      rw [ List.filterMap_eq_nil_iff ] ; aesop

/-
PROVIDED SOLUTION
Induction on w, using unwrap₂_of_wrap₁_eq_none at each step.
-/
private lemma filterMap_unwrap₂_map_wrap₁ (w : List (symbol T N₁)) :
    List.filterMap (@unwrap_symbol₂ T N₁ N₂) (List.map (wrap_symbol₁ N₂) w) = [] := by
      -- By the induction hypothesis, the filterMap of the map of wrap_symbol₁ N₂ over w is empty.
      simp [List.map_append, List.filterMap_append, *];
      exact?

/-
PROBLEM
Splitting Forall₂ at an append boundary

PROVIDED SOLUTION
Use m₁ = take l₁.length m and m₂ = drop l₁.length m. Then m = m₁ ++ m₂ by List.take_append_drop. Use List.forall₂_take and List.forall₂_drop, plus List.take_append (taking l₁.length from l₁ ++ l₂ gives l₁) and List.drop_append (dropping l₁.length from l₁ ++ l₂ gives l₂).
-/
private lemma forall₂_append_split {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {m : List β}
    (h : List.Forall₂ R (l₁ ++ l₂) m) :
    ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂ := by
      have h_split : ∀ {l₁ l₂ : List α} {m : List β}, List.Forall₂ R (l₁ ++ l₂) m → ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ R l₁ m₁ ∧ List.Forall₂ R l₂ m₂ := by
        intros l₁ l₂ m h; induction' l₁ with a l₁ ih generalizing l₂ m; aesop; (
        rcases m with ( _ | ⟨ b, m ⟩ ) <;> simp_all +decide [ List.forall₂_cons ];
        rcases ih h.2 with ⟨ m₁, m₂, rfl, hm₁, hm₂ ⟩ ; exact ⟨ b :: m₁, m₂, rfl, by aesop ⟩ ;);
      grind

/-
PROBLEM
The wrap_symbol₁ nonterminal Sum.inl (some (Sum.inl n₁)) cannot correspond to any wrap_symbol₂ output

PROVIDED SOLUTION
Cases on s₂. For terminal t: wrap_symbol₂ = nonterminal (Sum.inr (Sum.inr t)), corresponding_symbols with nonterminal (Sum.inl (some (Sum.inl n₁))) is False by definition. For nonterminal n: wrap_symbol₂ = nonterminal (Sum.inl (some (Sum.inr n))), corresponding_symbols with nonterminal (Sum.inl (some (Sum.inl n₁))) is False by definition.
-/
private lemma no_wrap₂_corr_sum_inl_inl {n₁ : N₁} {s₂ : symbol T N₂} :
    ¬ corresponding_symbols (wrap_symbol₂ N₁ s₂)
      (symbol.nonterminal (Sum.inl (some (Sum.inl n₁))) : nst T N₁ N₂) := by
        cases s₂ <;> aesop

/-
PROBLEM
Symmetric: wrap_symbol₂ nonterminal Sum.inl (some (Sum.inr n₂)) cannot correspond to any wrap_symbol₁ output

PROVIDED SOLUTION
Cases on s₁. For terminal t: wrap_symbol₁ = nonterminal (Sum.inr (Sum.inl t)), corresponding_symbols with nonterminal (Sum.inl (some (Sum.inr n₂))) is False. For nonterminal n: wrap_symbol₁ = nonterminal (Sum.inl (some (Sum.inl n))), corresponding_symbols with nonterminal (Sum.inl (some (Sum.inr n₂))) is False.
-/
private lemma no_wrap₁_corr_sum_inl_inr {n₂ : N₂} {s₁ : symbol T N₁} :
    ¬ corresponding_symbols (wrap_symbol₁ N₂ s₁)
      (symbol.nonterminal (Sum.inl (some (Sum.inr n₂))) : nst T N₁ N₂) := by
        cases s₁ <;> aesop

/-
PROBLEM
If corresponding_strings (map wrap₁ x ++ map wrap₂ y) a, then filterMap unwrap₁ (take x.length a) = x

PROVIDED SOLUTION
Use corresponding_strings_take x.length h. This gives corresponding_strings (take x.length (map wrap₁ x ++ map wrap₂ y)) (take x.length a). Since |map wrap₁ x| = x.length, take x.length (map wrap₁ x ++ map wrap₂ y) = map wrap₁ x (by List.take_left). So we get corresponding_strings (map wrap₁ x) (take x.length a). Then apply filter_map_unwrap_of_corresponding_strings₁.
-/
private lemma x_from_take_filterMap
    {x : List (symbol T N₁)} {y : List (symbol T N₂)}
    {a : List (nst T N₁ N₂)}
    (h : corresponding_strings (List.map (wrap_symbol₁ N₂) x ++ List.map (wrap_symbol₂ N₁) y) a) :
    List.filterMap (@unwrap_symbol₁ T N₁ N₂) (List.take x.length a) = x := by
      convert filter_map_unwrap_of_corresponding_strings₁ _;
      convert corresponding_strings_take x.length h using 1;
      simp +decide [ List.take_append ]

/-
PROBLEM
Symmetric: filterMap unwrap₂ (drop x.length a) = y

PROVIDED SOLUTION
Use corresponding_strings_drop x.length h. This gives corresponding_strings (drop x.length (map wrap₁ x ++ map wrap₂ y)) (drop x.length a). Since |map wrap₁ x| = x.length, drop x.length (map wrap₁ x ++ map wrap₂ y) = map wrap₂ y (by List.drop_left). So we get corresponding_strings (map wrap₂ y) (drop x.length a). Then apply filter_map_unwrap_of_corresponding_strings₂.
-/
private lemma y_from_drop_filterMap
    {x : List (symbol T N₁)} {y : List (symbol T N₂)}
    {a : List (nst T N₁ N₂)}
    (h : corresponding_strings (List.map (wrap_symbol₁ N₂) x ++ List.map (wrap_symbol₂ N₁) y) a) :
    List.filterMap (@unwrap_symbol₂ T N₁ N₂) (List.drop x.length a) = y := by
      convert filter_map_unwrap_of_corresponding_strings₂ _;
      convert corresponding_strings_drop x.length h using 1;
      simp +decide [ List.drop_append ]

/-
PROBLEM
The rule pattern from g₁ (wrapped) fits entirely within the first x.length elements

PROVIDED SOLUTION
By contradiction. Assume u.length + r₁.input_L.length + 1 + r₁.input_R.length > x.length. Then position p = u.length + r₁.input_L.length (the nonterminal position) satisfies p ≥ x.length (since p + 1 ≤ u.length + r₁.input_L.length + 1 + r₁.input_R.length > x.length, so p ≥ x.length).

At position p in a (from bef), a[p] = symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N))).

From ih_concat, at position p, the corresponding element in (map wrap₁ x ++ map wrap₂ y) is at position p. Since p ≥ x.length = |map wrap₁ x|, this element is in map wrap₂ y, specifically (map wrap₂ y)[p - x.length] = wrap_symbol₂ N₁ (y[p - x.length]).

So corresponding_symbols (wrap_symbol₂ N₁ (y[p - x.length])) (nt (Sum.inl (some (Sum.inl r₁.input_N)))) holds.

But this contradicts no_wrap₂_corr_sum_inl_inl.

Use corresponding_strings_nth_le or List.Forall₂ indexed access to get the element at position p.
-/
private lemma rule_in_first_half
    {x : List (symbol T N₁)} {y : List (symbol T N₂)}
    {a u v : List (nst T N₁ N₂)}
    {r₁ : grule T N₁}
    (ih_concat : corresponding_strings
      (List.map (wrap_symbol₁ N₂) x ++ List.map (wrap_symbol₂ N₁) y) a)
    (bef : a = u ++ (List.map (wrap_symbol₁ N₂) r₁.input_L) ++
               [symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++
               (List.map (wrap_symbol₁ N₂) r₁.input_R) ++ v) :
    u.length + r₁.input_L.length + 1 + r₁.input_R.length ≤ x.length := by
      contrapose! ih_concat; simp_all +decide [ corresponding_strings ] ;
      intro h; have := List.forall₂_iff_get.mp h; simp_all +decide [ List.getElem_append ] ;
      have := this.2 ( u.length + r₁.input_L.length ) ( by linarith ) ( by linarith ) ; simp_all +decide [ add_assoc ] ;
      split_ifs at this <;> simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
      · cases h : x[r₁.input_L.length + u.length] <;> simp_all +decide [ corresponding_symbols ];
        · cases this;
        · cases this;
          have := this.2 ( r₁.input_L.length + u.length + r₁.input_R.length ) ( by linarith ) ( by linarith ) ; simp_all +decide [ add_assoc ] ;
          grind +suggestions;
      · exact no_wrap₂_corr_sum_inl_inl this

/-
PROBLEM
Symmetric: rule from g₂ fits in the last y.length elements (i.e., starts at or after x.length)

PROVIDED SOLUTION
By contradiction. Assume x.length > u.length. Then position p = u.length + r₂.input_L.length (the nonterminal position) satisfies p ≤ u.length + r₂.input_L.length.

Actually, even just the nonterminal at position u.length + r₂.input_L.length: from bef, a[u.length + r₂.input_L.length] = symbol.nonterminal (Sum.inl (some (Sum.inr r₂.input_N))).

If this position < x.length, then in the reference list (map wrap₁ x ++ map wrap₂ y), the element at this position is (map wrap₁ x)[u.length + r₂.input_L.length] = wrap_symbol₁ N₂ (x[...]).

So corresponding_symbols (wrap_symbol₁ N₂ (...)) (nt (Sum.inl (some (Sum.inr r₂.input_N)))) holds.

But this contradicts no_wrap₁_corr_sum_inl_inr.

Actually the argument needs more care: we need u.length + r₂.input_L.length < x.length. Since x.length > u.length and r₂.input_L.length ≥ 0, we need x.length > u.length but u.length + r₂.input_L.length could be ≥ x.length. Let me fix: if u.length < x.length, then at position u.length in a, a[u.length] is the first element of r₂.input_L (if nonempty) or the nonterminal (if input_L is empty). If r₂.input_L is empty, the nonterminal is at position u.length < x.length, and we use no_wrap₁_corr_sum_inl_inr as above. If r₂.input_L is nonempty, at position u.length we have (map wrap₂ r₂.input_L)[0] = wrap_symbol₂ N₁ (r₂.input_L[0]), which is a wrap₂ output. The reference at position u.length < x.length is (map wrap₁ x)[u.length] = wrap_symbol₁ N₂ (x[u.length]). So corresponding_symbols (wrap_symbol₁ N₂ (...)) (wrap_symbol₂ N₁ (...)), which contradicts corresponding_symbols_never₂ (noting the order: corresponding_symbols (wrap₁ ...) (wrap₂ ...)). Wait, corresponding_symbols_never₂ says ¬ corresponding_symbols (wrap₂ ...) (wrap₁ ...). The order matters. Let me check: ih_concat says Forall₂ corresponding_symbols ref a, so corresponding_symbols (ref[i]) (a[i]). At position i = u.length, ref[i] = wrap₁ x[u.length], a[i] = wrap₂ r₂.input_L[0]. So corresponding_symbols (wrap₁ ...) (wrap₂ ...), which is ¬ by corresponding_symbols_never₁. Use that.
-/
private lemma rule_in_second_half
    {x : List (symbol T N₁)} {y : List (symbol T N₂)}
    {a u v : List (nst T N₁ N₂)}
    {r₂ : grule T N₂}
    (ih_concat : corresponding_strings
      (List.map (wrap_symbol₁ N₂) x ++ List.map (wrap_symbol₂ N₁) y) a)
    (bef : a = u ++ (List.map (wrap_symbol₂ N₁) r₂.input_L) ++
               [symbol.nonterminal (Sum.inl (some (Sum.inr r₂.input_N)))] ++
               (List.map (wrap_symbol₂ N₁) r₂.input_R) ++ v) :
    x.length ≤ u.length := by
      have h_p_le_x : u.length < x.length → False := by
        intro h_lt_x
        have h_p_le_x : corresponding_symbols (wrap_symbol₁ N₂ (x.get ⟨u.length, h_lt_x⟩)) (a.get ⟨u.length, by
          simp +arith +decide [ bef ]⟩) := by
          have := List.forall₂_iff_get.mp ih_concat;
          grind
        generalize_proofs at *;
        by_cases h : r₂.input_L.length = 0 <;> simp_all +decide [ List.getElem_append ];
        · exact no_wrap₁_corr_sum_inl_inr h_p_le_x |> fun h => by tauto;
        · split_ifs at h_p_le_x <;> simp_all +decide [ corresponding_symbols_never₁ ]
      exact le_of_not_gt h_p_le_x

/-
PROBLEM
Pure list fact: take of a concatenation u ++ L ++ [n] ++ R ++ v when the take length
exceeds u ++ L ++ [n] ++ R

PROVIDED SOLUTION
Since |u| + |L| + 1 + |R| ≤ m, taking m elements from u ++ L ++ [n] ++ R ++ v first takes all of u (|u| elements), then all of L (|L| elements), then [n] (1 element), then all of R (|R| elements), and then m - |u| - |L| - 1 - |R| elements from v. Use List.take_append_of_le_length repeatedly, or simp with List.take_append, List.length_append.
-/
private lemma take_of_append_five {α : Type} {u L : List α} {n : α} {R v : List α} {m : ℕ}
    (h_le : u.length + L.length + 1 + R.length ≤ m) :
    List.take m (u ++ L ++ [n] ++ R ++ v) =
      u ++ L ++ [n] ++ R ++ List.take (m - (u.length + L.length + 1 + R.length)) v := by
        rw [ List.take_append, List.take_append, List.take_append, List.take_append ] ; simp +arith +decide [ * ] ; ring;
        rw [ List.take_of_length_le, List.take_of_length_le, List.take_of_length_le ] <;> norm_num <;> omega;

/-
PROVIDED SOLUTION
Since |u| + |L| + 1 + |R| ≤ m ≤ |u| + |L| + 1 + |R| + |v|, dropping m elements from u ++ L ++ [n] ++ R ++ v first drops all of u, L, [n], R, then drops m - |u| - |L| - 1 - |R| elements from v. Use List.drop_append_of_le_length or omega/simp.
-/
private lemma drop_of_append_five {α : Type} {u L : List α} {n : α} {R v : List α} {m : ℕ}
    (h_le : u.length + L.length + 1 + R.length ≤ m)
    (h_le2 : m ≤ u.length + L.length + 1 + R.length + v.length) :
    List.drop m (u ++ L ++ [n] ++ R ++ v) =
      List.drop (m - (u.length + L.length + 1 + R.length)) v := by
        rw [ show m = 1 + u.length + L.length + R.length + ( m - ( 1 + u.length + L.length + R.length ) ) by rw [ add_tsub_cancel_of_le ] ; linarith ] ; simp +decide [ List.drop_append, add_comm, add_left_comm, add_assoc ] ; ring;
        rw [ List.drop_eq_nil_of_le, List.drop_eq_nil_of_le ] <;> simp +arith +decide

end helpers_for_induction_steps

section very_complicated

/-
PROVIDED SOLUTION
1. obtain ⟨r₁, hr₁_mem, rfl⟩ from List.mem_map.mp rin. simp only [wrap_grule₁] at bef aft.
2. have h_le := rule_in_first_half ih_concat bef.
3. set v₁ := take (x.length - (u.length + r₁.input_L.length + 1 + r₁.input_R.length)) v, v₂ := drop ... v.
4. Show take x.length a = u ++ map wrap₁ r₁.input_L ++ [nt (Sum.inl (some (Sum.inl r₁.input_N)))] ++ map wrap₁ r₁.input_R ++ v₁ using take_of_append_five on bef.
5. Show drop x.length a = v₂ using drop_of_append_five on bef.
6. Get h_corr_take from corresponding_strings_take and h_corr_drop from corresponding_strings_drop of ih_concat (using simp [List.take_left/drop_left]).
7. Get h_x_eq using filter_map_unwrap_of_corresponding_strings₁ on the take correspondence.
8. Simplify h_x_eq using filterMap_append, unwrap_wrap₁_string to get x = filterMap u ++ r₁.input_L ++ [nt r₁.input_N] ++ r₁.input_R ++ filterMap v₁.
9. Witness x' = filterMap unwrap₁ u ++ r₁.output_string ++ filterMap unwrap₁ v₁.
10. grammar_transforms via ⟨r₁, hr₁_mem, filterMap u, filterMap v₁, h_x_decomp, rfl⟩.
11. Correspondence: rw [aft, v=v₁++v₂], simp [List.map_append, List.append_assoc], then apply corresponding_strings_append 3 times for 4 parts:
   (a) map wrap₁ (filterMap unwrap₁ u) ~ u: use corresponding_string_after_wrap_unwrap_self₁ with witness from corresponding_strings_take u.length on the take-correspondence (need List.map_take to convert)
   (b) map wrap₁ r₁.output_string ~ map wrap₁ r₁.output_string: corresponding_strings_self
   (c) map wrap₁ (filterMap unwrap₁ v₁) ~ v₁: corresponding_string_after_wrap_unwrap_self₁ with witness from corresponding_strings_drop plen on take-correspondence (need List.map_drop to convert)
   (d) map wrap₂ y ~ v₂: from corresponding_strings_drop of ih_concat
-/
set_option maxHeartbeats 800000 in
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
  by_contra h_contra';
  obtain ⟨ r₁, hr₁_mem, rfl ⟩ := List.mem_map.mp rin;
  -- Set `v₁` and `v₂` as described.
  set v₁ := List.take (x.length - (u.length + r₁.input_L.length + 1 + r₁.input_R.length)) v
  set v₂ := List.drop (x.length - (u.length + r₁.input_L.length + 1 + r₁.input_R.length)) v;
  -- Show that the take of the list up to x.length is equal to the concatenation of the take of the first part and the take of the second part.
  have h_take : List.take x.length a = u ++ (List.map (wrap_symbol₁ g₂.nt) r₁.input_L) ++ [symbol.nonterminal (Sum.inl (some (Sum.inl r₁.input_N)))] ++ (List.map (wrap_symbol₁ g₂.nt) r₁.input_R) ++ v₁ := by
    have h_le : u.length + r₁.input_L.length + 1 + r₁.input_R.length ≤ x.length := by
      apply rule_in_first_half ih_concat bef;
    rw [bef];
    rw [take_of_append_five];
    · unfold wrap_grule₁; aesop;
    · unfold wrap_grule₁; aesop;
  -- Show that the drop of the list up to x.length is equal to the concatenation of the drop of the first part and the drop of the second part.
  have h_drop : List.drop x.length a = v₂ := by
    convert drop_of_append_five _ _ using 1;
    congr! 1;
    · unfold wrap_grule₁; aesop;
    · convert rule_in_first_half ih_concat bef using 1;
      unfold wrap_grule₁; simp +arith +decide;
    · have := corresponding_strings_length ih_concat; simp_all +decide ;
      lia;
  -- Show that the corresponding strings of the take and drop parts hold.
  have h_take_corr : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x) (List.take x.length a) := by
    have h_take_corr : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y) a := by
      exact ih_concat;
    have := corresponding_strings_take x.length h_take_corr; aesop;
  have h_drop_corr : corresponding_strings (List.map (wrap_symbol₂ g₁.nt) y) (List.drop x.length a) := by
    convert corresponding_strings_drop x.length ih_concat using 1;
    simp +decide [ List.drop_append ];
  -- Show that the corresponding strings of the take and drop parts hold for the new list b.
  have h_new_corr : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) (List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) u ++ r₁.output_string ++ List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) v₁) ++ List.map (wrap_symbol₂ g₁.nt) y) b := by
    have h_new_corr : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) (List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) u) ++ List.map (wrap_symbol₁ g₂.nt) r₁.output_string ++ List.map (wrap_symbol₁ g₂.nt) (List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) v₁)) (u ++ (wrap_grule₁ g₂.nt r₁).output_string ++ v₁) := by
      have h_new_corr : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) (List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) u)) u := by
        apply corresponding_string_after_wrap_unwrap_self₁
        generalize_proofs at *; (
        use List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) (List.take x.length a) |> fun z => z.take (u.length) |> fun z => z; (
        have h_filterMap_take : List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) (List.take x.length a) = x := by
          exact x_from_take_filterMap ih_concat
        generalize_proofs at *; (
        have := corresponding_strings_take u.length h_take_corr; simp_all +decide [ List.take_append ] ;));)
      have h_new_corr' : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) (List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) v₁)) v₁ := by
        have h_new_corr' : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x) (List.take x.length a) := by
          exact h_take_corr;
        have := corresponding_strings_split ( u.length + r₁.input_L.length + 1 + r₁.input_R.length ) h_new_corr'; simp_all +decide [ List.take_append, List.drop_append ] ;
        apply corresponding_string_after_wrap_unwrap_self₁; exact (by
          have := this.right; simp_all +decide [ List.drop_append, List.take_append ] ;
          simp_all +decide [ List.drop_eq_nil_of_le, add_assoc, add_tsub_assoc_of_le ];
          use List.drop (u.length + (r₁.input_L.length + (1 + r₁.input_R.length))) x; simp_all +decide [ List.drop_append, List.take_append ] ;
          convert this using 1 ; simp +decide [ add_comm, add_left_comm, add_assoc ] ;
        )
      have h_new_corr'' : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) r₁.output_string) (wrap_grule₁ g₂.nt r₁).output_string := by
        exact corresponding_strings_self
      exact corresponding_strings_append (corresponding_strings_append h_new_corr h_new_corr'') h_new_corr' |> fun h => by simpa [List.map_append] using h;
    convert corresponding_strings_append h_new_corr ( h_drop_corr ) using 1 ; simp +decide [ aft ] ; ring!;
    rw [ aft, h_drop ] ; simp +decide [ List.append_assoc ] ; ring!;
    rw [ show x.length - ( 1 + u.length + r₁.input_L.length + r₁.input_R.length ) = x.length - ( u.length + r₁.input_L.length + 1 + r₁.input_R.length ) by ring, List.take_append_drop ];
  refine h_contra' ⟨ List.filterMap unwrap_symbol₁ u ++ r₁.output_string ++ List.filterMap unwrap_symbol₁ v₁, ?_, ih_y, h_new_corr ⟩;
  have h_x_eq : x = List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) u ++ r₁.input_L ++ [symbol.nonterminal r₁.input_N] ++ r₁.input_R ++ List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) v₁ := by
    have h_x_eq : List.filterMap (@unwrap_symbol₁ T g₁.nt g₂.nt) (List.take x.length a) = x := by
      apply x_from_take_filterMap; assumption;
    rw [ ← h_x_eq, h_take, List.filterMap_append, List.filterMap_append, List.filterMap_append, List.filterMap_append ];
    simp +decide [ unwrap_wrap₁_string ];
    rw [ show unwrap_symbol₁ ∘ wrap_symbol₁ g₂.nt = Option.some from funext fun x => ?_ ] ; simp +decide [ List.filterMap ] ;
    · rfl;
    · cases x <;> rfl;
  rw [h_x_eq] at ih_x;
  exact grammar_deri_of_deri_tran ih_x ( by exact ⟨ r₁, hr₁_mem, List.filterMap unwrap_symbol₁ u, List.filterMap unwrap_symbol₁ v₁, rfl, rfl ⟩ )

/-
PROVIDED SOLUTION
Mirror of `induction_step_for_lifted_rule_from_g₁` (proved just above), with g₁↔g₂ swapped. Use `by_contra h_contra'`.

1. `obtain ⟨r₂, hr₂_mem, rfl⟩ := List.mem_map.mp rin` to get the original g₂ rule.
2. `rule_in_second_half ih_concat bef` gives `h_le : x.length ≤ u.length`.
3. Set `u₁ := List.take x.length u`, `u₂ := List.drop x.length u`.
4. Show `h_take : List.take x.length a = u₁` by rewriting bef and using that x.length ≤ u.length (so take x.length (u ++ ...) = take x.length u = u₁). Use `List.take_append_of_le_length` or just simp.
5. Show `h_drop : List.drop x.length a = u₂ ++ (List.map (wrap_symbol₂ g₁.nt) r₂.input_L) ++ [symbol.nonterminal (Sum.inl (some (Sum.inr r₂.input_N)))] ++ (List.map (wrap_symbol₂ g₁.nt) r₂.input_R) ++ v` by similar reasoning (drop x.length (u ++ ...) = drop x.length u ++ ... since x.length ≤ u.length).
6. Get `h_take_corr` from `corresponding_strings_take x.length ih_concat` and simplify with `List.take_left`.
7. Get `h_drop_corr` from `corresponding_strings_drop x.length ih_concat` and simplify with `List.drop_left`.
8. Get `h_y_eq` using `y_from_drop_filterMap ih_concat` giving `y = filterMap unwrap₂ (drop x.length a)`. Then rewrite h_drop into h_y_eq: `y = filterMap unwrap₂ u₂ ++ r₂.input_L ++ [nt r₂.input_N] ++ r₂.input_R ++ filterMap unwrap₂ v` (using filterMap_append, unwrap_wrap₂_string, and the identity `unwrap_symbol₂ ∘ wrap_symbol₂ g₁.nt = Option.some`).
9. Witness `y' = filterMap unwrap₂ u₂ ++ r₂.output_string ++ filterMap unwrap₂ v`.
10. Show grammar_transforms via `⟨r₂, hr₂_mem, filterMap unwrap₂ u₂, filterMap unwrap₂ v, h_y_eq, rfl⟩`.
11. Show new correspondence for b using corresponding_strings_append:
   (a) map wrap₁ x ~ u₁: from h_take_corr
   (b) map wrap₂ (filterMap unwrap₂ u₂) ~ u₂: corresponding_string_after_wrap_unwrap_self₂
   (c) map wrap₂ r₂.output_string ~ (wrap_grule₂ g₁.nt r₂).output_string: corresponding_strings_self
   (d) map wrap₂ (filterMap unwrap₂ v) ~ v: corresponding_string_after_wrap_unwrap_self₂
   Then b = u₁ ++ u₂ ++ wrap₂ r₂.output_string ++ v by rewriting aft and u = u₁ ++ u₂.
-/
set_option maxHeartbeats 800000 in
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
  obtain ⟨r₂, hr₂_mem, rfl⟩ := List.mem_map.mp rin;
  obtain ⟨u₁, u₂, hu₁, hu₂⟩ : ∃ u₁ u₂ : List (nst T g₁.nt g₂.nt), u = u₁ ++ u₂ ∧ u₁.length = x.length := by
    use List.take x.length u, List.drop x.length u;
    have := rule_in_second_half ih_concat bef; aesop;
  -- By definition of `wrap_grule₂`, we know that `r₂` is a rule in `g₂`.
  use (List.filterMap (@unwrap_symbol₂ T g₁.nt g₂.nt) u₂) ++ r₂.output_string ++ (List.filterMap (@unwrap_symbol₂ T g₁.nt g₂.nt) v);
  refine' ⟨ ih_x, _, _ ⟩;
  · have h_y_eq : y = List.filterMap (@unwrap_symbol₂ T g₁.nt g₂.nt) u₂ ++ r₂.input_L ++ [symbol.nonterminal r₂.input_N] ++ r₂.input_R ++ List.filterMap (@unwrap_symbol₂ T g₁.nt g₂.nt) v := by
      have h_y_eq : y = List.filterMap (@unwrap_symbol₂ T g₁.nt g₂.nt) (List.drop x.length a) := by
        apply Eq.symm; exact (by
        apply y_from_drop_filterMap ih_concat);
      rw [h_y_eq, bef, hu₁];
      simp +decide [ hu₂, List.drop_append ];
      unfold wrap_grule₂; simp +decide [ List.filterMap_append ] ;
      simp +decide [ Function.comp, List.filterMap_cons ];
      rw [ show unwrap_symbol₂ ( symbol.nonterminal ( Sum.inl ( some ( Sum.inr r₂.input_N ) ) ) ) = some ( symbol.nonterminal r₂.input_N ) from rfl ] ; simp +decide [ Function.comp, List.filterMap_append ] ;
      rw [ show unwrap_symbol₂ ∘ wrap_symbol₂ g₁.nt = Option.some from funext fun x => by cases x <;> rfl ] ; simp +decide [ List.filterMap_map ] ;
    convert grammar_deri_of_deri_tran ih_y _ using 1;
    exact ⟨ r₂, hr₂_mem, List.filterMap unwrap_symbol₂ u₂, List.filterMap unwrap_symbol₂ v, by aesop ⟩;
  · simp_all +decide [ corresponding_strings_append ];
    have h_take : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x) u₁ := by
      have := corresponding_strings_take x.length ih_concat; aesop;
    have h_drop : corresponding_strings (List.map (wrap_symbol₂ g₁.nt) (List.filterMap unwrap_symbol₂ u₂)) u₂ := by
      apply corresponding_string_after_wrap_unwrap_self₂;
      have h_drop : corresponding_strings (List.map (wrap_symbol₂ g₁.nt) y) (u₂ ++ ((wrap_grule₂ g₁.nt r₂).input_L ++ symbol.nonterminal (wrap_grule₂ g₁.nt r₂).input_N :: ((wrap_grule₂ g₁.nt r₂).input_R ++ v))) := by
        have h_drop : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y) (u₁ ++ (u₂ ++ ((wrap_grule₂ g₁.nt r₂).input_L ++ symbol.nonterminal (wrap_grule₂ g₁.nt r₂).input_N :: ((wrap_grule₂ g₁.nt r₂).input_R ++ v)))) → corresponding_strings (List.map (wrap_symbol₂ g₁.nt) y) (u₂ ++ ((wrap_grule₂ g₁.nt r₂).input_L ++ symbol.nonterminal (wrap_grule₂ g₁.nt r₂).input_N :: ((wrap_grule₂ g₁.nt r₂).input_R ++ v))) := by
          intro h_drop
          have h_drop : corresponding_strings (List.map (wrap_symbol₂ g₁.nt) y) (List.drop x.length (u₁ ++ (u₂ ++ ((wrap_grule₂ g₁.nt r₂).input_L ++ symbol.nonterminal (wrap_grule₂ g₁.nt r₂).input_N :: ((wrap_grule₂ g₁.nt r₂).input_R ++ v))))) := by
            convert corresponding_strings_drop x.length h_drop using 1
            generalize_proofs at *; (
            simp +decide [ hu₂ ])
          generalize_proofs at *; (
          convert h_drop using 1 ; simp +decide [ hu₂ ]);
        exact h_drop ‹_›;
      have := corresponding_strings_take ( List.length u₂ ) h_drop; simp_all +decide [ corresponding_strings ] ;
      use List.take u₂.length y;
      rw [ List.forall₂_iff_get ] at *;
      grind +splitIndPred
    have h_drop' : corresponding_strings (List.map (wrap_symbol₂ g₁.nt) (List.filterMap unwrap_symbol₂ v)) v := by
      apply corresponding_string_after_wrap_unwrap_self₂;
      have h_drop : corresponding_strings (List.map (wrap_symbol₂ g₁.nt) y) (u₂ ++ ((wrap_grule₂ g₁.nt r₂).input_L ++ symbol.nonterminal (wrap_grule₂ g₁.nt r₂).input_N :: ((wrap_grule₂ g₁.nt r₂).input_R ++ v))) := by
        convert corresponding_strings_drop x.length ih_concat using 1;
        · simp +decide [ hu₂ ];
        · simp +decide [ hu₂, List.drop_append ];
      have h_drop : corresponding_strings (List.map (wrap_symbol₂ g₁.nt) y) (u₂ ++ ((wrap_grule₂ g₁.nt r₂).input_L ++ symbol.nonterminal (wrap_grule₂ g₁.nt r₂).input_N :: ((wrap_grule₂ g₁.nt r₂).input_R ++ v))) → corresponding_strings (List.map (wrap_symbol₂ g₁.nt) (List.drop (u₂.length + ((wrap_grule₂ g₁.nt r₂).input_L.length + 1 + ((wrap_grule₂ g₁.nt r₂).input_R.length))) y)) v := by
        intro h_drop
        have h_drop' : corresponding_strings (List.map (wrap_symbol₂ g₁.nt) (List.drop (u₂.length + ((wrap_grule₂ g₁.nt r₂).input_L.length + 1 + ((wrap_grule₂ g₁.nt r₂).input_R.length))) y)) (List.drop (u₂.length + ((wrap_grule₂ g₁.nt r₂).input_L.length + 1 + ((wrap_grule₂ g₁.nt r₂).input_R.length))) (u₂ ++ ((wrap_grule₂ g₁.nt r₂).input_L ++ symbol.nonterminal (wrap_grule₂ g₁.nt r₂).input_N :: ((wrap_grule₂ g₁.nt r₂).input_R ++ v)))) := by
          convert corresponding_strings_drop _ h_drop using 1;
          rw [ List.map_drop ];
        convert h_drop' using 1;
        simp +decide [ add_comm, add_left_comm, add_assoc, List.drop_eq_nil_of_le ];
      exact ⟨ _, h_drop ‹_› ⟩
    have h_drop'' : corresponding_strings (List.map (wrap_symbol₂ g₁.nt) r₂.output_string) ((wrap_grule₂ g₁.nt r₂).output_string) := by
      exact corresponding_strings_self;
    exact corresponding_strings_append h_take ( corresponding_strings_append h_drop ( corresponding_strings_append h_drop'' h_drop' ) )

/-
PROVIDED SOLUTION
Cases on s: terminal t gives nt (Sum.inr (Sum.inl t)) ≠ nt (Sum.inl none), nonterminal n gives nt (Sum.inl (some (Sum.inl n))) ≠ nt (Sum.inl none). Both are straightforward by definition.
-/
private lemma no_none_in_wrapped₁ {N₁ N₂ : Type} (s : symbol T N₁) :
    wrap_symbol₁ N₂ s ≠ symbol.nonterminal (Sum.inl none) := by
  cases s <;> simp +decide [ * ];
  · exact fun h => by cases h;
  · grind +locals

/-
PROVIDED SOLUTION
Cases on s: terminal t gives nt (Sum.inr (Sum.inr t)) ≠ nt (Sum.inl none), nonterminal n gives nt (Sum.inl (some (Sum.inr n))) ≠ nt (Sum.inl none). Both are straightforward.
-/
private lemma no_none_in_wrapped₂ {N₁ N₂ : Type} (s : symbol T N₂) :
    wrap_symbol₂ N₁ s ≠ symbol.nonterminal (Sum.inl none) := by
  cases s <;> simp_all +decide [ wrap_symbol₂ ];
  grind +ring

/-
PROVIDED SOLUTION
The rule replaces nt (Sum.inr (Sum.inl t)) with terminal t in the string, at position u.length. corresponding_symbols maps (Sum.inr (Sum.inl t)) to terminal t' when t = t', so replacing one with the other preserves the correspondence.

Use corresponding_strings = List.Forall₂ corresponding_symbols. From ih_concat and bef, we have Forall₂ relation on a. For b, the only change is at position u.length where nt (Sum.inr (Sum.inl t)) becomes terminal t. By definition of corresponding_symbols, corresponding_symbols (nt (Sum.inr (Sum.inl t))) (terminal t) holds (since t = t), so the correspondence is preserved.

Concretely: split a at position u.length using corresponding_strings_take and corresponding_strings_drop. In bef, the element at position u.length is nt (Sum.inr (Sum.inl t)). In the reference string (map wrap₁ x ++ map wrap₂ y), the element at that position has corresponding_symbols with nt (Sum.inr (Sum.inl t)), and by definition of corresponding_symbols, it also has corresponding_symbols with terminal t. Then reassemble using corresponding_strings_append.
-/
private lemma induction_step_for_terminal_rule₁
    {g₁ g₂ : grammar T}
    {a b u v : List (nst T g₁.nt g₂.nt)}
    {x : List (symbol T g₁.nt)}
    {y : List (symbol T g₂.nt)}
    {t : T}
    (ht : t ∈ all_used_terminals g₁)
    (bef : a = u ++ [symbol.nonterminal (Sum.inr (Sum.inl t))] ++ v)
    (aft : b = u ++ [symbol.terminal t] ++ v)
    (ih_concat : corresponding_strings
        (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y) a) :
  corresponding_strings
    (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y) b := by
  have unfold_ih_concat : corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y) (u ++ [symbol.nonterminal (Sum.inr (Sum.inl t))] ++ v) := by
    aesop;
  have h_split : u.length < (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y).length := by
    have := corresponding_strings_length unfold_ih_concat; aesop;
  obtain ⟨l₁, l₂, hl₁, hl₂⟩ : ∃ l₁ l₂, List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y = l₁ ++ l₂ ∧ List.length l₁ = u.length ∧ corresponding_strings l₁ u ∧ corresponding_strings l₂ ([symbol.nonterminal (Sum.inr (Sum.inl t))] ++ v) := by
    obtain ⟨l₁, l₂, hl₁, hl₂⟩ : ∃ l₁ l₂, List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y = l₁ ++ l₂ ∧ List.length l₁ = u.length ∧ corresponding_strings l₁ (u ++ [symbol.nonterminal (Sum.inr (Sum.inl t))] ++ v |>.take u.length) := by
      use List.take u.length (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y), List.drop u.length (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y);
      exact ⟨ by rw [ List.take_append_drop ], by rw [ List.length_take, min_eq_left h_split.le ], by exact corresponding_strings_take _ unfold_ih_concat ⟩;
    simp_all +decide [ List.take_append ];
    exact ⟨ l₁, l₂, rfl, hl₂.1, hl₂.2, by simpa [ hl₂.1 ] using corresponding_strings_drop ( u.length ) ih_concat ⟩;
  have h_replace : corresponding_strings l₂ ([symbol.terminal t] ++ v) := by
    rcases l₂ with ( _ | ⟨ s, l₂ ⟩ ) <;> simp_all +decide [ corresponding_strings ];
    unfold corresponding_symbols at * ; aesop;
  convert corresponding_strings_append hl₂.2.1 h_replace using 1 ; aesop

/-
PROVIDED SOLUTION
Exactly symmetric to induction_step_for_terminal_rule₁ (proved just above). The rule replaces nt (Sum.inr (Sum.inr t)) with terminal t. By definition of corresponding_symbols, corresponding_symbols (nt (Sum.inr (Sum.inr t))) (terminal t) holds when t = t. Same approach: split the correspondence at position u.length, show the head element correspondence is preserved (Sum.inr (Sum.inr t) ↔ terminal t), reassemble with corresponding_strings_append.
-/
private lemma induction_step_for_terminal_rule₂
    {g₁ g₂ : grammar T}
    {a b u v : List (nst T g₁.nt g₂.nt)}
    {x : List (symbol T g₁.nt)}
    {y : List (symbol T g₂.nt)}
    {t : T}
    (ht : t ∈ all_used_terminals g₂)
    (bef : a = u ++ [symbol.nonterminal (Sum.inr (Sum.inr t))] ++ v)
    (aft : b = u ++ [symbol.terminal t] ++ v)
    (ih_concat : corresponding_strings
        (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y) a) :
  corresponding_strings
    (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y) b := by
  rw [bef] at ih_concat
  unfold corresponding_strings at *;
  rw [ List.forall₂_iff_get ] at *;
  simp_all +decide [ List.getElem_append ];
  intro i hi; specialize ih_concat; rcases ih_concat with ⟨ h₁, h₂ ⟩ ; rcases lt_trichotomy i u.length with hi' | rfl | hi' <;> simp_all +decide [ Nat.lt_succ_iff ] ;
  · simpa [ hi' ] using h₂ i ( by linarith );
  · specialize h₂ u.length ( by linarith ) ; simp_all +decide [ List.getElem_append ] ;
    unfold corresponding_symbols at * ; aesop;
  · grind +splitIndPred

/-
PROVIDED SOLUTION
Induction on the derivation `ass` using `induction ass`.

Base case (refl): x = [nt g₁.initial], y = [nt g₂.initial], grammar_deri_self for both, and corresponding_strings holds by corresponding_strings_self since map wrap₁ [nt g₁.initial] ++ map wrap₂ [nt g₂.initial] equals the starting string.

Inductive case (tail): We have v →* w₁ (by ih) and w₁ →₁ w (step). By ih, get x, y with the invariant for w₁. Extract the rule r from the step: ⟨r, r_in, u, v', bef, aft⟩.

Case split on r_in. The rules of big_grammar are:
- Initial rule (head): r.input_N = Sum.inl none, r.input_L = [], r.input_R = []. This is impossible because bef says w₁ contains [nt (Sum.inl none)], but from the invariant all symbols in w₁ are wrapped (corresponding to wrap₁ or wrap₂ outputs), and neither produces Sum.inl none (by no_none_in_wrapped₁/₂). Show this by: the reference string (map wrap₁ x ++ map wrap₂ y) has length = w₁.length (from corresponding_strings_length). At position u.length, w₁[u.length] = nt (Sum.inl none). The reference at that position is either wrap₁ (x[...]) or wrap₂ (y[...]). Use corresponding_strings_nth_le to get corresponding_symbols (ref[u.length]) (nt (Sum.inl none)). But ref[u.length] is some wrap₁ or wrap₂ output, and none of them can have corresponding_symbols with nt (Sum.inl none). More directly: from List.Forall₂, every element of w₁ corresponds to an element of the reference string. Show that nt (Sum.inl none) cannot correspond to any wrap₁ or wrap₂ symbol.

- Rules from g₁ (in map wrap_grule₁): use induction_step_for_lifted_rule_from_g₁ to get new x', keep y.
- Rules from g₂ (in map wrap_grule₂): use induction_step_for_lifted_rule_from_g₂ to get new y', keep x.
- Terminal rules from g₁ (in rules_for_terminals₁): use induction_step_for_terminal_rule₁, keep same x, y.
- Terminal rules from g₂ (in rules_for_terminals₂): use induction_step_for_terminal_rule₂, keep same x, y.

For the membership case analysis: `List.mem_cons` gives initial rule ∨ rest. Then `List.mem_append` splits rest into (g₁_rules ++ g₂_rules) and (terminal_rules₁ ++ terminal_rules₂), etc.
-/
set_option maxHeartbeats 800000 in
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
  have h_ind : ∀ {w : List (nst T g₁.nt g₂.nt)}, grammar_derives (big_grammar g₁ g₂) [symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))), symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))] w →
    ∃ x y : List (symbol T g₁.nt), ∃ y' : List (symbol T g₂.nt),
      (grammar_derives g₁ [symbol.nonterminal g₁.initial] x ∧
        grammar_derives g₂ [symbol.nonterminal g₂.initial] y' ∧
          corresponding_strings
            (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y' : List (nst T g₁.nt g₂.nt))
            w) := by
              intros w hw; induction' hw with w₁ w₂ hw₁ hw₂ ih₁ ih₂; simp_all +decide [ List.map_append ] ;
              · exact ⟨ [ symbol.nonterminal g₁.initial ], by tauto, [ symbol.nonterminal g₂.initial ], by tauto, by tauto ⟩;
              · obtain ⟨ x, y, y', hx, hy, hxy ⟩ := ih₁
                obtain ⟨ r, hr, u, v, bef, aft ⟩ := hw₂
                by_cases hr₁ : r ∈ List.map (wrap_grule₁ g₂.nt) g₁.rules ∨ r ∈ List.map (wrap_grule₂ g₁.nt) g₂.rules ∨ r ∈ rules_for_terminals₁ g₂.nt g₁ ∨ r ∈ rules_for_terminals₂ g₁.nt g₂ <;> simp_all +decide [ List.mem_append, List.mem_map ];
                · rcases hr₁ with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ | hr₁ | hr₁ ) <;> simp_all +decide [ big_grammar ] ;
                  · have := induction_step_for_lifted_rule_from_g₁ ( show wrap_grule₁ g₂.nt a ∈ List.map ( wrap_grule₁ g₂.nt ) g₁.rules from List.mem_map.mpr ⟨ a, ha, rfl ⟩ ) ( by aesop ) ( by aesop ) hx hy hxy; aesop;
                  · obtain ⟨ y'', hy'', hxy'' ⟩ := induction_step_for_lifted_rule_from_g₂ ( List.mem_map.mpr ⟨ a, ha, rfl ⟩ ) ( by aesop ) ( by aesop ) hx hy hxy; use x, hx, y''; aesop;
                  · unfold rules_for_terminals₁ at hr₁; simp_all +decide [ List.mem_map ] ;
                    obtain ⟨ a, ha, rfl ⟩ := hr₁; exact ⟨ x, hx, y', hy, by simpa using induction_step_for_terminal_rule₁ ha ( by aesop ) ( by aesop ) hxy ⟩ ;
                  · unfold rules_for_terminals₂ at hr₁; simp_all +decide [ List.mem_map ] ;
                    obtain ⟨ a, ha, rfl ⟩ := hr₁; exact ⟨ x, hx, y', hy, by simpa using induction_step_for_terminal_rule₂ ha ( by aesop ) ( by aesop ) hxy ⟩ ;
                · unfold big_grammar at hr; simp_all +decide [ List.mem_append, List.mem_map ] ;
                  rcases hr with ( rfl | ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ wrap_grule₁, wrap_grule₂ ];
                  · have := hxy; ( have := List.forall₂_iff_get.mp this; simp_all +decide [ List.get ] ; );
                    have := this.2 ( u.length ) ( by linarith ) ( by linarith ) ; simp_all +decide [ List.getElem_append ] ;
                    split_ifs at this <;> simp_all +decide [ wrap_symbol₁, wrap_symbol₂ ] ;
                    · cases h : x[u.length] <;> simp_all +decide [ corresponding_symbols ];
                    · cases h : y'[u.length - x.length] <;> simp_all +decide [ corresponding_symbols ];
                  · exact False.elim <| hr₁.1 a ha rfl rfl rfl rfl;
                  · exact False.elim <| hr₁.2.1 a ha rfl rfl rfl rfl;
  exact Exists.elim ( h_ind ass ) fun x hx => Exists.elim hx fun y hy => Exists.elim hy fun z hz => ⟨ x, z, hz.1, hz.2.1, hz.2.2 ⟩

/-
PROVIDED SOLUTION
1. Unfold grammar_language at ass to get: grammar_derives (big_grammar g₁ g₂) [nt (big_grammar g₁ g₂).initial] (map terminal w), where (big_grammar g₁ g₂).initial = Sum.inl none.

2. The first step of any derivation from [nt (Sum.inl none)] must use the initial rule, giving [nt (Sum.inl (some (Sum.inl g₁.initial))), nt (Sum.inl (some (Sum.inr g₂.initial)))]. Use first_transformation or show this directly.

3. Apply big_induction to the remaining derivation to get x, y with grammar_derives g₁ ... x, grammar_derives g₂ ... y, and corresponding_strings (map wrap₁ x ++ map wrap₂ y) (map terminal w).

4. Since the final string is all terminals (map terminal w), and corresponding_strings relates each wrapped symbol to the terminal, unwrap to get that x = map terminal w₁ and y = map terminal w₂ for some w₁, w₂ with w = w₁ ++ w₂.

5. Use x_from_take_filterMap and y_from_drop_filterMap, plus the fact that filterMap unwrap₁ (map terminal w) = w (since unwrap_symbol₁ (terminal t) = some (terminal t)) to extract w₁ and w₂.

6. Conclude w₁ ∈ grammar_language g₁ and w₂ ∈ grammar_language g₂, so w ∈ L(g₁) * L(g₂).

Actually, a cleaner approach:
- From ass, we get grammar_derives (big_grammar g₁ g₂) [nt initial] (map terminal w).
- The initial step gives grammar_transforms to [nt (Sum.inl (some (Sum.inl g₁.initial))), nt (Sum.inl (some (Sum.inr g₂.initial)))].
- We need to extract this. Use the fact that grammar_derives has either refl or tail cases. In the refl case, [nt initial] = map terminal w is impossible. In the tail case, the first step must use the initial rule (the only rule with input_N = Sum.inl none).
- Then apply big_induction to get x, y with the invariant.
- Since the final word is map terminal w, corresponding_strings (map wrap₁ x ++ map wrap₂ y) (map terminal w).
- For each position, corresponding_symbols (wrap_X s) (terminal t) implies t equals the terminal embedded in s, which means s was terminal t itself.
- So x = map terminal w₁, y = map terminal w₂ for appropriate w₁, w₂ with w = w₁ ++ w₂.

Actually simplest: extract the derivation from the initial state, show it goes through the two-symbol state, then apply big_induction. The result gives x, y plus correspondence with map terminal w. Use the correspondence to split w into w₁ ++ w₂ and conclude.
-/
set_option maxHeartbeats 800000 in
lemma in_concatenated_of_in_big
    {g₁ g₂ : grammar T}
    {w : List T}
    (ass : w ∈ grammar_language (big_grammar g₁ g₂)) :
  w ∈ grammar_language g₁ * grammar_language g₂ :=
by
  -- Apply `big_induction` to obtain the existence of `x` and `y`.
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y, grammar_derives g₁ [symbol.nonterminal g₁.initial] x ∧ grammar_derives g₂ [symbol.nonterminal g₂.initial] y ∧ corresponding_strings (List.map (wrap_symbol₁ g₂.nt) x ++ List.map (wrap_symbol₂ g₁.nt) y) (List.map symbol.terminal w) := by
    -- Apply the big_induction lemma to the derivation from the big grammar's initial state to the map of terminals w, to obtain x and y.
    obtain ⟨w', hw', hw'_eq⟩ : ∃ w', grammar_derives (big_grammar g₁ g₂) [symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))), symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))] w' ∧ w' = List.map (symbol.terminal) w := by
      obtain ⟨w', hw'⟩ : ∃ w', grammar_derives (big_grammar g₁ g₂) [symbol.nonterminal (big_grammar g₁ g₂).initial] w' ∧ w' = List.map (symbol.terminal) w := by
        exact ⟨ _, ass, rfl ⟩;
      have := hw'.left;
      obtain ⟨w'', hw''⟩ : ∃ w'', grammar_transforms (big_grammar g₁ g₂) [symbol.nonterminal (big_grammar g₁ g₂).initial] w'' ∧ grammar_derives (big_grammar g₁ g₂) w'' w' := by
        have h_induction_step : ∀ {u v : List (symbol T (big_grammar g₁ g₂).nt)}, grammar_derives (big_grammar g₁ g₂) u v → u ≠ v → ∃ w, grammar_transforms (big_grammar g₁ g₂) u w ∧ grammar_derives (big_grammar g₁ g₂) w v := by
          intros u v huv huv_ne;
          have := huv;
          cases this ; tauto;
          grind +suggestions;
        apply h_induction_step this;
        cases w <;> simp +decide [ hw'.2 ] at hw' ⊢;
      have h_initial_rule : ∀ r ∈ (big_grammar g₁ g₂).rules, r.input_N = (big_grammar g₁ g₂).initial → r.input_L = [] ∧ r.input_R = [] ∧ r.output_string = [symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))), symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))] := by
        grind +locals;
      obtain ⟨r, hr⟩ := hw''.left;
      obtain ⟨ u, v, h₁, h₂ ⟩ := hr.2;
      rcases u with ( _ | ⟨ u, u ⟩ ) <;> simp +decide at h₁ ⊢;
      rcases r : r.input_L with ( _ | ⟨ a, l ⟩ ) <;> simp +decide [ r ] at h₁ ⊢;
      grind +ring;
    have := big_induction hw';
    grind;
  -- By definition of `grammar_language`, we know that there exist `w₁` and `w₂` such that `w = w₁ ++ w₂`, `x.map unwrap_symbol₁ = w₁`, and `y.map unwrap_symbol₂ = w₂`.
  obtain ⟨w₁, w₂, hw₁, hw₂, hw⟩ : ∃ w₁ w₂ : List T, w = w₁ ++ w₂ ∧ x = List.map symbol.terminal w₁ ∧ y = List.map symbol.terminal w₂ := by
    -- By definition of `corresponding_strings`, we know that `x.map unwrap_symbol₁` and `y.map unwrap_symbol₂` are lists of terminals.
    have hx_terminals : ∀ s ∈ x, ∃ t : T, s = symbol.terminal t := by
      intro s hs
      obtain ⟨t, ht⟩ : ∃ t : T, corresponding_symbols (wrap_symbol₁ g₂.nt s) (symbol.terminal t) := by
        obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hs;
        have := List.forall₂_iff_get.mp hxy;
        simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ];
        exact ⟨ w[i], by simpa [ hi, List.getElem_append, i.2 ] using this.2 i ( by linarith [ Fin.is_lt i ] ) ( by linarith [ Fin.is_lt i ] ) ⟩;
      cases s <;> aesop
    have hy_terminals : ∀ s ∈ y, ∃ t : T, s = symbol.terminal t := by
      intro s hs; have := hxy; simp_all +decide [ corresponding_strings ] ;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hs; specialize hxy; simp_all +decide [ List.forall₂_iff_get ] ;
      specialize hxy ; have := hxy.2 ( x.length + i ) ( by linarith [ Fin.is_lt i ] ) ( by linarith [ Fin.is_lt i ] ) ; simp_all +decide [ List.getElem_append ] ;
      cases s <;> tauto;
    -- Since `x` and `y` are lists of terminals, we can extract the lists of terminals `w₁` and `w₂` such that `x = List.map symbol.terminal w₁` and `y = List.map symbol.terminal w₂`.
    obtain ⟨w₁, hw₁⟩ : ∃ w₁ : List T, x = List.map symbol.terminal w₁ := by
      have hx_terminals : ∀ {l : List (symbol T g₁.nt)}, (∀ s ∈ l, ∃ t : T, s = symbol.terminal t) → ∃ w : List T, l = List.map symbol.terminal w := by
        intros l hl; induction' l with s l ih <;> simp_all +decide [ List.map ] ;
        rcases hl.1 with ⟨ t, rfl ⟩ ; obtain ⟨ w, rfl ⟩ := ih; exact ⟨ t :: w, by simp +decide ⟩ ;
      exact hx_terminals ‹_›
    obtain ⟨w₂, hw₂⟩ : ∃ w₂ : List T, y = List.map symbol.terminal w₂ := by
      have hy_terminals : ∀ {l : List (symbol T g₂.nt)}, (∀ s ∈ l, ∃ t : T, s = symbol.terminal t) → ∃ w : List T, l = List.map symbol.terminal w := by
        intros l hl; induction' l with s l ih <;> simp_all +decide [ List.map ] ;
        rcases hl.1 with ⟨ t, rfl ⟩ ; obtain ⟨ w, rfl ⟩ := ih; exact ⟨ t :: w, by simp +decide ⟩ ;
      generalize_proofs at *; (
      exact hy_terminals ‹_›)
    use w₁, w₂;
    have := hxy; simp_all +decide [ corresponding_strings ] ;
    have h_eq : ∀ {l₁ l₂ : List T} {l₃ : List T}, List.Forall₂ (fun a c => corresponding_symbols a (symbol.terminal c)) (List.map (wrap_symbol₁ g₂.nt ∘ symbol.terminal) l₁ ++ List.map (wrap_symbol₂ g₁.nt ∘ symbol.terminal) l₂) l₃ → l₃ = l₁ ++ l₂ := by
      intros l₁ l₂ l₃ h; induction' l₁ with a l₁ ih generalizing l₂ l₃ <;> induction' l₂ with b l₂ ih' generalizing l₃ <;> simp_all +decide [ List.Forall₂ ] ;
      · rcases l₃ with ( _ | ⟨ c, l₃ ⟩ ) <;> simp_all +decide [ List.Forall₂ ];
        exact ⟨ by cases h.1; tauto, ih' h.2 ⟩;
      · rcases l₃ with ( _ | ⟨ b, l₃ ⟩ ) <;> simp_all +decide [ List.Forall₂ ];
        exact ⟨ by cases h.1; tauto, by simpa using ih ( show List.Forall₂ ( fun a c => corresponding_symbols a ( symbol.terminal c ) ) ( List.map ( wrap_symbol₁ g₂.nt ∘ symbol.terminal ) l₁ ++ List.map ( wrap_symbol₂ g₁.nt ∘ symbol.terminal ) [ ] ) l₃ from by simpa using h.2 ) ⟩;
      · rcases l₃ with ( _ | ⟨ c, l₃ ⟩ ) <;> simp_all +decide [ List.Forall₂ ];
        cases h.1 ; aesop ( simp_config := { singlePass := true } ) ;
    exact h_eq ‹_› ▸ rfl;
  exact ⟨ w₁, by aesop, w₂, by aesop, by aesop ⟩

end very_complicated

end hard_direction

/-
PROBLEM
The class of recursively-enumerable languages is closed under concatenation.

PROVIDED SOLUTION
From the hypotheses, extract g₁ with grammar_language g₁ = L₁ and g₂ with grammar_language g₂ = L₂. Witness big_grammar g₁ g₂. Show grammar_language (big_grammar g₁ g₂) = L₁ * L₂ using Set.Subset.antisymm with the two directions:
- Forward: use in_concatenated_of_in_big (rewriting L₁ and L₂)
- Backward: use in_big_of_in_concatenated (rewriting L₁ and L₂)
-/
theorem RE_of_RE_c_RE (L₁ : Language T) (L₂ : Language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ * L₂)   :=
by
  intro h
  obtain ⟨g₁, hg₁⟩ := h.left
  obtain ⟨g₂, hg₂⟩ := h.right
  use big_grammar g₁ g₂
  ext w
  apply Iff.intro;
  · convert in_concatenated_of_in_big ; aesop;
    exact hg₂.symm;
  · convert in_big_of_in_concatenated using 1;
    rw [ ← hg₁, ← hg₂ ]

/-- The class of recursively enumerable languages is closed under concatenation. -/
theorem RE_closedUnderConcatenation : ClosedUnderConcatenation (RE : Set (Language T)) :=
  fun L₁ L₂ h₁ h₂ => RE_of_RE_c_RE L₁ L₂ ⟨h₁, h₂⟩
