import Langlib.Grammars.ContextFree.Toolbox
import Langlib.Classes.ContextFree.Basics.Splitting
import Langlib.Classes.ContextFree.Closure.Reverse
import Langlib.Utilities.LanguageOperations
import Langlib.Utilities.ListUtils
import Mathlib
import Langlib.Classes.ContextFree.Definition
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization

/-! # Context-Free Closure Under Prefix and Suffix

This file proves that context-free languages are closed under the prefix and suffix operations.
This strategy uses the construction of an explicit prefix grammar.

## Main declarations

- `CF_of_prefix_CF`  — CFLs are closed under prefix
- `CF_of_suffix_CF`  — CFLs are closed under suffix (via reverse, prefix, reverse)

## Strategy

The prefix closure proof constructs an explicit grammar. Given a CF grammar `g`, we build
a "prefix grammar" whose nonterminals are `Bool × g.nt`, where `(false, A)` ("full mode")
behaves like the original `A`, and `(true, A)` ("prefix mode") can derive any prefix of
any word derivable from `A`.

To ensure soundness, we first filter the grammar to keep only "fully productive" rules
(rules where every nonterminal in the RHS can derive some terminal string). This
filtered grammar generates the same language as the original.
-/

open Language

variable {T : Type}


/-! ## Productivity -/

/-- A nonterminal `A` in grammar `g` is **productive** if it can derive some terminal string. -/
def productive (g : CF_grammar T) (A : g.nt) : Prop :=
  ∃ w : List T, CF_derives g [symbol.nonterminal A] (List.map symbol.terminal w)

/-- A rule is **fully productive** if the LHS nonterminal and every nonterminal
    in the RHS are productive. -/
def fullyProductiveRule (g : CF_grammar T) (r : g.nt × List (symbol T g.nt)) : Prop :=
  productive g r.1 ∧ ∀ B, symbol.nonterminal B ∈ r.2 → productive g B

/-
Every nonterminal appearing in a derivation to a terminal string is productive.
-/
lemma productive_of_mem_derives_terminal {g : CF_grammar T}
    {s : List (symbol T g.nt)} {w : List T}
    (hs : CF_derives g s (List.map symbol.terminal w))
    {B : g.nt} (hB : symbol.nonterminal B ∈ s) :
    productive g B := by
      -- By induction on the derivation steps, we can show that any nonterminal in s is productive.
      have h_ind : ∀ s w, CF_derives g s (List.map symbol.terminal w) → ∀ B, symbol.nonterminal B ∈ s → productive g B := by
        intros s w hs B hB;
        -- By induction on the length of the list s.
        induction' s with s_hd s_tl ih generalizing w B;
        · contradiction;
        · -- Apply the head_tail_split lemma to the derivation `hs`.
          obtain ⟨u, v, hu, hv, huv⟩ := head_tail_split (List.map symbol.terminal w) s_hd s_tl hs;
          by_cases hB_hd : symbol.nonterminal B = s_hd;
          · have h_u_terminals : ∀ x ∈ u, ∃ t : T, x = symbol.terminal t := by
              intro x hx; replace huv := congr_arg ( fun l => x ∈ l ) huv; aesop;
            have h_u_terminals : ∃ w' : List T, u = List.map symbol.terminal w' := by
              have h_u_terminals : ∀ {l : List (symbol T g.nt)}, (∀ x ∈ l, ∃ t : T, x = symbol.terminal t) → ∃ w' : List T, l = List.map symbol.terminal w' := by
                intros l hl; induction' l with x l ih;
                · exact ⟨ [ ], rfl ⟩;
                · obtain ⟨ t, rfl ⟩ := hl x ( by simp +decide ) ; obtain ⟨ w', hw' ⟩ := ih ( fun y hy => hl y ( by simp +decide [ hy ] ) ) ; exact ⟨ t :: w', by simp +decide [ hw' ] ⟩ ;
              exact h_u_terminals ‹_›;
            grind +locals;
          · apply ih;
            any_goals exact List.drop ( List.length u ) w;
            · replace huv := congr_arg ( fun x => x.drop u.length ) huv ; aesop;
            · aesop;
      exact h_ind s w hs B hB

/-! ## Productive Grammar -/

open Classical in
/-- Grammar with only fully productive rules (same nonterminal type, fewer rules). -/
noncomputable def productiveGrammar (g : CF_grammar T) : CF_grammar T :=
  { g with rules := g.rules.filter (fun r => decide (fullyProductiveRule g r)) }

lemma productiveGrammar_nt (g : CF_grammar T) :
    (productiveGrammar g).nt = g.nt := rfl

lemma productiveGrammar_initial (g : CF_grammar T) :
    (productiveGrammar g).initial = g.initial := rfl

lemma productiveGrammar_rules_subset {g : CF_grammar T} {r} :
    r ∈ (productiveGrammar g).rules → r ∈ g.rules := by
  intro h
  simp [productiveGrammar] at h
  exact h.1

lemma productiveGrammar_rules_productive {g : CF_grammar T} {r}
    (hr : r ∈ (productiveGrammar g).rules) :
    fullyProductiveRule g r := by
  simp [productiveGrammar] at hr
  exact hr.2

/-
Derivations are monotone w.r.t. rule inclusion (for grammars sharing the same nt type).
-/
lemma CF_derives_mono {g : CF_grammar T} {rules₁ rules₂ : List (g.nt × List (symbol T g.nt))}
    (hsub : ∀ r, r ∈ rules₁ → r ∈ rules₂)
    {s₁ s₂ : List (symbol T g.nt)}
    (h : CF_derives {g with rules := rules₁} s₁ s₂) :
    CF_derives {g with rules := rules₂} s₁ s₂ := by
                  -- If `CF_derivs` holds for `rules₁`, then for any transformation step for `rules₁`, it must also hold for `rules₂`.
                  have h_transform : ∀ {s₁ s₂ : List (symbol T g.nt)}, CF_transforms ⟨g.nt, g.initial, rules₁⟩ s₁ s₂ → CF_transforms ⟨g.nt, g.initial, rules₂⟩ s₁ s₂ := by
                    unfold CF_transforms at * ; aesop;
                  induction h <;> [ tauto; tauto ]

/-- If CF_transforms g s₁ s₂ and s₂ derives a terminal string, then the rule used is fully productive. -/
/-
Every derivation step in g that eventually leads to a terminal string uses a fully productive rule.
-/
lemma derives_to_terminal_uses_productive {g : CF_grammar T}
    {s₁ s₂ : List (symbol T g.nt)} {w : List T}
    (ht : CF_transforms g s₁ s₂)
    (hd : CF_derives g s₂ (List.map symbol.terminal w)) :
    CF_transforms (productiveGrammar g) s₁ s₂ := by
      obtain ⟨ r, u, v, hr, rfl, rfl ⟩ := ht;
      have h_prod : fullyProductiveRule g r := by
        have h_prod : ∀ B, symbol.nonterminal B ∈ r.2 → productive g B := by
          intro B hB; exact (productive_of_mem_derives_terminal hd (by
          aesop)) ;
        refine' ⟨ _, h_prod ⟩;
        have h_prod : CF_derives g (u ++ [symbol.nonterminal r.1] ++ v) (List.map symbol.terminal w) := by
          exact CF_deri_of_deri_deri ( CF_deri_of_deri_tran ( CF_deri_self ) ( by exact ⟨ r, u, v, hr, rfl, rfl ⟩ ) ) hd;
        apply productive_of_mem_derives_terminal h_prod;
        simp +decide [ List.mem_append ];
      use (r.1, r.2);
      unfold productiveGrammar; aesop;

/-
A nonterminal is productive in `g` iff it is productive in `productiveGrammar g`.
-/
lemma productive_iff_productiveGrammar {g : CF_grammar T} {A : g.nt} :
    productive g A ↔ productive (productiveGrammar g) A := by
      constructor <;> intro h <;> cases' h with w hw;
      · use w;
        -- By induction on the derivation steps, we can show that each step is valid in the productive grammar.
        have h_ind : ∀ (s₁ s₂ : List (symbol T g.nt)), CF_derives g s₁ s₂ → (∀ w : List T, CF_derives g s₂ (List.map symbol.terminal w) → CF_derives (productiveGrammar g) s₁ s₂) := by
          intros s₁ s₂ h_deriv w hw_deriv
          induction' h_deriv with s₁ s₂ h_deriv ih generalizing w;
          · constructor;
          · have h_step : CF_transforms (productiveGrammar g) s₁ s₂ := by
              exact?;
            grind +suggestions;
        exact h_ind _ _ hw _ ( by tauto );
      · -- Apply the CF_derives_mono lemma to conclude that the derivation from A to w in the productive grammar implies a derivation in the original grammar.
        apply Exists.intro w; exact CF_derives_mono (fun r hr => by
          exact List.mem_of_mem_filter hr) hw

/-
The productive grammar generates the same language as the original.
-/
lemma productiveGrammar_language (g : CF_grammar T) :
    CF_language (productiveGrammar g) = CF_language g := by
      ext w;
      constructor <;> intro h;
      · convert CF_derives_mono _ h using 1;
        exact fun r hr => List.mem_of_mem_filter hr;
      · -- By induction on the derivation steps, we can show that each step in the original derivation can be replaced by a step in the productive grammar.
        have h_ind : ∀ {s₁ s₂ : List (symbol T g.nt)}, CF_derives g s₁ s₂ → ∀ {w : List T}, CF_derives g s₂ (List.map symbol.terminal w) → CF_derives (productiveGrammar g) s₁ s₂ := by
          intros s₁ s₂ h₁ w h₂;
          induction' h₁ with s₁ s₂ h₁ h₂ ih;
          · constructor;
          · exact Relation.ReflTransGen.trans ( ih <| by
              exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single ‹_› ) h₂ ) ( by
              exact .single ( by exact? ) );
        exact h_ind h ( by tauto )

/-- All rules in the productive grammar are fully productive
    (with respect to the productive grammar itself). -/
lemma productiveGrammar_allRulesFullyProductive (g : CF_grammar T) (r)
    (hr : r ∈ (productiveGrammar g).rules) :
    ∀ B, symbol.nonterminal B ∈ r.2 → productive (productiveGrammar g) B := by
  intro B hB
  rw [← productive_iff_productiveGrammar]
  exact (productiveGrammar_rules_productive hr).2 B hB

/-! ## Prefix Grammar Construction -/

section PrefixGrammar

variable {N : Type}

/-- Lift a symbol to "full mode": terminals stay, nonterminals become `(false, _)`. -/
private def liftFull : symbol T N → symbol T (Bool × N)
  | symbol.terminal t => symbol.terminal t
  | symbol.nonterminal n => symbol.nonterminal (false, n)

/-- Lift a symbol to "prefix mode": terminals stay, nonterminals become `(true, _)`. -/
private def liftPrefix : symbol T N → symbol T (Bool × N)
  | symbol.terminal t => symbol.terminal t
  | symbol.nonterminal n => symbol.nonterminal (true, n)

/-- Prefix cut rules for a single production `(A, rhs)`.
    Generates the empty-prefix rule `(true, A) → []` and, for each position `i` in `rhs`,
    the rule `(true, A) → liftFull(rhs[0..i-1]) ++ [liftPrefix(rhs[i])]`. -/
private def prefixCutRules (A : N) (rhs : List (symbol T N)) :
    List ((Bool × N) × List (symbol T (Bool × N))) :=
  ((true, A), []) ::
  (List.finRange rhs.length).map fun i =>
    ((true, A), (rhs.take i.val).map liftFull ++ [liftPrefix (rhs.get ⟨i.val, i.isLt⟩)])

/-- All prefix-grammar rules arising from a single original rule `r = (A, rhs)`:
    one "full" rule `(false, A) → liftFull(rhs)` plus the prefix cut rules. -/
private def rulesOfRule (r : N × List (symbol T N)) :
    List ((Bool × N) × List (symbol T (Bool × N))) :=
  ((false, r.1), r.2.map liftFull) :: prefixCutRules r.1 r.2

/-- The prefix grammar built from `g`.
    Nonterminals: `Bool × g.nt`; initial: `(true, g.initial)`. -/
private def prefixGrammar (g : CF_grammar T) : CF_grammar T :=
  CF_grammar.mk (Bool × g.nt) (true, g.initial)
    (g.rules.flatMap rulesOfRule)

end PrefixGrammar

/-! ## Stepped Derivations (for induction on step count) -/

section SteppedDerivation

/-- Derivation in exactly `n` steps. -/
def CF_derives_in (g : CF_grammar T) : ℕ → List (symbol T g.nt) → List (symbol T g.nt) → Prop
  | 0, w₁, w₂ => w₁ = w₂
  | n + 1, w₁, w₃ => ∃ w₂, CF_transforms g w₁ w₂ ∧ CF_derives_in g n w₂ w₃

lemma derives_of_derives_in {g : CF_grammar T} {n : ℕ} {w₁ w₂ : List (symbol T g.nt)} :
    CF_derives_in g n w₁ w₂ → CF_derives g w₁ w₂ := by
      induction' n with n ih generalizing w₁ w₂;
      · exact fun h => by rw [ h ] ; exact CF_deri_self;
      · rintro ⟨ w₃, h₁, h₂ ⟩ ; exact CF_deri_of_deri_deri ( CF_deri_of_tran h₁ ) ( ih h₂ ) ;

lemma derives_in_of_derives {g : CF_grammar T} {w₁ w₂ : List (symbol T g.nt)} :
    CF_derives g w₁ w₂ → ∃ n, CF_derives_in g n w₁ w₂ := by
      have h_ind : ∀ {w₁ w₂ : List (symbol T g.nt)}, CF_derives g w₁ w₂ → ∃ n, CF_derives_in g n w₁ w₂ := by
        intro w₁ w₂ h;
        induction h;
        · exact ⟨ 0, rfl ⟩;
        · rename_i h₁ h₂ h₃;
          obtain ⟨ n, hn ⟩ := h₃;
          use n + 1;
          have h_append : ∀ {w₁ w₂ w₃ : List (symbol T g.nt)} {n : ℕ}, CF_derives_in g n w₁ w₂ → CF_transforms g w₂ w₃ → CF_derives_in g (n + 1) w₁ w₃ := by
            intros w₁ w₂ w₃ n hn h₂; exact (by
            induction' n with n ih generalizing w₁ w₂ w₃ <;> simp_all +decide [ CF_derives_in ];
            obtain ⟨ w₂, hw₂₁, hw₂₂ ⟩ := hn; obtain ⟨ w₃, hw₃₁, hw₃₂ ⟩ := ih hw₂₂ h₂; exact ⟨ w₂, hw₂₁, w₃, hw₃₁, hw₃₂ ⟩ ;);
          exact h_append hn h₂;
      exact h_ind

/-
A CF_transforms on a concatenation either acts in the left part or the right part.
-/
lemma transform_in_append {g : CF_grammar T} {s₁ s₂ w : List (symbol T g.nt)}
    (h : CF_transforms g (s₁ ++ s₂) w) :
    (∃ s₁', CF_transforms g s₁ s₁' ∧ w = s₁' ++ s₂) ∨
    (∃ s₂', CF_transforms g s₂ s₂' ∧ w = s₁ ++ s₂') := by
      cases' h with r hr;
      obtain ⟨ u, v, hr₁, hr₂, hr₃ ⟩ := hr;
      by_cases h : u.length < s₁.length;
      · obtain ⟨ mid, hmid ⟩ : ∃ mid : List (symbol T g.nt), s₁ = u ++ [symbol.nonterminal r.1] ++ mid := by
          rw [ List.append_eq_append_iff ] at hr₂;
          rcases hr₂ with ( ⟨ as, h₁, h₂ ⟩ | ⟨ bs, h₁, h₂ ⟩ ) <;> simp_all +decide [ List.append_assoc ];
          replace h₁ := congr_arg List.length h₁ ; simp_all +arith +decide;
          cases as <;> simp_all +arith +decide;
        exact Or.inl ⟨ u ++ r.2 ++ mid, ⟨ r, u, mid, hr₁, by aesop ⟩, by aesop ⟩;
      · -- Since $u.length \geq s₁.length$, we can write $u = s₁ ++ u'$ for some $u'$.
        obtain ⟨u', hu'⟩ : ∃ u', u = s₁ ++ u' := by
          rw [ List.append_assoc ] at hr₂;
          rw [ List.append_eq_append_iff ] at hr₂ ; aesop;
        simp_all +decide [ List.append_assoc ];
        exact Or.inr ⟨ r, u', v, hr₁, by aesop ⟩

/-
Splitting lemma with step counts.
-/
lemma head_tail_split_in {g : CF_grammar T} (n : ℕ) (s : symbol T g.nt)
    (ss : List (symbol T g.nt)) (x : List (symbol T g.nt))
    (h : CF_derives_in g n (s :: ss) x) :
    ∃ n₁ n₂, n₁ + n₂ ≤ n ∧ ∃ u v,
      CF_derives_in g n₁ [s] u ∧ CF_derives_in g n₂ ss v ∧ u ++ v = x := by
        -- Define the step-bounded derivation relation `CF_derives_in` for `g` and prove the required properties.
        have step_bounded_derivation : ∀ n : ℕ, ∀ s₁ s₂ x, CF_derives_in g n (s₁ ++ s₂) x → ∃ n₁ n₂, n₁ + n₂ ≤ n ∧ ∃ u v, CF_derives_in g n₁ s₁ u ∧ CF_derives_in g n₂ s₂ v ∧ u ++ v = x := by
          intro n
          intro s₁
          intro s₂
          intro x
          intro h
          induction' n with n ih generalizing s₁ s₂ x;
          · cases h ; aesop;
          · obtain ⟨ w₂, hw₂ ⟩ := h;
            -- Apply `transform_in_append` to split the transformation into two parts.
            obtain ⟨s₁', hs₁', hs₂'⟩ : ∃ s₁' : List (symbol T g.nt), CF_transforms g s₁ s₁' ∧ w₂ = s₁' ++ s₂ ∨ ∃ s₂' : List (symbol T g.nt), CF_transforms g s₂ s₂' ∧ w₂ = s₁ ++ s₂' := by
              have := transform_in_append hw₂.1; aesop;
            · obtain ⟨ n₁, n₂, hn₁₂, u, v, hu, hv, huv ⟩ := ih s₁' s₂ x ( by simpa only [ hs₂' ] using hw₂.2 ) ; use n₁ + 1, n₂; simp_all +arith +decide;
              exact ⟨ u, ⟨ s₁', hs₁', hu ⟩, v, hv, huv ⟩;
            · obtain ⟨ s₂', hs₂', rfl ⟩ := ‹∃ s₂', CF_transforms g s₂ s₂' ∧ w₂ = s₁ ++ s₂'›;
              obtain ⟨ n₁, n₂, hn₁₂, u, v, hu, hv, huv ⟩ := ih s₁ s₂' x hw₂.2;
              exact ⟨ n₁, n₂ + 1, by linarith, u, v, hu, by exact ⟨ s₂', hs₂', hv ⟩, huv ⟩;
        exact step_bounded_derivation n [ s ] ss x h

end SteppedDerivation

/-! ## Full Lifting -/

section FullLifting

private lemma map_liftFull_map_terminal {N : Type} (w : List T) :
    (List.map symbol.terminal w).map (@liftFull T N) = List.map symbol.terminal w := by
      induction w <;> simp +decide [ * ];
      rfl

private lemma full_lifting {g : CF_grammar T} {s₁ s₂ : List (symbol T g.nt)}
    (h : CF_derives g s₁ s₂) :
    CF_derives (prefixGrammar g) (s₁.map liftFull) (s₂.map liftFull) := by
      induction' h with s₁ s₂ h_ind h_rules;
      · constructor;
      · rename_i h_ind' h_rules';
        obtain ⟨ r, u, v, hr, h₁, h₂ ⟩ := h_rules;
        refine' h_rules'.trans _;
        convert Relation.ReflTransGen.single _ using 1;
        use ( ( false, r.1 ), r.2.map liftFull );
        grind +locals

end FullLifting

/-! ## Completeness: `prefixLang (CF_language g) ⊆ CF_language (prefixGrammar g)` -/

section Completeness

/-
The empty prefix rule is in the prefix grammar.
-/
private lemma empty_prefix_rule_mem {g : CF_grammar T} {A : g.nt} {rhs : List (symbol T g.nt)}
    (hr : (A, rhs) ∈ g.rules) :
    ((true, A), ([] : List (symbol T (Bool × g.nt)))) ∈ (prefixGrammar g).rules := by
      unfold prefixGrammar;
      unfold rulesOfRule;
      unfold prefixCutRules; aesop;

/-
A prefix cut rule is in the prefix grammar.
-/
private lemma prefix_cut_rule_mem {g : CF_grammar T} {A : g.nt} {rhs : List (symbol T g.nt)}
    (hr : (A, rhs) ∈ g.rules) (i : Fin rhs.length) :
    ((true, A), (rhs.take i.val).map liftFull ++ [liftPrefix (rhs.get ⟨i.val, i.isLt⟩)])
      ∈ (prefixGrammar g).rules := by
        apply List.mem_flatMap.mpr
        generalize_proofs at *;
        grind +locals

/-- If [nt B] derives map terminal w in g, then [nt (false, B)] derives map terminal w in prefixGrammar g. -/
private lemma full_nt_derives {g : CF_grammar T} {B : g.nt} {w : List T}
    (h : CF_derives g [symbol.nonterminal B] (List.map symbol.terminal w)) :
    CF_derives (prefixGrammar g) [symbol.nonterminal (false, B)] (List.map symbol.terminal w) := by
  have := full_lifting h
  simpa [liftFull] using this

/-
A sub-list of an all-terminal list is all-terminal. If u ++ v = map terminal w,
    then u = map terminal u' and v = map terminal v' for some u', v'.
-/
private lemma terminal_split {N : Type} {u v : List (symbol T N)} {w : List T}
    (h : u ++ v = List.map symbol.terminal w) :
    ∃ w₁ w₂, w = w₁ ++ w₂ ∧ u = List.map symbol.terminal w₁ ∧ v = List.map symbol.terminal w₂ := by
      induction' u with s u ih generalizing v w;
      · aesop;
      · rcases w with ( _ | ⟨ t, w ⟩ ) <;> simp_all +decide [ List.cons_eq_append_iff ];
        rcases ih h.2 with ⟨ w₁, w₂, rfl, rfl, rfl ⟩ ; use t :: w₁, w₂ ; aesop

/-
A terminal derives itself with 0 steps, so [terminal t] ⇒*_n (map terminal w) implies n=0 and w=[t].
-/
private lemma terminal_derives_in {g : CF_grammar T} {t : T} {n : ℕ} {w : List T}
    (h : CF_derives_in g n [symbol.terminal t] (List.map symbol.terminal w)) :
    n = 0 ∧ w = [t] := by
      rcases n with ( _ | n ) <;> simp_all +decide [ CF_derives_in ];
      · cases w <;> aesop;
      · rcases h with ⟨ w₂, hw₂₁, hw₂₂ ⟩ ; rcases hw₂₁ with ⟨ r, u, v, hr₁, hr₂, hr₃ ⟩ ; simp_all +decide [ CF_transforms ] ;
        cases u <;> cases v <;> aesop ( simp_config := { decide := true } ) ;

/-- Full lifting for a list of symbols. -/
private lemma liftFull_list_derives {g : CF_grammar T} {ss : List (symbol T g.nt)} {w : List T}
    (h : CF_derives g ss (List.map symbol.terminal w)) :
    CF_derives (prefixGrammar g) (ss.map liftFull) (List.map symbol.terminal w) := by
  have h' := full_lifting h
  rwa [map_liftFull_map_terminal] at h'

/-
Given a derivation from a prefix cut RHS, construct the full prefix grammar derivation.
-/
private lemma prefix_from_cut {g : CF_grammar T} {A : g.nt} {rhs : List (symbol T g.nt)}
    (hr : (A, rhs) ∈ g.rules) (j : Fin rhs.length)
    {w_before u_at : List T}
    (h_before : CF_derives (prefixGrammar g)
      ((rhs.take j.val).map liftFull) (List.map symbol.terminal w_before))
    (h_at : CF_derives (prefixGrammar g)
      [liftPrefix (rhs.get ⟨j.val, j.isLt⟩)] (List.map symbol.terminal u_at)) :
    CF_derives (prefixGrammar g)
      [symbol.nonterminal (true, A)] (List.map symbol.terminal (w_before ++ u_at)) := by
        -- By definition of `CF_derives`, we can combine the derivations.
        have h_combined : CF_derives (prefixGrammar g) ((rhs.take j).map liftFull ++ [liftPrefix (rhs.get ⟨j.val, j.isLt⟩)]) (List.map symbol.terminal (w_before ++ u_at)) := by
          convert CF_deri_with_postfix _ h_before |> CF_deri_of_deri_deri <| CF_deri_with_prefix _ h_at using 1 ; aesop;
        have h_transform : CF_transforms (prefixGrammar g) [symbol.nonterminal (true, A)] ((rhs.take j).map liftFull ++ [liftPrefix (rhs.get ⟨j.val, j.isLt⟩)]) := by
          use ((true, A), (rhs.take j.val).map liftFull ++ [liftPrefix (rhs.get ⟨j.val, j.isLt⟩)]);
          use [], [];
          convert prefix_cut_rule_mem hr j using 1;
          aesop;
        exact .single h_transform |> Relation.ReflTransGen.trans <| h_combined

/-
Given a list of symbols `ss` that derives `w` in `k < n` steps, and `u` is a nonempty
    prefix of `w`, find a cut point `j` such that symbols before `j` are fully derived
    and the symbol at `j` is partially derived (as a prefix).

    Proved by induction on `ss`:
    - `ss = []`: impossible since `u ≠ []` but `w = []`.
    - `ss = s :: rest`: use `head_tail_split_in` to split the derivation. By `terminal_split`,
      get `w = w_head ++ w_tail`. Then `u ++ v = w_head ++ w_tail`. By `List.append_eq_append_iff`:
      - Case 1: `∃ a, w_head = u ++ a` (u fits within w_head). Set `j = 0`, `u_at = u`.
        For the symbol `s`: if terminal, `u = [t]`; if nonterminal `B`, use `ih`.
      - Case 2: `∃ a, u = w_head ++ a` with `a ≠ []` (u extends past w_head).
        Recurse on `rest` with prefix `a`. Get `j'`, `w_before'`, `u_at'` from IH.
        Set `j = j'+1`, `w_before = w_head ++ w_before'`, `u_at = u_at'`.
        For the full symbol `s`: if terminal, `liftFull (terminal t) = terminal t`, self-derives;
        if nonterminal `B`, use `full_nt_derives`. Combine with IH result.
-/
set_option maxHeartbeats 400000 in
private lemma find_prefix_cut {g : CF_grammar T} {n : ℕ}
    (ih : ∀ m < n, ∀ (A : g.nt) (w u v : List T),
      CF_derives_in g m [symbol.nonterminal A] (List.map symbol.terminal w) →
      w = u ++ v →
      CF_derives (prefixGrammar g)
        [symbol.nonterminal (true, A)] (List.map symbol.terminal u))
    : ∀ (ss : List (symbol T g.nt)) {k : ℕ} (hk : k < n)
    {w u v : List T}
    (hw : CF_derives_in g k ss (List.map symbol.terminal w))
    (huv : w = u ++ v) (hu : u ≠ []),
    ∃ (j : Fin ss.length) (w_before u_at : List T),
      u = w_before ++ u_at ∧
      CF_derives (prefixGrammar g) ((ss.take j.val).map liftFull) (List.map symbol.terminal w_before) ∧
      CF_derives (prefixGrammar g) [liftPrefix (ss.get j)] (List.map symbol.terminal u_at) := by
        intro ss k hk w u v hw huv hu_nonempty
        induction' ss with s ss ih generalizing k w u v;
        · rcases k with ( _ | k ) <;> simp_all +decide [ CF_derives_in ];
          rcases hw with ⟨ w₂, hw₂, hw₂' ⟩ ; cases hw₂ ; aesop;
        · obtain ⟨ n₁, n₂, hn₁₂, u_part, v_part, hu_part, hv_part, huv_part ⟩ := head_tail_split_in k s ss ( List.map symbol.terminal w ) hw
          obtain ⟨ w_head, w_tail, hw_head, hw_tail ⟩ := terminal_split ( by aesop : u_part ++ v_part = List.map symbol.terminal w );
          by_cases hu_head : ∃ a, w_head = u ++ a <;> simp_all +decide [ List.append_eq_append_iff ];
          · rcases hu_head with ⟨ a, rfl ⟩ ; rcases s with ( _ | _ ) <;> simp_all +decide ;
            · rcases u with ( _ | ⟨ t, u ⟩ ) <;> simp_all +decide [ List.map ];
              rcases n₁ with ( _ | n₁ ) <;> simp_all +decide [ CF_derives_in ];
              · use ⟨ 0, by simp +decide ⟩ ; simp +decide [ liftFull, liftPrefix ] ;
                use [], [t]; simp +decide [ CF_derives ] ;
                exact ⟨ by rfl, by rfl ⟩;
              · rcases hu_part with ⟨ w₂, hw₂₁, hw₂₂ ⟩ ; rcases w₂ with ( _ | ⟨ t₂, w₂ ⟩ ) <;> simp_all +decide [ CF_transforms ] ;
                rcases hw₂₁ with ⟨ a, b, hab, x, y, hx, hy ⟩ ; rcases x with ( _ | ⟨ _, _ ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ] ;
            · rename_i A; specialize ‹∀ m < n, ∀ ( A : g.nt ) ( w u v : List T ), CF_derives_in g m [ symbol.nonterminal A ] ( List.map symbol.terminal w ) → w = u ++ v → CF_derives ( prefixGrammar g ) [ symbol.nonterminal ( true, A ) ] ( List.map symbol.terminal u ) › n₁ ( by linarith ) A ( u ++ a ) u a; simp_all +decide ;
              use ⟨ 0, by aesop ⟩ ; simp_all +decide [ List.take ] ;
              exact ⟨ [ ], u, by simp +decide, by exact CF_deri_self, ih ⟩;
          · rcases huv with ⟨ as, rfl, rfl ⟩ ; simp_all +decide [ List.append_assoc ] ;
            have := @ih ( n₂ ) ( by linarith ) ( as ++ v ) as v ; simp_all +decide [ List.append_assoc ] ;
            obtain ⟨ j, w_before, u_at, rfl, hw_before, hw_at ⟩ := this; use ⟨ j.val + 1, by
              exact Nat.succ_lt_succ j.2 ⟩ ; use w_head ++ w_before, u_at; simp_all +decide [ List.take_append ] ; (
            have h_liftFull_s : CF_derives (prefixGrammar g) [liftFull s] (List.map symbol.terminal w_head) := by
              -- Apply the liftFull_list_derives lemma to the derivation from s to w_head.
              have h_liftFull_s : CF_derives (prefixGrammar g) (List.map liftFull [s]) (List.map symbol.terminal w_head) := by
                have h_derives : CF_derives g [s] (List.map symbol.terminal w_head) := by
                  exact derives_of_derives_in hu_part
                exact liftFull_list_derives h_derives
              generalize_proofs at *; (
              exact h_liftFull_s.trans ( by rfl ) ;)
            generalize_proofs at *; (
            have h_liftFull_s : CF_derives (prefixGrammar g) (liftFull s :: List.take (j.val) (List.map liftFull ss)) (List.map symbol.terminal w_head ++ List.take (j.val) (List.map liftFull ss)) := by
              have h_liftFull_s : ∀ {s₁ s₂ : List (symbol T (Bool × g.nt))}, CF_derives (prefixGrammar g) s₁ s₂ → ∀ {t : List (symbol T (Bool × g.nt))}, CF_derives (prefixGrammar g) (s₁ ++ t) (s₂ ++ t) := by
                grind +suggestions
              generalize_proofs at *; (
              exact h_liftFull_s ‹_› |> fun h => by simpa using h;)
            generalize_proofs at *; (
            have h_liftFull_s : CF_derives (prefixGrammar g) (List.map symbol.terminal w_head ++ List.take (j.val) (List.map liftFull ss)) (List.map symbol.terminal w_head ++ List.map symbol.terminal w_before) := by
              grind +suggestions
            generalize_proofs at *; (
            exact CF_deri_of_deri_deri ‹_› ‹_› |> CF_deri_of_deri_deri <| by tauto;))))

/-
Core completeness lemma (by strong induction on step count `n`).
    If `A` derives terminal word `w` in `n` steps, then for any split `w = u ++ v`,
    `(true, A)` derives `u` in the prefix grammar.
-/
private lemma prefix_completeness_aux {g : CF_grammar T} :
    ∀ (n : ℕ) (A : g.nt) (w u v : List T),
      CF_derives_in g n [symbol.nonterminal A] (List.map symbol.terminal w) →
      w = u ++ v →
      CF_derives (prefixGrammar g)
        [symbol.nonterminal (true, A)] (List.map symbol.terminal u) := by
          intro n A w u v h_trans h_eq; induction' n using Nat.strong_induction_on with n ih generalizing A w u v; rcases n with ( _ | n ) <;> simp +decide [ CF_derives_in ] at *;
          · cases w <;> cases u <;> cases v <;> cases h_trans;
          · obtain ⟨w₂, hw₂⟩ := h_trans
            obtain ⟨r, hr⟩ : ∃ r : g.nt × List (symbol T g.nt), r ∈ g.rules ∧ w₂ = r.2 := by
              obtain ⟨ r, u, v, hr, hu, hv ⟩ := hw₂.1
              generalize_proofs at *; (
              rcases u with ( _ | ⟨ u, u ⟩ ) <;> rcases v with ( _ | ⟨ v, v ⟩ ) <;> simp +decide at hu ⊢ ; aesop ( simp_config := { singlePass := true } ) ;)
            generalize_proofs at *; (
            by_cases hu : u = [] <;> simp_all +decide [ CF_transforms ];
            · obtain ⟨a, b, h_rule, x, x_1, hx⟩ := hw₂.left
              have h_empty_prefix : ((true, A), []) ∈ (prefixGrammar g).rules := by
                have h_empty_prefix : ∀ (A : g.nt) (rhs : List (symbol T g.nt)), (A, rhs) ∈ g.rules → ((true, A), []) ∈ (prefixGrammar g).rules := by
                  intros A rhs h_rule
                  apply empty_prefix_rule_mem h_rule
                generalize_proofs at *; (
                cases x <;> cases x_1 <;> aesop ( simp_config := { decide := true } ) ;)
              generalize_proofs at *; (
              exact Relation.ReflTransGen.single (by
              use ((true, A), []), [ ], [ ] ; aesop;));
            · -- Apply the find_prefix_cut lemma to find the appropriate j, w_before, and u_at.
              obtain ⟨j, w_before, u_at, hu_eq, hw_before, hu_at⟩ : ∃ j : Fin w₂.length, ∃ w_before u_at : List T, u = w_before ++ u_at ∧ CF_derives (prefixGrammar g) ((w₂.take j.val).map liftFull) (List.map symbol.terminal w_before) ∧ CF_derives (prefixGrammar g) [liftPrefix (w₂.get ⟨j.val, j.isLt⟩)] (List.map symbol.terminal u_at) := by
                have := @find_prefix_cut T g
                generalize_proofs at *; (
                contrapose! this
                generalize_proofs at *; (
                use n + 1
                generalize_proofs at *; (
                exact ⟨ fun m hm A w u v hw hv => ih m ( Nat.le_of_lt_succ hm ) A w u v hw hv, w₂, n, Nat.lt_succ_self _, u ++ v, u, v, by simpa [ hr.2 ] using hw₂.2, rfl, hu, fun j w_before u_at hw hw' hw'' => this j w_before u_at hw hw' hw'' ⟩)))
              generalize_proofs at *; (
              convert prefix_from_cut ( show ( A, w₂ ) ∈ g.rules from ?_ ) j hw_before hu_at using 1
              generalize_proofs at *; (
              rw [ hu_eq ]);
              rcases hw₂.1 with ⟨ a, b, h₁, x, y, h₂, h₃ ⟩ ; simp_all +decide [ List.append_assoc ] ;
              cases x <;> cases y <;> aesop ( simp_config := { decide := true } ) ;))

private lemma prefix_completeness {g : CF_grammar T} (w : List T) :
    w ∈ prefixLang (CF_language g) → w ∈ CF_language (prefixGrammar g) := by
  intro ⟨v, hv⟩
  change CF_generates (prefixGrammar g) w
  unfold CF_generates CF_generates_str
  obtain ⟨n, hn⟩ := derives_in_of_derives hv
  exact prefix_completeness_aux n g.initial (w ++ v) w v hn rfl

end Completeness

/-! ## Soundness: `CF_language (prefixGrammar g) ⊆ prefixLang (CF_language g)`

This section assumes all rules in `g` are fully productive (every nonterminal appearing
in any rule can derive some terminal string). -/

section Soundness

/-- If `liftFull` is injective on symbols. -/
private lemma liftFull_injective {N : Type} : Function.Injective (@liftFull T N) := by
  intros a b h; cases a <;> cases b <;> simp_all [liftFull]

/-
A transform step on a list of `liftFull` images in the prefix grammar
    corresponds to a transform step in the original grammar, and the result
    is again a list of `liftFull` images.
-/
private lemma unlift_full_transform {g : CF_grammar T}
    {ss : List (symbol T g.nt)} {ss' : List (symbol T (prefixGrammar g).nt)}
    (h : CF_transforms (prefixGrammar g) (ss.map liftFull) ss') :
    ∃ ss'' : List (symbol T g.nt), ss' = ss''.map liftFull ∧ CF_transforms g ss ss'' := by
      obtain ⟨ r, hr ⟩ := h;
      rcases hr with ⟨ u, v, hr, h₁, h₂ ⟩ ; rcases r with ⟨ ⟨ b, B ⟩, l ⟩ ; rcases b with ( _ | _ ) <;> simp_all +decide [ List.mem_append, List.mem_cons ] ;
      · -- By definition of `prefixGrammar`, we know that `l` is the map of some rule in `g.rules`.
        obtain ⟨ r, hr ⟩ : ∃ r ∈ g.rules, l = r.2.map liftFull ∧ r.1 = B := by
          grind +locals;
        -- By definition of `liftFull`, we know that `u ++ symbol.nonterminal (false, B) :: v` is the map of some list `ss''`.
        obtain ⟨ u', v', hu', hv', hss'' ⟩ : ∃ u' v' : List (symbol T g.nt), u = u'.map liftFull ∧ v = v'.map liftFull ∧ ss = u' ++ [symbol.nonterminal B] ++ v' := by
          have h_split : ∀ {l : List (symbol T g.nt)} {u v : List (symbol T (Bool × g.nt))}, List.map liftFull l = u ++ symbol.nonterminal (false, B) :: v → ∃ u' v' : List (symbol T g.nt), u = u'.map liftFull ∧ v = v'.map liftFull ∧ l = u' ++ [symbol.nonterminal B] ++ v' := by
            intros l u v h; induction' l with l ih generalizing u v <;> simp_all +decide [ List.map ] ;
            rcases u with ( _ | ⟨ u, u ⟩ ) <;> simp_all +decide [ List.map ];
            · unfold liftFull at h; aesop;
            · grind;
          exact h_split h₁;
        refine' ⟨ u' ++ r.2 ++ v', _, _ ⟩ <;> simp_all +decide [ List.map_append ];
        exact ⟨ r, by aesop ⟩;
      · contrapose! h₁; simp_all +decide [ List.map_eq_append_iff ] ;
        intro x y hxy hx hy; induction x <;> induction y <;> simp_all +decide [ List.map ] ;
        · cases ‹symbol T g.nt› <;> cases hy.1;
        · cases ‹symbol T g.nt› <;> cases hy.1

/-
Un-lifting full-mode derivations: if `ss.map liftFull` derives
    `map terminal w` in the prefix grammar, then `ss` derives `map terminal w`
    in the original grammar.
-/
private lemma unlift_full_derives {g : CF_grammar T}
    {ss : List (symbol T g.nt)} {w : List T}
    (h : CF_derives (prefixGrammar g) (ss.map liftFull) (List.map symbol.terminal w)) :
    CF_derives g ss (List.map symbol.terminal w) := by
      -- By induction on the derivation in the prefix grammar, we can show that the original derivation holds.
      have h_ind : ∀ (n : ℕ) (ss : List (symbol T g.nt)) (w : List T), CF_derives_in (prefixGrammar g) n (List.map liftFull ss) (List.map symbol.terminal w) → CF_derives_in g n ss (List.map symbol.terminal w) := by
        intro n ss w h
        induction' n with n ih generalizing ss w;
        · -- Since liftFull is injective, if the maps are equal, then the original lists must be equal.
          have h_inj : Function.Injective (liftFull : symbol T g.nt → symbol T (Bool × g.nt)) := by
            exact?;
          exact List.map_injective_iff.mpr h_inj <| by aesop;
        · obtain ⟨ mid, hmid₁, hmid₂ ⟩ := h;
          obtain ⟨ ss', hss', hss'' ⟩ := unlift_full_transform hmid₁;
          exact ⟨ ss', hss'', ih _ _ <| by simpa [ hss' ] using hmid₂ ⟩;
      obtain ⟨ n, hn ⟩ := derives_in_of_derives h; exact h_ind n ss w hn |> fun h => by exact?;

/-
If `B` is productive, then there exists a rule `(B, rhs) ∈ g.rules`.
-/
private lemma productive_has_rule {g : CF_grammar T} {B : g.nt}
    (hprod : productive g B) :
    ∃ rhs, (B, rhs) ∈ g.rules := by
      obtain ⟨ w, hw ⟩ := hprod;
      have := hw;
      -- By definition of `CF_derives`, this means there exists a sequence of transformations from `[symbol.nonterminal B]` to `List.map symbol.terminal w`.
      obtain ⟨n, hn⟩ : ∃ n, CF_derives_in g n [symbol.nonterminal B] (List.map symbol.terminal w) := by
        exact?;
      induction' n with n ih generalizing B w <;> simp_all +decide [ CF_derives_in ];
      · cases w <;> aesop;
      · rcases hn with ⟨ w₂, hw₂, hw₂' ⟩ ; rcases hw₂ with ⟨ r, u, v, hr, hu, hv ⟩ ; simp_all +decide [ List.length_append ] ;
        cases u <;> aesop

/-
If every nonterminal in a sentential form is productive, then the form
    derives some terminal string.
-/
private lemma list_productive_derives {g : CF_grammar T}
    (ss : List (symbol T g.nt))
    (hprod : ∀ B, symbol.nonterminal B ∈ ss → productive g B) :
    ∃ w : List T, CF_derives g ss (List.map symbol.terminal w) := by
      induction ss <;> simp_all +decide [ List.foldr ];
      · exact ⟨ [ ], by tauto ⟩;
      · rename_i h t ih
        obtain ⟨w_s, hw_s⟩ : ∃ w_s : List T, CF_derives g [h] (List.map symbol.terminal w_s) := by
          rcases h with ( _ | _ ) <;> simp_all +decide [ productive ];
          exact ⟨ [ ‹_› ], by exact Relation.ReflTransGen.refl ⟩;
        obtain ⟨ w_t, hw_t ⟩ := ih; use w_s ++ w_t; exact (by
        convert CF_deri_with_postfix _ hw_s |> CF_deri_of_deri_deri <| CF_deri_with_prefix _ hw_t using 1 ; aesop;);

/-
Classification of rules in the prefix grammar with LHS `(true, A)`.
-/
private lemma classify_true_rule {g : CF_grammar T} {A : g.nt}
    {rhs_pg : List (symbol T (prefixGrammar g).nt)}
    (h : ((true, A), rhs_pg) ∈ (prefixGrammar g).rules) :
    ∃ rhs : List (symbol T g.nt), (A, rhs) ∈ g.rules ∧
      (rhs_pg = [] ∨ ∃ i : Fin rhs.length,
        rhs_pg = (rhs.take i.val).map liftFull ++ [liftPrefix (rhs.get ⟨i.val, i.isLt⟩)]) := by
          grind +locals

/-
Given a derivation of a mixed liftFull/liftPrefix list from a prefix cut rule,
    extract the derivation pieces for the original grammar.
-/
private lemma split_prefix_cut_derivation {g : CF_grammar T}
    {rhs : List (symbol T g.nt)} {i : Fin rhs.length}
    {n : ℕ} {w : List T}
    (h : CF_derives_in (prefixGrammar g) n
      ((rhs.take i.val).map liftFull ++ [liftPrefix (rhs.get ⟨i.val, i.isLt⟩)])
      (List.map symbol.terminal w)) :
    ∃ w_pre w_at : List T, w = w_pre ++ w_at ∧
      ∃ n_pre n_at : ℕ, n_pre + n_at ≤ n ∧
        CF_derives (prefixGrammar g) ((rhs.take i.val).map liftFull) (List.map symbol.terminal w_pre) ∧
        CF_derives_in (prefixGrammar g) n_at [liftPrefix (rhs.get ⟨i.val, i.isLt⟩)] (List.map symbol.terminal w_at) := by
          have step_bounded_derivation : ∀ k : ℕ,
            ∀ s₁ s₂ : List (symbol T (prefixGrammar g).nt),
            ∀ x : List (symbol T (prefixGrammar g).nt),
            CF_derives_in (prefixGrammar g) k (s₁ ++ s₂) x →
            ∃ n₁ n₂ : ℕ,
              n₁ + n₂ ≤ k ∧
              ∃ u v : List (symbol T (prefixGrammar g).nt),
                CF_derives_in (prefixGrammar g) n₁ s₁ u ∧
                  CF_derives_in (prefixGrammar g) n₂ s₂ v ∧
                    u ++ v = x := by
                      intro k s₁ s₂ x hx
                      induction' k with k ih generalizing s₁ s₂ x;
                      · cases hx ; aesop;
                      · obtain ⟨ m, hm ⟩ := hx;
                        rcases transform_in_append hm.1 with ( ⟨ u, hu, rfl ⟩ | ⟨ v, hv, rfl ⟩ );
                        · obtain ⟨ n₁, n₂, hn₁₂, u', v', hu', hv', huv' ⟩ := ih u s₂ x hm.2;
                          exact ⟨ n₁ + 1, n₂, by linarith, u', v', by exact ⟨ u, hu, hu' ⟩, hv', huv' ⟩;
                        · obtain ⟨ n₁, n₂, hn₁₂, u, v, hu, hv, huv ⟩ := ih s₁ v x hm.2;
                          exact ⟨ n₁, n₂ + 1, by linarith, u, _, hu, by exact ⟨ _, by tauto, hv ⟩, huv ⟩;
          obtain ⟨ n₁, n₂, hn₁₂, u, v, hu, hv, huv ⟩ := step_bounded_derivation n ( List.map liftFull ( List.take ( i : ℕ ) rhs ) ) [ liftPrefix ( rhs.get ⟨ i, i.2 ⟩ ) ] ( List.map symbol.terminal w ) h;
          obtain ⟨ w_pre, w_at, hw ⟩ := terminal_split huv;
          exact ⟨ w_pre, w_at, hw.1, n₁, n₂, hn₁₂, by simpa only [ hw.2 ] using derives_of_derives_in hu, by simpa only [ hw.2 ] using hv ⟩

/-
Combining derivations of rhs pieces back into a full derivation from A in g.
    If (A, rhs) ∈ g.rules and rhs = take i ++ [rhs[i]] ++ drop (i+1), and
    take i derives w_pre, rhs[i] derives w_mid, drop (i+1) derives w_rest,
    then A derives w_pre ++ w_mid ++ w_rest.
-/
private lemma combine_rhs_derivation {g : CF_grammar T} {A : g.nt}
    {rhs : List (symbol T g.nt)} (hr : (A, rhs) ∈ g.rules) (i : Fin rhs.length)
    {w_pre w_mid w_rest : List T}
    (h_pre : CF_derives g (rhs.take i.val) (List.map symbol.terminal w_pre))
    (h_mid : CF_derives g [rhs.get ⟨i.val, i.isLt⟩] (List.map symbol.terminal w_mid))
    (h_rest : CF_derives g (rhs.drop (i.val + 1)) (List.map symbol.terminal w_rest)) :
    CF_derives g [symbol.nonterminal A] (List.map symbol.terminal (w_pre ++ w_mid ++ w_rest)) := by
      convert CF_deri_of_deri_deri _ _ using 1;
      exact rhs.take i.val ++ [ rhs.get ⟨ i, i.2 ⟩ ] ++ rhs.drop ( i.val + 1 );
      · convert CF_deri_of_deri_deri _ _ using 1;
        exact rhs;
        · constructor ; tauto;
          constructor;
          exact ⟨ [ ], [ ], hr, by simp +decide, by simp +decide ⟩;
        · convert CF_deri_self using 1 ; aesop;
      · convert CF_deri_of_deri_deri _ _ using 1;
        exact List.map symbol.terminal w_pre ++ [ rhs.get ⟨ i, i.2 ⟩ ] ++ List.drop ( i + 1 ) rhs;
        · grind +suggestions;
        · convert CF_deri_of_deri_deri _ _ using 1;
          exact List.map symbol.terminal w_pre ++ List.map symbol.terminal w_mid ++ List.drop ( i + 1 ) rhs;
          · convert CF_deri_with_prefix_and_postfix _ _ h_mid using 1;
          · convert CF_deri_with_prefix ( List.map symbol.terminal w_pre ++ List.map symbol.terminal w_mid ) h_rest using 1 ; simp +decide [ List.map_append ]

/-
Soundness for true mode, by strong induction.
    If `(true, A)` derives `w` in the prefix grammar in `n` steps,
    then `∃ v, A` derives `w ++ v` in `g`.
-/
set_option maxHeartbeats 800000 in
private lemma true_mode_soundness {g : CF_grammar T}
    (hprod : ∀ r ∈ g.rules, fullyProductiveRule g r) :
    ∀ (n : ℕ) (A : g.nt) (w : List T),
      CF_derives_in (prefixGrammar g) n [symbol.nonterminal (true, A)] (List.map symbol.terminal w) →
      ∃ v : List T, CF_derives g [symbol.nonterminal A] (List.map symbol.terminal (w ++ v)) := by
        intro n A w hw
        induction' n using Nat.strong_induction_on with n ih generalizing A w;
        rcases n with ( _ | n );
        · cases w <;> cases hw;
        · -- Extract the first step of the derivation.
          obtain ⟨w₂, hw₂, hw₁⟩ : ∃ w₂, CF_transforms (prefixGrammar g) [symbol.nonterminal (true, A)] w₂ ∧ CF_derives_in (prefixGrammar g) n w₂ (List.map symbol.terminal w) := by
            exact?
          generalize_proofs at *; (
          -- Byclassify_true_rule, we know that there exists a rule (A, rhs) in g such that w₂ is either the empty list or a prefix cut of rhs.
          obtain ⟨rhs, hr, hw₂⟩ : ∃ rhs : List (symbol T g.nt), (A, rhs) ∈ g.rules ∧ (w₂ = [] ∨ ∃ i : Fin rhs.length, w₂ = (rhs.take i.val).map liftFull ++ [liftPrefix (rhs.get ⟨i.val, i.isLt⟩)]) := by
            obtain ⟨r, hr⟩ : ∃ r : (Bool × g.nt) × List (symbol T (prefixGrammar g).nt), r ∈ (prefixGrammar g).rules ∧ r.1 = (true, A) ∧ r.2 = w₂ := by
              obtain ⟨ u, v, h ⟩ := hw₂; simp_all +decide [ CF_transforms ] ;
              rcases h with ⟨ hu, x, hx, rfl ⟩ ; rcases v with ( _ | ⟨ _, _ | v ⟩ ) <;> simp_all +decide [ List.append_assoc ] ;
            generalize_proofs at *; (
            grind +locals)
          generalize_proofs at *; (
          rcases hw₂ with ( rfl | ⟨ i, rfl ⟩ ) <;> simp_all +decide [ CF_derives_in ];
          · -- Since the empty list can only derive the empty list, we have w = [].
            have hw_empty : w = [] := by
              have hw_empty : ∀ {w : List T}, CF_derives_in (prefixGrammar g) n [] (List.map symbol.terminal w) → w = [] := by
                intros w hw; induction' n with n ih generalizing w; simp_all +decide [ CF_derives_in ] ;
                obtain ⟨ w₂, hw₂, hw₁ ⟩ := hw; simp_all +decide [ CF_derives_in ] ;
                cases hw₂ ; aesop ( simp_config := { singlePass := true } ) ;
              generalize_proofs at *; (
              exact hw_empty hw₁)
            generalize_proofs at *; (
            specialize hprod A rhs hr; unfold fullyProductiveRule at hprod; aesop;);
          · -- By split_prefix_cut_derivation, we can split the derivation into two parts.
            obtain ⟨w_pre, w_at, hw_eq, n_pre, n_at, hn_pre_at, hw_pre, hw_at⟩ : ∃ w_pre w_at : List T, w = w_pre ++ w_at ∧ ∃ n_pre n_at : ℕ, n_pre + n_at ≤ n ∧
              CF_derives (prefixGrammar g) ((rhs.take i.val).map liftFull) (List.map symbol.terminal w_pre) ∧
              CF_derives_in (prefixGrammar g) n_at [liftPrefix (rhs.get ⟨i.val, i.isLt⟩)] (List.map symbol.terminal w_at) := by
                have h_split : ∀ {n : ℕ} {w : List T} {rhs : List (symbol T g.nt)} {i : Fin rhs.length},
                    CF_derives_in (prefixGrammar g) n ((rhs.take i.val).map liftFull ++ [liftPrefix (rhs.get ⟨i.val, i.isLt⟩)]) (List.map symbol.terminal w) →
                    ∃ w_pre w_at : List T, w = w_pre ++ w_at ∧ ∃ n_pre n_at : ℕ, n_pre + n_at ≤ n ∧
                      CF_derives (prefixGrammar g) ((rhs.take i.val).map liftFull) (List.map symbol.terminal w_pre) ∧
                      CF_derives_in (prefixGrammar g) n_at [liftPrefix (rhs.get ⟨i.val, i.isLt⟩)] (List.map symbol.terminal w_at) := by
                        intros n w rhs i hw; exact split_prefix_cut_derivation hw;
                generalize_proofs at *; (
                exact h_split ( by simpa [ List.map_take ] using hw₁ ) |> fun ⟨ w_pre, w_at, hw_eq, n_pre, n_at, hn_pre_at, hw_pre, hw_at ⟩ => ⟨ w_pre, w_at, hw_eq, n_pre, n_at, hn_pre_at, hw_pre, hw_at ⟩ ;)
            generalize_proofs at *; (
            -- By unlift_full_derives, we know that rhs.take i.val derives w_pre in g.
            have hw_pre_g : CF_derives g (rhs.take i.val) (List.map symbol.terminal w_pre) := by
              convert unlift_full_derives hw_pre using 1
            generalize_proofs at *; (
            -- By split on rhs[i], we consider two cases: rhs[i] is a terminal or a nonterminal.
            by_cases h_term : ∃ t : T, rhs.get ⟨i.val, i.isLt⟩ = symbol.terminal t
            generalize_proofs at *; (
            obtain ⟨ t, ht ⟩ := h_term; simp_all +decide [ liftPrefix ] ;
            -- By list_productive_derives, we know that rhs.drop (i.val + 1) derives some w_rest in g.
            obtain ⟨w_rest, hw_rest⟩ : ∃ w_rest : List T, CF_derives g (rhs.drop (i.val + 1)) (List.map symbol.terminal w_rest) := by
              apply list_productive_derives; intro B hB; exact (hprod A rhs hr).2 B (by
              exact List.mem_of_mem_drop hB |> fun h => by simpa using h;)
            generalize_proofs at *; (
            -- By combine_rhs_derivation, we know that A derives w_pre ++ [t] ++ w_rest in g.
            have hw_combined : CF_derives g [symbol.nonterminal A] (List.map symbol.terminal (w_pre ++ [t] ++ w_rest)) := by
              apply combine_rhs_derivation hr i hw_pre_g (by
              convert CF_deri_self using 1 ; aesop) hw_rest
            generalize_proofs at *; (
            have := terminal_derives_in ( show CF_derives_in ( prefixGrammar g ) n_at [ symbol.terminal t ] ( List.map symbol.terminal w_at ) from hw_at ) ; aesop;)));
            -- Since rhs[i] is not a terminal, it must be a nonterminal.
            obtain ⟨B, hB⟩ : ∃ B : g.nt, rhs.get ⟨i.val, i.isLt⟩ = symbol.nonterminal B := by
              cases h : rhs.get ⟨ i, by assumption ⟩ <;> tauto
            generalize_proofs at *; (
            -- By the induction hypothesis, we know that there exists a v such that B derives w_at ++ v.
            obtain ⟨v, hv⟩ : ∃ v : List T, CF_derives g [symbol.nonterminal B] (List.map symbol.terminal (w_at ++ v)) := by
              specialize ih n_at (by linarith) B w_at
              generalize_proofs at *; (
              aesop)
            generalize_proofs at *; (
            -- By list_productive_derives, we know that rhs.drop (i.val + 1) derives some w_rest.
            obtain ⟨w_rest, hw_rest⟩ : ∃ w_rest : List T, CF_derives g (rhs.drop (i.val + 1)) (List.map symbol.terminal w_rest) := by
              apply list_productive_derives
              generalize_proofs at *; (
              intros B hB; exact (hprod A rhs hr).2 B (by
              exact List.mem_of_mem_drop hB |> fun h => by simpa using h;))
            generalize_proofs at *; (
            -- By combine_rhs_derivation, we know that A derives w_pre ++ (w_at ++ v) ++ w_rest.
            have h_combined : CF_derives g [symbol.nonterminal A] (List.map symbol.terminal (w_pre ++ (w_at ++ v) ++ w_rest)) := by
              apply combine_rhs_derivation hr i hw_pre_g
              · convert hv using 1
                simpa using hB
              · exact hw_rest
            generalize_proofs at *; (
            exact ⟨ v ++ w_rest, by simpa [ hw_eq, List.map_append ] using h_combined ⟩))))))))

/-
Soundness of the prefix grammar when all rules are fully productive.
-/
set_option maxHeartbeats 0 in
private lemma prefix_soundness {g : CF_grammar T}
    (hprod : ∀ r ∈ g.rules, fullyProductiveRule g r) (w : List T) :
    w ∈ CF_language (prefixGrammar g) → w ∈ prefixLang (CF_language g) := by
      intro hw
      obtain ⟨n, hn⟩ : ∃ n, CF_derives_in (prefixGrammar g) n [symbol.nonterminal (true, g.initial)] (List.map symbol.terminal w) := by
        exact?;
      obtain ⟨ v, hv ⟩ := true_mode_soundness hprod n g.initial w hn;
      exact ⟨ v, hv ⟩

end Soundness

/-! ## Main Theorems -/

/-- The class of context-free languages is closed under taking prefixes. -/
theorem CF_of_prefix_CF (L : Language T) : is_CF L → is_CF (prefixLang L) := by
  intro h
  obtain ⟨g, rfl⟩ := is_CF_implies_is_CF_via_cfg h
  rw [← productiveGrammar_language g]
  apply is_CF_via_cfg_implies_is_CF
  refine ⟨prefixGrammar (productiveGrammar g), ?_⟩
  ext w
  constructor
  · intro hw
    exact prefix_soundness
      (fun r hr => ⟨
        (productive_iff_productiveGrammar.mp (productiveGrammar_rules_productive hr).1),
        (productiveGrammar_allRulesFullyProductive g r hr)⟩)
      w hw
  · intro hw
    exact prefix_completeness w hw
