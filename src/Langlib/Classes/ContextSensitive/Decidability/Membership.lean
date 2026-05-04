import Mathlib
import Langlib.Grammars.ContextSensitive.Toolbox

/-! # Decidability of Membership in Context-Sensitive Languages

This file proves that membership in a context-sensitive language is decidable.

The key insight is that in a context-sensitive grammar (where every rule has non-empty
output), every derivation step preserves or increases the length of the sentential form.
Therefore, when checking whether a word `w` belongs to the language, all intermediate
sentential forms have length at most `|w|`. Since there are only finitely many such
forms (when the terminal and nonterminal alphabets are finite), the reachability problem
reduces to search over a finite graph.

Since the `CS_grammar` structure now requires `output_nonempty` (matching the standard
definition of context-sensitive grammars), the non-contracting property
`CSG_noncontracting` holds automatically. The main decidability result
`CS_membership_decidable'` therefore needs no extra hypothesis.

## Main results

- `CSG_noncontracting_of_CS_grammar` — every CS grammar is non-contracting
- `CS_membership_decidable'` — membership in any context-sensitive grammar is decidable
-/

open List Relation

variable {T : Type}

/-! ## Fintype instance for `symbol` -/

/-- `symbol T N` is finite when both `T` and `N` are. -/
noncomputable instance symbol.fintype (T : Type) (N : Type) [Fintype T] [Fintype N] :
    Fintype (symbol T N) :=
  Fintype.ofEquiv (T ⊕ N) {
    toFun := fun s => match s with | .inl t => .terminal t | .inr n => .nonterminal n
    invFun := fun s => match s with | .terminal t => .inl t | .nonterminal n => .inr n
    left_inv := by intro x; cases x <;> rfl
    right_inv := by intro x; cases x <;> rfl
  }

/-! ## Non-contracting property and length bounds -/

/-- A single non-contracting transformation step does not decrease the length of the
    sentential form. -/
lemma CS_transforms_length_le (g : CS_grammar T)
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CS_transforms g w₁ w₂) : w₁.length ≤ w₂.length := by
  obtain ⟨r, u, v, hr, rfl, rfl⟩ := h
  simp [List.length_append]
  exact List.length_pos_of_ne_nil (g.output_nonempty r hr)

/-- In a non-contracting grammar, derivation does not decrease the length. -/
lemma CS_derives_length_le (g : CS_grammar T)
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CS_derives g w₁ w₂) : w₁.length ≤ w₂.length := by
  induction h with
  | refl => exact le_refl _
  | tail h₁ h₂ ih => exact le_trans ih (CS_transforms_length_le g h₂)

/-- The empty word is not in the language of a non-contracting grammar. -/
lemma empty_not_in_CS_language (g : CS_grammar T) : [] ∉ CS_language g := by
  intro h
  have := CS_derives_length_le g h
  simp at this

/-! ## Fintype instance for bounded-length lists -/

/-- Lists of bounded length over a finite type form a finite type. -/
noncomputable instance fintypeBoundedList (α : Type) [Fintype α] [DecidableEq α] (n : ℕ) :
    Fintype {l : List α // l.length ≤ n} :=
  Fintype.ofSurjective
    (f := fun (p : Σ k : Fin (n+1), List.Vector α k.val) =>
      (⟨p.2.1, by have := p.2.2; have := p.1.2; omega⟩ : {l : List α // l.length ≤ n}))
    (fun ⟨l, hl⟩ => ⟨⟨⟨l.length, by omega⟩, l, rfl⟩, by simp⟩)

/-! ## BFS-based reachability on Fintype -/

section Reachability

variable {α : Type} [Fintype α] [DecidableEq α] (R : α → α → Prop) [DecidableRel R]

/-- The set of elements reachable from `S` in one more step. -/
noncomputable def stepClosure (S : Finset α) : Finset α :=
  S ∪ Finset.univ.filter (fun b => ∃ a ∈ S, R a b)

/-- BFS iteration: the set of elements reachable from `{start}` in at most `n` steps. -/
noncomputable def reachSet (start : α) : ℕ → Finset α
  | 0 => {start}
  | n + 1 => stepClosure R (reachSet start n)

/-
`stepClosure` is monotone: `S ⊆ stepClosure R S`.
-/
lemma subset_stepClosure (S : Finset α) : S ⊆ stepClosure R S := by
  -- By definition of `stepClosure`, we know that `S ⊆ stepClosure R S`.
  simp [stepClosure]

/-
`reachSet` is monotonically increasing.
-/
lemma reachSet_mono (start : α) (n : ℕ) :
    reachSet R start n ⊆ reachSet R start (n + 1) := by
  exact Finset.subset_iff.mpr fun x hx => by exact Finset.mem_union_left _ hx;

/-
`reachSet` is monotone for any step difference.
-/
lemma reachSet_mono_of_le (start : α) {n m : ℕ} (h : n ≤ m) :
    reachSet R start n ⊆ reachSet R start m := by
  induction' h with n m h ih;
  · rfl;
  · exact h.trans ( reachSet_mono R start n )

/-
`start` is always in `reachSet`.
-/
lemma start_mem_reachSet (start : α) (n : ℕ) : start ∈ reachSet R start n := by
  induction' n with n ih;
  · exact Finset.mem_singleton_self _;
  · exact reachSet_mono R start n ih

/-
Elements in `reachSet` are reachable via `ReflTransGen`.
-/
lemma ReflTransGen_of_mem_reachSet (start : α) (n : ℕ) {b : α}
    (hb : b ∈ reachSet R start n) : ReflTransGen R start b := by
  induction' n with n ih generalizing b;
  · rw [ show reachSet R start 0 = { start } from rfl ] at hb; aesop;
  · -- By definition of `reachSet`, we have two cases: either `b` is in `reachSet R start n` or `b` is in the filter of elements reachable from `reachSet R start n` in one step.
    have h_cases : b ∈ reachSet R start n ∨ ∃ a ∈ reachSet R start n, R a b := by
      exact Finset.mem_union.mp ( hb ) |> Or.imp id fun h => by aesop;
    exact h_cases.elim ( fun h => ih h ) fun ⟨ a, ha, hab ⟩ => ReflTransGen.tail ( ih ha ) hab

/-
One-step reachable elements are added by `stepClosure`.
-/
lemma mem_stepClosure_of_R {S : Finset α} {a b : α}
    (ha : a ∈ S) (hab : R a b) : b ∈ stepClosure R S := by
  unfold stepClosure; aesop;

/-
If `reachSet` doesn't grow in one step, it has reached the fixpoint for all future steps.
-/
lemma reachSet_fixpoint (start : α) {n : ℕ}
    (hfix : reachSet R start n = reachSet R start (n + 1)) (m : ℕ) :
    reachSet R start n = reachSet R start (n + m) := by
  induction' m with m ih;
  · rfl;
  · grind +locals

/-
`reachSet` stabilizes after at most `Fintype.card α` steps.
    This is because at each step, either the set grows by at least one element
    or it has reached the fixpoint. Since the set is bounded by `Fintype.card α`,
    it can grow at most `Fintype.card α - 1` times.
-/
lemma reachSet_stabilizes (start : α) :
    reachSet R start (Fintype.card α) = reachSet R start (Fintype.card α + 1) := by
  by_contra h_neq;
  -- By induction on $k$, we can show that $|reachSet R start k| \geq k + 1$ for all $k \leq Fintype.card α$.
  have h_card_ge_add_one : ∀ k ≤ Fintype.card α, (reachSet R start k).card ≥ k + 1 := by
    intro k hk; induction' k with k ih <;> simp_all +decide [ Nat.succ_le_succ_iff ] ;
    · exact ⟨ start, start_mem_reachSet R start 0 ⟩;
    · have h_card_growth : (reachSet R start (k + 1)).card > (reachSet R start k).card := by
        by_cases h_eq : reachSet R start (k + 1) = reachSet R start k;
        · have h_card_growth : ∀ m ≥ k + 1, reachSet R start m = reachSet R start (k + 1) := by
            intro m hm; induction hm <;> simp_all +decide [ reachSet ] ;
          grind +ring;
        · exact Finset.card_lt_card ( lt_of_le_of_ne ( reachSet_mono R start k ) ( Ne.symm h_eq ) );
      linarith [ ih ( Nat.le_of_lt hk ) ];
  exact absurd ( h_card_ge_add_one ( Fintype.card α ) le_rfl ) ( by linarith [ show Finset.card ( reachSet R start ( Fintype.card α ) ) ≤ Fintype.card α from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ] )

/-
`ReflTransGen R start b` implies `b ∈ reachSet R start n` for some `n`.
-/
lemma mem_reachSet_of_ReflTransGen {start b : α}
    (h : ReflTransGen R start b) : ∃ n, b ∈ reachSet R start n := by
  induction h;
  · exact ⟨ 0, start_mem_reachSet R start 0 ⟩;
  · rename_i b c hb hc ih;
    obtain ⟨ n, hn ⟩ := ih;
    exact ⟨ n + 1, by exact Finset.mem_union_right _ <| Finset.mem_filter.mpr ⟨ Finset.mem_univ _, b, hn, hc ⟩ ⟩

/-- Full characterization: `b ∈ reachSet R start (Fintype.card α) ↔ ReflTransGen R start b`. -/
lemma mem_reachSet_iff_ReflTransGen (start b : α) :
    b ∈ reachSet R start (Fintype.card α) ↔ ReflTransGen R start b := by
  constructor
  · exact ReflTransGen_of_mem_reachSet R start (Fintype.card α)
  · intro h
    obtain ⟨n, hn⟩ := mem_reachSet_of_ReflTransGen R h
    by_cases hle : n ≤ Fintype.card α
    · exact reachSet_mono_of_le R start hle hn
    · push_neg at hle
      have hstab := reachSet_stabilizes R start
      have hfix : ∀ m, reachSet R start (Fintype.card α) = reachSet R start (Fintype.card α + m) :=
        reachSet_fixpoint R start hstab
      rw [hfix (n - Fintype.card α)]
      convert hn using 2
      omega

/-- `ReflTransGen R a b` is decidable on a finite type with a decidable relation. -/
noncomputable instance ReflTransGen_decidable_fintype (a b : α) :
    Decidable (ReflTransGen R a b) :=
  decidable_of_iff (b ∈ reachSet R a (Fintype.card α))
    (mem_reachSet_iff_ReflTransGen R a b)

end Reachability

/-! ## Restricting CS_transforms to bounded-length forms -/

/-- `CS_transforms` restricted to sentential forms of bounded length. -/
def CS_transforms_bounded (g : CS_grammar T) (bound : ℕ)
    (w₁ w₂ : {l : List (symbol T g.nt) // l.length ≤ bound}) : Prop :=
  CS_transforms g w₁.val w₂.val

/-
Decidability of `CS_transforms` for concrete sentential forms.
-/
noncomputable instance decidable_CS_transforms [DecidableEq T] (g : CS_grammar T) [DecidableEq g.nt]
    (w₁ w₂ : List (symbol T g.nt)) : Decidable (CS_transforms g w₁ w₂) := by
  unfold CS_transforms
  apply decidable_of_iff
    (∃ r ∈ g.rules, ∃ i : Fin (w₁.length + 1),
      let pattern := r.context_left ++ [symbol.nonterminal r.input_nonterminal] ++ r.context_right
      (w₁.drop i.val).take pattern.length = pattern ∧
      w₂ = w₁.take i.val ++ r.context_left ++ r.output_string ++ r.context_right ++
        w₁.drop (i.val + pattern.length))
  constructor;
  · simp +zetaDelta at *;
    intro r hr i hi hw₂;
    refine' ⟨ r, hr, w₁.take i, w₁.drop ( i + ( r.context_left.length + ( r.context_right.length + 1 ) ) ), _, _ ⟩ <;> simp_all +decide [ ← List.append_assoc ];
    have := List.take_append_drop ( r.context_left.length + ( r.context_right.length + 1 ) ) ( List.drop ( i : ℕ ) w₁ ) ; simp_all +decide [ List.drop_append ] ;
  · rintro ⟨ r, u, v, hr, rfl, rfl ⟩;
    refine' ⟨ r, hr, ⟨ u.length, _ ⟩, _, _ ⟩ <;> simp +decide [ add_assoc, List.take_append, List.drop_append ];
    simp +arith +decide [ List.drop_eq_nil_of_le ]

/-- Decidability of the bounded transform relation. -/
noncomputable instance decidable_CS_transforms_bounded [DecidableEq T]
    (g : CS_grammar T) [DecidableEq g.nt] (bound : ℕ)
    (w₁ w₂ : {l : List (symbol T g.nt) // l.length ≤ bound}) :
    Decidable (CS_transforms_bounded g bound w₁ w₂) :=
  decidable_CS_transforms g w₁.val w₂.val

/-! ## Main equivalence -/

/-
For a non-contracting grammar, `CS_derives g w₁ w₂` with `w₁.length ≤ w₂.length ≤ bound`
    is equivalent to `ReflTransGen (CS_transforms_bounded g bound)` between the corresponding
    bounded words.
-/
lemma CS_derives_iff_bounded [DecidableEq T] (g : CS_grammar T) [DecidableEq g.nt]
    (w₁ w₂ : List (symbol T g.nt))
    (h₁ : w₁.length ≤ w₂.length)
    (h₂ : w₂.length ≤ bound) :
    CS_derives g w₁ w₂ ↔
      ReflTransGen (CS_transforms_bounded g bound)
        ⟨w₁, le_trans h₁ h₂⟩ ⟨w₂, h₂⟩ := by
  constructor <;> intro h;
  · induction h;
    · rfl;
    · rename_i b c hb hc ih;
      refine' ih _ _ |> fun h => h.trans ( _ );
      exact CS_derives_length_le g hb;
      exact le_trans ( CS_transforms_length_le g hc ) h₂
      generalize_proofs at *;
      exact .single hc;
  · -- By definition of `ReflTransGen`, we can construct a sequence of transformations from `w₁` to `w₂`.
    have h_seq : ∀ {w₁ w₂ : {l : List (symbol T g.nt) // l.length ≤ bound}}, ReflTransGen (CS_transforms_bounded g bound) w₁ w₂ → CS_derives g w₁.val w₂.val := by
      intro w₁ w₂ h
      induction' h with w₁ w₂ h₁ h₂ ih;
      · exact CS_deri_self;
      · exact CS_deri_of_deri_tran ih h₂;
    exact h_seq h

/-! ## Main theorem -/

/-- Membership in a non-contracting context-sensitive grammar is decidable.
    This is the version with an explicit `CSG_noncontracting` hypothesis. -/
noncomputable def CS_membership_decidable
    [Fintype T] [DecidableEq T]
    (g : CS_grammar T) [Fintype g.nt] [DecidableEq g.nt]
    (w : List T) : Decidable (w ∈ CS_language g) := by
  by_cases hw : w = []
  · -- Empty word case: not in language of non-contracting grammar
    subst hw
    exact isFalse (empty_not_in_CS_language g)
  · -- Non-empty word case: reduce to bounded reachability
    change Decidable (CS_derives g [symbol.nonterminal g.initial]
      (w.map (symbol.terminal (N := g.nt))))
    rw [CS_derives_iff_bounded g
      [symbol.nonterminal g.initial] (w.map (symbol.terminal (N := g.nt)))
      (by simp [List.length_map]; exact List.length_pos_of_ne_nil hw) (le_refl _)]
    exact ReflTransGen_decidable_fintype
      (CS_transforms_bounded g (w.map (symbol.terminal (N := g.nt))).length) _ _
