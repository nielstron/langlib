/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Langlib.Classes.Linear.Definition
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Basics.Inclusion
import Langlib.Classes.Regular.Closure.Bijection
import Langlib.Classes.ContextFree.Examples.AnBn
import Langlib.Grammars.RightRegular.UnrestrictedCharacterization

/-! # Linear Language Inclusions

This file shows that the class of linear languages sits between
the regular and the context-free languages, with both inclusions being strict.

## Main results

- `Linear_subclass_CF`          — `Linear ⊆ CF`
- `RG_subclass_Linear`          — `RG ⊆ Linear`
- `anbn_is_Linear`              — `{aⁿbⁿ}` is a linear language
- `RG_strict_subclass_Linear`   — `RG ⊊ Linear`  (over any nontrivial alphabet)
-/

open Language List Relation Classical

noncomputable section

variable {T : Type}

-- ============================================================================
-- Part 1: Linear ⊆ CF
-- ============================================================================

/-- A linear output is trivially a valid context-free output (no additional restriction). -/
theorem grammar_context_free_of_linear {g : grammar T}
    (hg : grammar_linear g) : grammar_context_free g := by
  intro r hr
  exact ⟨(hg r hr).1, (hg r hr).2.1⟩

/-- Every linear language is context-free. -/
theorem is_CF_of_is_Linear {L : Language T} (h : is_Linear L) : is_CF L := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g, grammar_context_free_of_linear hg, rfl⟩

/-- The class of linear languages is a subclass of the context-free languages. -/
theorem Linear_subclass_CF :
    (Linear : Set (Language T)) ⊆ (CF : Set (Language T)) := by
  intro L hL
  exact is_CF_of_is_Linear hL

-- ============================================================================
-- Part 2: RG ⊆ Linear
-- ============================================================================

/-- A right-regular output has linear form. -/
theorem linear_output_of_right_regular {N : Type} {s : List (symbol T N)}
    (h : right_regular_output s) : linear_output s := by
  rcases h with ⟨a, B, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact Or.inr ⟨[a], B, [], by simp⟩
  · exact Or.inl (by intro x hx; simp at hx; exact ⟨a, hx⟩)
  · exact Or.inl (by simp)

/-- A right-regular grammar is linear. -/
theorem grammar_linear_of_right_regular {g : grammar T}
    (hg : grammar_right_regular g) : grammar_linear g := by
  intro r hr
  obtain ⟨h1, h2, h3⟩ := hg r hr
  exact ⟨h1, h2, linear_output_of_right_regular h3⟩

/-- Every regular language is linear. -/
theorem is_Linear_of_is_RG {L : Language T} (h : is_RG L) : is_Linear L := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g, grammar_linear_of_right_regular hg, rfl⟩

/-- The class of regular languages is a subclass of the linear languages. -/
theorem RG_subclass_Linear :
    (RG : Set (Language T)) ⊆ (Linear : Set (Language T)) := by
  intro L hL
  exact is_Linear_of_is_RG hL

-- ============================================================================
-- Part 3: aⁿbⁿ is linear  (witness for RG ⊊ Linear)
-- ============================================================================

/-- An unrestricted grammar for the language `{aⁿbⁿ | n ∈ ℕ}` with linear rules.
Rules:
  S → aSb   (i.e., [] S [] → [a, S, b])
  S → ε     (i.e., [] S [] → [])
-/
def linear_grammar_anbn : grammar Bool where
  nt := Unit
  initial := ()
  rules := [
    ⟨[], (), [], [symbol.terminal false, symbol.nonterminal (), symbol.terminal true]⟩,
    ⟨[], (), [], []⟩
  ]

/-- The grammar `linear_grammar_anbn` is linear. -/
theorem linear_grammar_anbn_is_linear :
    grammar_linear linear_grammar_anbn := by
  intro r hr
  simp [linear_grammar_anbn] at hr
  rcases hr with rfl | rfl <;> refine ⟨rfl, rfl, ?_⟩
  · exact Or.inr ⟨[false], (), [true], by simp⟩
  · exact Or.inl (by simp)

/-- Derivation in `linear_grammar_anbn` can produce `aⁿSbⁿ`. -/
lemma linear_grammar_anbn_derives_n (n : ℕ) :
    grammar_derives linear_grammar_anbn
      [symbol.nonterminal ()]
      (List.replicate n (symbol.terminal false) ++
        [symbol.nonterminal ()] ++
        List.replicate n (symbol.terminal true)) := by
  induction n with
  | zero => simp; exact ReflTransGen.refl
  | succ n ih =>
    apply ReflTransGen.trans ih
    apply ReflTransGen.single
    refine ⟨⟨[], (), [], [symbol.terminal false, symbol.nonterminal (), symbol.terminal true]⟩,
      ?_, List.replicate n (symbol.terminal false), List.replicate n (symbol.terminal true), ?_, ?_⟩
    · simp [linear_grammar_anbn]
    · simp
    · simp [List.replicate_succ']
      rw [← List.replicate_succ, ← List.replicate_succ']

/-- Derivation in `linear_grammar_anbn`: apply ε-rule to get `aⁿbⁿ`. -/
lemma linear_grammar_anbn_derives_final (n : ℕ) :
    grammar_derives linear_grammar_anbn
      (List.replicate n (symbol.terminal false) ++
        [symbol.nonterminal ()] ++
        List.replicate n (symbol.terminal true))
      (List.replicate n (symbol.terminal false) ++
        List.replicate n (symbol.terminal true)) := by
  apply ReflTransGen.single
  refine ⟨⟨[], (), [], []⟩, ?_,
    List.replicate n (symbol.terminal false),
    List.replicate n (symbol.terminal true), ?_, ?_⟩
  · simp [linear_grammar_anbn]
  · simp
  · simp

/-- Every word in `anbn` is generated by `linear_grammar_anbn`. -/
lemma anbn_sub_linear_grammar_anbn_language :
    ∀ w, w ∈ anbn → w ∈ grammar_language linear_grammar_anbn := by
  intro w hw
  obtain ⟨n, rfl⟩ := hw
  show grammar_generates linear_grammar_anbn _
  unfold grammar_generates
  have h1 := linear_grammar_anbn_derives_n n
  have h2 := linear_grammar_anbn_derives_final n
  apply ReflTransGen.trans h1
  simp only [List.map_append, List.map_replicate]
  exact h2

/-- A sentential form of `linear_grammar_anbn` is either `aⁿSbⁿ` or `aⁿbⁿ`. -/
private def anbn_sentential (w : List (symbol Bool Unit)) : Prop :=
  (∃ n : ℕ, w = List.replicate n (symbol.terminal false) ++
    [symbol.nonterminal ()] ++
    List.replicate n (symbol.terminal true)) ∨
  (∃ n : ℕ, w = List.map symbol.terminal
    (List.replicate n false ++ List.replicate n true))

/-
One step of derivation preserves `anbn_sentential` form.
-/
private lemma anbn_sentential_step (w w' : List (symbol Bool Unit))
    (hw : anbn_sentential w) (ht : grammar_transforms linear_grammar_anbn w w') :
    anbn_sentential w' := by
      rcases ht with ⟨ r, hr, u, v, hw₁, hw₂ ⟩;
      rcases hw with ( ⟨ n, rfl ⟩ | ⟨ n, rfl ⟩ ) <;> simp_all +decide [ List.append_assoc ];
      · rcases r with ⟨ L, N, R, S ⟩ ; simp_all +decide [ linear_grammar_anbn ];
        rcases hr with ( ⟨ rfl, rfl, rfl, rfl ⟩ | ⟨ rfl, rfl, rfl, rfl ⟩ ) <;> simp_all +decide [ anbn_sentential ];
        · rw [ List.append_eq_append_iff ] at hw₁;
          rcases hw₁ with ( ⟨ as, rfl, h ⟩ | ⟨ bs, h₁, h₂ ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
          · rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.replicate ];
            · refine' Or.inl ⟨ n + 1, Or.inl ⟨ [ symbol.terminal false ], _, _ ⟩ ⟩ <;> simp +decide [ *, List.replicate ];
              exact Nat.recOn n ( by trivial ) fun n ih => by simp +decide [ List.replicate ] at * ; aesop;
            · replace h := congr_arg List.toFinset h.2; rw [ Finset.ext_iff ] at h; specialize h ( symbol.nonterminal () ) ; aesop;
          · rcases bs with ( _ | ⟨ a, bs ⟩ ) <;> simp_all +decide [ List.replicate ];
            · refine Or.inl ⟨ n + 1, ?_ ⟩ ; simp_all +decide [ List.replicate ];
              exact Or.inl ⟨ [ symbol.terminal false ], by rw [ ← h₁ ] ; exact Nat.recOn n ( by simp +decide ) fun n ihn => by simp +decide [ List.replicate ] at * ; aesop ⟩;
            · replace h₁ := congr_arg List.toFinset h₁ ; rw [ Finset.ext_iff ] at h₁ ; specialize h₁ a ; aesop;
        · rw [ List.append_eq_append_iff ] at hw₁;
          rcases hw₁ with ( ⟨ as, rfl, h ⟩ | ⟨ bs, h₁, h₂ ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
          · rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.replicate ];
            · exact Or.inr ⟨ n, Or.inl ⟨ [ ], by simp +decide [ h.symm ] ⟩ ⟩;
            · replace h := congr_arg List.toFinset h.2; rw [ Finset.ext_iff ] at h; specialize h ( symbol.nonterminal () ) ; aesop;
          · rcases bs with ( _ | ⟨ a, bs ⟩ ) <;> simp_all +decide [ List.append_assoc ];
            · exact Or.inr ⟨ n, Or.inl ⟨ [ ], by aesop ⟩ ⟩;
            · replace h₁ := congr_arg List.toFinset h₁ ; rw [ Finset.ext_iff ] at h₁ ; specialize h₁ a ; aesop;
      · replace hw₁ := congr_arg List.toFinset hw₁ ; rw [ Finset.ext_iff ] at hw₁ ; specialize hw₁ ( symbol.nonterminal r.input_N ) ; aesop;

/-- Derivation preserves `anbn_sentential` form. -/
private lemma anbn_sentential_of_derives (w : List (symbol Bool Unit))
    (hd : grammar_derives linear_grammar_anbn [symbol.nonterminal ()] w) :
    anbn_sentential w := by
  induction hd with
  | refl => exact Or.inl ⟨0, by simp⟩
  | tail _ ht ih => exact anbn_sentential_step _ _ ih ht

/-- Every word generated by `linear_grammar_anbn` is in `anbn`. -/
lemma linear_grammar_anbn_language_sub_anbn :
    ∀ w, w ∈ grammar_language linear_grammar_anbn → w ∈ anbn := by
  intro w hw
  have hsf := anbn_sentential_of_derives (List.map symbol.terminal w) hw
  rcases hsf with ⟨n, hn⟩ | ⟨n, hn⟩
  · exfalso
    have : symbol.nonterminal () ∈ List.map symbol.terminal w := by
      rw [hn]; simp
    simp at this
  · have hinj : Function.Injective (symbol.terminal (T := Bool) (N := Unit)) := by
      intro a b h; cases h; rfl
    exact ⟨n, hinj.list_map hn⟩

/-- The grammar `linear_grammar_anbn` generates exactly `{aⁿbⁿ}`. -/
theorem linear_grammar_anbn_language :
    grammar_language linear_grammar_anbn = anbn := by
  ext w
  exact ⟨fun h => linear_grammar_anbn_language_sub_anbn w h,
         fun h => anbn_sub_linear_grammar_anbn_language w h⟩

/-- The language `{aⁿbⁿ}` is linear. -/
theorem anbn_is_Linear : is_Linear anbn :=
  ⟨linear_grammar_anbn, linear_grammar_anbn_is_linear,
   linear_grammar_anbn_language⟩

-- ============================================================================
-- Part 4: RG ⊊ Linear  (strict inclusion)
-- ============================================================================

/-- There exists a linear language that is not regular. -/
theorem exists_Linear_not_regular : ∃ L : Language Bool, is_Linear L ∧ ¬ L.IsRegular :=
  ⟨anbn, anbn_is_Linear, anbn_not_isRegular⟩

private lemma map_anbn_is_Linear (f : Bool → T) (hf : Function.Injective f) :
    is_Linear (Language.map f anbn) := by
      refine' ⟨ _, _, _ ⟩;
      exact ⟨ Unit, (), [ ⟨ [ ], (), [ ], [ symbol.terminal ( f false ), symbol.nonterminal (), symbol.terminal ( f true ) ] ⟩, ⟨ [ ], (), [ ], [ ] ⟩ ] ⟩;
      · simp +decide [ grammar_linear ];
        exact ⟨ Or.inr ⟨ [ f false ], (), [ f true ], rfl ⟩, Or.inl fun x hx => by aesop ⟩;
      · ext w;
        constructor;
        · intro hw;
          -- By definition of grammar_derives, we know that there exists a sequence of derivations from the initial state to the final state.
          have h_deriv : ∀ w, grammar_derives { nt := Unit, initial := (), rules := [{ input_L := [], input_N := (), input_R := [], output_string := [symbol.terminal (f false), symbol.nonterminal (), symbol.terminal (f true)] }, { input_L := [], input_N := (), input_R := [], output_string := [] }] } [symbol.nonterminal ()] w → ∃ n : ℕ, w = List.replicate n (symbol.terminal (f false)) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal (f true)) ∨ w = List.map symbol.terminal (List.replicate n (f false) ++ List.replicate n (f true)) := by
                                                                                                                                                                                                                                        intro w hw
                                                                                                                                                                                                                                        induction' hw with w' hw' ih;
                                                                                                                                                                                                                                        · exact ⟨ 0, by simp +decide ⟩;
                                                                                                                                                                                                                                        · rename_i h₁ h₂ h₃;
                                                                                                                                                                                                                                          rcases h₃ with ⟨ n, rfl | rfl ⟩ <;> simp_all +decide [ grammar_transforms ];
                                                                                                                                                                                                                                          · rcases h₂ with ( ⟨ u, v, h₁, rfl ⟩ | ⟨ u, v, h₁, rfl ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
                                                                                                                                                                                                                                            · rcases h₁ with ( ⟨ as, rfl, h₁ ⟩ | ⟨ bs, h₁, h₂ ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
                                                                                                                                                                                                                                              · rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.replicate ];
                                                                                                                                                                                                                                                · use n + 1;
                                                                                                                                                                                                                                                  simp +decide [ List.replicate_add, h₁.symm ];
                                                                                                                                                                                                                                                  exact Or.inl ( by exact Nat.recOn n ( by simp +decide ) fun n ihn => by simp +decide [ List.replicate ] at ihn ⊢; aesop );
                                                                                                                                                                                                                                                · replace h₁ := congr_arg List.toFinset h₁.2; rw [ Finset.ext_iff ] at h₁; specialize h₁ ( symbol.nonterminal () ) ; aesop;
                                                                                                                                                                                                                                              · rcases bs with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
                                                                                                                                                                                                                                                · use n + 1;
                                                                                                                                                                                                                                                  simp +decide [ ← h₁, List.replicate_add ];
                                                                                                                                                                                                                                                  exact Or.inl ( by exact Nat.recOn n ( by simp +decide ) fun n ihn => by simp +decide [ List.replicate ] at ihn ⊢; aesop );
                                                                                                                                                                                                                                                · replace h₁ := congr_arg List.toFinset h₁; rw [ Finset.ext_iff ] at h₁; specialize h₁ b; aesop;
                                                                                                                                                                                                                                            · rcases h₁ with ( ⟨ as, rfl, h₁ ⟩ | ⟨ bs, h₁, h₂ ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
                                                                                                                                                                                                                                              · rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
                                                                                                                                                                                                                                                · exact ⟨ n, Or.inr <| Or.inr <| ⟨ [ ], by aesop ⟩ ⟩;
                                                                                                                                                                                                                                                · replace h₁ := congr_arg List.toFinset h₁.2; rw [ Finset.ext_iff ] at h₁; specialize h₁ ( symbol.nonterminal () ) ; aesop;
                                                                                                                                                                                                                                              · rcases bs with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
                                                                                                                                                                                                                                                · exact ⟨ n, Or.inr <| Or.inl ⟨ [ ], by aesop ⟩ ⟩;
                                                                                                                                                                                                                                                · replace h₁ := congr_arg List.toFinset h₁; rw [ Finset.ext_iff ] at h₁; specialize h₁ b; aesop;
                                                                                                                                                                                                                                          · rcases h₂ with ( ⟨ u, v, h₁, rfl ⟩ | ⟨ u, v, h₁, rfl ⟩ ) <;> simp_all +decide [ List.replicate ];
                                                                                                                                                                                                                                            · replace h₁ := congr_arg List.toFinset h₁ ; rw [ Finset.ext_iff ] at h₁ ; specialize h₁ ( symbol.nonterminal () ) ; aesop;
                                                                                                                                                                                                                                            · replace h₁ := congr_arg List.toFinset h₁ ; rw [ Finset.ext_iff ] at h₁ ; specialize h₁ ( symbol.nonterminal () ) ; aesop;
          obtain ⟨ n, hn ⟩ := h_deriv _ hw;
          rcases hn with ( hn | hn );
          · replace hn := congr_arg List.toFinset hn; rw [ Finset.ext_iff ] at hn; specialize hn ( symbol.nonterminal () ) ; aesop;
          · use List.replicate n false ++ List.replicate n true;
            exact ⟨ ⟨ n, rfl ⟩, by simpa using List.map_injective_iff.mpr ( show Function.Injective ( fun x : T => symbol.terminal x ) from fun x y hxy => by simpa using hxy ) hn.symm ⟩;
        · rintro ⟨ v, ⟨ n, rfl ⟩, rfl ⟩;
          -- By definition of `grammar_derives`, we need to show that there exists a derivation from the initial state to the final state.
          have h_derives : grammar_derives { nt := Unit, initial := (), rules := [{ input_L := [], input_N := (), input_R := [], output_string := [symbol.terminal (f false), symbol.nonterminal (), symbol.terminal (f true)] }, { input_L := [], input_N := (), input_R := [], output_string := [] }] } [symbol.nonterminal ()] (List.replicate n (symbol.terminal (f false)) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal (f true))) := by
                                                                                                                                                                                                                                      induction' n with n ih;
                                                                                                                                                                                                                                      · constructor;
                                                                                                                                                                                                                                      · -- Apply the first rule to the nonterminal in the middle of the string.
                                                                                                                                                                                                                                        have h_step : grammar_transforms { nt := Unit, initial := (), rules := [{ input_L := [], input_N := (), input_R := [], output_string := [symbol.terminal (f false), symbol.nonterminal (), symbol.terminal (f true)] }, { input_L := [], input_N := (), input_R := [], output_string := [] }] } (replicate n (symbol.terminal (f false)) ++ [symbol.nonterminal ()] ++ replicate n (symbol.terminal (f true))) (replicate n (symbol.terminal (f false)) ++ [symbol.terminal (f false), symbol.nonterminal (), symbol.terminal (f true)] ++ replicate n (symbol.terminal (f true))) := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    use ⟨ [], (), [], [ symbol.terminal ( f false ), symbol.nonterminal (), symbol.terminal ( f true ) ] ⟩;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    exact ⟨ by simp +decide, replicate n ( symbol.terminal ( f false ) ), replicate n ( symbol.terminal ( f true ) ), by simp +decide, by simp +decide ⟩;
                                                                                                                                                                                                                                        convert ih.tail h_step using 1 ; simp +decide [ List.replicate_add ];
                                                                                                                                                                                                                                        exact Nat.recOn n rfl fun n ih => by rw [ replicate_succ' ] ; aesop;
          convert h_derives.tail _;
          use ⟨ [ ], (), [ ], [ ] ⟩ ; aesop

/-- Regular languages form a strict subclass of linear languages over any
    nontrivial alphabet. -/
theorem RG_strict_subclass_Linear [Nontrivial T] :
    (RG : Set (Language T)) ⊂ (Linear : Set (Language T)) := by
  refine ⟨RG_subclass_Linear, ?_⟩
  intro hLinearsubsetRG
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  let f : Bool → T := fun x => if x then b else a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> try rfl
    · simp [f] at hxy; exact False.elim (hab hxy)
    · simp [f] at hxy; exact False.elim (hab hxy.symm)
  have hLinear : Language.map f anbn ∈ (Linear : Set (Language T)) :=
    map_anbn_is_Linear f hf
  have hRG : Language.map f anbn ∈ (RG : Set (Language T)) := hLinearsubsetRG hLinear
  have hreg : (Language.map f anbn).IsRegular := isRegular_of_is_RG hRG
  exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf hreg)

end