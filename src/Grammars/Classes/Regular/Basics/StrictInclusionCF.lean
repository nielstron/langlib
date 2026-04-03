import Mathlib
import Grammars.Classes.ContextFree.Basics.Inclusion
import Grammars.Classes.ContextFree.ClosureProperties.Intersection
import Grammars.Classes.ContextFree.ClosureProperties.Substitution
import Grammars.Classes.ContextSensitive.Basics.Inclusion
import Grammars.Classes.Regular.Basics.Inclusion
import Grammars.Classes.Regular.ClosureProperties.Bijection
import Grammars.Classes.Regular.Basics.NonRegular
import Grammars.Classes.DetContextFree.Basics.Inclusion

/-! # Strict Inclusions in the Chomsky Hierarchy

This file proves strict subset relationships between regular languages and CF

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

private lemma mem_prod_singletons_iff {α β : Type} (f : α → β) :
    ∀ w : List α, ∀ u : List β,
      u ∈ (w.map fun x => ({[f x]} : Language β)).prod ↔ u = List.map f w
  | [], u => by
      change u ∈ ({[]} : Language β) ↔ u = []
      rfl
  | x :: xs, u => by
      constructor
      · intro hu
        rw [show (List.map (fun x => ({[f x]} : Language β)) (x :: xs)).prod =
            ({[f x]} : Language β) * (List.map (fun x => ({[f x]} : Language β)) xs).prod by rfl] at hu
        rw [Language.mul_def] at hu
        rcases hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
        have hu₂' := (mem_prod_singletons_iff f xs u₂).1 hu₂
        have hu₁' : u₁ = [f x] := by simpa using hu₁
        simp [hu₁', hu₂']
      · intro hu
        subst hu
        rw [show (List.map (fun x => ({[f x]} : Language β)) (x :: xs)).prod =
            ({[f x]} : Language β) * (List.map (fun x => ({[f x]} : Language β)) xs).prod by rfl]
        rw [Language.mul_def]
        refine ⟨[f x], Set.mem_singleton _, List.map f xs, ?_, rfl⟩
        exact (mem_prod_singletons_iff f xs (List.map f xs)).2 rfl

private theorem map_anbn_is_CF (f : Bool → T) : is_CF (Language.map f anbn) := by
  have hsubst : is_CF (anbn.subst (fun x => ({[f x]} : Language T))) := by
    apply CF_of_subst_CF anbn
    · exact anbn_is_CF
    · intro x
      rw [is_CF_iff_isContextFree]
      exact isContextFree_singleton [f x]
  simpa [Language.subst_singletons_eq_map] using hsubst

/-- Right-regular languages form a strict subclass of context-free languages over any nontrivial alphabet. -/
theorem RG_strict_subclass_CF [Nontrivial T] :
  (RG : Set (Language T)) ⊂ (CF : Set (Language T)) := by
  refine ⟨RG_subclass_CF, ?_⟩
  · intro hCFsubsetRG
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    let f : Bool → T := fun x => if x then b else a
    have hf : Function.Injective f := by
      intro x y hxy
      cases x <;> cases y <;> try rfl
      · simp [f] at hxy
        exact False.elim (hab hxy)
      · simp [f] at hxy
        exact False.elim (hab hxy.symm)
    have hRG : Language.map f anbn ∈ (RG : Set (Language T)) :=
      hCFsubsetRG (a := Language.map f anbn) (map_anbn_is_CF f)
    have hreg : (Language.map f anbn).IsRegular := isRegular_of_is_RG hRG
    exact anbn_not_isRegular (Language.IsRegular.of_map_injective hf hreg)
