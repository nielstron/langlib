import Mathlib
import Langlib.Automata.FiniteState.Equivalence.RegularDFAEquiv
import Langlib.Utilities.Tactics
import Langlib.Classes.Linear.Definition
import Langlib.Classes.Linear.Examples.AnBn
import Langlib.Classes.Regular.Inclusion.Linear
import Langlib.Classes.Regular.Basics.NonRegular
import Langlib.Classes.Regular.Closure.Bijection

/-! # RG ⊊ Linear

This file uses the example language `{aⁿbⁿ}` to show that regular languages
form a strict subclass of linear languages.

## Main results

- `exists_Linear_not_regular` — There exists a linear language that is not regular.
- `RG_strict_subclass_Linear` — Right-regular languages form a strict subclass of linear languages.
-/

open Language List Relation Classical

noncomputable section

variable {T : Type}

/-- There exists a linear language that is not regular. -/
theorem exists_Linear_not_regular : ∃ L : Language Bool, is_Linear L ∧ ¬ L.IsRegular :=
  ⟨anbn, anbn_is_Linear, anbn_not_isRegular⟩

private lemma map_anbn_is_Linear (f : Bool → T) (_hf : Function.Injective f) :
    is_Linear (Language.map f anbn) := by
      refine' ⟨ _, _, _ ⟩;
      exact ⟨ Unit, (), [ ⟨ [ ], (), [ ], [ symbol.terminal ( f false ), symbol.nonterminal (), symbol.terminal ( f true ) ] ⟩, ⟨ [ ], (), [ ], [ ] ⟩ ] ⟩;
      · simp +decide [ grammar_linear ];
        exact ⟨ Or.inr ⟨ [ f false ], (), [ f true ], rfl ⟩, Or.inl fun x hx => by aesop ⟩;
      · ext w;
        constructor;
        · intro hw;
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
                                                                                                                                                                                                                                                · no_nonterminal (b) at h₁
                                                                                                                                                                                                                                            · rcases h₁ with ( ⟨ as, rfl, h₁ ⟩ | ⟨ bs, h₁, h₂ ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
                                                                                                                                                                                                                                              · rcases as with ( _ | ⟨ a, as ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
                                                                                                                                                                                                                                                · exact ⟨ n, Or.inr <| Or.inr <| ⟨ [ ], by aesop ⟩ ⟩;
                                                                                                                                                                                                                                                · replace h₁ := congr_arg List.toFinset h₁.2; rw [ Finset.ext_iff ] at h₁; specialize h₁ ( symbol.nonterminal () ) ; aesop;
                                                                                                                                                                                                                                              · rcases bs with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide [ List.append_eq_append_iff ];
                                                                                                                                                                                                                                                · exact ⟨ n, Or.inr <| Or.inl ⟨ [ ], by aesop ⟩ ⟩;
                                                                                                                                                                                                                                                · no_nonterminal (b) at h₁
                                                                                                                                                                                                                                          · rcases h₂ with ( ⟨ u, v, h₁, rfl ⟩ | ⟨ u, v, h₁, rfl ⟩ ) <;> simp_all +decide [ List.replicate ];
                                                                                                                                                                                                                                            · no_nonterminal (symbol.nonterminal ())
                                                                                                                                                                                                                                            · no_nonterminal (symbol.nonterminal ())
          obtain ⟨ n, hn ⟩ := h_deriv _ hw;
          rcases hn with ( hn | hn );
          · no_nonterminal (symbol.nonterminal ())
          · use List.replicate n false ++ List.replicate n true;
            exact ⟨ ⟨ n, rfl ⟩, by simpa using List.map_injective_iff.mpr ( show Function.Injective ( fun x : T => symbol.terminal x ) from fun x y hxy => by simpa using hxy ) hn.symm ⟩;
        · rintro ⟨ v, ⟨ n, rfl ⟩, rfl ⟩;
          have h_derives : grammar_derives { nt := Unit, initial := (), rules := [{ input_L := [], input_N := (), input_R := [], output_string := [symbol.terminal (f false), symbol.nonterminal (), symbol.terminal (f true)] }, { input_L := [], input_N := (), input_R := [], output_string := [] }] } [symbol.nonterminal ()] (List.replicate n (symbol.terminal (f false)) ++ [symbol.nonterminal ()] ++ List.replicate n (symbol.terminal (f true))) := by
                                                                                                                                                                                                                                      induction' n with n ih;
                                                                                                                                                                                                                                      · constructor;
                                                                                                                                                                                                                                      · have h_step : grammar_transforms { nt := Unit, initial := (), rules := [{ input_L := [], input_N := (), input_R := [], output_string := [symbol.terminal (f false), symbol.nonterminal (), symbol.terminal (f true)] }, { input_L := [], input_N := (), input_R := [], output_string := [] }] } (replicate n (symbol.terminal (f false)) ++ [symbol.nonterminal ()] ++ replicate n (symbol.terminal (f true))) (replicate n (symbol.terminal (f false)) ++ [symbol.terminal (f false), symbol.nonterminal (), symbol.terminal (f true)] ++ replicate n (symbol.terminal (f true))) := by
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    use ⟨ [], (), [], [ symbol.terminal ( f false ), symbol.nonterminal (), symbol.terminal ( f true ) ] ⟩;
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    exact ⟨ by simp +decide, replicate n ( symbol.terminal ( f false ) ), replicate n ( symbol.terminal ( f true ) ), by simp +decide, by simp +decide ⟩;
                                                                                                                                                                                                                                        convert ih.tail h_step using 1 ; simp +decide [ List.replicate_add ];
                                                                                                                                                                                                                                        exact Nat.recOn n rfl fun n ih => by rw [ replicate_succ' ] ; aesop;
          convert h_derives.tail _;
          use ⟨ [ ], (), [ ], [ ] ⟩ ; aesop

/-- Right-regular languages form a strict subclass of linear languages over any nontrivial alphabet. -/
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
