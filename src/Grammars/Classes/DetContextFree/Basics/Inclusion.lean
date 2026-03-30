/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Classes.DetContextFree.Basics.DCFL
import Grammars.Classes.DetContextFree.ClosureProperties.Complement

/-! # DCFLs are a strict subset of CFLs

This file shows that DCFLs are a subset of the CFLs
and that they are a strict subset

--/

-- ============================================================================
-- DCFL inclusion into CFL
-- ============================================================================

theorem is_CF_of_is_DCFL {T : Type} [Fintype T] {L : Language T} (h : is_DCFL L) : is_CF L := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  exact is_CF_of_is_PDA M.is_PDA_acceptsByFinalState


-- ============================================================================
-- The main result: CFL ⊋ DCFL (strict inclusion)
-- ============================================================================

/-- If every CFL (over a fixed finite alphabet `T`) were a DCFL, then every CFL's
    complement would also be a CFL. -/
theorem complement_CF_of_all_CF_DCFL {T : Type} [Fintype T]
    (h : ∀ L : Language T, is_CF L → is_DCFL L) :
    ∀ L : Language T, is_CF L → is_CF Lᶜ :=
  fun L hCF => is_CF_of_is_DCFL (is_DCFL_compl (h L hCF))

/-- `lang_eq_any ⊓ lang_any_eq = lang_eq_eq` -/
private lemma lang_intersection_eq :
    lang_eq_any ⊓ lang_any_eq = lang_eq_eq := by
  ext w
  exact ⟨lang_eq_eq_of_intersection, intersection_of_lang_eq_eq⟩

/-- CFL over Fin 3 is NOT closed under complement. This is a specialized version
    of `nnyCF_of_complement_CF` that works over a fixed alphabet. -/
private lemma not_complement_closed_Fin3 :
    ¬ (∀ L : Language (Fin 3), is_CF L → is_CF Lᶜ) := by
  intro h
  -- If CFL were closed under complement, then Lᶜ₁ and Lᶜ₂ are CFL
  have h1 : is_CF lang_eq_anyᶜ := h _ CF_lang_eq_any
  have h2 : is_CF lang_any_eqᶜ := h _ CF_lang_any_eq
  -- Their union is CFL
  have h_union : is_CF (lang_eq_anyᶜ + lang_any_eqᶜ) :=
    CF_of_CF_u_CF _ _ ⟨h1, h2⟩
  -- The complement of their union is CFL (by the hypothesis)
  have h_inter : is_CF (lang_eq_anyᶜ + lang_any_eqᶜ)ᶜ :=
    h _ h_union
  -- (L₁ᶜ ∪ L₂ᶜ)ᶜ = L₁ ∩ L₂
  have h_eq : (lang_eq_anyᶜ + lang_any_eqᶜ)ᶜ = lang_eq_any ⊓ lang_any_eq := by
    simp only [Language.add_def]; rw [Set.compl_union]; simp [compl_compl]; rfl
  rw [h_eq, lang_intersection_eq] at h_inter
  exact notCF_lang_eq_eq h_inter

/-- There exist context-free languages over `Fin 3` that are not deterministic
    context-free. This is the strict inclusion DCFL ⊊ CFL. -/
theorem exists_CF_not_DCFL : ∃ L : Language (Fin 3), is_CF L ∧ ¬ is_DCFL L := by
  by_contra h_all
  push_neg at h_all
  -- h_all : ∀ L : Language (Fin 3), is_CF L → is_DCFL L
  exact not_complement_closed_Fin3 (complement_CF_of_all_CF_DCFL h_all)

-- ============================================================================
-- Specific witness: lang_aibjck is CF but not DCFL
-- ============================================================================

-- ============================================================================
-- The explicit witness: {aⁱ bʲ cᵏ | i = j ∨ j = k}
-- ============================================================================

section explicit_witness

/-- The language `{aⁿ bⁿ cᵐ | n, m ∈ ℕ}` over `{0, 1, 2}` = `{a, b, c}`. -/
def lang_anbnck : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n 0 ++ List.replicate n 1 ++ List.replicate m 2

/-- The language `{aⁿ bᵐ cᵐ | n, m ∈ ℕ}` over `{0, 1, 2}` = `{a, b, c}`. -/
def lang_anbmcm : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n 0 ++ List.replicate m 1 ++ List.replicate m 2

/-- The language `{aⁱ bʲ cᵏ | i = j ∨ j = k}` over `{0, 1, 2}`.
    The standard explicit witness of a CFL that is not a DCFL. -/
def lang_aibjck : Language (Fin 3) :=
  fun w => ∃ i j k : ℕ,
    w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2 ∧ (i = j ∨ j = k)

/-- `lang_aibjck` equals the union of `lang_anbnck` and `lang_anbmcm`. -/
theorem lang_aibjck_eq_union : lang_aibjck = lang_anbnck + lang_anbmcm := by
  ext w
  simp only [Language.mem_add]
  constructor
  · rintro ⟨i, j, k, hw, hij | hjk⟩
    · left; exact ⟨i, k, hij ▸ hw⟩
    · right; exact ⟨i, j, hjk ▸ hw⟩
  · rintro (⟨n, m, hw⟩ | ⟨n, m, hw⟩)
    · exact ⟨n, n, m, hw, Or.inl rfl⟩
    · exact ⟨n, m, m, hw, Or.inr rfl⟩

/-- `{aⁿ bⁿ cᵐ}` is context-free. -/
theorem is_CF_lang_anbnck : is_CF lang_anbnck := by
  have h : lang_anbnck = lang_eq_any := by
    ext w; unfold lang_anbnck lang_eq_any a_ b_ c_; rfl
  rw [h]; exact CF_lang_eq_any

/-- `{aⁿ bᵐ cᵐ}` is context-free. -/
theorem is_CF_lang_anbmcm : is_CF lang_anbmcm := by
  have h : lang_anbmcm = lang_any_eq := by
    ext w; unfold lang_anbmcm lang_any_eq a_ b_ c_; rfl
  rw [h]; exact CF_lang_any_eq

/-- `{aⁱ bʲ cᵏ | i = j ∨ j = k}` is context-free. -/
theorem lang_aibjck_CFL : is_CF lang_aibjck := by
  rw [lang_aibjck_eq_union]
  exact CF_of_CF_u_CF _ _ ⟨is_CF_lang_anbnck, is_CF_lang_anbmcm⟩



/-- The language `{a^i b^j c^k | i ≠ j ∧ j ≠ k}` over `Fin 3`. -/
def lang_neq_neq : Language (Fin 3) :=
  fun w => ∃ i j k : ℕ,
    w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2 ∧ i ≠ j ∧ j ≠ k

/-- The regular language `a*b*c*` over `Fin 3`. -/
def lang_abc_star : Language (Fin 3) :=
  fun w => ∃ i j k : ℕ, w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2

/-- Decomposition of a word in `a*b*c*` into components is unique. -/
lemma abc_decomp_unique {i j k i' j' k' : ℕ}
    (h : List.replicate i (0 : Fin 3) ++ List.replicate j 1 ++ List.replicate k 2 =
         List.replicate i' 0 ++ List.replicate j' 1 ++ List.replicate k' 2) :
    i = i' ∧ j = j' ∧ k = k' := by
  have := congr_arg ( fun b => List.count 0 b ) h ; have := congr_arg ( fun b => List.count 1 b ) h ; have := congr_arg ( fun b => List.count 2 b ) h ; norm_num [ List.count_replicate ] at * ; aesop;

/-- The complement of `lang_aibjck` intersected with `a*b*c*` equals `lang_neq_neq`. -/
lemma compl_aibjck_inter_abc_eq_neq_neq :
    lang_aibjckᶜ ⊓ lang_abc_star = lang_neq_neq := by
  ext w
  simp
  constructor;
  · rintro ⟨ hw₁, ⟨ i, j, k, rfl ⟩ ⟩ ; exact ⟨ i, j, k, rfl, by intros hi; exact hw₁ ⟨ i, j, k, rfl, Or.inl hi ⟩, by intros hj; exact hw₁ ⟨ i, j, k, rfl, Or.inr hj ⟩ ⟩ ;
  · rintro ⟨ i, j, k, rfl, hij, hjk ⟩ ; exact ⟨ fun ⟨ i', j', k', h₁, h₂ ⟩ => by have := abc_decomp_unique h₁; aesop, i, j, k, rfl ⟩ ;

/-
PROVIDED SOLUTION
The maxHeartbeats is already set to 1600000 for this lemma. Construct a DFA (Fin 3) (Fin 4) for the language a*b*c*. Use `decide` or `fin_cases` for the finite case analyses. The DFA:
- step function: use a function that's written with pattern matching on Fin 4 and Fin 3 values
- start = 0
- accept = {0, 1, 2}

Then show it accepts exactly lang_abc_star. Use induction on the word, with reverseRecOn.

For the forward direction (DFA accepts → lang_abc_star): track what the DFA state tells us about the word. State 0 = only 0s seen. State 1 = 0s then 1s seen. State 2 = 0s then 1s then 2s seen. State 3 = invalid.

For the backward direction (lang_abc_star → DFA accepts): given w = rep i 0 ++ rep j 1 ++ rep k 2, compute the DFA run. State goes 0→...→0→1→...→1→2→...→2 which is accepting.

Key insight: define the DFA step as `![![0,1,2,3], ![3,1,2,3], ![3,3,2,3], ![3,3,3,3]] q a` using matrix notation for Fin 4 × Fin 3 → Fin 4. Or define using explicit if-then-else.

For the backward direction proof, use induction on i, then j, then k, computing the DFA evaluation step by step using List.foldl_append and List.foldl_replicate or similar.
-/
set_option maxHeartbeats 1600000 in
/-- `lang_abc_star` (a*b*c*) is a regular language. -/
lemma isRegular_lang_abc_star : lang_abc_star.IsRegular := by
  -- Define the DFA that accepts a*b*c*.
  let dfa : DFA (Fin 3) (Fin 4) := {
    step := fun q a => if q = 0 ∧ a = 0 then 0 else if q = 0 ∧ a = 1 then 1 else if q = 0 ∧ a = 2 then 2 else if q = 1 ∧ a = 0 then 3 else if q = 1 ∧ a = 1 then 1 else if q = 1 ∧ a = 2 then 2 else if q = 2 ∧ a = 0 then 3 else if q = 2 ∧ a = 1 then 3 else if q = 2 ∧ a = 2 then 2 else 3,
    start := 0,
    accept := {0, 1, 2}
  };
  refine' ⟨ Fin 4, inferInstance, dfa, _ ⟩;
  ext w
  simp [DFA.accepts];
  constructor;
  · intro hw
    have h_state : ∀ w : List (Fin 3), dfa.evalFrom dfa.start w = 0 → ∃ i : ℕ, w = List.replicate i 0 := by
      intro w hw
      induction' w using List.reverseRecOn with w ih;
      · exists 0;
      · fin_cases ih <;> simp +decide [ dfa ] at hw ⊢;
        · rename_i h; rcases h hw with ⟨ i, rfl ⟩ ; exact ⟨ i + 1, by simp +decide [ List.replicate_succ' ] ⟩ ;
        · grind;
        · grind +ring
    have h_state1 : ∀ w : List (Fin 3), dfa.evalFrom dfa.start w = 1 → ∃ i j : ℕ, w = List.replicate i 0 ++ List.replicate j 1 := by
      intro w hw; induction' w using List.reverseRecOn with w ih <;> simp_all +decide [ DFA.evalFrom ] ;
      by_cases h : List.foldl dfa.step dfa.start w = 1 <;> simp_all +decide [ DFA.step ];
      · rcases ‹∃ i j : ℕ, w = List.replicate i 0 ++ List.replicate j 1› with ⟨ i, j, rfl ⟩ ; use i, j + 1; simp +decide [ List.replicate_add ] ;
        grind +splitImp;
      · rcases h : List.foldl dfa.step dfa.start w with ( _ | _ | _ | _ ) <;> simp_all +decide [ Fin.forall_fin_succ ];
        · rcases h_state w h with ⟨ i, rfl ⟩ ; use i, 1 ; simp +decide [ hw ] ;
          grind +splitImp;
        · grind;
        · grind +ring
    have h_state2 : ∀ w : List (Fin 3), dfa.evalFrom dfa.start w = 2 → ∃ i j k : ℕ, w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2 := by
      intro w hw
      induction' w using List.reverseRecOn with w ih;
      · exists 0, 0, 0;
      · simp +zetaDelta at *;
        fin_cases ih <;> simp +decide [ * ] at hw ⊢;
        · split_ifs at hw <;> contradiction;
        · grind +ring;
        · rename_i h;
          by_cases h2 : dfa.evalFrom dfa.start w = 2;
          · obtain ⟨ i, j, k, rfl ⟩ := h h2; exact ⟨ i, j, k + 1, by simp +decide [ List.replicate_add ] ⟩ ;
          · by_cases h3 : dfa.evalFrom dfa.start w = 0 <;> by_cases h4 : dfa.evalFrom dfa.start w = 1 <;> simp +decide [ h3, h4 ] at hw h2 ⊢;
            · cases h3.symm.trans h4;
            · obtain ⟨ i, hi ⟩ := h_state w h3; use i, 0, 1; simp +decide [ hi ] ;
            · obtain ⟨ i, j, rfl ⟩ := h_state1 w h4; exact ⟨ i, j, 1, by simp +decide [ List.replicate ] ⟩ ;
            · grind +ring;
    rcases hw with ( hw | hw | hw ) <;> [ exact Exists.elim ( h_state w hw ) fun i hi => ⟨ i, 0, 0, by simpa using hi ⟩ ; exact Exists.elim ( h_state1 w hw ) fun i hi => Exists.elim hi fun j hj => ⟨ i, j, 0, by simpa using hj ⟩ ; exact Exists.elim ( h_state2 w hw ) fun i hi => Exists.elim hi fun j hj => Exists.elim hj fun k hk => ⟨ i, j, k, by simpa using hk ⟩ ];
  · rintro ⟨ i, j, k, rfl ⟩ ; simp +decide [ DFA.acceptsFrom ] ;
    induction i <;> simp_all +decide [ DFA.evalFrom ];
    · induction j <;> simp_all +decide [ List.replicate ];
      · induction k <;> simp_all +decide [ List.replicate ];
        · exact Or.inl rfl;
        · rename_i n ih;
          induction n <;> simp_all +decide [ List.replicate ];
          · grind;
          · grind;
      · rename_i n ih;
        induction n <;> simp_all +decide [ List.replicate ];
        · induction k <;> simp_all +decide [ List.replicate ];
          · grind +locals;
          · grind +ring;
        · grind +ring;
    · grind

/-- `{a^i b^j c^k | i ≠ j ∧ j ≠ k}` is NOT context-free (provable by Ogden's lemma). -/
lemma not_CF_lang_neq_neq : ¬ is_CF lang_neq_neq := by
  sorry

/-- `{aⁱ bʲ cᵏ | i = j ∨ j = k}` is NOT a deterministic context-free language. -/
theorem not_DCFL_lang_aibjck : ¬ is_DCFL lang_aibjck := by
  intro h_dcfl
  have h_compl_cf : is_CF lang_aibjckᶜ := is_CF_of_is_DCFL (is_DCFL_compl h_dcfl)
  have h_inter_cf : is_CF (lang_aibjckᶜ ⊓ lang_abc_star) :=
    CF_of_CF_inter_regular h_compl_cf isRegular_lang_abc_star
  rw [compl_aibjck_inter_abc_eq_neq_neq] at h_inter_cf
  exact not_CF_lang_neq_neq h_inter_cf


end explicit_witness
