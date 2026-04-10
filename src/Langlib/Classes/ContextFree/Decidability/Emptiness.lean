import Mathlib
import Langlib.Grammars.ContextFree.EquivMathlibCFG
import Langlib.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
import Langlib.Classes.ContextFree.Pumping.ParseTree
import Langlib.Classes.ContextFree.Decidability.Membership
import Langlib.Utilities.PrimrecHelpers

/-! # Decidability of Emptiness

This file proves that emptiness is decidable for context-free languages
(represented by context-free grammars), using the productive nonterminals
fixpoint algorithm.

## Main results

- `cf_emptiness_decidable` – emptiness of a context-free language is decidable
  (constructively, via the productive nonterminals fixpoint algorithm).
- `cf_emptiness_computable` – **fixed-grammar** computable predicate over `Unit`.
  This proves `ComputablePred (fun (_ : Unit) => CF_language g = ∅)` for a fixed
  grammar `g`. Since the predicate is constant, this is trivially computable.
  For a **uniform** computability result where the grammar varies, see
  `encoded_cf_emptiness_computable` in `EncodedCFG.lean`.
-/

open List Relation

section CNF

variable {T : Type} [DecidableEq T]

namespace ChomskyNormalFormGrammar

open ChomskyNormalFormGrammar

/-! ## Part 1: Productive Nonterminals Algorithm -/

/-- Initialize the productive nonterminals set: all nonterminals with leaf rules. -/
def productiveInit (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] : Finset g.NT :=
  g.rules.biUnion fun r =>
    match r with
    | .leaf n _ => {n}
    | .node _ _ _ => ∅

/-- One step of the productive nonterminals fixpoint: add nonterminals whose
    node rule has both children already in `S`. -/
def productiveStep (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (S : Finset g.NT) : Finset g.NT :=
  S ∪ g.rules.biUnion fun r =>
    match r with
    | .node n c1 c2 => if c1 ∈ S ∧ c2 ∈ S then {n} else ∅
    | .leaf _ _ => ∅

/-- The set of productive nonterminals, computed by iterating `productiveStep`
    `g.rules.card` times. -/
def productiveNTs (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] : Finset g.NT :=
  (g.productiveStep)^[g.rules.card] g.productiveInit

/-- The set of all nonterminals that appear as inputs of rules. -/
def ruleInputs (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] : Finset g.NT :=
  g.rules.image fun r => r.input

/-! ## Part 2: Monotonicity -/

lemma productiveStep_subset_self (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (S : Finset g.NT) : S ⊆ g.productiveStep S := by
  exact fun x hx => Finset.mem_union_left _ hx

lemma productiveStep_mono (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    {S₁ S₂ : Finset g.NT} (h : S₁ ⊆ S₂) : g.productiveStep S₁ ⊆ g.productiveStep S₂ := by
  grind +locals

lemma iterate_productiveStep_mono (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    {n m : ℕ} (h : n ≤ m) :
    (g.productiveStep)^[n] g.productiveInit ⊆ (g.productiveStep)^[m] g.productiveInit := by
  induction' h with m hm ih <;> simp_all +decide [ Function.iterate_succ_apply', Finset.subset_iff ] ;
  exact fun x hx => Finset.mem_union_left _ ( ih hx )

/-! ## Part 3: Range bound – productive nonterminals are rule inputs -/

lemma productiveInit_subset_ruleInputs (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] :
    g.productiveInit ⊆ g.ruleInputs := by
  intro n hn;
  simp_all +decide [ ChomskyNormalFormGrammar.productiveInit ];
  rcases hn with ⟨ r, hr, hn ⟩ ; rcases r with ( _ | _ ) <;> simp_all +decide [ ChomskyNormalFormGrammar.ruleInputs ];
  exact ⟨ _, hr, rfl ⟩

lemma productiveStep_subset_ruleInputs (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    {S : Finset g.NT} (hS : S ⊆ g.ruleInputs) :
    g.productiveStep S ⊆ g.ruleInputs := by
  intro x hx; by_cases hx' : x ∈ S <;> simp_all +decide [ ChomskyNormalFormGrammar.productiveStep ] ;
  · exact hS hx';
  · obtain ⟨ a, ha, hx ⟩ := hx; rcases a with ( _ | _ ) <;> simp_all +decide [ Finset.subset_iff ] ;
    split_ifs at hx <;> simp_all +decide [ ChomskyNormalFormGrammar.ruleInputs ];
    exact ⟨ _, ha, rfl ⟩

lemma iterate_productiveStep_subset_ruleInputs (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (n : ℕ) :
    (g.productiveStep)^[n] g.productiveInit ⊆ g.ruleInputs := by
  induction' n with n ih
  · exact productiveInit_subset_ruleInputs g
  · rw [Function.iterate_succ_apply']
    exact productiveStep_subset_ruleInputs g ih

/-! ## Part 4: Fixpoint property -/

/-
The fixpoint stabilizes: `productiveStep` applied to `productiveNTs` is `productiveNTs`.
-/
lemma productiveNTs_is_fixpoint (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] :
    g.productiveStep g.productiveNTs = g.productiveNTs := by
  have h_card : ∀ k, (g.productiveStep^[k] g.productiveInit).card ≤ g.rules.card := by
    exact fun k => le_trans ( iterate_productiveStep_subset_ruleInputs _ _ |> Finset.card_le_card ) ( Finset.card_image_le ) |> le_trans <| by simp +decide ;
  have h_pigeonhole : ∃ m ≤ g.rules.card, (g.productiveStep^[m] g.productiveInit).card = (g.productiveStep^[m+1] g.productiveInit).card := by
    by_contra! h_contra;
    have h_pigeonhole : ∃ m ≤ g.rules.card, (g.productiveStep^[m] g.productiveInit).card = (g.productiveStep^[m+1] g.productiveInit).card := by
      have h_seq : ∀ m ≤ g.rules.card, (g.productiveStep^[m] g.productiveInit).card < (g.productiveStep^[m+1] g.productiveInit).card := by
        exact fun m hm => lt_of_le_of_ne ( Finset.card_le_card ( by simpa only [ Function.iterate_succ_apply' ] using ChomskyNormalFormGrammar.productiveStep_subset_self _ _ ) ) ( h_contra m hm )
      have h_seq : ∀ m ≤ g.rules.card, (g.productiveStep^[m] g.productiveInit).card ≥ m := by
        intro m hm; induction' m with m ih <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
        exact lt_of_le_of_lt ( ih hm.le ) ( h_seq m hm.le );
      have h_seq : (g.productiveStep^[g.rules.card] g.productiveInit).card = g.rules.card := by
        exact le_antisymm ( h_card _ ) ( h_seq _ le_rfl );
      grind;
    exact h_contra _ h_pigeonhole.choose_spec.1 h_pigeonhole.choose_spec.2;
  obtain ⟨ m, hm₁, hm₂ ⟩ := h_pigeonhole;
  have h_eq : (g.productiveStep^[m+1] g.productiveInit) = (g.productiveStep^[m] g.productiveInit) := by
    refine' Finset.eq_of_subset_of_card_le _ _;
    · exact Finset.eq_of_subset_of_card_le ( iterate_productiveStep_mono g ( Nat.le_succ m ) ) ( by aesop ) ▸ Finset.Subset.refl _;
    · exact hm₂.le;
  have h_eq : ∀ k ≥ m, (g.productiveStep^[k] g.productiveInit) = (g.productiveStep^[m] g.productiveInit) := by
    intro k hk; induction hk <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
  convert h_eq ( m + 1 ) ( Nat.le_succ m ) using 1;
  · unfold ChomskyNormalFormGrammar.productiveNTs; simp +decide [ *, Function.iterate_succ_apply' ] ;
  · exact h_eq _ hm₁

/-! ## Part 5: Soundness -/

/-
`canDerive g nt w` implies `w ≠ []`.
-/
lemma canDerive_ne_nil (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (nt : g.NT) (w : List T) (h : canDerive g nt w) : w ≠ [] := by
  contrapose! h;
  unfold ChomskyNormalFormGrammar.canDerive;
  aesop

/-
Composition lemma for `canDerive`: if `c1` derives `w1` and `c2` derives `w2`,
    and `node n c1 c2 ∈ g.rules`, then `n` derives `w1 ++ w2`.
-/
lemma canDerive_node (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (n c1 c2 : g.NT) (w1 w2 : List T)
    (hrule : ChomskyNormalFormRule.node n c1 c2 ∈ g.rules)
    (h1 : canDerive g c1 w1) (h2 : canDerive g c2 w2) :
    canDerive g n (w1 ++ w2) := by
  have h_len : w1 ≠ [] ∧ w2 ≠ [] := by
    exact ⟨ by rintro rfl; exact absurd h1 ( by unfold ChomskyNormalFormGrammar.canDerive; tauto ), by rintro rfl; exact absurd h2 ( by unfold ChomskyNormalFormGrammar.canDerive; tauto ) ⟩;
  -- Apply the definition of canDerive for lists of length ≥ 2.
  unfold ChomskyNormalFormGrammar.canDerive;
  rcases w1 with ( _ | ⟨ t1, _ | ⟨ t2, w1 ⟩ ⟩ ) <;> rcases w2 with ( _ | ⟨ t3, _ | ⟨ t4, w2 ⟩ ⟩ ) <;> simp_all +decide;
  · exact ⟨ _, hrule, ⟨ rfl, h1, h2 ⟩ ⟩;
  · exact ⟨ ⟨ 0, by simp +decide ⟩, ChomskyNormalFormRule.node n c1 c2, hrule, rfl, by simpa using h1, by simpa using h2 ⟩;
  · use ⟨ w1.length + 1, by
      simp +arith +decide ⟩
    generalize_proofs at *;
    use ChomskyNormalFormRule.node n c1 c2;
    simp_all +decide [ List.take_append, List.drop_append ];
  · refine' ⟨ ⟨ w1.length + 1, _ ⟩, ChomskyNormalFormRule.node n c1 c2, hrule, _, _, _ ⟩ <;> simp_all +decide [ List.take, List.drop ]

lemma productiveInit_sound (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (nt : g.NT) (h : nt ∈ g.productiveInit) :
    ∃ w : List T, canDerive g nt w := by
  -- By definition of productiveInit, nt is in the biUnion of the rules' inputs.
  obtain ⟨r, hr⟩ : ∃ r ∈ g.rules, r.input = nt ∧ r.output.length = 1 := by
    contrapose! h;
    simp +decide [ ChomskyNormalFormGrammar.productiveInit ];
    intro r hr; specialize h r hr; rcases r with ( _ | _ ) <;> simp_all +decide ;
    tauto;
  rcases r with ( _ | _ ) <;> simp_all +decide;
  -- By definition of canDerive, if (ChomskyNormalFormRule.leaf n t) ∈ g.rules, then canDerive g n [t].
  use [‹T›]
  simp [ChomskyNormalFormGrammar.canDerive, hr];
  grind

lemma productiveStep_sound (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (S : Finset g.NT) (hS : ∀ nt ∈ S, ∃ w : List T, canDerive g nt w)
    (nt : g.NT) (h : nt ∈ g.productiveStep S) :
    ∃ w : List T, canDerive g nt w := by
  unfold ChomskyNormalFormGrammar.productiveStep at h;
  rw [ Finset.mem_union, Finset.mem_biUnion ] at h;
  rcases h with ( h | ⟨ r, hr, hr' ⟩ );
  · exact hS nt h;
  · rcases r with ( _ | _ ) <;> simp_all +decide;
    split_ifs at hr' <;> simp_all +decide;
    rename_i h₁ h₂;
    obtain ⟨ w₁, hw₁ ⟩ := hS _ h₂.1; obtain ⟨ w₂, hw₂ ⟩ := hS _ h₂.2; exact ⟨ w₁ ++ w₂, canDerive_node _ _ _ _ _ _ hr hw₁ hw₂ ⟩ ;

lemma productiveNTs_sound (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (nt : g.NT) (h : nt ∈ g.productiveNTs) :
    ∃ w : List T, canDerive g nt w := by
  -- By induction on the number of steps, we can show that every element in the set after k steps is productive.
  have h_ind : ∀ k, ∀ nt ∈ (g.productiveStep)^[k] g.productiveInit, ∃ w : List T, g.canDerive nt w := by
    intro k;
    induction' k with k ih;
    · exact fun nt a => productiveInit_sound g nt a
    · rw [Function.iterate_succ_apply']
      exact fun nt a => productiveStep_sound g _ ih nt a
  exact h_ind _ _ h

/-! ## Part 6: Completeness -/

/-
At the fixpoint, every productive nonterminal is captured.
-/
lemma productive_mem_fixpoint (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (S : Finset g.NT)
    (h_init : g.productiveInit ⊆ S)
    (h_fix : g.productiveStep S = S)
    (nt : g.NT) (w : List T) (hw : canDerive g nt w) :
    nt ∈ S := by
  induction' n : w.length using Nat.strong_induction_on with n ih generalizing nt w;
  unfold ChomskyNormalFormGrammar.canDerive at hw;
  rcases w with ( _ | ⟨ t, _ | ⟨ t', w ⟩ ⟩ ) <;> simp_all +decide;
  · exact h_init <| Finset.mem_biUnion.mpr ⟨ _, hw, Finset.mem_singleton_self _ ⟩;
  · rcases hw with ⟨ i, r, hr, hr' ⟩ ; rcases r with ( _ | _ ) <;> simp_all +decide [ ChomskyNormalFormGrammar.productiveStep ] ;
    specialize h_fix _ hr;
    grind

lemma productiveNTs_complete (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (nt : g.NT) (w : List T) (h : canDerive g nt w) :
    nt ∈ g.productiveNTs := by
  convert @productive_mem_fixpoint T ‹_› g _ g.productiveNTs _ _ nt w h;
  · convert iterate_productiveStep_mono g ( Nat.zero_le _ ) using 1;
  · exact productiveNTs_is_fixpoint g

/-! ## Part 7: Main Correctness -/

theorem mem_productiveNTs_iff (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (nt : g.NT) :
    nt ∈ g.productiveNTs ↔ ∃ w : List T, canDerive g nt w := by
  exact ⟨productiveNTs_sound g nt, fun ⟨w, hw⟩ => productiveNTs_complete g nt w hw⟩

theorem language_eq_empty_iff (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] :
    g.language = (∅ : Set (List T)) ↔ g.initial ∉ g.productiveNTs := by
  constructor <;> intro h;
  · contrapose! h;
    obtain ⟨ w, hw ⟩ := ChomskyNormalFormGrammar.productiveNTs_sound g g.initial h;
    exact Set.Nonempty.ne_empty ⟨ w, by simpa [ ChomskyNormalFormGrammar.mem_language_iff, ChomskyNormalFormGrammar.canDerive_iff_derives ] using hw ⟩;
  · contrapose! h;
    obtain ⟨w, hw⟩ : ∃ w : List T, g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := by
      exact Set.nonempty_iff_ne_empty.mpr h;
    convert ChomskyNormalFormGrammar.productiveNTs_complete g g.initial w _;
    exact (canDerive_iff_derives g g.initial w).mpr hw

/-! ## Part 8: Constructive Decidability -/

/-- Emptiness of a CNF grammar's language is decidable (constructively,
    without `Classical.propDecidable`). -/
def cnf_emptiness_dec (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] :
    Decidable (g.language = (∅ : Set (List T))) :=
  if h : g.initial ∈ g.productiveNTs then
    .isFalse (by rw [g.language_eq_empty_iff]; exact not_not.mpr h)
  else
    .isTrue (by rwa [g.language_eq_empty_iff])

end ChomskyNormalFormGrammar

end CNF

/-! ## Part 9: Context-Free Languages – General CFG -/

section ContextFree

variable {T : Type} [Fintype T] [DecidableEq T]

noncomputable def cf_emptiness_decidable
    (g : CF_grammar T) [Fintype g.nt] [DecidableEq g.nt] :
    Decidable (CF_language g = (∅ : Set (List T))) := by
  rw [CF_language_eq_mathlib_language]
  have h_cnf := @ContextFreeGrammar.toCNF_correct T (mathlib_cfg_of_cfg g) _ _
  have hNTdec : DecidableEq (mathlib_cfg_of_cfg g).toCNF.NT := by
    change DecidableEq ((g.nt ⊕ T) ⊕
      (r : ContextFreeRule T (g.nt ⊕ T)) × Fin (r.output.length - 2))
    infer_instance
  have key : (mathlib_cfg_of_cfg g).language = (∅ : Set (List T)) ↔
      ([] ∉ (mathlib_cfg_of_cfg g).language ∧
       (mathlib_cfg_of_cfg g).toCNF.language = (∅ : Set (List T))) := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [h]; exact fun x => x
      · rw [← h_cnf, h]; exact Set.empty_diff _
    · rintro ⟨hnil, hcnf⟩
      apply Set.subset_eq_empty (fun w (hw : w ∈ (mathlib_cfg_of_cfg g).language) => ?_) rfl
      by_cases hwnil : w = []
      · exact absurd (hwnil ▸ hw) hnil
      · have : w ∈ (mathlib_cfg_of_cfg g).toCNF.language := by
          rw [← h_cnf]; exact ⟨hw, hwnil⟩
        rw [hcnf] at this; exact this
  rw [key]
  have d1 : Decidable ([] ∈ (mathlib_cfg_of_cfg g).language) := by
    have : [] ∈ (mathlib_cfg_of_cfg g).language ↔
        (mathlib_cfg_of_cfg g).initial ∈ (mathlib_cfg_of_cfg g).computeNullables := by
      constructor
      · intro h; rw [ContextFreeGrammar.computeNullables_iff]; exact h
      · intro h; rw [ContextFreeGrammar.computeNullables_iff] at h; exact h
    rw [this]; infer_instance
  have d2 := ChomskyNormalFormGrammar.cnf_emptiness_dec (mathlib_cfg_of_cfg g).toCNF
  exact @instDecidableAnd _ _ (@instDecidableNot _ d1) d2

/-! ## Part 10: ComputablePred -/

/-- **Fixed-grammar** emptiness is a computable predicate over `Unit`.

    This theorem proves `ComputablePred (fun (_ : Unit) => CF_language g = ∅)`
    for a fixed grammar `g`. Because the predicate is constant (it does not
    depend on the `Unit` argument), computability is trivial (`Computable.const`).

    For a genuine **uniform** computability result where the grammar itself is
    the argument, see `encoded_cf_emptiness_computable` in
    `Langlib.Classes.ContextFree.Decidability.EncodedCFG`. -/
theorem cf_emptiness_computable
    (g : CF_grammar T) [Fintype g.nt] [DecidableEq g.nt]
    [Primcodable T] :
    ComputablePred (fun (_ : Unit) => CF_language g = (∅ : Set (List T))) := by
  constructor;
  swap;
  exact Classical.decPred fun _ => CF_language g = (∅ : Set (List T))
  convert Computable.const (decide (CF_language g = (∅ : Set (List T))))
  exact Classical.propDecidable (CF_language g = (∅ : Set (List T)))

end ContextFree