import Mathlib
import Grammars.Classes.ContextFree.Basics.Inclusion
import Grammars.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
import Grammars.Classes.ContextFree.Pumping.ParseTree

/-! # Decidability of Membership

This file proves that membership is decidable for context-free languages
(represented by context-free grammars).

## Main results

- `cf_membership_decidable` – membership in a context-free language is decidable
-/

open List Relation

/-! ## Part 1: Context-Free Languages – CNF Decidability -/

section CNF

variable {T : Type} [DecidableEq T]

namespace ChomskyNormalFormGrammar

open ChomskyNormalFormGrammar

/-- CYK-style predicate: can nonterminal `n` derive word `w` in CNF grammar `g`?
    Quantifies over rules (a Finset) instead of nonterminals, so does NOT require
    `Fintype g.NT`. -/
noncomputable def canDerive (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (n : g.NT) : List T → Prop
  | [] => False
  | [t] => ChomskyNormalFormRule.leaf n t ∈ g.rules
  | t₁ :: t₂ :: rest =>
    let w := t₁ :: t₂ :: rest
    ∃ (i : Fin (w.length - 1)),
      ∃ r ∈ g.rules,
        match r with
        | ChomskyNormalFormRule.node nᵢ c₁ c₂ =>
          nᵢ = n ∧ canDerive g c₁ (w.take (i.val + 1)) ∧
            canDerive g c₂ (w.drop (i.val + 1))
        | _ => False
termination_by w => w.length
decreasing_by
  all_goals simp_all [List.length_take, List.length_drop]
  all_goals omega

/-- The CYK predicate is decidable by induction on word length. -/
noncomputable def canDerive_decidable (g : ChomskyNormalFormGrammar T)
    [DecidableEq g.NT] (n : g.NT) (w : List T) :
    Decidable (canDerive g n w) := by
  induction h : w.length using Nat.strongRecOn generalizing n w with
  | _ k ih =>
    match w, h with
    | [], _ => simp [canDerive]; exact instDecidableFalse
    | [t], _ => simp [canDerive]; infer_instance
    | t₁ :: t₂ :: rest, hw =>
      simp only [canDerive]
      have innerDec : ∀ (i : Fin (rest.length + 1))
          (r : ChomskyNormalFormRule T g.NT),
          Decidable (match r with
            | ChomskyNormalFormRule.node nᵢ c₁ c₂ =>
              nᵢ = n ∧ canDerive g c₁ ((t₁ :: t₂ :: rest).take (i.val + 1)) ∧
                canDerive g c₂ ((t₁ :: t₂ :: rest).drop (i.val + 1))
            | _ => False) := by
        intro ⟨i, hi⟩ r
        match r with
        | ChomskyNormalFormRule.leaf _ _ => exact instDecidableFalse
        | ChomskyNormalFormRule.node nᵢ c₁ c₂ =>
          have hlt : ((t₁ :: t₂ :: rest).take (i + 1)).length < k := by
            rw [List.length_take]; simp only [List.length_cons] at hw ⊢; omega
          have hld : ((t₁ :: t₂ :: rest).drop (i + 1)).length < k := by
            rw [List.length_drop]; simp only [List.length_cons] at hw ⊢; omega
          exact @instDecidableAnd _ _ _ (@instDecidableAnd _ _
            (ih _ hlt c₁ _ rfl) (ih _ hld c₂ _ rfl))
      have midDec : ∀ (i : Fin (rest.length + 1)),
          Decidable (∃ r ∈ g.rules, match r with
            | ChomskyNormalFormRule.node nᵢ c₁ c₂ =>
              nᵢ = n ∧ canDerive g c₁ ((t₁ :: t₂ :: rest).take (i.val + 1)) ∧
                canDerive g c₂ ((t₁ :: t₂ :: rest).drop (i.val + 1))
            | _ => False) := by
        intro i; exact @Finset.decidableExistsAndFinset _ _ _ (innerDec i)
      exact @Fintype.decidableExistsFintype _ _ midDec _


lemma parseTree_of_canDerive (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (n : g.NT) (w : List T) (h : canDerive g n w) :
    ∃ p : @parseTree _ g n, p.yield = w := by
  induction' k : w.length using Nat.strong_induction_on with k ih generalizing n w;
  rcases w with ( _ | ⟨ t, _ | ⟨ t', w ⟩ ⟩ ) <;> simp_all +decide;
  · unfold ChomskyNormalFormGrammar.canDerive at h; aesop;
  · -- By definition of canDerive, if g.canDerive n [t], then there exists a rule in g.rules that matches the leaf rule for n and t.
    obtain ⟨h_rule, h_leaf⟩ : ∃ r ∈ g.rules, r = ChomskyNormalFormRule.leaf n t := by
      unfold ChomskyNormalFormGrammar.canDerive at h; aesop;
    exact ⟨ ChomskyNormalFormGrammar.parseTree.leaf t ( by aesop ), rfl ⟩;
  · unfold ChomskyNormalFormGrammar.canDerive at h;
    rcases h with ⟨ i, r, hr, h ⟩ ; rcases r with ( _ | ⟨ n₁, n₂ ⟩ ) <;> simp_all +decide ;
    obtain ⟨ p₁, hp₁ ⟩ := ih _ ( by
      grind +splitIndPred ) _ _ h.2.1 rfl
    obtain ⟨ p₂, hp₂ ⟩ := ih _ ( by
      simp +arith +decide [ ← k ] ) _ _ h.2.2 rfl
    use ChomskyNormalFormGrammar.parseTree.node p₁ p₂ hr
    generalize_proofs at *;
    simp_all +decide [ ChomskyNormalFormGrammar.parseTree.yield ]


lemma canDerive_of_parseTree (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    {n : g.NT} (p : @parseTree _ g n) :
    canDerive g n p.yield := by
  induction' p with n t hnt p₁ p₂ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀ v hv₁ hv₂ hv₃ hv₄ hv₅ hv₆ hv₇ hv₈ hv₉ hv₁₀ hv₁₁ hv₁₂ hv₁₃ hv₁₄ hv₁₅ hv₁₆ hv₁₇ hv₁₈ hv₁₉ hv₂₀ hv₂₁ hv₂₂ hv₂₃ hv₂₄ hv₂₅ hv₂₆ hv₂₇ hv₂₈ hv₂₉ hv₃₀ hv₃₁ hv₃₂ hv₃₃ hv₃₄ hv₃₅ hv₃₆ hv₃₇ hv₃₈ hv₃₉ hv₄₀ hv₄₁ hv₄₂ hv₄₃ hv₄₄ hv₄₅ hv₄₆ hv₄₇ hv₄₈ hv₄₉ hv₅₀ h₁ₚ h₂ₚ h₃ₚ h₄ₚ h₅ₚ h₆ₚ h₇ₚ h₈ₚ h₉ₚ h₁₀ₚ h₁₁ₚ h₁₂ₚ h₁₃ₚ h₁₄ₚ h₁₅ₚ h₁₆ₚ h₁₇ₚ h₁₈ₚ h₁₉ₚ h₂₀ₚ h₂₁ₚ h₂₂ₚ h₂₃ₚ h₂₄ₚ h₂₅ₚ h₂₆ₚ h₂₇ₚ h₂₈ₚ hi₁ hi₂ hi₃ hi₄ hi₅ hi₆ hi₇ hi₈ hi₉ hi₁₀;
  · unfold parseTree.yield;
    unfold ChomskyNormalFormGrammar.canDerive; aesop;
  · have h_split : (h₂.node h₃ h₄).yield = h₂.yield ++ h₃.yield := by
      rfl;
    rcases h₂_yld : h₂.yield with ( _ | ⟨ t₁, _ | ⟨ t₂, rest ⟩ ⟩ ) <;> simp_all +decide [ List.length ];
    · exact absurd h₅ ( by unfold ChomskyNormalFormGrammar.canDerive; aesop );
    · rcases h₃_yld : h₃.yield with ( _ | ⟨ t₂, _ | ⟨ t₃, rest ⟩ ⟩ ) <;> simp_all +decide [ List.length ];
      · exact absurd h₆ ( by unfold ChomskyNormalFormGrammar.canDerive; simp +decide );
      · -- By definition of canDerive, we can use the node rule to combine the derivations of p₂ and h₁.
        have h_node : g.canDerive p₁ ([t₁] ++ [t₂]) := by
          have h_node_rule : ChomskyNormalFormRule.node p₁ p₂ h₁ ∈ g.rules := h₄
          have h_node_deriv : ∃ i : Fin (List.length ([t₁] ++ [t₂]) - 1), ∃ r ∈ g.rules, match r with | ChomskyNormalFormRule.node nᵢ c₁ c₂ => nᵢ = p₁ ∧ g.canDerive c₁ (([t₁] ++ [t₂]).take (i.val + 1)) ∧ g.canDerive c₂ (([t₁] ++ [t₂]).drop (i.val + 1)) | _ => False := by
            exact ⟨ ⟨ 0, by simp +decide ⟩, ChomskyNormalFormRule.node p₁ p₂ h₁, h_node_rule, by simp +decide [ h₅, h₆ ] ⟩
          generalize_proofs at *; (
          obtain ⟨ i, r, hr₁, hr₂ ⟩ := h_node_deriv; exact (by
          exact (by
            unfold ChomskyNormalFormGrammar.canDerive;
            exact ⟨i, r, hr₁, hr₂⟩));)
        generalize_proofs at *; (
        exact h_node);
      · rw [ ChomskyNormalFormGrammar.canDerive ];
        refine' ⟨ ⟨ 0, by simp +decide ⟩, ChomskyNormalFormRule.node p₁ p₂ h₁, h₄, _ ⟩ ; simp +decide [ * ];
    · unfold ChomskyNormalFormGrammar.canDerive;
      refine' ⟨ ⟨ t₂ :: rest |> List.length, _ ⟩, ChomskyNormalFormRule.node p₁ p₂ h₁, h₄, _ ⟩ <;> simp +decide [ * ];
      exact h₃.yield_length_pos

/-- `canDerive` is equivalent to `Derives` (derivation in the CNF grammar). -/
lemma canDerive_iff_derives (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (n : g.NT) (w : List T) :
    canDerive g n w ↔ g.Derives [Symbol.nonterminal n] (w.map Symbol.terminal) := by
  constructor
  · intro h
    obtain ⟨p, rfl⟩ := parseTree_of_canDerive g n w h
    exact p.yield_derives
  · intro h
    obtain ⟨p, rfl⟩ := Derives.yield h
    exact canDerive_of_parseTree g p

/-- Membership in a CNF grammar's language is decidable. Does NOT require `Fintype g.NT`. -/
noncomputable def decidable_mem_language {g : ChomskyNormalFormGrammar T}
    [DecidableEq g.NT] (w : List T) :
    Decidable (w ∈ g.language) := by
  -- w ∈ g.language ↔ g.Generates (w.map Symbol.terminal)
  --                  ↔ g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal)
  --                  ↔ canDerive g g.initial w
  change Decidable (g.Generates (w.map Symbol.terminal))
  unfold ChomskyNormalFormGrammar.Generates
  rw [← canDerive_iff_derives]
  exact canDerive_decidable g g.initial w



end ChomskyNormalFormGrammar

end CNF

/-! ## Part 2: Context-Free Languages – General CFG -/

section ContextFree

variable {T : Type} [Fintype T] [DecidableEq T]


noncomputable def cf_membership_decidable
    (g : CF_grammar T) [Fintype g.nt] [DecidableEq g.nt]
    (w : List T) : Decidable (w ∈ CF_language g) := by
  rw [CF_language_eq_mathlib_language]
  have h_cnf := @ContextFreeGrammar.toCNF_correct T (mathlib_cfg_of_cfg g) _ _
  have hNTdec : DecidableEq (mathlib_cfg_of_cfg g).toCNF.NT := by
    change DecidableEq ((g.nt ⊕ T) ⊕
      (r : ContextFreeRule T (g.nt ⊕ T)) × Fin (r.output.length - 2))
    infer_instance
  by_cases hw : w = []
  · -- Empty word: use computeNullables
    subst hw
    have : [] ∈ (mathlib_cfg_of_cfg g).language ↔
        (mathlib_cfg_of_cfg g).initial ∈ (mathlib_cfg_of_cfg g).computeNullables := by
      constructor
      · intro h; rw [ContextFreeGrammar.computeNullables_iff]; exact h
      · intro h; rw [ContextFreeGrammar.computeNullables_iff] at h; exact h
    rw [this]
    infer_instance
  · -- Nonempty word: use CNF translation
    have equiv : w ∈ (mathlib_cfg_of_cfg g).language ↔
        w ∈ (mathlib_cfg_of_cfg g).toCNF.language := by
      constructor
      · intro hmem; rw [← h_cnf]; exact ⟨hmem, hw⟩
      · intro hmem; exact (h_cnf ▸ hmem).1
    rw [equiv]
    exact @ChomskyNormalFormGrammar.decidable_mem_language _ _ _ hNTdec w



end ContextFree
