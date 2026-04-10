import Mathlib
import Langlib.Grammars.ContextFree.Definition
import Langlib.Classes.ContextFree.Decidability.Emptiness

set_option maxHeartbeats 800000

/-! # Encoded Context-Free Grammars and Uniform Computability of Emptiness

This file introduces a concrete encoded representation of context-free grammars
(`EncodedCFG`) that is `Primcodable`, enabling a genuine uniform computability
theorem for CFG emptiness where the grammar itself is the argument.

## Encoding

An `EncodedCFG T` is a triple `(numNT, initial, rules)` where:
- `numNT : ℕ` — the number of nonterminals minus one (the actual nonterminal type
  is `Fin (numNT + 1)`, ensuring it is always nonempty)
- `initial : ℕ` — index of the initial nonterminal (taken mod `numNT + 1`)
- `rules : List (ℕ × List (ℕ ⊕ T))` — production rules, where `Sum.inl k` represents
  nonterminal `k % (numNT + 1)` and `Sum.inr t` represents terminal `t`

The underlying type is `ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))`, which inherits `Primcodable`
from the standard Mathlib instances for products, sums, lists, and `ℕ` (plus
`Primcodable T`). It is `Primcodable` because each component is: `ℕ` has
`Primcodable.nat`, `⊕` has `Primcodable.sum`, `List` has `Primcodable.list`,
and `×` has `Primcodable.prod`.

## Main results

- `EncodedCFG` — the encoded grammar type
- `EncodedCFG.toCFGrammar` — translation to the project's `CF_grammar T`
- `encoded_cf_emptiness_decidable` — constructive `Decidable` instance for
  emptiness of the language of an encoded grammar
- `encoded_cf_emptiness_computable` — `ComputablePred` for emptiness, where
  the grammar is the argument (uniform over all encoded grammars)
-/

open List Relation

/-! ## The Encoded Grammar Type -/

/-- An encoded context-free grammar over terminal alphabet `T`. -/
def EncodedCFG (T : Type) := ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))

namespace EncodedCFG

variable {T : Type}

instance [Primcodable T] : Primcodable (EncodedCFG T) :=
  inferInstanceAs (Primcodable (ℕ × ℕ × List (ℕ × List (ℕ ⊕ T))))

instance [DecidableEq T] : DecidableEq (EncodedCFG T) :=
  @instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance inferInstance)

def numNT (G : EncodedCFG T) : ℕ := G.1
def initialIdx (G : EncodedCFG T) : ℕ := G.2.1
def rawRules (G : EncodedCFG T) : List (ℕ × List (ℕ ⊕ T)) := G.2.2
def ntCount (G : EncodedCFG T) : ℕ := G.numNT + 1

lemma ntCount_pos (G : EncodedCFG T) : 0 < G.ntCount := by
  unfold ntCount numNT; omega

def toNT (G : EncodedCFG T) (k : ℕ) : Fin G.ntCount :=
  ⟨k % G.ntCount, Nat.mod_lt k G.ntCount_pos⟩

def toSymbol (G : EncodedCFG T) : ℕ ⊕ T → symbol T (Fin G.ntCount)
  | .inl k => symbol.nonterminal (G.toNT k)
  | .inr t => symbol.terminal t

def toCFGrammar (G : EncodedCFG T) : CF_grammar T :=
  { nt := Fin G.ntCount
    initial := G.toNT G.initialIdx
    rules := G.rawRules.map fun (lhs, rhs) =>
      (G.toNT lhs, rhs.map G.toSymbol) }

instance (G : EncodedCFG T) : Fintype (G.toCFGrammar).nt :=
  inferInstanceAs (Fintype (Fin G.ntCount))

instance (G : EncodedCFG T) : DecidableEq (G.toCFGrammar).nt :=
  inferInstanceAs (DecidableEq (Fin G.ntCount))

end EncodedCFG

/-! ## Decidability and Computability -/

variable {T : Type} [Fintype T] [DecidableEq T]

noncomputable def encoded_cf_emptiness_decidable (G : EncodedCFG T) :
    Decidable (CF_language G.toCFGrammar = (∅ : Set (List T))) :=
  cf_emptiness_decidable G.toCFGrammar

/-! ### Direct Emptiness Check

All nonterminal indices are normalized modulo `ntCount` to ensure the
algorithm correctly identifies productive nonterminals regardless of
the raw index values used in the encoding. -/

/-- Check whether all nonterminal indices (mod `nc`) in a rule's RHS appear
    in the set `S` (a list of `ℕ`). Terminals always pass. -/
def allNTsInListN (nc : ℕ) (rhs : List (ℕ ⊕ T)) (S : List ℕ) : Bool :=
  rhs.all fun s =>
    match s with
    | .inl k => decide (k % nc ∈ S)
    | .inr _ => true

/-- One step of the productive-nonterminals fixpoint on encoded rules.
    Each LHS is normalized mod `nc` before addition. -/
def prodStepN (nc : ℕ)
    (rules : List (ℕ × List (ℕ ⊕ T))) (S : List ℕ) : List ℕ :=
  rules.foldl (fun acc (rule : ℕ × List (ℕ ⊕ T)) =>
    if allNTsInListN nc rule.2 acc then
      let lhs := rule.1 % nc
      if decide (lhs ∈ acc) then acc else acc ++ [lhs]
    else acc) S

/-- Compute the productive nonterminals by iterating `prodStepN`. -/
def prodNTsN (nc : ℕ)
    (rules : List (ℕ × List (ℕ ⊕ T))) : List ℕ :=
  (prodStepN nc rules)^[rules.length] []

/-- Check whether the encoded CFG has an empty language. -/
def checkCFGEmpty (G : EncodedCFG T) : Bool :=
  !(decide (G.initialIdx % G.ntCount ∈ prodNTsN G.ntCount G.rawRules))

/-! ### Correctness -/

def IsProductive (g : CF_grammar T) (nt : g.nt) : Prop :=
  ∃ w : List T, CF_derives g [symbol.nonterminal nt] (w.map symbol.terminal)

lemma CF_language_eq_empty_iff_not_productive (g : CF_grammar T) :
    CF_language g = (∅ : Set (List T)) ↔ ¬IsProductive g g.initial := by
  unfold IsProductive; rw [Set.ext_iff]; unfold CF_language; aesop

omit [Fintype T] in
lemma mem_prodStepN_of_mem (nc : ℕ)
    (rules : List (ℕ × List (ℕ ⊕ T))) (S : List ℕ) (x : ℕ) (hx : x ∈ S) :
    x ∈ prodStepN nc rules S := by
  unfold prodStepN
  induction rules generalizing S with
  | nil => simpa
  | cons r rs ih =>
    simp only [List.foldl_cons]
    apply ih; split_ifs <;> simp_all [List.mem_append]

omit [Fintype T] in
lemma prodStepN_mono (nc : ℕ)
    (rules : List (ℕ × List (ℕ ⊕ T))) {S₁ S₂ : List ℕ}
    (h : ∀ x ∈ S₁, x ∈ S₂) :
    ∀ x ∈ prodStepN nc rules S₁, x ∈ prodStepN nc rules S₂ := by
  revert h;
  induction' rules using List.reverseRecOn with rules ih <;> simp_all +decide [ prodStepN ];
  split_ifs <;> simp_all +decide [ List.mem_append, List.mem_singleton ];
  · grind;
  · grind;
  · rename_i h₁ h₂ h₃;
    grind +locals

omit [Fintype T] in
lemma allNTsInListN_mono (nc : ℕ) {rhs : List (ℕ ⊕ T)} {S₁ S₂ : List ℕ}
    (hsub : ∀ x ∈ S₁, x ∈ S₂) (h : allNTsInListN nc rhs S₁ = true) :
    allNTsInListN nc rhs S₂ = true := by
  unfold allNTsInListN at h ⊢;
  grind

omit [Fintype T] in
lemma iterate_prodStepN_mono (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T)))
    {n m : ℕ} (h : n ≤ m) :
    ∀ x ∈ (prodStepN nc rules)^[n] [],
      x ∈ (prodStepN nc rules)^[m] [] := by
  induction' h with k hk;
  · exact?;
  · exact fun x hx => by simpa only [ Function.iterate_succ_apply' ] using mem_prodStepN_of_mem _ _ _ _ ( by tauto ) ;

lemma productive_sentential_form (g : CF_grammar T)
    (syms : List (symbol T g.nt))
    (h : ∀ s ∈ syms, match s with
      | .terminal _ => True
      | .nonterminal nt => IsProductive g nt) :
    ∃ w : List T, CF_derives g syms (w.map symbol.terminal) := by
  induction' syms with s syms ih;
  · exact ⟨ [ ], by constructor ⟩;
  · rcases s with ( _ | _ ) <;> simp_all +decide;
    · obtain ⟨ w, hw ⟩ := ih; use ‹_› :: w; exact (by
      have h_append : ∀ (u v : List (symbol T g.nt)), CF_derives g u v → ∀ (w : List (symbol T g.nt)), CF_derives g (w ++ u) (w ++ v) := by
        exact?;
      exact h_append _ _ hw [ symbol.terminal _ ]);
    · obtain ⟨ w, hw ⟩ := h.1;
      obtain ⟨ w', hw' ⟩ := ih;
      have h_concat : CF_derives g (symbol.nonterminal ‹_› :: syms) (List.map symbol.terminal w ++ syms) := by
        have h_concat : ∀ {α β : List (symbol T g.nt)}, CF_derives g α β → ∀ {γ : List (symbol T g.nt)}, CF_derives g (α ++ γ) (β ++ γ) := by
          exact?;
        exact h_concat hw;
      have h_concat : CF_derives g (List.map symbol.terminal w ++ syms) (List.map symbol.terminal w ++ List.map symbol.terminal w') := by
        exact?;
      exact ⟨ w ++ w', by simpa using Relation.ReflTransGen.trans ‹CF_derives g ( symbol.nonterminal _ :: syms ) ( map symbol.terminal w ++ syms ) › h_concat ⟩

lemma productive_from_rule (G : EncodedCFG T)
    (lhs : ℕ) (rhs : List (ℕ ⊕ T))
    (hrule : (lhs, rhs) ∈ G.rawRules)
    (hprod : ∀ k, Sum.inl k ∈ rhs → IsProductive G.toCFGrammar (G.toNT k)) :
    IsProductive G.toCFGrammar (G.toNT lhs) := by
  have h_rule : (G.toNT lhs, rhs.map G.toSymbol) ∈ G.toCFGrammar.rules := by
    unfold EncodedCFG.toCFGrammar; aesop;
  obtain ⟨w, hw⟩ : ∃ w : List T, CF_derives G.toCFGrammar (rhs.map G.toSymbol) (w.map symbol.terminal) := by
    apply productive_sentential_form;
    intro s hs; rw [ List.mem_map ] at hs; obtain ⟨ k, hk, rfl ⟩ := hs; cases k <;> tauto;
  use w;
  have h_transform : CF_transforms G.toCFGrammar [symbol.nonterminal (G.toNT lhs)] (map G.toSymbol rhs) := by
    use (G.toNT lhs, rhs.map G.toSymbol), [], [];
    aesop;
  exact .single h_transform |> Relation.ReflTransGen.trans <| hw

lemma prodStepN_sound_step (G : EncodedCFG T)
    (S : List ℕ)
    (hS : ∀ k ∈ S, IsProductive G.toCFGrammar (G.toNT k)) :
    ∀ k ∈ prodStepN G.ntCount G.rawRules S,
      IsProductive G.toCFGrammar (G.toNT k) := by
  -- By definition of `prodStepN`, if `k` is in the result of `prodStepN`, then `k` is either in `S` or in the result of adding `lhs` to `S`.
  intro k hk
  by_cases h : k ∈ S;
  · exact hS k h;
  · contrapose! hk;
    -- By definition of `prodStepN`, if `k` is not in `S`, then `k` cannot be added to `S` by `prodStepN`.
    have h_not_in_prodStepN : ∀ (rules : List (ℕ × List (ℕ ⊕ T))) (S : List ℕ), (∀ k ∈ S, IsProductive G.toCFGrammar (G.toNT k)) → (∀ (rule : ℕ × List (ℕ ⊕ T)), rule ∈ rules → (∀ k, Sum.inl k ∈ rule.2 → IsProductive G.toCFGrammar (G.toNT k)) → IsProductive G.toCFGrammar (G.toNT rule.1)) → ∀ k, k ∉ S → ¬IsProductive G.toCFGrammar (G.toNT k) → k ∉ prodStepN G.ntCount rules S := by
      intros rules S hS h_rules k hk hk_not_prod
      induction' rules with rule rules ih generalizing S;
      · exact?;
      · unfold prodStepN; simp +decide [ hk ] ;
        split_ifs <;> simp_all +decide [ List.foldl ];
        · convert ih _ _ _ using 1;
          rotate_left;
          exact S;
          · assumption;
          · assumption;
          · unfold prodStepN; aesop;
        · convert ih ( S ++ [ rule.1 % G.ntCount ] ) _ _ using 1;
          · unfold prodStepN; aesop;
          · simp_all +decide [ allNTsInListN ];
            rintro k ( hk | rfl ) <;> [ exact hS k hk; exact h_rules.1 fun a ha => hS _ ( by solve_by_elim ) ];
            convert h_rules.1 _ using 1;
            · unfold EncodedCFG.toNT; simp +decide [ Nat.mod_eq_of_lt ] ;
            · exact fun k hk => hS _ ( by solve_by_elim ) |> fun h => by simpa [ EncodedCFG.toNT ] using h;
          · simp_all +decide [ List.mem_append, List.mem_singleton ];
            rintro rfl;
            apply hk_not_prod;
            convert h_rules.1 _ using 1;
            · unfold EncodedCFG.toNT; simp +decide [ Nat.mod_eq_of_lt ] ;
            · intro k hk; exact (by
              convert hS ( k % G.ntCount ) _ using 1;
              · unfold EncodedCFG.toNT; simp +decide [ Nat.mod_eq_of_lt ] ;
              · unfold allNTsInListN at *; aesop;);
        · convert ih S hS hk using 1;
          unfold prodStepN; aesop;
    exact h_not_in_prodStepN _ _ hS ( fun rule hr hprod => productive_from_rule _ _ _ hr hprod ) _ h hk

lemma prodNTsN_sound (G : EncodedCFG T)
    (k : ℕ) (hk : k ∈ prodNTsN G.ntCount G.rawRules) :
    IsProductive G.toCFGrammar (G.toNT k) := by
  unfold prodNTsN at hk
  suffices h : ∀ n, ∀ k ∈ (prodStepN G.ntCount G.rawRules)^[n] [],
      IsProductive G.toCFGrammar (G.toNT k) from h _ _ hk
  intro n; induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply']; exact prodStepN_sound_step G _ ih

omit [Fintype T] in
lemma mem_prodStepN_of_rule (nc : ℕ)
    (rules : List (ℕ × List (ℕ ⊕ T))) (S : List ℕ)
    (lhs : ℕ) (rhs : List (ℕ ⊕ T))
    (hrule : (lhs, rhs) ∈ rules)
    (hall : allNTsInListN nc rhs S = true) :
    lhs % nc ∈ prodStepN nc rules S := by
  induction rules generalizing S <;> simp_all +decide [ prodStepN ];
  rename_i k hk;
  cases hrule <;> simp_all +decide [ List.foldl_append ];
  · convert mem_prodStepN_of_mem nc k _ _ _ using 1;
    rotate_left;
    exact if allNTsInListN nc rhs S = true then if lhs % nc ∈ S then S else S ++ [ lhs % nc ] else S;
    · aesop;
    · unfold prodStepN; aesop;
  · split_ifs <;> simp_all +decide [ allNTsInListN ]

omit [Fintype T] in
lemma CF_derives_first_step (g : CF_grammar T) (nt : g.nt)
    (w : List (symbol T g.nt))
    (hd : CF_derives g [symbol.nonterminal nt] w)
    (hne : w ≠ [symbol.nonterminal nt]) :
    ∃ rhs, (nt, rhs) ∈ g.rules ∧ CF_derives g rhs w := by
  -- Apply the definition of CF_derives to obtain the existence of such a rule.
  have h_step : ∃ w', CF_transforms g [symbol.nonterminal nt] w' ∧ CF_derives g w' w := by
    induction hd;
    · contradiction;
    · grind +suggestions;
  obtain ⟨ w', hw₁, hw₂ ⟩ := h_step;
  rcases hw₁ with ⟨ r, hr, u, v, hu, hv ⟩;
  rcases hr with ( _ | ⟨ a, hr ⟩ ) <;> rcases u with ( _ | ⟨ b, u ⟩ ) <;> simp +decide at hu ⊢;
  grind

lemma CF_derives_each_nt_productive (g : CF_grammar T)
    (syms : List (symbol T g.nt)) (w : List T)
    (hd : CF_derives g syms (w.map symbol.terminal)) :
    ∀ s ∈ syms, match s with
      | .terminal _ => True
      | .nonterminal nt => IsProductive g nt := by
  intro s hs
  by_contra h_nonprod;
  -- By induction on the derivation, we can show that any non-productive nonterminal in `syms` will remain in the derived sentential form.
  have h_ind : ∀ {u v : List (symbol T g.nt)}, CF_derives g u v → (∃ s ∈ u, ¬match s with | .terminal _ => True | .nonterminal nt => IsProductive g nt) → (∃ s ∈ v, ¬match s with | .terminal _ => True | .nonterminal nt => IsProductive g nt) := by
    intro u v huv hu;
    induction' huv with u v huv ih;
    · exact hu;
    · rcases ih with ⟨ r, u', v', hr, hu, hv ⟩;
      by_cases h : ∃ s ∈ r.2, ¬match s with | .terminal _ => True | .nonterminal nt => IsProductive g nt;
      · exact ⟨ h.choose, hv.symm ▸ List.mem_append_left _ ( List.mem_append_right _ h.choose_spec.1 ), h.choose_spec.2 ⟩;
      · have h_prod : IsProductive g r.1 := by
          have h_prod : ∃ w : List T, CF_derives g r.2 (w.map symbol.terminal) := by
            apply productive_sentential_form;
            exact fun s hs => Classical.not_not.1 fun hs' => h ⟨ s, hs, hs' ⟩;
          obtain ⟨ w, hw ⟩ := h_prod;
          use w;
          have h_prod : CF_derives g [symbol.nonterminal r.1] r.2 := by
            apply_rules [ Relation.ReflTransGen.single ];
            exact ⟨ r, [ ], [ ], hr, by simp +decide ⟩;
          exact h_prod.trans hw;
        grind;
  specialize h_ind hd ⟨ s, hs, h_nonprod ⟩ ; simp +decide at h_ind;

omit [Fintype T] in
lemma prodStepN_eq_self_iff (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (S : List ℕ) :
    prodStepN nc rules S = S ↔
      ∀ rule ∈ rules, allNTsInListN nc rule.2 S = true → rule.1 % nc ∈ S := by
  refine' ⟨ _, fun h => _ ⟩;
  · intro h rule hrule hall;
    convert mem_prodStepN_of_rule nc rules S rule.1 rule.2 hrule hall using 1;
    exact h.symm;
  · induction' rules with rule rules ih generalizing S;
    · rfl;
    · convert ih S _ using 1;
      · unfold prodStepN; aesop;
      · exact fun rule hrule hrule' => h rule ( List.mem_cons_of_mem _ hrule ) hrule'

omit [Fintype T] in
lemma prodStepN_iterate_stable (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T)))
    (S : List ℕ) (hstab : prodStepN nc rules S = S) :
    ∀ m, (prodStepN nc rules)^[m] S = S := by
  exact fun m => Function.iterate_fixed hstab m

omit [Fintype T] in
lemma iterate_subset_rule_lhs (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (n : ℕ) :
    ∀ x ∈ (prodStepN nc rules)^[n] [],
      ∃ rule ∈ rules, x = rule.1 % nc := by
  intros x hx;
  contrapose! hx;
  induction n <;> simp_all +decide [ Function.iterate_succ_apply', prodStepN ];
  -- By definition of `foldl`, we can prove this by induction on the list `rules`.
  have h_foldl : ∀ (acc : List ℕ) (rules : List (ℕ × List (ℕ ⊕ T))), x ∉ acc → (∀ rule ∈ rules, x ≠ rule.1 % nc) → x ∉ List.foldl (fun acc rule => if allNTsInListN nc rule.2 acc = true then if rule.1 % nc ∈ acc then acc else acc ++ [rule.1 % nc] else acc) acc rules := by
    intros acc rules hx_acc hx_rules; induction' rules using List.reverseRecOn with rules ih <;> simp_all +decide [ List.foldl ] ;
    grind;
  exact h_foldl _ _ ‹_› fun rule hrule => hx _ _ hrule

omit [Fintype T] in
lemma iterate_nodup (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) (n : ℕ) :
    ((prodStepN nc rules)^[n] []).Nodup := by
  induction' n with n ih;
  · exact List.nodup_nil;
  · simp +decide only [Function.iterate_succ'] at *;
    have h_foldl_nodup : ∀ (l : List (ℕ × List (ℕ ⊕ T))) (acc : List ℕ), List.Nodup acc → List.Nodup (List.foldl (fun (acc : List ℕ) (rule : ℕ × List (ℕ ⊕ T)) => if allNTsInListN nc rule.2 acc = true then if decide (rule.1 % nc ∈ acc) = true then acc else acc ++ [rule.1 % nc] else acc) acc l) := by
      intros l acc hacc; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
      grind;
    exact h_foldl_nodup _ _ ih

omit [Fintype T] in
lemma prodNTsN_fixpoint (nc : ℕ) (rules : List (ℕ × List (ℕ ⊕ T))) :
    ∀ x, x ∈ prodStepN nc rules (prodNTsN nc rules) ↔
      x ∈ prodNTsN nc rules := by
  intro x; unfold prodNTsN;
  -- We'll use induction to prove that the size of the list increases by at least one in each step until it reaches the limit.
  have h_inductive_step : ∀ k ≤ rules.length, (prodStepN nc rules)^[k + 1] [] = (prodStepN nc rules)^[k] [] ∨ List.length ((prodStepN nc rules)^[k + 1] []) > List.length ((prodStepN nc rules)^[k] []) := by
    intro k hk
    simp [Function.iterate_succ_apply', prodStepN];
    by_cases h : foldl (fun acc rule => if allNTsInListN nc rule.2 acc = true then if rule.1 % nc ∈ acc then acc else acc ++ [rule.1 % nc] else acc) ((prodStepN nc rules)^[k] []) rules = (prodStepN nc rules)^[k] [] <;> simp_all +decide [ Function.iterate_succ_apply' ];
    have h_inductive_step : ∀ (acc : List ℕ) (rules : List (ℕ × List (ℕ ⊕ T))), foldl (fun acc rule => if allNTsInListN nc rule.2 acc = true then if rule.1 % nc ∈ acc then acc else acc ++ [rule.1 % nc] else acc) acc rules ≠ acc → List.length (foldl (fun acc rule => if allNTsInListN nc rule.2 acc = true then if rule.1 % nc ∈ acc then acc else acc ++ [rule.1 % nc] else acc) acc rules) > List.length acc := by
      intros acc rules h; induction' rules using List.reverseRecOn with rules ih <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
      split_ifs at h ⊢ <;> simp_all +decide [ List.length_append ];
      grind;
    exact h_inductive_step _ _ h;
  have h_limit : List.length ((prodStepN nc rules)^[rules.length + 1] []) ≤ rules.length := by
    have h_limit : ∀ k, List.length ((prodStepN nc rules)^[k] []) ≤ rules.length := by
      intro k
      have h_subset : ∀ x ∈ (prodStepN nc rules)^[k] [], ∃ rule ∈ rules, x = rule.1 % nc := by
        exact?;
      have h_subset : List.toFinset ((prodStepN nc rules)^[k] []) ⊆ List.toFinset (List.map (fun rule => rule.1 % nc) rules) := by
        intro x hx; specialize h_subset x; aesop;
      have := Finset.card_le_card h_subset; simp_all +decide [ List.toFinset_card_of_nodup ] ;
      exact le_trans ( by rw [ List.toFinset_card_of_nodup ( iterate_nodup nc rules k ) ] ) ( this.trans ( List.toFinset_card_le _ ) |> le_trans <| by simp +decide [ List.length_map ] );
    exact h_limit _;
  -- By contradiction, assume that the length of the list after `rules.length + 1` steps is greater than the length after `rules.length` steps.
  by_contra h_contra;
  have h_length_increasing : ∀ k ≤ rules.length, List.length ((prodStepN nc rules)^[k] []) ≥ k := by
    intro k hk
    induction' k with k ih;
    · norm_num;
    · cases h_inductive_step k ( Nat.le_of_succ_le hk ) <;> simp_all +decide [ Function.iterate_succ_apply' ];
      · have h_length_increasing : ∀ m ≥ k, (prodStepN nc rules)^[m] [] = (prodStepN nc rules)^[k] [] := by
          intro m hm; induction hm <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
        grind;
      · linarith [ ih ( Nat.le_of_lt hk ) ];
  cases h_inductive_step rules.length le_rfl <;> simp_all +decide [ Function.iterate_succ_apply' ];
  linarith [ h_length_increasing rules.length le_rfl ]

/-
If S is a fixpoint and a rule (nt, rhs) is in the grammar with all
    nonterminals in the RHS having their values in S, then nt.val ∈ S.
-/
lemma fixpoint_rule_closed (G : EncodedCFG T)
    (S : List ℕ)
    (hfix : ∀ x, x ∈ prodStepN G.ntCount G.rawRules S ↔ x ∈ S)
    (nt : Fin G.ntCount) (rhs : List (symbol T (Fin G.ntCount)))
    (hrule : (nt, rhs) ∈ G.toCFGrammar.rules)
    (hall : ∀ nt' : Fin G.ntCount, symbol.nonterminal nt' ∈ rhs → nt'.val ∈ S) :
    nt.val ∈ S := by
      convert hfix _ |>.1 <| ?_;
      obtain ⟨ lhs, rawRhs, hraw, rfl, rfl ⟩ : ∃ lhs rawRhs, ( lhs, rawRhs ) ∈ G.rawRules ∧ nt = G.toNT lhs ∧ rhs = rawRhs.map G.toSymbol := by
        unfold EncodedCFG.toCFGrammar at hrule; aesop;
      apply mem_prodStepN_of_rule;
      exact hraw;
      simp_all +decide [ allNTsInListN ];
      intro a ha; specialize hall ( G.toNT a ) ; aesop;

/-
If S is a fixpoint and syms derives a terminal string, then
    every nonterminal in syms has its value in S.
-/
lemma all_nts_in_S_of_derives (G : EncodedCFG T)
    (S : List ℕ)
    (hfix : ∀ x, x ∈ prodStepN G.ntCount G.rawRules S ↔ x ∈ S)
    (syms : List (symbol T (Fin G.ntCount))) (w : List T)
    (hd : CF_derives G.toCFGrammar syms (w.map symbol.terminal)) :
    ∀ nt : Fin G.ntCount, symbol.nonterminal nt ∈ syms → nt.val ∈ S := by
      -- By induction on the derivation, we can show that all nonterminals in the sentential form have their values in S.
      have h_ind : ∀ (u v : List (symbol T (Fin G.ntCount))), CF_derives G.toCFGrammar u v → (∀ nt : Fin G.ntCount, symbol.nonterminal nt ∈ v → nt.val ∈ S) → (∀ nt : Fin G.ntCount, symbol.nonterminal nt ∈ u → nt.val ∈ S) := by
        intros u v hd hv;
        induction' hd with u v hd ih;
        · assumption;
        · obtain ⟨ rule, hrule, prefix_list, suffix_list, hu, hv ⟩ := ih;
          have := fixpoint_rule_closed G S hfix rule.1 rule.2 suffix_list; simp_all +decide [ List.mem_append ] ;
          grind +ring;
      specialize h_ind _ _ hd ; aesop

/-- For a fixpoint S, if all nonterminals in a sentential form that derives
    some terminal string have their indices in S, and a rule (nt, rhs) with
    rhs = that form is in the grammar, then nt's index is in S. -/
lemma fixpoint_captures_productive (G : EncodedCFG T)
    (S : List ℕ)
    (hfix : ∀ x, x ∈ prodStepN G.ntCount G.rawRules S ↔ x ∈ S)
    (nt : Fin G.ntCount)
    (h : IsProductive G.toCFGrammar nt) :
    nt.val ∈ S := by
  obtain ⟨w, hw⟩ := h
  exact all_nts_in_S_of_derives G S hfix [symbol.nonterminal nt] w hw nt (List.mem_singleton_self _)

lemma complete_of_fixpoint (G : EncodedCFG T)
    (S : List ℕ)
    (hfix : ∀ x, x ∈ prodStepN G.ntCount G.rawRules S ↔ x ∈ S)
    (k : ℕ) (hk : IsProductive G.toCFGrammar (G.toNT k)) :
    k % G.ntCount ∈ S := by
  have := fixpoint_captures_productive G S hfix (G.toNT k) hk
  simpa [EncodedCFG.toNT] using this

lemma prodNTsN_complete (G : EncodedCFG T)
    (k : ℕ) (hk : IsProductive G.toCFGrammar (G.toNT k)) :
    k % G.ntCount ∈ prodNTsN G.ntCount G.rawRules :=
  complete_of_fixpoint G _ (prodNTsN_fixpoint G.ntCount G.rawRules) k hk

omit [Fintype T] in
private lemma toNT_mod (G : EncodedCFG T) (k : ℕ) :
    G.toNT (k % G.ntCount) = G.toNT k := by
  simp [EncodedCFG.toNT, EncodedCFG.ntCount, EncodedCFG.numNT, Nat.mod_mod_of_dvd]

theorem checkCFGEmpty_iff (G : EncodedCFG T) :
    checkCFGEmpty G = true ↔ CF_language G.toCFGrammar = (∅ : Set (List T)) := by
  unfold checkCFGEmpty
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  rw [CF_language_eq_empty_iff_not_productive]
  constructor
  · intro h hprod
    exact h (prodNTsN_complete G G.initialIdx hprod)
  · intro h hmem
    exact h (by have := prodNTsN_sound G _ hmem; rwa [toNT_mod] at this)

/-! ### Computability -/

variable [Primcodable T]

/-- `List.foldl` is primitive recursive when the fold function, list, and initial
    value are all primitive recursive functions of a context parameter. -/
private lemma list_foldl_primrec {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec (fun a => (f a).foldl (fun s b => h a (s, b)) (g a)) := by
  have key : (fun a => (f a).foldl (fun s b => h a (s, b)) (g a)) =
    (fun a => (f a).reverse.foldr (fun b s => h a (s, b)) (g a)) := by
    ext a; rw [List.foldl_eq_foldr_reverse]
  rw [key]
  have hh' : Primrec₂ (fun (a : α) (p : β × σ) => h a (p.2, p.1)) :=
    hh.comp Primrec.fst
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
  exact Primrec.list_foldr (Primrec.list_reverse.comp hf) hg hh'

private lemma nat_list_mem_primrec :
    Primrec₂ (fun (x : ℕ) (l : List ℕ) => (decide (x ∈ l) : Bool)) := by
  have hmem : (fun (x : ℕ) (l : List ℕ) => (decide (x ∈ l) : Bool)) =
    (fun (x : ℕ) (l : List ℕ) => l.foldr (fun y r => decide (x = y) || r) false) := by
    ext x l; induction l with
    | nil => simp
    | cons h t ih => simp [List.foldr, List.mem_cons, ih]
  rw [hmem]
  have h_step : Primrec₂ (fun (a : ℕ × List ℕ) (b : ℕ × Bool) => decide (a.1 = b.1) || b.2) := by
    show Primrec (fun q : (ℕ × List ℕ) × (ℕ × Bool) => decide (q.1.1 = q.2.1) || q.2.2)
    have heq : (fun q : (ℕ × List ℕ) × (ℕ × Bool) => decide (q.1.1 = q.2.1) || q.2.2) =
      (fun q : (ℕ × List ℕ) × (ℕ × Bool) => bif (q.1.1 == q.2.1) then true else q.2.2) := by
      ext q; simp [BEq.beq]
    rw [heq]
    exact Primrec.cond
      (Primrec.beq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.const true) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.snd (Primrec.const false) h_step

/-- Per-element check for allNTsInListN is primitive recursive.
    Given (nc, S) and an element s : ℕ ⊕ T, checks whether s is a terminal (true)
    or a nonterminal whose index mod nc is in S. -/
private lemma per_elem_primrec :
    Primrec (fun (p : (ℕ × List ℕ) × (ℕ ⊕ T)) =>
      match p.2 with | .inl k => (decide (k % p.1.1 ∈ p.1.2) : Bool) | .inr _ => true) := by
  have h : Primrec (fun (p : (ℕ × List ℕ) × (ℕ ⊕ T)) =>
    @Sum.casesOn ℕ T (fun _ => Bool) p.2
      (fun k => (decide (k % p.1.1 ∈ p.1.2) : Bool)) (fun _ => true)) :=
    Primrec.sumCasesOn Primrec.snd
      (nat_list_mem_primrec.comp
        (Primrec.nat_mod.comp Primrec.snd (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec₂.const true)
  exact h.of_eq (by intro ⟨_, s⟩; cases s <;> rfl)

/-- `allNTsInListN` is primitive recursive in its arguments. -/
private lemma allNTsInListN_primrec :
    Primrec (fun (p : (ℕ × List ℕ) × List (ℕ ⊕ T)) =>
      allNTsInListN p.1.1 p.2 p.1.2) := by
  have heq : (fun (p : (ℕ × List ℕ) × List (ℕ ⊕ T)) => allNTsInListN p.1.1 p.2 p.1.2) =
    (fun (p : (ℕ × List ℕ) × List (ℕ ⊕ T)) => p.2.foldr
      (fun s acc => (match s with | .inl k => (decide (k % p.1.1 ∈ p.1.2) : Bool) | .inr _ => true) && acc) true) := by
    ext ⟨⟨nc, S⟩, rhs⟩; simp [allNTsInListN]
    induction rhs with
    | nil => simp
    | cons h t ih => simp [List.all, List.foldr, ih]
  rw [heq]
  have hstep : Primrec₂ (fun (ctx : (ℕ × List ℕ) × List (ℕ ⊕ T)) (sa : (ℕ ⊕ T) × Bool) =>
    (match sa.1 with | .inl k => (decide (k % ctx.1.1 ∈ ctx.1.2) : Bool) | .inr _ => true) && sa.2) := by
    show Primrec (fun q : ((ℕ × List ℕ) × List (ℕ ⊕ T)) × ((ℕ ⊕ T) × Bool) =>
      (match q.2.1 with | .inl k => (decide (k % q.1.1.1 ∈ q.1.1.2) : Bool) | .inr _ => true) && q.2.2)
    have heq2 : (fun q : ((ℕ × List ℕ) × List (ℕ ⊕ T)) × ((ℕ ⊕ T) × Bool) =>
      (match q.2.1 with | .inl k => (decide (k % q.1.1.1 ∈ q.1.1.2) : Bool) | .inr _ => true) && q.2.2) =
      (fun q : ((ℕ × List ℕ) × List (ℕ ⊕ T)) × ((ℕ ⊕ T) × Bool) =>
        bif (match q.2.1 with | .inl k => (decide (k % q.1.1.1 ∈ q.1.1.2) : Bool) | .inr _ => true)
        then q.2.2 else false) := by
      ext q; cases (match q.2.1 with | .inl k => (decide (k % q.1.1.1 ∈ q.1.1.2) : Bool) | .inr _ => true) <;> simp
    rw [heq2]
    exact Primrec.cond
      (per_elem_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd) (Primrec.const false)
  exact @Primrec.list_foldr ((ℕ × List ℕ) × List (ℕ ⊕ T)) (ℕ ⊕ T) Bool _ _ _ _ _ _
    Primrec.snd (Primrec.const true) hstep

/-
One step of the productive-nonterminals fixpoint is primitive recursive.
-/
private lemma prodStepN_primrec :
    Primrec (fun (p : (ℕ × List (ℕ × List (ℕ ⊕ T))) × List ℕ) =>
      prodStepN p.1.1 p.1.2 p.2) := by
        have prodStepN_foldl_primrec : Primrec (fun (p : (ℕ × List (ℕ × List (ℕ ⊕ T))) × List ℕ) => (p.1.2.foldl (fun acc rule => if allNTsInListN p.1.1 rule.2 acc then let lhs := rule.1 % p.1.1; if (decide (lhs ∈ acc) : Bool) then acc else acc ++ [lhs] else acc) p.2)) := by
          convert list_foldl_primrec _ _ _;
          rotate_left;
          exact?;
          exact fun p q => if allNTsInListN p.1.1 q.2.2 q.1 then let lhs := q.2.1 % p.1.1; if (decide (lhs ∈ q.1) : Bool) then q.1 else q.1 ++ [lhs] else q.1;
          · exact Primrec.snd.comp ( Primrec.fst );
          · exact Primrec.snd;
          · refine' Primrec.of_eq _ _;
            exact fun p => if allNTsInListN p.1.1.1 p.2.2.2 p.2.1 then let lhs := p.2.2.1 % p.1.1.1; if decide (lhs ∈ p.2.1) then p.2.1 else p.2.1 ++ [lhs] else p.2.1;
            · convert Primrec.cond _ _ _;
              rotate_left;
              exact fun p => allNTsInListN p.1.1.1 p.2.2.2 p.2.1;
              · convert allNTsInListN_primrec.comp _ using 1;
                rotate_left;
                exact T;
                all_goals try infer_instance;
                exact fun p => ( ( p.1.1.1, p.2.1 ), p.2.2.2 );
                · exact Primrec.pair ( Primrec.pair ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ( Primrec.fst.comp ( Primrec.snd ) ) ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) );
                · exact?;
              · convert Primrec.cond _ _ _ using 1;
                rotate_left;
                exact fun p => decide ( p.2.2.1 % p.1.1.1 ∈ p.2.1 );
                exact fun p => p.2.1;
                exact fun p => p.2.1 ++ [ p.2.2.1 % p.1.1.1 ];
                · convert nat_list_mem_primrec.comp _ _ using 1;
                  · exact Primrec.nat_mod.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst ) ) );
                  · exact Primrec.fst.comp ( Primrec.snd );
                · exact Primrec.fst.comp ( Primrec.snd );
                · exact Primrec.list_append.comp ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.list_cons.comp ( Primrec.nat_mod.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst ) ) ) ) ( Primrec.const [ ] ) );
                · grind;
              · exact Primrec.fst.comp ( Primrec.snd );
              · grind +extAll;
            · grind +revert;
          · rfl;
        convert prodStepN_foldl_primrec.comp ( Primrec.id ) using 1

/-
The productive-nonterminals fixpoint is primitive recursive.
-/
private lemma prodNTsN_primrec :
    Primrec (fun (p : ℕ × List (ℕ × List (ℕ ⊕ T))) =>
      prodNTsN p.1 p.2) := by
        unfold prodNTsN;
        have h_iterate : Primrec (fun (p : (ℕ × List (ℕ × List (ℕ ⊕ T))) × ℕ) => (prodStepN p.1.1 p.1.2)^[p.2] []) := by
          have h_iterate : Primrec (fun (p : (ℕ × List (ℕ × List (ℕ ⊕ T))) × ℕ × List ℕ) => (prodStepN p.1.1 p.1.2 p.2.2)) := by
            convert prodStepN_primrec.comp _;
            rotate_left;
            rotate_left;
            rotate_left;
            all_goals try infer_instance;
            exact fun p => ( p.1, p.2.2 );
            · exact Primrec.pair ( Primrec.fst ) ( Primrec.snd.comp ( Primrec.snd ) );
            · rfl;
            · rfl;
            · rfl;
          convert Primrec.nat_rec _ _ using 1;
          rotate_left;
          exact ( ℕ × List ( ℕ × List ( ℕ ⊕ T ) ) );
          exact List ℕ;
          exact inferInstance;
          exact?;
          exact fun p => [];
          exact fun p q => prodStepN p.1 p.2 q.2;
          · exact Primrec.const [];
          · convert h_iterate using 1;
          · constructor <;> intro h <;> simp_all +decide [ Primrec₂ ];
            · convert h using 1;
              exact funext fun p => by induction p.2 <;> simp +decide [ *, Function.iterate_succ_apply' ] ;
            · convert h using 1;
              exact funext fun p => by induction p.2 <;> simp +decide [ *, Function.iterate_succ_apply' ] ;
        convert h_iterate.comp ( show Primrec fun p : ℕ × List ( ℕ × List ( ℕ ⊕ T ) ) => ( ( p.1, p.2 ), p.2.length ) from ?_ ) using 1;
        exact Primrec.pair ( Primrec.pair ( Primrec.fst ) ( Primrec.snd ) ) ( Primrec.list_length.comp ( Primrec.snd ) )

theorem checkCFGEmpty_computable :
    Computable (checkCFGEmpty : EncodedCFG T → Bool) := by
      unfold checkCFGEmpty;
      -- The composition of primitive recursive functions is primitive recursive.
      have h_comp : Primrec (fun G : EncodedCFG T => decide (G.initialIdx % G.ntCount ∈ prodNTsN G.ntCount G.rawRules)) := by
        have h_mod : Primrec (fun G : EncodedCFG T => G.initialIdx % G.ntCount) := by
          have h_mod : Primrec (fun p : ℕ × ℕ => p.1 % p.2) := by
            exact Primrec.nat_mod.comp ( Primrec.fst ) ( Primrec.snd );
          convert h_mod.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.id ) ) |> Primrec.pair <| Primrec.succ.comp ( Primrec.fst.comp ( Primrec.id ) ) ) using 1;
        have h_prodNTsN : Primrec (fun G : EncodedCFG T => prodNTsN G.ntCount G.rawRules) := by
          convert prodNTsN_primrec.comp ( show Primrec ( fun G : EncodedCFG T => ( G.1 + 1, G.2.2 ) ) from ?_ ) using 1;
          exact Primrec.pair ( Primrec.succ.comp ( Primrec.fst ) ) ( Primrec.snd.comp ( Primrec.snd ) );
        convert Primrec.comp ( nat_list_mem_primrec ) ( Primrec.pair h_mod h_prodNTsN ) using 1;
      convert Primrec.to_comp ( Primrec.cond h_comp ( Primrec.const Bool.false ) ( Primrec.const Bool.true ) ) using 1

theorem encoded_cf_emptiness_computable :
    ComputablePred (fun G : EncodedCFG T =>
      CF_language G.toCFGrammar = (∅ : Set (List T))) := by
  rw [ComputablePred.computable_iff]
  exact ⟨checkCFGEmpty, checkCFGEmpty_computable,
    funext (fun G => propext (checkCFGEmpty_iff G).symm)⟩