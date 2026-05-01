import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Classes.ContextFree.Closure.IntersectionRegular
import Langlib.Classes.ContextFree.Closure.Union
import Langlib.Utilities.LanguageOperations
import Mathlib
import Langlib.Classes.ContextFree.Definition
import Langlib.Utilities.ClosurePredicates

/-! # Context-Free Closure Under Right Quotient with Regular Languages

This file proves that context-free languages are closed under right quotient with
regular languages: if `L` is context-free and `R` is regular, then `L / R`
is context-free.

## Strategy

We use an abstract, closure-property-based proof. The key idea is to "tag" each letter
with whether it belongs to the kept prefix (`Sum.inl`) or the removed suffix (`Sum.inr`),
then intersect with a regular "block" language that enforces the structure and R-membership,
and finally erase the suffix tags via substitution.

Concretely, given a CFL `L` over `T` and a regular language `R` over `T`:

1. **Tag substitution** `σ : T → Language (T ⊕ T)` maps each letter `a` to `{[inl a], [inr a]}`.
   Since each `σ(a)` is CF, `L.subst σ` is CF (by `CF_of_subst_CF`).

2. **Block language** `blockLang R` over `T ⊕ T` consists of words of the form
   `u.map inl ++ v.map inr` where `v ∈ R`. This is regular (we construct a DFA).

3. **Intersection**: `L.subst σ ⊓ blockLang R` is CF (CF ∩ Regular = CF).

4. **Erasure** `η : (T ⊕ T) → Language T` keeps `inl`-tagged letters and erases `inr`-tagged ones.
   Since each `η(x)` is CF, `(L.subst σ ⊓ blockLang R).subst η` is CF.

5. **Correctness**: `(L.subst σ ⊓ blockLang R).subst η = L / R`.

## Main declarations

- `blockLang` — the regular "block" language
- `blockLangDFA` — a DFA recognising `blockLang R`
- `is_CF_rightQuotient_regular` — the main theorem (`is_CF` formulation)
- `Language.IsContextFree.rightQuotient_regular` — Mathlib-style formulation
-/

open Language Set List

noncomputable section

variable {T : Type}

-- ═══════════════════════════════════════════════════════════════════
-- § 1  Block language and its DFA
-- ═══════════════════════════════════════════════════════════════════

/-- The "block language" over the tagged alphabet `T ⊕ T`.  A word belongs to `blockLang R`
iff it has the form `u.map Sum.inl ++ v.map Sum.inr` with `v ∈ R`. -/
def blockLang (R : Language T) : Language (T ⊕ T) :=
  { w | ∃ u v : List T, w = u.map Sum.inl ++ v.map Sum.inr ∧ v ∈ R }

/-- Given a DFA `D` for `R`, build a DFA over `T ⊕ T` that recognises `blockLang (D.accepts)`.

States: `Option (Bool × σ)` where
  - `some (false, q)` = phase 1 (reading `inl`-tagged letters), DFA state `q`
  - `some (true, q)` = phase 2 (reading `inr`-tagged letters), DFA state `q`
  - `none` = dead (saw `inl` after `inr`)
-/
def blockLangDFA {σ : Type*} (D : DFA T σ) : DFA (T ⊕ T) (Option (Bool × σ)) where
  step := fun s x =>
    match s, x with
    | some (false, q), Sum.inl _ => some (false, q)
    | some (false, q), Sum.inr a => some (true, D.step q a)
    | some (true, q), Sum.inl _ => none
    | some (true, q), Sum.inr a => some (true, D.step q a)
    | none, _ => none
  start := some (false, D.start)
  accept := { s | match s with
    | some (_, q) => q ∈ D.accept
    | none => False }

-- ═══════════════════════════════════════════════════════════════════
-- § 2  DFA correctness
-- ═══════════════════════════════════════════════════════════════════

section DFACorrectness

variable {σ : Type*} (D : DFA T σ)

/-- After processing a list of `inl`-tagged elements, the DFA stays in phase 1 with unchanged
    DFA state. -/
private theorem blockLangDFA_eval_inl (q : σ) (u : List T) :
    (blockLangDFA D).evalFrom (some (false, q)) (u.map Sum.inl) = some (false, q) := by
  induction u with
  | nil => simp [DFA.evalFrom]
  | cons a u ih =>
    simp only [map_cons, DFA.evalFrom, List.foldl_cons, blockLangDFA]
    exact ih

/-- After processing a list of `inr`-tagged elements from phase 2, the DFA stays in phase 2. -/
private theorem blockLangDFA_eval_inr_from_phase2 (q : σ) (v : List T) :
    (blockLangDFA D).evalFrom (some (true, q)) (v.map Sum.inr) =
      some (true, D.evalFrom q v) := by
  induction v generalizing q with
  | nil => simp [DFA.evalFrom]
  | cons a v ih =>
    simp only [map_cons, DFA.evalFrom, List.foldl_cons, blockLangDFA]
    exact ih (D.step q a)

/-- After processing a list of `inr`-tagged elements from phase 1, the DFA reaches phase 2 with
    the DFA state equal to `D.evalFrom q v`. -/
private theorem blockLangDFA_eval_inr_from_phase1 (q : σ) (v : List T) (hv : v ≠ []) :
    (blockLangDFA D).evalFrom (some (false, q)) (v.map Sum.inr) =
      some (true, D.evalFrom q v) := by
  cases v with
  | nil => exact absurd rfl hv
  | cons a v =>
    simp only [map_cons, DFA.evalFrom, List.foldl_cons, blockLangDFA]
    exact blockLangDFA_eval_inr_from_phase2 D (D.step q a) v

/-- Any `inl`-tagged element from the dead state stays dead. -/
private theorem blockLangDFA_eval_none (w : List (T ⊕ T)) :
    (blockLangDFA D).evalFrom none w = none := by
  induction w with
  | nil => simp [DFA.evalFrom]
  | cons a w ih =>
    simp only [DFA.evalFrom, List.foldl_cons, blockLangDFA]
    cases a <;> exact ih

/-
Correctness: the block-language DFA accepts exactly `blockLang D.accepts`.
-/
theorem blockLangDFA_accepts :
    (blockLangDFA D).accepts = blockLang D.accepts := by
  ext w
  simp only [DFA.mem_accepts, DFA.eval, blockLang, Set.mem_setOf_eq]
  constructor
  · -- (→) accepted ⟹ in blockLang
    intro hacc
    -- By definition of `blockLangDFA`, we know that if `w` is accepted, then `w` must be of the form `u.map Sum.inl ++ v.map Sum.inr` for some `u` and `v`. Use this fact.
    have h_form : ∀ w : List (T ⊕ T), (blockLangDFA D).evalFrom (some (false, D.start)) w ∈ (blockLangDFA D).accept → ∃ u v : List T, w = u.map Sum.inl ++ v.map Sum.inr ∧ D.evalFrom D.start v ∈ D.accept := by
      intros w hw
      induction' w with x w ih;
      · exact ⟨ [ ], [ ], rfl, by simpa using hw ⟩;
      · cases x <;> simp +decide [ *, DFA.evalFrom ] at hw ⊢;
        · unfold blockLangDFA at *; simp_all +decide [ DFA.evalFrom ] ;
          rcases ih with ⟨ u, v, rfl, hv ⟩ ; use ( ‹_› :: u ), v; simp +decide [ *, List.map ] ;
        · -- By definition of `blockLangDFA`, we know that if `w` is accepted, then `w` must be of the form `u.map Sum.inl ++ v.map Sum.inr` for some `u` and `v`. Use this fact to find `u` and `v`.
          have h_ind : ∀ w : List (T ⊕ T), ∀ q : σ, (blockLangDFA D).evalFrom (some (true, q)) w ∈ (blockLangDFA D).accept → ∃ v : List T, w = v.map Sum.inr ∧ D.evalFrom q v ∈ D.accept := by
            intros w q hw
            induction' w with x w ih generalizing q <;> simp_all +decide [ DFA.evalFrom ];
            · exact hw;
            · cases x <;> simp_all +decide [ blockLangDFA ];
              · -- Since the foldl of the function over w, starting from none, results in none, the match expression evaluates to false.
                have h_foldl_none : ∀ w : List (T ⊕ T), foldl (fun s x =>
                  match s, x with
                  | some (false, q), Sum.inl val => some (false, q)
                  | some (false, q), Sum.inr a => some (true, D.step q a)
                  | some (true, q), Sum.inl val => none
                  | some (true, q), Sum.inr a => some (true, D.step q a)
                  | none, x => none) none w = none := by
                    intro w; induction' w using List.reverseRecOn with w ih <;> simp +decide [ * ] ;
                exact absurd hw ( by erw [ h_foldl_none ] ; simp +decide );
              · obtain ⟨ v, hv₁, hv₂ ⟩ := ih _ hw; use ‹_› :: v; simp +decide [ hv₁, hv₂ ] ;
          obtain ⟨ v, hv₁, hv₂ ⟩ := h_ind w ( D.step D.start ‹_› ) ( by simpa [ DFA.evalFrom ] using hw ) ; use [ ], ‹_› :: v; aesop;
    exact h_form w hacc
  · -- (←) in blockLang ⟹ accepted
    rintro ⟨u, v, rfl, hv⟩
    -- Apply the induction hypothesis to show that the DFA's state after processing the inl elements is some (false, D.start).
    have h_ind : (blockLangDFA D).evalFrom (blockLangDFA D).start (List.map Sum.inl u) = some (false, D.start) := by
      have := blockLangDFA_eval_inl D D.start u; aesop;
    by_cases hv' : v = [];
    · aesop;
    · rw [ DFA.evalFrom_of_append, h_ind, blockLangDFA_eval_inr_from_phase1 ] <;> aesop

end DFACorrectness

-- ═══════════════════════════════════════════════════════════════════
-- § 3  Tag substitution and erasure
-- ═══════════════════════════════════════════════════════════════════

/-- Tag substitution: each letter `a` can be tagged as either `inl a` or `inr a`. -/
def tagSubst : T → Language (T ⊕ T) :=
  fun a => {[Sum.inl a], [Sum.inr a]}

/-- Erasure substitution: keep `inl`-tagged letters, erase `inr`-tagged ones. -/
def eraseInr : (T ⊕ T) → Language T :=
  fun x => match x with
  | Sum.inl a => {[a]}
  | Sum.inr _ => {[]}

-- ═══════════════════════════════════════════════════════════════════
-- § 4  Helper lemmas: tagSubst and eraseInr map to CF languages
-- ═══════════════════════════════════════════════════════════════════

/-- Each `tagSubst a` is a two-element language, hence context-free. -/
theorem is_CF_tagSubst (a : T) : is_CF (tagSubst a) := by
  unfold tagSubst
  apply (CF_of_CF_u_CF {[Sum.inl a]} {[Sum.inr a]} ⟨_, _⟩)
  · rw [is_CF_iff_isContextFree]; exact isContextFree_singleton _
  · rw [is_CF_iff_isContextFree]; exact isContextFree_singleton _

/-- Each `eraseInr x` is a singleton language, hence context-free. -/
theorem is_CF_eraseInr (x : T ⊕ T) : is_CF (eraseInr x) := by
  cases x with
  | inl a => exact (is_CF_iff_isContextFree).mpr (isContextFree_singleton [a])
  | inr a => exact (is_CF_iff_isContextFree).mpr (isContextFree_singleton [])

/-
═══════════════════════════════════════════════════════════════════
§ 5  Key set equality
═══════════════════════════════════════════════════════════════════

The composition of tag-substitution, block-language intersection, and erasure
    equals the right quotient.
-/
theorem subst_inter_block_subst_eq_rightQuotient (L : Language T) (R : Language T) :
    ((L.subst tagSubst) ⊓ blockLang R).subst eraseInr = L / R := by
  ext w
  simp only [Language.subst, Set.mem_setOf_eq, Set.mem_inter_iff, mem_rightQuotient,
    blockLang]
  constructor
  · -- (→) in LHS ⟹ in rightQuotient
    rintro ⟨w', ⟨⟨u, hu, hw'_in_prod⟩, ⟨p, q, hw'_eq, hq⟩⟩, hw_in_prod⟩
    -- Since $w' \in (u.map tagSubst).prod$, we have $p ++ q = u$.
    have hpq_eq_u : p ++ q = u := by
      have hpq_eq_u : ∀ {u : List T} {p q : List T}, (List.map Sum.inl p ++ List.map Sum.inr q) ∈ (List.map tagSubst u).prod → p ++ q = u := by
        intros u p q hpq_eq_u; induction' u with u_head u_tail ih generalizing p q <;> simp_all +decide [ tagSubst ] ;
        cases' hpq_eq_u with hpq_eq_u hpq_eq_u ; simp_all +decide [ Set.mem_mul ];
        rcases hpq_eq_u with ⟨ hpq_eq_u₁, b, hb₁, hb₂ ⟩ ; rcases hpq_eq_u₁ with ( rfl | rfl ) <;> simp_all +decide [ List.map ] ;
        · cases p <;> cases q <;> simp_all +decide [ List.map ];
          specialize @ih ‹_› [ ] ; aesop;
        · cases p <;> cases q <;> simp_all +decide [ List.map ];
          specialize @ih [ ] ‹_› ; aesop;
      exact hpq_eq_u <| hw'_eq ▸ hw'_in_prod;
    -- Since $w' = p.map Sum.inl ++ q.map Sum.inr$, we have $(w'.map eraseInr).prod = {p}$.
    have h_prod_eraseInr : (w'.map eraseInr).prod = {p} := by
      -- Applying the definition of `List.prod` and the fact that `eraseInr` maps `Sum.inl` to `{[a]}` and `Sum.inr` to `{[]}`, we can simplify the expression.
      have h_prod_eraseInr : ∀ (p q : List T), (List.map eraseInr (p.map Sum.inl ++ q.map Sum.inr)).prod = {p} := by
        intros p q; induction' p with a p ih generalizing q <;> simp_all +decide [ List.prod_cons ] ;
        · induction q <;> simp_all +decide [ List.prod_cons, List.prod_nil ];
          · rfl;
          · ext; simp [eraseInr];
            simp +decide [ Language.mem_mul ];
            grind;
        · ext; simp [eraseInr];
          exact ⟨ fun ⟨ u, hu, v, hv, h ⟩ => by cases hu; cases hv; aesop, fun h => by cases h; exact ⟨ [ a ], by aesop ⟩ ⟩;
      rw [hw'_eq, h_prod_eraseInr];
    have hw_eq_p : w = p := by
      rw [h_prod_eraseInr] at hw_in_prod
      simpa using hw_in_prod
    have hpq_in_L : p ++ q ∈ L := by
      simpa [hpq_eq_u] using hu
    have hw_in_quotient : w ∈ L / R := by
      refine ⟨q, hq, ?_⟩
      simpa [hw_eq_p] using hpq_in_L
    exact hw_in_quotient
  · -- (←) in rightQuotient ⟹ in LHS
    rintro ⟨v, hv, hwv⟩
    -- By definition of $tagSubst$, we know that $[inl a_1, ..., inl a_m, inr b_1, ..., inr b_n]$ is in the product of the tagSubst of $w ++ v$.
    have h_tagSubst : List.map Sum.inl w ++ List.map Sum.inr v ∈ (List.map tagSubst (w ++ v)).prod := by
      have h_prod : ∀ (xs : List T) (ys : List T), List.map Sum.inl xs ++ List.map Sum.inr ys ∈ (List.map tagSubst (xs ++ ys)).prod := by
        intros xs ys; induction' xs with x xs ih generalizing ys <;> simp_all +decide [ List.prod_cons ] ;
        · induction' ys with y ys ih <;> simp_all +decide [ List.prod_cons ];
          exact ⟨ [ Sum.inr y ], by exact Set.mem_insert_of_mem _ ( Set.mem_singleton _ ), _, ih, rfl ⟩;
        · exact ⟨ _, Set.mem_insert _ _, _, ih _, rfl ⟩;
      exact h_prod _ _;
    refine' ⟨ _, ⟨ ⟨ w ++ v, hwv, h_tagSubst ⟩, _, _, rfl, hv ⟩, _ ⟩;
    clear h_tagSubst hwv hv;
    induction w <;> simp_all +decide [ List.prod ];
    · induction v <;> simp_all +decide [ Language.mul_def ];
      exact ⟨ _, by tauto, _, by tauto, by tauto ⟩;
    · exact ⟨ _, rfl, _, ‹_›, rfl ⟩

-- ═══════════════════════════════════════════════════════════════════
-- § 6  Main theorems
-- ═══════════════════════════════════════════════════════════════════

/-- Context-free languages are closed under right quotient with regular languages
(`is_CF` formulation). -/
theorem is_CF_rightQuotient_regular {L : Language T} {R : Language T}
    (hL : is_CF L) (hR : R.IsRegular) :
    is_CF (L / R) := by
  rw [← subst_inter_block_subst_eq_rightQuotient L R]
  apply CF_of_subst_CF _ eraseInr _ is_CF_eraseInr
  apply CF_of_CF_inter_regular
  · exact CF_of_subst_CF L tagSubst hL is_CF_tagSubst
  · obtain ⟨σ_type, _, D, rfl⟩ := hR
    exact ⟨_, inferInstance, blockLangDFA D, blockLangDFA_accepts D⟩

/-- Context-free languages are closed under right quotient with regular languages
(Mathlib-style `Language.IsContextFree` formulation). -/
theorem Language.IsContextFree.rightQuotient_regular {L : Language T}
    (hL : L.IsContextFree) {R : Language T} (hR : R.IsRegular) :
    (L / R).IsContextFree := by
  rw [← is_CF_iff_isContextFree] at hL ⊢
  exact is_CF_rightQuotient_regular hL hR

/-- `prefixLang` as a special case: if `L` is CF, then `prefixLang L` is CF. -/
theorem is_CF_prefixLang' {L : Language T} (hL : is_CF L) :
    is_CF (Language.prefixLang L) := by
  rw [Language.prefixLang_eq_rightQuotient_univ]
  exact is_CF_rightQuotient_regular hL
    ⟨Unit, inferInstance, ⟨fun _ _ => (), (), Set.univ⟩,
     by ext; simp [DFA.accepts, DFA.acceptsFrom, DFA.evalFrom]⟩

/-- The class of context-free languages is closed under right quotient with regular languages. -/
theorem CF_closedUnderRightQuotientWithRegular :
    ClosedUnderRightQuotientWithRegular (α := T) is_CF :=
  fun L hL R hR => is_CF_rightQuotient_regular hL hR

end
