module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Utilities.ClosurePredicates
public import Langlib.Examples.A2nBnPosStar
public import Langlib.Examples.BnAnPosStarB
public import Langlib.Examples.UnaryA2PowSucc
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Order.BourbakiWitt
import Langlib.Classes.ContextFree.Closure.IntersectionRegular
import Langlib.Classes.ContextFree.Closure.Bijection
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Classes.ContextFree.Closure.Union
import Langlib.Classes.ContextFree.Examples.A2nBnPosStar
import Langlib.Classes.ContextFree.Examples.BnAnPosStarB
import Langlib.Classes.ContextFree.Examples.UnaryA2PowSucc
import Langlib.Classes.Regular.Closure.Homomorphism
import Langlib.Classes.Regular.Closure.Star
import Langlib.Grammars.ContextFree.MathlibCFG
import Langlib.Utilities.ListUtils
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
@[expose]
public section



/-! # Context-Free Right Quotients

This file proves the sharp closure behavior for right quotients of context-free languages:

* CFLs are closed under right quotient with regular languages: if `L` is context-free and
  `R` is regular, then `L / R` is context-free.
* CFLs are not closed under right quotient with context-free languages.

## Regular Quotient Strategy

For the positive theorem, we use an abstract, closure-property-based proof.
The key idea is to "tag" each letter
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

## CFL Quotient Counterexample

For the negative theorem, the witness is
`quotientNumerator / quotientDenominator`, where

* `quotientNumerator = {a^(2n)b^n | n ≥ 1}*`
* `quotientDenominator = {b^n a^n | n ≥ 1}* {b}`

with `false = a` and `true = b`. Both languages are CFLs. Their quotient has unary
regular slice exactly `{a^(2^(k+1)) | k ∈ ℕ}`, which is not CFL by the pumping lemma.

## Main declarations

- `blockLang` — the regular "block" language
- `blockLangDFA` — a DFA recognising `blockLang R`
- `is_CF_rightQuotient_regular` — the main theorem (`is_CF` formulation)
- `Language.IsContextFree.rightQuotient_regular` — Mathlib-style formulation
- `quotient_slice_eq_unaryPow2` — identifies the unary slice of the CFL/CFL quotient
- `CF_notClosedUnderRightQuotient` — CFLs are not closed under right quotient by CFLs
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
    | some (true, _q), Sum.inl _ => none
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
  simp only [DFA.mem_accepts, DFA.eval, blockLang]
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
  simp only [Language.subst, 
    blockLang]
  constructor
  · -- (→) in LHS ⟹ in rightQuotient
    rintro ⟨w', ⟨⟨u, hu, hw'_in_prod⟩, ⟨p, q, hw'_eq, hq⟩⟩, hw_in_prod⟩
    -- Since $w' \in (u.map tagSubst).prod$, we have $p ++ q = u$.
    have hpq_eq_u : p ++ q = u := by
      have hpq_eq_u : ∀ {u : List T} {p q : List T}, (List.map Sum.inl p ++ List.map Sum.inr q) ∈ (List.map tagSubst u).prod → p ++ q = u := by
        intros u p q hpq_eq_u; induction' u with u_head u_tail ih generalizing p q <;> simp_all +decide [ tagSubst ] ;
        cases' hpq_eq_u with hpq_eq_u hpq_eq_u ; simp_all +decide [  ];
        rcases hpq_eq_u with ⟨ hpq_eq_u₁, b, hb₁, hb₂ ⟩ ; rcases hpq_eq_u₁ with ( rfl | rfl ) <;> simp_all +decide [  ] ;
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
  fun _L hL _R hR => is_CF_rightQuotient_regular hL hR

/-! ## Standard CFL/CFL quotient witnesses

The eventual counterexample uses
`({a^(2n)b^n | n ∈ ℕ})* / (({b^n a^n | n ∈ ℕ})* {b})`.
The unary slice of this quotient is `unaryPow2`.
-/

/-- Flattened concatenation of positive left-block sizes. -/
def quotientLeftBlocks (ns : List ℕ) : List Bool :=
  (ns.map fun n => List.replicate (2 * n) false ++ List.replicate n true).flatten

/-- Flattened concatenation of positive right-block sizes. -/
def quotientRightBlocks (ns : List ℕ) : List Bool :=
  (ns.map fun n => List.replicate n true ++ List.replicate n false).flatten

private def isFalseBool (b : Bool) : Bool := !b

private def isTrueBool (b : Bool) : Bool := b

private lemma quotientLeftBlocks_of_mem :
    ∀ blocks : List (List Bool),
      (∀ y ∈ blocks, y ∈ quotientLeftBlock) →
        ∃ ns : List ℕ, (∀ n ∈ ns, 0 < n) ∧ blocks.flatten = quotientLeftBlocks ns
  | [], _ => ⟨[], by simp, by simp [quotientLeftBlocks]⟩
  | b :: bs, hmem => by
      rcases hmem b (by simp) with ⟨n, hb⟩
      have hbs : ∀ y ∈ bs, y ∈ quotientLeftBlock := by
        intro y hy
        exact hmem y (by simp [hy])
      rcases quotientLeftBlocks_of_mem bs hbs with ⟨ns, hns, hflat⟩
      refine ⟨(n + 1) :: ns, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · omega
        · exact hns p hp
      · simp [quotientLeftBlocks, hb, hflat, List.append_assoc]

private lemma quotientRightBlocks_of_mem :
    ∀ blocks : List (List Bool),
      (∀ y ∈ blocks, y ∈ quotientRightBlock) →
        ∃ ns : List ℕ, (∀ n ∈ ns, 0 < n) ∧ blocks.flatten = quotientRightBlocks ns
  | [], _ => ⟨[], by simp, by simp [quotientRightBlocks]⟩
  | b :: bs, hmem => by
      rcases hmem b (by simp) with ⟨n, hb⟩
      have hbs : ∀ y ∈ bs, y ∈ quotientRightBlock := by
        intro y hy
        exact hmem y (by simp [hy])
      rcases quotientRightBlocks_of_mem bs hbs with ⟨ns, hns, hflat⟩
      refine ⟨(n + 1) :: ns, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · omega
        · exact hns p hp
      · simp [quotientRightBlocks, hb, hflat, List.append_assoc]

private lemma mem_quotientNumerator_blocks {w : List Bool} (hw : w ∈ quotientNumerator) :
    ∃ ns : List ℕ, (∀ n ∈ ns, 0 < n) ∧ w = quotientLeftBlocks ns := by
  rw [quotientNumerator, Language.mem_kstar] at hw
  rcases hw with ⟨blocks, rfl, hmem⟩
  rcases quotientLeftBlocks_of_mem blocks hmem with ⟨ns, hns, hflat⟩
  exact ⟨ns, hns, hflat⟩

private lemma mem_quotientDenominator_blocks {w : List Bool} (hw : w ∈ quotientDenominator) :
    ∃ ns : List ℕ, (∀ n ∈ ns, 0 < n) ∧ w = quotientRightBlocks ns ++ [true] := by
  rw [quotientDenominator, Language.mem_mul] at hw
  rcases hw with ⟨r, hr, t, ht, hrt⟩
  rw [Set.mem_singleton_iff] at ht
  subst ht
  rw [Language.mem_kstar] at hr
  rcases hr with ⟨blocks, rfl, hmem⟩
  rcases quotientRightBlocks_of_mem blocks hmem with ⟨ns, hns, hflat⟩
  refine ⟨ns, hns, ?_⟩
  rw [← hrt, hflat]

private lemma takeFalse_rightBlocks_append_true (ms : List ℕ)
    (hpos : ∀ n ∈ ms, 0 < n) :
    List.takeWhile isFalseBool (quotientRightBlocks ms ++ [true]) = [] := by
  cases ms with
  | nil => simp [quotientRightBlocks, isFalseBool]
  | cons n ns =>
      have hn : 0 < n := hpos n (by simp)
      simp [quotientRightBlocks, isFalseBool, hn]

private lemma takeFalse_replicate_false_append {tail : List Bool} (m : ℕ)
    (htail : List.takeWhile isFalseBool tail = []) :
    List.takeWhile isFalseBool (List.replicate m false ++ tail) =
      List.replicate m false := by
  induction m with
  | zero => simpa using htail
  | succ m ih =>
      change List.takeWhile isFalseBool (false :: (List.replicate m false ++ tail)) =
        false :: List.replicate m false
      simp [isFalseBool, ih]

private lemma takeFalse_prefix_rightBlocks (m : ℕ) (ms : List ℕ)
    (hpos : ∀ n ∈ ms, 0 < n) :
    (List.takeWhile isFalseBool
      (List.replicate m false ++ (quotientRightBlocks ms ++ [true]))).length = m := by
  rw [takeFalse_replicate_false_append m (takeFalse_rightBlocks_append_true ms hpos)]
  simp

private lemma takeFalse_leftBlocks_cons (n : ℕ) (ns : List ℕ) (hn : 0 < n) :
    (List.takeWhile isFalseBool (quotientLeftBlocks (n :: ns))).length = 2 * n := by
  simp [quotientLeftBlocks, isFalseBool, hn, List.append_assoc]

private lemma takeTrue_rightBlocks_cons (n : ℕ) (ns : List ℕ) (hn : 0 < n) :
    (List.takeWhile isTrueBool (quotientRightBlocks (n :: ns) ++ [true])).length = n := by
  simp [quotientRightBlocks, isTrueBool, hn, List.append_assoc]

private lemma takeTrue_replicate_true_leftBlocks (n : ℕ) (ns : List ℕ)
    (_hn : 0 < n) (hns : ∀ p ∈ ns, 0 < p) :
    (List.takeWhile isTrueBool
      (List.replicate n true ++ quotientLeftBlocks ns)).length = n := by
  cases ns with
  | nil => simp [quotientLeftBlocks, isTrueBool]
  | cons p ps =>
      have hp : 0 < p := hns p (by simp)
      simp [quotientLeftBlocks, isTrueBool, hp, List.append_assoc]

private lemma quotient_block_parser : ∀ (ns : List ℕ) (m : ℕ) (ms : List ℕ),
    (∀ n ∈ ns, 0 < n) → (∀ n ∈ ms, 0 < n) →
    List.replicate m false ++ (quotientRightBlocks ms ++ [true]) = quotientLeftBlocks ns →
      ∃ k : ℕ, m = (2 : ℕ) ^ (k + 1)
  | [], m, _ms, _hns, _hms, h => by
      have hlen := congrArg List.length h
      simp [quotientLeftBlocks, List.length_append] at hlen
  | n :: ns, m, ms, hns, hms, h => by
      have hn : 0 < n := hns n (by simp)
      have hns_tail : ∀ p ∈ ns, 0 < p := by
        intro p hp
        exact hns p (by simp [hp])
      have hm : m = 2 * n := by
        have ht := congrArg
          (fun l : List Bool => (List.takeWhile isFalseBool l).length) h
        simpa [takeFalse_prefix_rightBlocks m ms hms, takeFalse_leftBlocks_cons n ns hn] using ht
      have htail :
          quotientRightBlocks ms ++ [true] = List.replicate n true ++ quotientLeftBlocks ns := by
        rw [hm] at h
        have h' : List.replicate (2 * n) false ++ (quotientRightBlocks ms ++ [true]) =
            List.replicate (2 * n) false ++ (List.replicate n true ++ quotientLeftBlocks ns) := by
          simpa [quotientLeftBlocks, List.append_assoc] using h
        exact List.append_cancel_left h'
      cases ms with
      | nil =>
          have hlen := congrArg List.length htail
          simp [quotientRightBlocks, List.length_append] at hlen
          refine ⟨0, ?_⟩
          omega
      | cons r rs =>
          have hr : 0 < r := hms r (by simp)
          have hrs : ∀ p ∈ rs, 0 < p := by
            intro p hp
            exact hms p (by simp [hp])
          have hrn : r = n := by
            have ht := congrArg
              (fun l : List Bool => (List.takeWhile isTrueBool l).length) htail
            simpa [takeTrue_rightBlocks_cons r rs hr,
              takeTrue_replicate_true_leftBlocks n ns hn hns_tail] using ht
          have hrec :
              List.replicate r false ++ (quotientRightBlocks rs ++ [true]) =
                quotientLeftBlocks ns := by
            rw [hrn] at htail
            have h' : List.replicate n true ++
                (List.replicate n false ++ (quotientRightBlocks rs ++ [true])) =
                List.replicate n true ++ quotientLeftBlocks ns := by
              simpa [quotientRightBlocks, List.append_assoc] using htail
            simpa [hrn] using List.append_cancel_left h'
          rcases quotient_block_parser ns r rs hns_tail hrs hrec with ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          rw [hm, ← hrn, hk]
          rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
          ring

/-- Denominator blocks for the explicit suffix witnessing
`a^(2^(k+1)) ∈ quotientNumerator / quotientDenominator`. -/
def quotientRightWitnessBlocks : ℕ → List (List Bool)
  | 0 => []
  | k + 1 => (List.replicate ((2 : ℕ) ^ (k + 1)) true ++
      List.replicate ((2 : ℕ) ^ (k + 1)) false) :: quotientRightWitnessBlocks k

/-- The suffix `b^(2^k)a^(2^k) ... b²a² b` used for the forward slice inclusion. -/
def quotientWitnessSuffix (k : ℕ) : List Bool :=
  (quotientRightWitnessBlocks k).flatten ++ [true]

/-- Numerator blocks matching `a^(2^(k+1)) ++ quotientWitnessSuffix k`. -/
def quotientLeftWitnessBlocks : ℕ → List (List Bool)
  | 0 => [List.replicate 2 false ++ [true]]
  | k + 1 => (List.replicate ((2 : ℕ) ^ (k + 2)) false ++
      List.replicate ((2 : ℕ) ^ (k + 1)) true) :: quotientLeftWitnessBlocks k

lemma quotientRightWitnessBlocks_mem (k : ℕ) :
    ∀ y ∈ quotientRightWitnessBlocks k, y ∈ quotientRightBlock := by
  induction k with
  | zero => simp [quotientRightWitnessBlocks]
  | succ k ih =>
      intro y hy
      simp [quotientRightWitnessBlocks] at hy
      rcases hy with rfl | hy
      · let N := (2 : ℕ) ^ (k + 1)
        have hNpos : 0 < N := pow_pos (by decide : (0 : ℕ) < 2) _
        refine ⟨N - 1, ?_⟩
        have hNm : N - 1 + 1 = N := by omega
        simp [N, hNm]
      · exact ih y hy

lemma quotientLeftWitnessBlocks_mem (k : ℕ) :
    ∀ y ∈ quotientLeftWitnessBlocks k, y ∈ quotientLeftBlock := by
  induction k with
  | zero =>
      intro y hy
      simp [quotientLeftWitnessBlocks] at hy
      subst hy
      refine ⟨0, ?_⟩
      simp
  | succ k ih =>
      intro y hy
      simp [quotientLeftWitnessBlocks] at hy
      rcases hy with rfl | hy
      · let N := (2 : ℕ) ^ (k + 1)
        have hNpos : 0 < N := pow_pos (by decide : (0 : ℕ) < 2) _
        refine ⟨N - 1, ?_⟩
        have hNm : N - 1 + 1 = N := by omega
        have hpow : (2 : ℕ) ^ (k + 2) = 2 * N := by
          dsimp [N]
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
        rw [hpow]
        change List.replicate (2 * N) false ++ List.replicate N true =
          List.replicate (2 * (N - 1 + 1)) false ++ List.replicate (N - 1 + 1) true
        rw [hNm]
      · exact ih y hy

lemma quotientWitnessSuffix_mem_denominator (k : ℕ) :
    quotientWitnessSuffix k ∈ quotientDenominator := by
  rw [quotientDenominator, Language.mem_mul]
  refine ⟨(quotientRightWitnessBlocks k).flatten, ?_, [true], Set.mem_singleton _, rfl⟩
  exact Language.join_mem_kstar (quotientRightWitnessBlocks_mem k)

lemma prefix_quotientWitnessSuffix_eq_leftWitnessBlocks (k : ℕ) :
    List.replicate ((2 : ℕ) ^ (k + 1)) false ++ quotientWitnessSuffix k =
      (quotientLeftWitnessBlocks k).flatten := by
  induction k with
  | zero => simp [quotientWitnessSuffix, quotientRightWitnessBlocks, quotientLeftWitnessBlocks]
  | succ k ih =>
      simp [quotientWitnessSuffix, quotientRightWitnessBlocks, quotientLeftWitnessBlocks,
        List.append_assoc]
      simpa [quotientWitnessSuffix] using ih

/-- The regular unary language `a*`, with `false = a`. -/
def unaryFalseStar : Language Bool :=
  KStar.kstar ({[false]} : Language Bool)

lemma unaryFalseStar_regular : unaryFalseStar.IsRegular := by
  exact (Language.isRegular_singleton_word [false]).kstar'

lemma unaryPow2_subset_quotient_slice :
    unaryPow2 ≤ (quotientNumerator / quotientDenominator) ⊓ unaryFalseStar := by
  intro w hw
  constructor
  · rcases hw with ⟨k, rfl⟩
    refine ⟨quotientWitnessSuffix k, quotientWitnessSuffix_mem_denominator k, ?_⟩
    rw [prefix_quotientWitnessSuffix_eq_leftWitnessBlocks]
    exact Language.join_mem_kstar (quotientLeftWitnessBlocks_mem k)
  · rcases hw with ⟨k, rfl⟩
    unfold unaryFalseStar
    rw [Language.mem_kstar]
    refine ⟨List.replicate ((2 : ℕ) ^ (k + 1)) [false], ?_, ?_⟩
    · induction ((2 : ℕ) ^ (k + 1)) <;> simp_all
    · intro y hy
      exact (List.mem_replicate.mp hy).2

private lemma flatten_singleton_false_of_mem :
    ∀ blocks : List (List Bool),
      (∀ y ∈ blocks, y ∈ ({[false]} : Language Bool)) →
        blocks.flatten = List.replicate blocks.length false
  | [], _ => by simp
  | b :: bs, hmem => by
      have hb : b = [false] := by simpa using hmem b (by simp)
      have hbs : ∀ y ∈ bs, y ∈ ({[false]} : Language Bool) := by
        intro y hy
        exact hmem y (by simp [hy])
      rw [List.flatten_cons, hb, flatten_singleton_false_of_mem bs hbs]
      rw [List.length_cons, List.replicate_succ]
      simp

private lemma mem_unaryFalseStar_replicate {w : List Bool} (hw : w ∈ unaryFalseStar) :
    ∃ m : ℕ, w = List.replicate m false := by
  rw [unaryFalseStar, Language.mem_kstar] at hw
  rcases hw with ⟨blocks, rfl, hmem⟩
  exact ⟨blocks.length, flatten_singleton_false_of_mem blocks hmem⟩

lemma quotient_slice_subset_unaryPow2 :
    (quotientNumerator / quotientDenominator) ⊓ unaryFalseStar ≤ unaryPow2 := by
  intro w hw
  rcases hw with ⟨hquot, hunary⟩
  rcases mem_unaryFalseStar_replicate hunary with ⟨m, rfl⟩
  rcases hquot with ⟨v, hvden, hvnum⟩
  rcases mem_quotientDenominator_blocks hvden with ⟨ms, hms, hv⟩
  rcases mem_quotientNumerator_blocks hvnum with ⟨ns, hns, hnum⟩
  rw [hv] at hnum
  rcases quotient_block_parser ns m ms hns hms hnum with ⟨k, hk⟩
  exact ⟨k, by rw [hk]⟩

lemma quotient_slice_eq_unaryPow2 :
    (quotientNumerator / quotientDenominator) ⊓ unaryFalseStar = unaryPow2 :=
  Set.Subset.antisymm quotient_slice_subset_unaryPow2 unaryPow2_subset_quotient_slice

/-- Since the quotient's unary regular slice is `unaryPow2`, the quotient cannot be CFL. -/
lemma notCF_quotient :
    ¬ is_CF (quotientNumerator / quotientDenominator) := by
  intro hquot
  have hslice_cf : is_CF ((quotientNumerator / quotientDenominator) ⊓ unaryFalseStar) :=
    CF_of_CF_inter_regular hquot unaryFalseStar_regular
  rw [quotient_slice_eq_unaryPow2] at hslice_cf
  exact notCF_unaryPow2 hslice_cf

/-- CFLs are not closed under right quotient by CFLs. -/
theorem CF_notClosedUnderRightQuotient :
    ¬ ClosedUnderRightQuotient (α := Bool) is_CF := by
  intro hclosed
  exact notCF_quotient
    (hclosed quotientNumerator quotientDenominator CF_quotientNumerator CF_quotientDenominator)

private theorem Language.map_rightQuotient_injective {α β : Type} {f : α → β}
    (hf : Function.Injective f) (L R : Language α) :
    Language.map f (Language.rightQuotient L R) =
      Language.rightQuotient (Language.map f L) (Language.map f R) := by
  ext w
  constructor
  · rintro ⟨u, ⟨v, hvR, huvL⟩, rfl⟩
    exact ⟨v.map f, ⟨v, hvR, rfl⟩, ⟨u ++ v, huvL, by simp⟩⟩
  · rintro ⟨v, ⟨v₀, hv₀R, hv⟩, ⟨z, hzL, hz⟩⟩
    subst v
    have hz' : z.map f = w ++ v₀.map f := by simpa using hz
    obtain ⟨w₀, v₁, hz_eq, hw₀, hv₁⟩ := List.map_eq_append_iff.mp hz'
    have hv₁_eq : v₁ = v₀ := List.map_injective_iff.mpr hf hv₁
    subst v₁
    rw [← hw₀]
    exact ⟨w₀, ⟨v₀, hv₀R, by simpa [hz_eq] using hzL⟩, rfl⟩

/-- CFLs are not closed under right quotient over any alphabet into which the binary
witness alphabet embeds. -/
public theorem CF_notClosedUnderRightQuotient_of_embedding {α : Type}
    (e : Bool ↪ α) :
    ¬ ClosedUnderRightQuotient (α := α) is_CF := by
  intro hclosed
  apply CF_notClosedUnderRightQuotient
  intro L R hL hR
  have hq := hclosed (Language.map e L) (Language.map e R)
    (CF_of_map_CF e L hL) (CF_of_map_CF e R hR)
  rw [← Language.map_rightQuotient_injective e.injective] at hq
  exact CF_of_map_injective_CF_rev e.injective _ hq

/-- CFLs are not closed under right quotient over any finite alphabet with at least
two symbols. -/
public theorem CF_notClosedUnderRightQuotient_of_card {α : Type} [Fintype α]
    (hα : 2 ≤ Fintype.card α) :
    ¬ ClosedUnderRightQuotient (α := α) is_CF := by
  let πB : Bool ≃ Fin (Fintype.card Bool) := Fintype.equivFin Bool
  let πA : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have hBA : Fintype.card Bool ≤ Fintype.card α := by simpa using hα
  exact CF_notClosedUnderRightQuotient_of_embedding
    (πB.toEmbedding.trans ((Fin.castLEEmb hBA).trans πA.symm.toEmbedding))

end
