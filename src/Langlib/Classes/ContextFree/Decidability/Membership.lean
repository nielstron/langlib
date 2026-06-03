module

public import Langlib.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
public import Langlib.Classes.ContextFree.Pumping.ParseTree
public import Langlib.Classes.ContextFree.Decidability.Helper
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Matrix.Mul
import Langlib.Classes.ContextFree.Decidability.PrimrecSatStep
import Langlib.Grammars.ContextFree.EquivMathlibCFG
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
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Cases
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
@[expose]
public section



/-! # Decidability and Computability of Membership

This file proves that membership is decidable—and indeed computable—for context-free
languages (represented by context-free grammars).

The proof proceeds via the CYK algorithm on Chomsky-normal-form grammars.

## Main results

- `cf_membership_computable` – membership in a context-free language is a computable
  predicate (`ComputablePred`), which in particular implies decidability.
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
@[expose]
public noncomputable def canDerive (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
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

/-- Bool-valued CYK decision function. Takes an explicit list of rules so that the
    function is genuinely computable (not `noncomputable`). -/
def cykDecideAux {NT : Type} [DecidableEq NT]
    (rulesList : List (ChomskyNormalFormRule T NT))
    (n : NT) (w : List T) : Bool :=
  match w with
  | [] => false
  | [t] => rulesList.any fun r =>
      match r with
      | ChomskyNormalFormRule.leaf nᵢ tᵢ => decide (nᵢ = n ∧ tᵢ = t)
      | _ => false
  | h₁ :: h₂ :: rest =>
    let w' := h₁ :: h₂ :: rest
    (List.finRange (w'.length - 1)).any fun ⟨i, hi⟩ =>
      have hi' : i < rest.length + 1 := by simp [w'] at hi; omega
      rulesList.any fun r =>
        match r with
        | ChomskyNormalFormRule.node nᵢ c₁ c₂ =>
          have htake : (w'.take (i + 1)).length < w'.length := by
            simp [List.length_take]; omega
          have hdrop : (w'.drop (i + 1)).length < w'.length := by
            simp [List.length_drop]; omega
          decide (nᵢ = n) && cykDecideAux rulesList c₁ (w'.take (i + 1)) &&
            cykDecideAux rulesList c₂ (w'.drop (i + 1))
        | _ => false
termination_by w.length

/-
`cykDecideAux` is equivalent to `canDerive` when the rule list contains exactly the
    rules of the grammar.
-/
lemma cykDecideAux_iff_canDerive (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (rulesList : List (ChomskyNormalFormRule T g.NT))
    (hrules : ∀ r, r ∈ rulesList ↔ r ∈ g.rules)
    (n : g.NT) (w : List T) :
    cykDecideAux rulesList n w = true ↔ canDerive g n w := by
  apply Iff.intro;
  · intro h;
    induction' k : w.length using Nat.strong_induction_on with k ih generalizing n w;
    rcases w with ( _ | ⟨ t, _ | ⟨ t', w ⟩ ⟩ ) <;> simp_all +decide [ List.finRange ];
    · unfold cykDecideAux at h; aesop;
    · unfold cykDecideAux at h;
      rw [ List.any_eq_true ] at h;
      obtain ⟨ r, hr₁, hr₂ ⟩ := h;
      cases r <;> simp_all +decide [ hrules ];
      unfold ChomskyNormalFormGrammar.canDerive; aesop;
    · unfold cykDecideAux at h;
      rw [ List.any_eq_true ] at h;
      obtain ⟨ i, hi, h ⟩ := h;
      rw [ List.any_eq_true ] at h;
      obtain ⟨ r, hr₁, hr₂ ⟩ := h;
      rcases r with ( _ | ⟨ n₁, n₂ ⟩ ) <;> simp_all +decide;
      unfold ChomskyNormalFormGrammar.canDerive;
      use ⟨ i, by
        exact i.2 ⟩
      generalize_proofs at *;
      use ChomskyNormalFormRule.node n n₂ ‹_›;
      grind;
  · induction' k : w.length using Nat.strong_induction_on with k ih generalizing n w;
    rcases w with ( _ | ⟨ t, _ | ⟨ t', w ⟩ ⟩ ) <;> simp_all +decide;
    · unfold ChomskyNormalFormGrammar.canDerive; aesop;
    · unfold cykDecideAux;
      unfold ChomskyNormalFormGrammar.canDerive;
      exact fun h => List.any_of_mem ( hrules _ |>.2 h ) ( by simp +decide );
    · unfold ChomskyNormalFormGrammar.canDerive;
      rintro ⟨ i, r, hr, hr' ⟩;
      rcases r with ( _ | ⟨ nᵢ, c₁, c₂ ⟩ ) <;> simp_all +decide;
      unfold cykDecideAux;
      rw [ List.any_eq_true ];
      use i;
      rw [ List.any_eq_true ];
      refine' ⟨ _, ChomskyNormalFormRule.node n c₁ c₂, _, _ ⟩ <;> simp_all +decide;
      grind

public lemma parseTree_of_canDerive (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (n : g.NT) (w : List T) (h : canDerive g n w) :
    ∃ p : @parseTree _ g n, p.yield = w := by
  induction' k : w.length using Nat.strong_induction_on with k ih generalizing n w;
  rcases w with ( _ | ⟨ t, _ | ⟨ t', w ⟩ ⟩ ) <;> simp_all +decide;
  · unfold ChomskyNormalFormGrammar.canDerive at h; aesop;
  · obtain ⟨h_rule, h_leaf⟩ : ∃ r ∈ g.rules, r = ChomskyNormalFormRule.leaf n t := by
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


public lemma canDerive_of_parseTree (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
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
      · have h_node : g.canDerive p₁ ([t₁] ++ [t₂]) := by
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
public lemma canDerive_iff_derives (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (n : g.NT) (w : List T) :
    canDerive g n w ↔ g.Derives [Symbol.nonterminal n] (w.map Symbol.terminal) := by
  constructor
  · intro h
    obtain ⟨p, rfl⟩ := parseTree_of_canDerive g n w h
    exact p.yield_derives
  · intro h
    obtain ⟨p, rfl⟩ := Derives.yield h
    exact canDerive_of_parseTree g p

end ChomskyNormalFormGrammar

end CNF

open List

/-! ## Bitvector operations -/

section BitvectorOps

/-- Check if bit `idx` is set in `bv`. -/
def ntInSet (bv : ℕ) (idx : ℕ) : Bool := Nat.testBit bv idx

/-- Set bit `idx` in `bv`. -/
def ntSetBit (bv : ℕ) (idx : ℕ) : ℕ := bv ||| (1 <<< idx)

lemma ntInSet_ntSetBit_self (bv : ℕ) (idx : ℕ) :
    ntInSet (ntSetBit bv idx) idx = true := by
  simp [ntInSet, ntSetBit, Nat.testBit_or, Nat.testBit_shiftLeft]

lemma ntInSet_ntSetBit_of_true (bv : ℕ) (idx idx' : ℕ)
    (h : ntInSet bv idx = true) :
    ntInSet (ntSetBit bv idx') idx = true := by
  simp [ntInSet, ntSetBit, Nat.testBit_or] at *
  exact Or.inl h

private lemma ntInSet_zero (idx : ℕ) : ntInSet 0 idx = false := by
  simp [ntInSet]

end BitvectorOps

/-! ## Primrec proofs for bitvector operations -/

section BitvectorPrimrec

lemma primrec₂_ntInSet : Primrec₂ (fun bv idx => ntInSet bv idx) := by
  have h_div : Primrec₂ (fun (bv : ℕ) (idx : ℕ) => bv / 2 ^ idx) := by
    have h_div : Primrec₂ (fun (bv : ℕ) (idx : ℕ) => bv / 2 ^ idx) := by
      have h_exp : Primrec₂ (fun (idx : ℕ) (bv : ℕ) => 2 ^ idx) := by
        have h_exp : Primrec (fun (idx : ℕ) => 2 ^ idx) := by
          rw [ show ( fun idx => 2 ^ idx : ℕ → ℕ ) = fun idx => Nat.recOn idx 1 fun n ih => 2 * ih by funext n; induction n <;> simp +decide [ *, pow_succ' ] ];
          have h_pow : Primrec₂ (fun (n : ℕ) (ih : ℕ) => 2 * ih) := by
            exact Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.snd );
          field_simp;
          exact?;
        exact h_exp.comp ( Primrec.fst )
      exact Primrec.nat_div.comp ( Primrec.fst ) ( h_exp.comp ( Primrec.snd ) ( Primrec.fst ) );
    exact h_div;
  have h_mod : Primrec₂ (fun (n : ℕ) (m : ℕ) => n % m) := by
    exact?;
  have h_mod : Primrec₂ (fun (bv : ℕ) (idx : ℕ) => (bv / 2 ^ idx) % 2) := by
    exact h_mod.comp₂ h_div ( Primrec₂.const 2 );
  have h_eq : Primrec₂ (fun (n : ℕ) (m : ℕ) => decide (n = m)) := by
    convert Primrec.eq using 1;
    exact?;
  convert h_eq.comp₂ h_mod ( Primrec₂.const 1 ) using 1;
  ext; simp [ntInSet];
  exact?

lemma primrec₂_ntSetBit : Primrec₂ (fun bv idx => ntSetBit bv idx) := by
  unfold ntSetBit;
  refine' Primrec.of_eq _ _;
  exact fun n => if Nat.testBit n.1 n.2 then n.1 else n.1 + 2 ^ n.2;
  · convert Primrec.cond _ _ _ using 1;
    rotate_left;
    exact fun n => Nat.testBit n.1 n.2;
    exact fun n => n.1;
    exact fun n => n.1 + 2 ^ n.2;
    · convert primrec₂_ntInSet using 1;
    · exact Primrec.fst;
    · have h_primrec_exp : Primrec (fun (n : ℕ) => 2 ^ n) := by
        have h_pow_two_primrec : Primrec (fun n => 2 ^ n) := by
          have : ∀ n, 2 ^ n = Nat.rec 1 (fun _ m => 2 * m) n := by
            exact fun n => by induction n <;> simp +decide [ *, pow_succ' ] ;
          rw [ show ( fun n => 2 ^ n ) = _ from funext this ];
          convert Primrec.nat_rec₁ _ _ using 1;
          exact Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.snd );
        exact h_pow_two_primrec;
      exact Primrec.nat_add.comp ( Primrec.fst ) ( h_primrec_exp.comp ( Primrec.snd ) );
    · grind;
  · intro n; split_ifs <;> simp_all +decide [ Nat.testBit, Nat.shiftLeft_eq ] ;
    · refine' Eq.symm ( Nat.eq_of_testBit_eq fun i => _ );
      by_cases hi : i = n.2 <;> simp_all +decide [ Nat.testBit_two_pow ];
      · simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
      · aesop;
    · -- Since $n.1$ and $2^n.2$ have no overlapping 1s in their binary representations, their bitwise OR is equal to their sum.
      have h_no_overlap : ∀ (m n : ℕ), (m &&& n = 0) → (m ||| n = m + n) := by
        intro m n h; induction' m using Nat.binaryRec with m ih generalizing n <;> induction' n using Nat.binaryRec with n ih' <;> simp_all +decide [ Nat.shiftLeft, Nat.shiftRight ] ;
        cases m <;> cases n <;> simp_all +decide [ Nat.bit ];
        · ring;
        · ring;
        · ring;
      rw [ h_no_overlap ];
      refine' Nat.eq_of_testBit_eq fun i => _;
      by_cases hi : i = n.2 <;> simp_all +decide [ Nat.testBit_two_pow ];
      · simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
      · grind

end BitvectorPrimrec

/-! ## Fold over fixed lists is Primrec -/

section FoldFixed

variable {α σ : Type} [Primcodable α] [Primcodable σ]

/-- Folding over a fixed list with a Primrec step function is Primrec. -/
lemma primrec_foldl_fixed {β : Type} (l : List β)
    (step : β → (α → σ → σ))
    (h_step : ∀ b : β, Primrec₂ (step b)) :
    Primrec₂ (fun (a : α) (init : σ) => l.foldl (fun acc b => step b a acc) init) := by
  induction l with
  | nil => exact Primrec.snd
  | cons hd tl ih =>
    simp only [List.foldl]
    show Primrec₂ fun a init => tl.foldl (fun acc b => step b a acc) (step hd a init)
    exact ih.comp Primrec.fst ((h_step hd).comp Primrec.fst Primrec.snd)

end FoldFixed

/-! ## CYK Table Definitions (Bitvector-based) -/

section CYKDefs

variable {T : Type} [DecidableEq T]

/-- Bitvector lookup for terminal rules: given terminal `t`, compute the bitvector
    of nonterminals with leaf rule `nt → t`. -/
def cykLeafBV (leafData : List (ℕ × T)) (t : T) : ℕ :=
  leafData.foldl (fun bv p => if p.2 == t then ntSetBit bv p.1 else bv) 0

/-- Build the CYK table bottom-up.

    The result is a flat `List ℕ` where entry at index `l * n + i`
    (with `n = w.length`) is the bitvector of nonterminals that derive
    the substring `w[i .. i+l]` (length `l+1` starting at position `i`).

    `extraRows` is the number of rows beyond the base row. -/
def cykBuildTable (leafData : List (ℕ × T)) (nodeData : List (ℕ × ℕ × ℕ))
    (w : List T) : ℕ → List ℕ
  | 0 => w.map (cykLeafBV leafData)
  | k + 1 =>
    let prev := cykBuildTable leafData nodeData w k
    let n := w.length
    prev ++ (List.range n).map fun i =>
      if i + k + 2 > n then 0
      else (List.range (k + 1)).foldl (fun bv j =>
        nodeData.foldl (fun bv' r =>
          if ntInSet (prev.getD (j * n + i) 0) r.2.1 &&
             ntInSet (prev.getD ((k - j) * n + (i + j + 1)) 0) r.2.2
          then ntSetBit bv' r.1 else bv') bv
      ) 0

/-- Full membership check via CYK bitvector table. -/
def cykMemCheck (leafData : List (ℕ × T)) (nodeData : List (ℕ × ℕ × ℕ))
    (startIdx : ℕ) (w : List T) : Bool :=
  match w with
  | [] => false
  | _ => ntInSet ((cykBuildTable leafData nodeData w (w.length - 1)).getD
            ((w.length - 1) * w.length) 0) startIdx

end CYKDefs

/-! ## CYK Bitvector is Primitive Recursive -/

section CYKPrimrec

variable {T : Type} [DecidableEq T] [Primcodable T]

/-
`cykLeafBV` with fixed leaf data is Primrec.
-/
private lemma primrec_cykLeafBV (ld : List (ℕ × T)) :
    Primrec (fun t : T => cykLeafBV ld t) := by
  have h_foldl : ∀ (l : List (ℕ × T)), Primrec (fun t => List.foldl (fun bv p => if p.2 == t then ntSetBit bv p.1 else bv) 0 l) := by
    intro l
    induction' l using List.reverseRecOn with p l ih;
    · exact Primrec.const 0;
    · simp +zetaDelta at *;
      convert Primrec.ite _ _ _ using 1;
      · exact Primrec.eq.comp ( Primrec.const _ ) ( Primrec.id );
      · exact Primrec.comp ( primrec₂_ntSetBit.comp ( Primrec.fst ) ( Primrec.snd ) ) ( ih.pair ( Primrec.const _ ) );
      · exact ih;
  exact h_foldl ld

/-
The innermost rule step is Primrec₂.
    Context: `(table, n, i, k, j)`. Accumulator: bitvector.
-/
lemma primrec₂_ruleStep (ntR lR rR : ℕ) :
    Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) =>
      if ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) lR &&
         ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 +
            (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) rR
      then ntSetBit bv ntR else bv) := by
  have h_primrec : Primrec (fun ctx : List ℕ × ℕ × ℕ × ℕ × ℕ => ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) := by
    have h_getD : Primrec₂ (fun (l : List ℕ) (i : ℕ) => l.getD i 0) := by
      convert Primrec.list_getD 0 using 1;
    exact h_getD.comp ( Primrec.fst ) ( by exact Primrec.nat_add.comp ( Primrec.nat_mul.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) ) ( Primrec.fst.comp ( Primrec.snd ) ) ) ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) );
  have h_primrec : Primrec (fun ctx : List ℕ × ℕ × ℕ × ℕ × ℕ => ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 + (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) := by
    convert Primrec.list_getD 0 |> Primrec.comp <| Primrec.fst.comp ( Primrec.id ) |> Primrec.pair <| _ using 1;
    apply_rules [ Primrec.nat_add.comp, Primrec.nat_mul.comp, Primrec.nat_sub.comp, Primrec.fst, Primrec.snd ];
    all_goals try { exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd ) ) ) };
    · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) ) ) );
    · exact Primrec.fst.comp ( Primrec.snd );
    · exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd ) );
    · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) ) ) );
    · exact Primrec.const 1;
  have h_primrec : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) => if ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) lR && ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 + (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) rR then ntSetBit bv ntR else bv) := by
    have h_cond : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) => if ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) lR && ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 + (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) rR then true else false) := by
      have h_cond : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) => ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) lR) := by
        have h_cond : Primrec₂ (fun (x : ℕ) (y : ℕ) => ntInSet x y) := by
          exact?;
        convert h_cond.comp ( ‹Primrec fun ctx : List ℕ × ℕ × ℕ × ℕ × ℕ => ctx.1.getD ( ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1 ) 0›.comp ( Primrec.fst ) ) ( Primrec.const lR ) using 1;
      have h_cond : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) => ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 + (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) rR) := by
        convert Primrec₂.comp ( primrec₂_ntInSet ) ( h_primrec.comp ( Primrec.fst ) ) ( Primrec.const rR ) using 1;
      simp +zetaDelta at *;
      exact Primrec₂.comp ( Primrec.and ) ‹_› ‹_›
    convert Primrec.cond h_cond ( show Primrec₂ ( fun ( ctx : List ℕ × ℕ × ℕ × ℕ × ℕ ) ( bv : ℕ ) => ntSetBit bv ntR ) from ?_ ) ( show Primrec₂ ( fun ( ctx : List ℕ × ℕ × ℕ × ℕ × ℕ ) ( bv : ℕ ) => bv ) from ?_ ) using 1;
    · simp +decide [ Primrec₂ ];
      grind;
    · exact Primrec₂.comp ( primrec₂_ntSetBit ) ( Primrec.snd ) ( Primrec.const _ );
    · exact Primrec.snd;
  exact h_primrec

/-- The fold over all rules (fixed `nodeData`) is Primrec₂. -/
lemma primrec₂_allRulesStep (nd : List (ℕ × ℕ × ℕ)) :
    Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ × ℕ) (bv : ℕ) =>
      nd.foldl (fun bv' r =>
        if ntInSet (ctx.1.getD (ctx.2.2.2.2 * ctx.2.1 + ctx.2.2.1) 0) r.2.1 &&
           ntInSet (ctx.1.getD ((ctx.2.2.2.1 - ctx.2.2.2.2) * ctx.2.1 +
              (ctx.2.2.1 + ctx.2.2.2.2 + 1)) 0) r.2.2
        then ntSetBit bv' r.1 else bv') bv) := by
  apply primrec_foldl_fixed
  intro ⟨ntR, lR, rR⟩
  exact primrec₂_ruleStep ntR lR rR

/-
The split-point fold is Primrec.
-/
lemma primrec_splitFold (nd : List (ℕ × ℕ × ℕ)) :
    Primrec (fun (ctx : List ℕ × ℕ × ℕ × ℕ) =>
      (List.range (ctx.2.2.2 + 1)).foldl (fun bv j =>
        nd.foldl (fun bv' r =>
          if ntInSet (ctx.1.getD (j * ctx.2.1 + ctx.2.2.1) 0) r.2.1 &&
             ntInSet (ctx.1.getD ((ctx.2.2.2 - j) * ctx.2.1 +
                (ctx.2.2.1 + j + 1)) 0) r.2.2
          then ntSetBit bv' r.1 else bv') bv
      ) 0) := by
  have h_split_point_fold : Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ × ℕ) (bv : ℕ) =>
    List.range (ctx.2.2.2 + 1) |>.foldl (fun bv' j =>
      nd.foldl (fun bv'' r =>
        if ntInSet (ctx.1.getD (ctx.2.2.1 + j * ctx.2.1) 0) r.2.1 &&
           ntInSet (ctx.1.getD (ctx.2.2.1 + j + 1 + (ctx.2.2.2 - j) * ctx.2.1) 0) r.2.2
        then ntSetBit bv'' r.1 else bv'') bv') bv) := by
          apply_rules [ Primrec₂.comp, Primrec₂.mk ];
          have := @primrec₂_allRulesStep;
          specialize this nd;
          convert Primrec.list_foldl _ _ _ using 1;
          rotate_left;
          exact ℕ;
          exact?;
          exact fun p => List.range ( p.1.2.2.2 + 1 );
          exact fun p => p.2;
          exact fun p q => foldl ( fun bv' r => if ( ntInSet ( p.1.1.getD ( p.1.2.2.1 + q.2 * p.1.2.1 ) 0 ) r.2.1 && ntInSet ( p.1.1.getD ( p.1.2.2.1 + q.2 + 1 + ( p.1.2.2.2 - q.2 ) * p.1.2.1 ) 0 ) r.2.2 ) = true then ntSetBit bv' r.1 else bv' ) q.1 nd;
          · have h_range : Primrec (fun (n : ℕ) => List.range (n + 1)) := by
              exact Primrec.list_range.comp ( Primrec.succ );
            exact h_range.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) );
          · exact Primrec.snd;
          · convert this using 1;
            constructor <;> intro h <;> simp_all +decide [ Primrec₂ ];
            convert this.comp _ using 1;
            rotate_left;
            exact fun p => ⟨ ⟨ p.1.1.1, p.1.1.2.1, p.1.1.2.2.1, p.1.1.2.2.2, p.2.2 ⟩, p.2.1 ⟩;
            · exact Primrec.pair ( Primrec.pair ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.id ) ) ) ) ( Primrec.pair ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.id ) ) ) ) ) ( Primrec.pair ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.id ) ) ) ) ) ) ( Primrec.pair ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst.comp ( Primrec.fst.comp ( Primrec.id ) ) ) ) ) ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) ) ) ) ) ) ) ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.id ) ) );
            · grind;
          · lia;
  convert h_split_point_fold.comp ( Primrec.id ) ( Primrec.const 0 ) using 1;
  grind

/-
The cell computation is Primrec₂.
    First arg: `(table, n, k)`. Second arg: `i`.
-/
lemma primrec₂_cellValue (nd : List (ℕ × ℕ × ℕ)) :
    Primrec₂ (fun (ctx : List ℕ × ℕ × ℕ) (i : ℕ) =>
      if i + ctx.2.2 + 2 > ctx.2.1 then 0
      else (List.range (ctx.2.2 + 1)).foldl (fun bv j =>
        nd.foldl (fun bv' r =>
          if ntInSet (ctx.1.getD (j * ctx.2.1 + i) 0) r.2.1 &&
             ntInSet (ctx.1.getD ((ctx.2.2 - j) * ctx.2.1 + (i + j + 1)) 0) r.2.2
          then ntSetBit bv' r.1 else bv') bv
      ) 0) := by
  refine' Primrec.ite _ _ _;
  · refine' ⟨ _, _ ⟩;
    infer_instance;
    convert Primrec.nat_lt.comp _ _ using 1;
    exact?;
    · exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) );
    · exact Primrec.nat_add.comp ( Primrec.nat_add.comp ( Primrec.snd ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) ( Primrec.const 2 );
  · exact Primrec.const 0;
  · convert primrec_splitFold nd |> Primrec.comp <| _ using 1;
    rotate_left;
    exact fun p => ( p.1.1, p.1.2.1, p.2, p.1.2.2 );
    · exact Primrec.pair ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.pair ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ( Primrec.pair ( Primrec.snd ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) );
    · grind +revert

/-
The step function for Nat.rec is Primrec₂.
-/
lemma primrec₂_cykStep (nd : List (ℕ × ℕ × ℕ)) :
    Primrec₂ (fun (w : List T) (p : ℕ × List ℕ) =>
      p.2 ++ (List.range w.length).map fun i =>
        if i + p.1 + 2 > w.length then 0
        else (List.range (p.1 + 1)).foldl (fun bv j =>
          nd.foldl (fun bv' r =>
            if ntInSet (p.2.getD (j * w.length + i) 0) r.2.1 &&
               ntInSet (p.2.getD ((p.1 - j) * w.length + (i + j + 1)) 0) r.2.2
            then ntSetBit bv' r.1 else bv') bv
        ) 0) := by
  apply_rules [ Primrec₂.comp, Primrec₂.pair, Primrec₂.const ];
  all_goals try apply_rules [ Primrec.fst, Primrec.snd, Primrec.list_map ];
  · exact?;
  · exact Primrec.snd.comp ( Primrec.snd );
  · exact Primrec.list_range.comp ( Primrec.list_length.comp ( Primrec.fst ) );
  · convert primrec₂_cellValue nd using 1;
    constructor <;> intro h;
    · convert primrec₂_cellValue nd using 1;
    · convert h.comp ( Primrec.snd.comp ( Primrec.snd.comp Primrec.fst ) |> Primrec.pair <| Primrec.list_length.comp ( Primrec.fst.comp Primrec.fst ) |> Primrec.pair <| Primrec.fst.comp ( Primrec.snd.comp Primrec.fst ) ) ( Primrec.snd ) using 1

/-
The full CYK table build is Primrec.
-/
lemma primrec_cykBuildTable (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ)) :
    Primrec (fun w : List T =>
      cykBuildTable ld nd w (w.length - 1)) := by
  have h_primrec : Primrec (fun w : List T => w.map (cykLeafBV ld)) := by
    have h_primrec : Primrec (fun t : T => cykLeafBV ld t) := by
      exact?;
    convert Primrec.list_map _ _;
    all_goals try infer_instance;
    · exact Primrec.id;
    · exact Primrec.comp h_primrec ( Primrec.snd );
  have h_primrec_step : Primrec₂ (fun (w : List T) (p : ℕ × List ℕ) => p.2 ++ (List.range w.length).map fun i =>
    if i + p.1 + 2 > w.length then 0
    else (List.range (p.1 + 1)).foldl (fun bv j =>
      nd.foldl (fun bv' r =>
        if ntInSet (p.2.getD (j * w.length + i) 0) r.2.1 &&
           ntInSet (p.2.getD ((p.1 - j) * w.length + (i + j + 1)) 0) r.2.2
        then ntSetBit bv' r.1 else bv') bv
    ) 0) := by
      exact?;
  have := @Primrec.nat_rec;
  convert this h_primrec ( h_primrec_step ) |> Primrec.comp <| Primrec.pair ( Primrec.id ) ( Primrec.nat_sub.comp ( Primrec.list_length ) ( Primrec.const 1 ) ) using 1;
  funext w; exact (by
  induction' w.length - 1 with k ih generalizing w <;> simp +decide [ *, cykBuildTable ])

/-- The full membership check is Primrec. -/
lemma cykMemCheck_eq (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ)) (si : ℕ)
    (w : List T) :
    cykMemCheck ld nd si w =
    ntInSet ((cykBuildTable ld nd w (w.length - 1)).getD
      ((w.length - 1) * w.length) 0) si := by
  cases w with
  | nil => simp [cykMemCheck, cykBuildTable, ntInSet]
  | cons h t => simp [cykMemCheck]

/-- The full membership check is Primrec. -/
lemma primrec_cykMemCheck (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ)) (si : ℕ) :
    Primrec (fun w : List T => cykMemCheck ld nd si w) := by
  have : Primrec (fun w : List T =>
      ntInSet ((cykBuildTable ld nd w (w.length - 1)).getD
        ((w.length - 1) * w.length) 0) si) := by
    exact (primrec₂_ntInSet.comp
      ((Primrec.list_getD 0).comp (primrec_cykBuildTable ld nd)
        (Primrec.nat_mul.comp
          (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
          Primrec.list_length))
      (Primrec.const si))
  exact this.of_eq (fun w => (cykMemCheck_eq ld nd si w).symm)

end CYKPrimrec

/-! ## CYK Bitvector Correctness -/

section CYKCorrectness

variable {T : Type} [DecidableEq T]

/-
Setting a different bit doesn't affect the queried bit.
-/
lemma ntInSet_ntSetBit_ne (bv idx idx' : ℕ) (h : idx ≠ idx') :
    ntInSet (ntSetBit bv idx') idx = ntInSet bv idx := by
  unfold ntSetBit;
  unfold ntInSet; rw [ Nat.shiftLeft_eq ] ;
  grind

/-
`cykLeafBV` correctly tracks membership: bit `idx` is set iff
    `leafData` contains `(idx, t)`.
-/
lemma cykLeafBV_correct (leafData : List (ℕ × T)) (t : T) (idx : ℕ) :
    ntInSet (cykLeafBV leafData t) idx = true ↔ (idx, t) ∈ leafData := by
  induction' leafData using List.reverseRecOn with leafData p ih generalizing idx;
  · simp +decide [ cykLeafBV, ntInSet ];
  · by_cases h : p.2 = t <;> simp_all +decide [ cykLeafBV ];
    · by_cases h' : idx = p.1 <;> simp_all +decide [ ntInSet_ntSetBit_self, ntInSet_ntSetBit_of_true, ntInSet_ntSetBit_ne ];
      · lia;
      · grind;
    · aesop

/-
The CYK table has the expected length.
-/
lemma cykBuildTable_length (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ))
    (w : List T) (k : ℕ) :
    (cykBuildTable ld nd w k).length = (k + 1) * w.length := by
  induction' k with k ih generalizing w;
  · simp [cykBuildTable];
  · unfold cykBuildTable;
    grind

/-
Entries from earlier rows are preserved when adding a new row.
-/
lemma cykBuildTable_getD_prev (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ))
    (w : List T) (k : ℕ) (idx : ℕ) (h : idx < (k + 1) * w.length) :
    (cykBuildTable ld nd w (k + 1)).getD idx 0 =
    (cykBuildTable ld nd w k).getD idx 0 := by
  rw [cykBuildTable];
  rw [ List.getD_append ];
  rw [ cykBuildTable_length ] ; exact h

/-
Generalized stability: entries are preserved across all later rows.
-/
lemma cykBuildTable_getD_stable (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ))
    (w : List T) (k k' : ℕ) (hk : k ≤ k') (idx : ℕ) (h : idx < (k + 1) * w.length) :
    (cykBuildTable ld nd w k').getD idx 0 =
    (cykBuildTable ld nd w k).getD idx 0 := by
  induction' hk with k' hk ih;
  · rfl;
  · rw [ ← ih, cykBuildTable_getD_prev ];
    nlinarith [ Nat.succ_le_succ hk ]

/-
Characterization of the nodeData fold: bit `idx` is set in the result iff
    it was set in `init` or there's a matching rule in `nd`.
-/
lemma foldl_rules_ntInSet (nd : List (ℕ × ℕ × ℕ)) (left_bv right_bv init : ℕ) (idx : ℕ) :
    ntInSet (nd.foldl (fun bv' r =>
      if ntInSet left_bv r.2.1 && ntInSet right_bv r.2.2
      then ntSetBit bv' r.1 else bv') init) idx = true ↔
    (ntInSet init idx = true ∨
     ∃ r ∈ nd, r.1 = idx ∧ ntInSet left_bv r.2.1 = true ∧ ntInSet right_bv r.2.2 = true) := by
  induction' nd using List.reverseRecOn with nd hd ih generalizing init;
  · aesop;
  · by_cases h : ntInSet left_bv hd.2.1 && ntInSet right_bv hd.2.2 <;> simp_all +decide [ List.foldl_append ];
    · by_cases h' : idx = hd.1 <;> simp_all +decide [ ntInSet_ntSetBit_self, ntInSet_ntSetBit_of_true, ntInSet_ntSetBit_ne ];
      · exact Or.inr ⟨ _, _, Or.inr rfl, h ⟩;
      · grind;
    · grind

/-
Characterization of the double fold: bit `idx` is set iff there's a matching
    split point and rule.
-/
lemma foldl_splits_ntInSet (nd : List (ℕ × ℕ × ℕ)) (table : List ℕ)
    (n i k : ℕ) (idx : ℕ) :
    ntInSet ((List.range (k + 1)).foldl (fun bv j =>
      nd.foldl (fun bv' r =>
        if ntInSet (table.getD (j * n + i) 0) r.2.1 &&
           ntInSet (table.getD ((k - j) * n + (i + j + 1)) 0) r.2.2
        then ntSetBit bv' r.1 else bv') bv
    ) 0) idx = true ↔
    ∃ j ∈ List.range (k + 1), ∃ r ∈ nd,
      r.1 = idx ∧
      ntInSet (table.getD (j * n + i) 0) r.2.1 = true ∧
      ntInSet (table.getD ((k - j) * n + (i + j + 1)) 0) r.2.2 = true := by
  simp +decide [ foldl_rules_ntInSet ];
  constructor <;> intro h;
  · contrapose! h;
    -- By induction on the range, we can show that the bit at `idx` is not set after each step of the fold.
    have h_ind : ∀ (j : ℕ) (hj : j ≤ k + 1), ntInSet (List.foldl (fun bv j => List.foldl (fun bv' r => if ntInSet (table[j * n + i]?.getD 0) r.2.1 = true ∧ ntInSet (table[(k - j) * n + (i + j + 1)]?.getD 0) r.2.2 = true then ntSetBit bv' r.1 else bv') bv nd) 0 (List.range j)) idx = false := by
      intro j hj; induction' j with j ih <;> simp_all +decide [ List.range_succ ] ;
      · exact?;
      · convert foldl_rules_ntInSet nd _ _ _ _ using 1;
        rotate_left;
        exact table[j * n + i]?.getD 0;
        exact table[(k - j) * n + (i + j + 1)]?.getD 0;
        exact foldl ( fun bv j => foldl ( fun bv' r => if ntInSet ( table[j * n + i]?.getD 0 ) r.2.1 = true ∧ ntInSet ( table[( k - j ) * n + ( i + j + 1 ) ]?.getD 0 ) r.2.2 = true then ntSetBit bv' r.1 else bv' ) bv nd ) 0 ( range j );
        exact idx;
        grind;
    exact ne_of_eq_of_ne ( h_ind _ le_rfl ) ( by decide );
  · -- By definition of `foldl`, if there exists a `j` in the range such that the condition holds, then the bit at `idx` will be set to `true` after processing all `j`'s.
    have h_foldl : ∀ (l : List ℕ) (j : ℕ) (hj : j ∈ l), (∃ r ∈ nd, r.1 = idx ∧ ntInSet (table[j * n + i]?.getD 0) r.2.1 ∧ ntInSet (table[(k - j) * n + (i + j + 1)]?.getD 0) r.2.2) → ntInSet (List.foldl (fun bv j => List.foldl (fun bv' r => if ntInSet (table[j * n + i]?.getD 0) r.2.1 ∧ ntInSet (table[(k - j) * n + (i + j + 1)]?.getD 0) r.2.2 then ntSetBit bv' r.1 else bv') bv nd) 0 l) idx := by
      intro l j hj h; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl_append ] ;
      by_cases h : j ∈ l <;> simp_all +decide [ foldl_rules_ntInSet ];
      · have h_foldl_rules : ∀ (bv : ℕ) (idx : ℕ), ntInSet bv idx = true → ∀ (nd : List (ℕ × ℕ × ℕ)), ntInSet (List.foldl (fun bv' r => if ntInSet (table[ih * n + i]?.getD 0) r.2.1 ∧ ntInSet (table[(k - ih) * n + (i + ih + 1)]?.getD 0) r.2.2 then ntSetBit bv' r.1 else bv') bv nd) idx = true := by
          intros bv idx hbv nd; induction' nd using List.reverseRecOn with nd ih <;> simp_all +decide [ List.foldl_append ] ;
          split_ifs <;> simp_all +decide [ ntInSet_ntSetBit_self, ntInSet_ntSetBit_of_true ];
        exact h_foldl_rules _ _ ‹_› _;
      · rename_i h₁ h₂;
        obtain ⟨ a, b, h₁, h₂, h₃ ⟩ := h₂;
        convert foldl_rules_ntInSet nd _ _ _ _ |>.2 _ using 1;
        congr! 1;
        congr! 1;
        rotate_left;
        exact table[ih * n + i]?.getD 0;
        exact table[(k - ih) * n + (i + ih + 1)]?.getD 0;
        · exact Or.inr ⟨ _, h₁, rfl, h₂, h₃ ⟩;
        · grind;
    obtain ⟨ j, hj₁, hj₂ ⟩ := h; specialize h_foldl ( List.range ( k + 1 ) ) j; aesop;

open ChomskyNormalFormGrammar in
/-- Base case of CYK correctness: single characters. -/
lemma cykBuildTable_correct_base
    (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (enc : g.NT → ℕ) (enc_inj : Function.Injective enc)
    (leafData : List (ℕ × T))
    (h_leaf : ∀ nt t, (enc nt, t) ∈ leafData ↔
        ChomskyNormalFormRule.leaf nt t ∈ g.rules)
    (nodeData : List (ℕ × ℕ × ℕ))
    (w : List T) (hw : w ≠ [])
    (i : ℕ) (hi : i < w.length)
    (nt : g.NT) :
    ntInSet ((cykBuildTable leafData nodeData w 0).getD i 0) (enc nt) =
    cykDecideAux (g.rules.toList) nt (w.drop i |>.take 1) := by
  convert cykLeafBV_correct leafData ( w[i] ) ( enc nt ) using 1;
  rw [ show cykBuildTable leafData nodeData w 0 = w.map ( cykLeafBV leafData ) from rfl ] ; simp +decide [ List.getElem?_map, hi ] ;
  rw [ show drop i w = w[i] :: drop ( i + 1 ) w from ?_, List.take ] <;> norm_num [ hi ];
  rw [ cykDecideAux ];
  rw [ List.any_eq ];
  by_cases h : ( enc nt, w[i] ) ∈ leafData <;> simp +decide [ h, h_leaf ];
  · rw [ decide_eq_true ];
    exact ⟨ ChomskyNormalFormRule.leaf nt ( w[i] ), h_leaf nt ( w[i] ) |>.1 h, by simp +decide ⟩;
  · rw [ decide_eq_false ];
    contrapose! h;
    rcases h with ⟨ x, hx₁, hx₂ ⟩ ; rcases x with ( _ | _ ) <;> simp_all +decide ;

/-
The table entry at row (l+1), column i unfolds to the fold expression.
-/
lemma cykBuildTable_entry_step (ld : List (ℕ × T)) (nd : List (ℕ × ℕ × ℕ))
    (w : List T) (l i : ℕ) (hi : i + l + 2 ≤ w.length) :
    (cykBuildTable ld nd w (l + 1)).getD ((l + 1) * w.length + i) 0 =
    (List.range (l + 1)).foldl (fun bv j =>
      nd.foldl (fun bv' r =>
        if ntInSet ((cykBuildTable ld nd w l).getD (j * w.length + i) 0) r.2.1 &&
           ntInSet ((cykBuildTable ld nd w l).getD ((l - j) * w.length + (i + j + 1)) 0) r.2.2
        then ntSetBit bv' r.1 else bv') bv
    ) 0 := by
  rw [ cykBuildTable ];
  simp +zetaDelta at *;
  rw [ List.getElem?_append ] ; norm_num;
  rw [ cykBuildTable_length ];
  grind

open ChomskyNormalFormGrammar in
/-- cykDecideAux on a word of length ≥ 2 checks split points and node rules. -/
lemma cykDecideAux_long {NT : Type} [DecidableEq NT]
    (rules : List (ChomskyNormalFormRule T NT))
    (nt : NT) (w : List T) (hw : w.length ≥ 2) :
    cykDecideAux rules nt w =
    (List.finRange (w.length - 1)).any fun ⟨j, hj⟩ =>
      rules.any fun r =>
        match r with
        | ChomskyNormalFormRule.node n' c₁ c₂ =>
          decide (n' = nt) && cykDecideAux rules c₁ (w.take (j + 1)) &&
            cykDecideAux rules c₂ (w.drop (j + 1))
        | _ => false := by
  rcases w with ( _ | ⟨ h₁, _ | ⟨ h₂, w ⟩ ⟩ ) <;> simp +arith +decide at hw ⊢;
  rw [ cykDecideAux ];
  congr! 2

set_option maxHeartbeats 800000 in
open ChomskyNormalFormGrammar in
/-- Step case of CYK correctness: longer substrings.
    Requires `h_node_range` to ensure all nodeData entries are in range of enc. -/
lemma cykBuildTable_correct_step
    (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (enc : g.NT → ℕ) (enc_inj : Function.Injective enc)
    (leafData : List (ℕ × T))
    (h_leaf : ∀ nt t, (enc nt, t) ∈ leafData ↔
        ChomskyNormalFormRule.leaf nt t ∈ g.rules)
    (nodeData : List (ℕ × ℕ × ℕ))
    (h_node : ∀ nt l r, (enc nt, enc l, enc r) ∈ nodeData ↔
        ChomskyNormalFormRule.node nt l r ∈ g.rules)
    (h_node_range : ∀ r ∈ nodeData, ∃ nt l r', r = (enc nt, enc l, enc r'))
    (h_leaf_range : ∀ p ∈ leafData, ∃ nt, p.1 = enc nt)
    (w : List T) (hw : w ≠ [])
    (l : ℕ) (i : ℕ) (hi : i + l + 2 ≤ w.length)
    (nt : g.NT)
    (ih : ∀ l' < l + 1, ∀ i' : ℕ, i' + l' + 1 ≤ w.length → ∀ nt' : g.NT,
      ntInSet ((cykBuildTable leafData nodeData w l').getD
        (l' * w.length + i') 0) (enc nt') =
      cykDecideAux (g.rules.toList) nt'
        (w.drop i' |>.take (l' + 1))) :
    ntInSet ((cykBuildTable leafData nodeData w (l + 1)).getD
      ((l + 1) * w.length + i) 0) (enc nt) =
    cykDecideAux (g.rules.toList) nt
      (w.drop i |>.take (l + 2)) := by
  have h_LHS : ntInSet ((cykBuildTable leafData nodeData w (l + 1)).getD ((l + 1) * w.length + i) 0) (enc nt) = true ↔ ∃ j ∈ List.range (l + 1), ∃ r ∈ nodeData, r.1 = enc nt ∧ ntInSet ((cykBuildTable leafData nodeData w l).getD (j * w.length + i) 0) r.2.1 ∧ ntInSet ((cykBuildTable leafData nodeData w l).getD ((l - j) * w.length + (i + j + 1)) 0) r.2.2 := by
    rw [ cykBuildTable_entry_step ];
    · convert foldl_splits_ntInSet nodeData ( cykBuildTable leafData nodeData w l ) w.length i l ( enc nt ) using 1;
    · linarith;
  have h_LHS_simplified : ntInSet ((cykBuildTable leafData nodeData w (l + 1)).getD ((l + 1) * w.length + i) 0) (enc nt) = true ↔ ∃ j ∈ List.range (l + 1), ∃ c₁ c₂ : g.NT, ChomskyNormalFormRule.node nt c₁ c₂ ∈ g.rules ∧ cykDecideAux g.rules.toList c₁ (take (j + 1) (drop i w)) ∧ cykDecideAux g.rules.toList c₂ (take (l - j + 1) (drop (i + j + 1) w)) := by
    constructor <;> intro h;
    · obtain ⟨ j, hj, r, hr, hr', hr'', hr''' ⟩ := h_LHS.mp h;
      obtain ⟨ nt', l', r', rfl ⟩ := h_node_range r hr; simp_all +decide [ enc_inj.eq_iff ] ;
      use j, hj, l', r';
      have := ih j hj i ( by linarith ) l'; have := ih ( l - j ) ( Nat.sub_le _ _ ) ( i + j + 1 ) ( by omega ) r'; simp_all +decide [ Nat.sub_add_comm hj ] ;
      have h_stable : ∀ (k k' : ℕ) (hk : k ≤ k') (idx : ℕ) (h : idx < (k + 1) * w.length), (cykBuildTable leafData nodeData w k').getD idx 0 = (cykBuildTable leafData nodeData w k).getD idx 0 :=
        fun k k' hk idx hidx => cykBuildTable_getD_stable leafData nodeData w k k' hk idx hidx;
      have := h_stable j l hj ( j * w.length + i ) ( by nlinarith ) ; have := h_stable ( l - j ) l ( Nat.sub_le _ _ ) ( ( l - j ) * w.length + ( i + j + 1 ) ) ( by nlinarith [ Nat.sub_add_cancel hj ] ) ; aesop;
    · obtain ⟨ j, hj₁, c₁, c₂, h₁, h₂, h₃ ⟩ := h;
      refine' h_LHS.mpr ⟨ j, hj₁, _, _, _, _, _ ⟩;
      exact ( enc nt, enc c₁, enc c₂ );
      · exact h_node nt c₁ c₂ |>.2 h₁;
      · rfl;
      · specialize ih j (by
        linarith [ List.mem_range.mp hj₁ ]) i (by
        linarith [ List.mem_range.mp hj₁ ]) c₁;
        grind +suggestions;
      · convert ih ( l - j ) ( by linarith [ Nat.sub_add_cancel ( show j ≤ l from by linarith [ List.mem_range.mp hj₁ ] ) ] ) ( i + j + 1 ) ( by linarith [ Nat.sub_add_cancel ( show j ≤ l from by linarith [ List.mem_range.mp hj₁ ] ) ] ) c₂ using 1;
        · rw [ cykBuildTable_getD_stable ];
          · exact Nat.sub_le _ _;
          · nlinarith [ Nat.sub_add_cancel ( show j ≤ l from by linarith [ List.mem_range.mp hj₁ ] ) ];
        · exact h₃.symm;
  have h_RHS : cykDecideAux g.rules.toList nt (take (l + 2) (drop i w)) = true ↔ ∃ j < l + 1, ∃ c₁ c₂ : g.NT, ChomskyNormalFormRule.node nt c₁ c₂ ∈ g.rules ∧ cykDecideAux g.rules.toList c₁ (take (j + 1) (drop i w)) ∧ cykDecideAux g.rules.toList c₂ (take (l - j + 1) (drop (i + j + 1) w)) := by
    rw [cykDecideAux_long];
    · simp +decide [ List.any_eq_true, List.finRange ];
      constructor;
      · rintro ⟨ a, x, hx, hx' ⟩;
        rcases x with ( _ | ⟨ n', c₁, c₂ ⟩ ) <;> simp +decide at hx' ⊢;
        refine' ⟨ a, _, c₁, c₂, _, _, _ ⟩;
        · exact Nat.le_of_lt_succ ( lt_of_lt_of_le a.2 ( Nat.sub_le_of_le_add <| by omega ) );
        · lia;
        · grind;
        · convert hx'.2 using 2;
          rw [ List.drop_take ];
          rw [ show l + 2 - ( a + 1 ) = l - a + 1 by omega ] ; simp +decide [ add_assoc, List.drop_drop ] ;
      · rintro ⟨ j, hj, c₁, c₂, h₁, h₂, h₃ ⟩;
        use ⟨ j, by
          omega ⟩
        generalize_proofs at *;
        use ChomskyNormalFormRule.node nt c₁ c₂;
        simp_all +decide [ List.take_take, List.drop_take ];
        exact ⟨ by rw [ min_eq_left ( by linarith ) ] ; exact h₂, by rw [ show l + 1 - j = l - j + 1 by omega ] ; exact h₃ ⟩;
    · grind +revert;
  simp_all +decide [ List.mem_range ];
  convert h_LHS_simplified using 1;
  convert Bool.eq_iff_iff using 1;
  convert Iff.rfl using 2;
  convert foldl_splits_ntInSet nodeData ( cykBuildTable leafData nodeData w l ) w.length i l ( enc nt ) using 1;
  · congr! 1;
    congr! 1;
    convert cykBuildTable_entry_step leafData nodeData w l i ( by linarith ) using 1;
  · simp +decide [ List.mem_range, Nat.lt_succ_iff ]

open ChomskyNormalFormGrammar in
/-- Key correctness lemma: CYK bitvector table entries correspond to `cykDecideAux`.
    Proved by strong induction on `l`. -/
lemma cykBuildTable_correct
    (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT]
    (enc : g.NT → ℕ) (enc_inj : Function.Injective enc)
    (leafData : List (ℕ × T))
    (h_leaf : ∀ nt t, (enc nt, t) ∈ leafData ↔
        ChomskyNormalFormRule.leaf nt t ∈ g.rules)
    (nodeData : List (ℕ × ℕ × ℕ))
    (h_node : ∀ nt l r, (enc nt, enc l, enc r) ∈ nodeData ↔
        ChomskyNormalFormRule.node nt l r ∈ g.rules)
    (h_node_range : ∀ r ∈ nodeData, ∃ nt l r', r = (enc nt, enc l, enc r'))
    (h_leaf_range : ∀ p ∈ leafData, ∃ nt, p.1 = enc nt)
    (w : List T) (hw : w ≠ [])
    (k l : ℕ) (hl : l ≤ k) (hk : k < w.length)
    (i : ℕ) (hi : i + l + 1 ≤ w.length)
    (nt : g.NT) :
    ntInSet ((cykBuildTable leafData nodeData w k).getD
      (l * w.length + i) 0) (enc nt) =
    cykDecideAux (g.rules.toList) nt
      (w.drop i |>.take (l + 1)) := by
  -- First reduce to l = k via stability
  rw [cykBuildTable_getD_stable leafData nodeData w l k hl
    (l * w.length + i) (by nlinarith)]
  -- Now induct on l
  induction l using Nat.strongRecOn generalizing k i nt with
  | _ l ih_strong =>
    match l with
    | 0 =>
      -- Base case
      simp only [zero_mul, zero_add]
      exact cykBuildTable_correct_base g enc enc_inj leafData h_leaf nodeData w hw i (by omega) nt
    | l + 1 =>
      -- Step case: use cykBuildTable_correct_step
      apply cykBuildTable_correct_step g enc enc_inj leafData h_leaf nodeData h_node h_node_range h_leaf_range w hw l i hi nt
      intro l' hl' i' hi' nt'
      exact ih_strong l' hl' l' (le_refl l') (by omega) i' hi' nt'

end CYKCorrectness

/-! ## Main theorem: CF membership is ComputablePred -/

section CFComputablePred

variable {T : Type} [Fintype T] [DecidableEq T]

-- Helper: the CYK membership check correctly decides CNF language membership
open ChomskyNormalFormGrammar in
lemma cykMemCheck_correct_cnf
    {T : Type} [DecidableEq T] [Primcodable T]
    (cnf : ChomskyNormalFormGrammar.{0, 0} T) [DecidableEq cnf.NT]
    (enc : cnf.NT → ℕ) (enc_inj : Function.Injective enc)
    (leafData : List (ℕ × T))
    (h_leaf : ∀ nt t, (enc nt, t) ∈ leafData ↔ ChomskyNormalFormRule.leaf nt t ∈ cnf.rules)
    (nodeData : List (ℕ × ℕ × ℕ))
    (h_node : ∀ nt l r, (enc nt, enc l, enc r) ∈ nodeData ↔ ChomskyNormalFormRule.node nt l r ∈ cnf.rules)
    (h_node_range : ∀ r ∈ nodeData, ∃ nt l r', r = (enc nt, enc l, enc r'))
    (h_leaf_range : ∀ p ∈ leafData, ∃ nt, p.1 = enc nt)
    (w : List T) (hw : w ≠ []) :
    cykMemCheck leafData nodeData (enc cnf.initial) w = true ↔ w ∈ cnf.language := by
  rw [cykMemCheck_eq]
  have hlen : 0 < w.length := by cases w <;> simp_all
  have hcorr := @cykBuildTable_correct T _ cnf _ enc enc_inj leafData h_leaf nodeData h_node
    h_node_range h_leaf_range w hw (w.length - 1) (w.length - 1) (le_refl _)
    (by omega) 0 (by omega) cnf.initial
  simp only [List.drop_zero, Nat.sub_add_cancel hlen, List.take_length, Nat.add_zero] at hcorr
  rw [hcorr]
  have h_cyk := cykDecideAux_iff_canDerive cnf cnf.rules.toList (fun r => Finset.mem_toList) cnf.initial w
  have h_cd := canDerive_iff_derives cnf cnf.initial w
  rw [mem_language_iff]
  unfold Generates
  exact h_cyk.trans h_cd

/-- Membership in a context-free language is a computable predicate. -/
theorem cf_membership_computable
    (g : CF_grammar T) [Fintype g.nt] [DecidableEq g.nt]
    [Primcodable T] :
    ComputablePred (fun w : List T => w ∈ CF_language g) := by
  obtain ⟨enc, enc_inj⟩ : ∃ enc : (mathlib_cfg_of_cfg g).toCNF.NT → ℕ, Function.Injective enc := by
    have h_encodable : Encodable (mathlib_cfg_of_cfg g).toCNF.NT := by
      have h_encodable : Encodable ((g.nt ⊕ T) ⊕ (r : ContextFreeRule T (g.nt ⊕ T)) × Fin (r.output.length - 2)) := by
        have h_encodable : Countable ((g.nt ⊕ T) ⊕ (r : ContextFreeRule T (g.nt ⊕ T)) × Fin (r.output.length - 2)) := by
          have h_countable : Countable (ContextFreeRule T (g.nt ⊕ T)) := by
            have h_countable : Countable ((g.nt ⊕ T) × List (Symbol T (g.nt ⊕ T))) := by
              infer_instance;
            exact ( Equiv.ofBijective ( fun x => ( x.input, x.output ) ) ⟨ fun x y h => by cases x; cases y; aesop, fun x => by cases x; exact ⟨ ⟨ _, _ ⟩, rfl ⟩ ⟩ ) |> fun h => h.countable_iff.mpr h_countable;
          infer_instance;
        exact Encodable.ofCountable _;
      exact h_encodable;
    exact ⟨ _, Encodable.encode_injective ⟩;
  obtain ⟨leafData, nodeData, h_leaf, h_node, h_node_range, h_leaf_range⟩ : ∃ leafData : List (ℕ × T), ∃ nodeData : List (ℕ × ℕ × ℕ),
    (∀ nt t, (enc nt, t) ∈ leafData ↔ ChomskyNormalFormRule.leaf nt t ∈ (mathlib_cfg_of_cfg g).toCNF.rules) ∧
    (∀ nt l r, (enc nt, enc l, enc r) ∈ nodeData ↔ ChomskyNormalFormRule.node nt l r ∈ (mathlib_cfg_of_cfg g).toCNF.rules) ∧
    (∀ r ∈ nodeData, ∃ nt l r', r = (enc nt, enc l, enc r')) ∧
    (∀ p ∈ leafData, ∃ nt, p.1 = enc nt) := by
      refine' ⟨ _, _, _, _, _, _ ⟩;
      exact (mathlib_cfg_of_cfg g).toCNF.rules.toList.filterMap (fun r => match r with | ChomskyNormalFormRule.leaf nt t => some (enc nt, t) | _ => none);
      exact (mathlib_cfg_of_cfg g).toCNF.rules.toList.filterMap (fun r => match r with | ChomskyNormalFormRule.node nt l r => some (enc nt, enc l, enc r) | _ => none);
      · intro nt t; simp +decide [ ChomskyNormalFormRule.leaf ] ;
        constructor <;> intro h;
        · obtain ⟨ a, ha, ha' ⟩ := h; rcases a with ( _ | _ | a ) <;> simp_all +decide ;
          grind;
        · exact ⟨ _, h, rfl ⟩;
      · intro nt l r;
        rw [ List.mem_filterMap ];
        constructor;
        · rintro ⟨ a, ha, ha' ⟩;
          cases a <;> simp_all +decide [ enc_inj.eq_iff ];
        · exact fun h => ⟨ ChomskyNormalFormRule.node nt l r, by simpa using h, rfl ⟩;
      · grind;
      · grind;
  obtain ⟨emptyVal, h_empty⟩ : ∃ emptyVal : Bool, [] ∈ CF_language g ↔ emptyVal = true := by
    by_cases h : [] ∈ CF_language g <;> [ exact ⟨ Bool.true, by simpa ⟩ ; exact ⟨ Bool.false, by simpa ⟩ ];
  obtain ⟨f, hf⟩ : ∃ f : List T → Bool, Computable f ∧ ∀ w, w ∈ CF_language g ↔ f w = true := by
    refine' ⟨ fun w => if w = [] then emptyVal else cykMemCheck leafData nodeData ( enc ( ( mathlib_cfg_of_cfg g ).toCNF.initial ) ) w, _, _ ⟩;
    · convert Computable.cond _ _ _ using 1;
      rotate_left;
      exact fun w => w = [];
      exact fun _ => emptyVal;
      exact fun w => cykMemCheck leafData nodeData ( enc ( ( mathlib_cfg_of_cfg g ).toCNF.initial ) ) w;
      · convert Computable.of_eq _ _;
        exact fun w => w.length = 0;
        · convert Computable.of_eq _ _;
          exact fun w => Nat.recOn w.length ( Bool.true ) fun _ _ => Bool.false;
          · convert Computable.nat_casesOn _ _ _ using 1;
            · exact Computable.list_length;
            · exact Computable.const Bool.true;
            · exact Computable.const Bool.false;
          · intro n; cases n <;> simp +decide ;
        · aesop;
      · exact Computable.const _;
      · exact Primrec.to_comp ( primrec_cykMemCheck _ _ _ );
      · grind;
    · intro w; by_cases hw : w = [] <;> simp +decide [ hw, h_empty ] ;
      rw [ CF_language_eq_mathlib_language ];
      convert cykMemCheck_correct_cnf ( mathlib_cfg_of_cfg g |> ContextFreeGrammar.toCNF ) enc enc_inj leafData h_leaf nodeData h_node h_node_range h_leaf_range w hw |> Iff.symm using 1;
      · rw [ ← ContextFreeGrammar.toCNF_correct ];
        grind;
      · exact?;
  convert hf.1 using 1;
  constructor <;> intro h <;> rw [ ComputablePred ] at * <;> aesop

/-
Context-free membership is uniformly computable for encoded CFGs (raw `ComputablePred`
decider; the packaged `ComputableMembership` statement over the CF class lives in
`ContextFree/Decidability/Characterization.lean`).
-/
theorem contextFree_membership_computablePred [Primcodable T] :
    ComputablePred (fun p : EncodedCFG T × List T => p.2 ∈ contextFreeLanguageOf p.1) := by
  constructor;
  convert checkMembershipEncoded_computable' using 1;
  all_goals try infer_instance;
  ext ⟨G, w⟩; simp [checkMembershipEncoded_correct];
  rw [ eq_comm ];
  grind +suggestions;
  exact Classical.decPred _

end CFComputablePred
