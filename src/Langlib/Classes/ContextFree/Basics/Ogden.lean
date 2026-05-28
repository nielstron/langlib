module

public import Langlib.Classes.ContextFree.Definition
public import Langlib.Classes.ContextFree.Pumping.Pumping
public import Mathlib.CategoryTheory.Category.Basic
import Langlib.Classes.ContextFree.NormalForms.ChomskyNormalFormTranslation
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
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

set_option maxHeartbeats 400000

/-! # Ogden's Lemma for Context-Free Languages

This file states and proves Ogden's lemma, a strengthened version of the pumping lemma
for context-free languages. While the pumping lemma guarantees that long enough strings
in a CFL can be "pumped", Ogden's lemma allows the user to *mark* certain positions of
the string and guarantees that the pump pieces contain marked positions.

## Main declarations

- `countMarkedIn` — counts how many positions in a range `[start, start + len)` are marked.
- `Language.IsContextFree.ogdens_lemma` — Ogden's lemma stated using Mathlib's `Language.IsContextFree`.
- `CF_ogdens_lemma` — Ogden's lemma stated using the project's `is_CF` predicate.

## Implementation notes

The proof follows the standard Ogden argument:
1. Convert to Chomsky Normal Form (CNF).
2. Navigate along the "marked path" to find a subtree with bounded marked height.
3. Use the pigeonhole principle on branching nonterminals to find a repeat.
4. The branching property ensures marked positions in the pump parts (v, y).
5. The bounded marked height ensures the marked-count bound on vxy.

The core technical lemma `ogdens_marked_path_decomp` implements the marked-path
pigeonhole argument. It tracks branching nonterminals in a finite set and detects
collisions to construct the Ogden decomposition.

## References

* William F. Ogden, "A Helpful Result for Proving Inherent Ambiguity",
  *Mathematical Systems Theory* **2** (1968), 191–194.
-/

open List

variable {T : Type}

/-! ## Counting marked positions -/

/-- Count how many natural numbers in the interval `[start, start + len)` satisfy `P`. -/
noncomputable def countMarkedIn (P : ℕ → Prop) [DecidablePred P] (start len : ℕ) : ℕ :=
  ((Finset.range len).filter (fun i => P (start + i))).card

@[simp]
lemma countMarkedIn_zero (P : ℕ → Prop) [DecidablePred P] (start : ℕ) :
    countMarkedIn P start 0 = 0 := by simp [countMarkedIn]

lemma countMarkedIn_le (P : ℕ → Prop) [DecidablePred P] (start len : ℕ) :
    countMarkedIn P start len ≤ len :=
  le_trans (Finset.card_filter_le _ _) (by simp)

lemma countMarkedIn_add (P : ℕ → Prop) [DecidablePred P] (start len₁ len₂ : ℕ) :
    countMarkedIn P start (len₁ + len₂) =
      countMarkedIn P start len₁ + countMarkedIn P (start + len₁) len₂ := by
  unfold countMarkedIn
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]
  ac_rfl

lemma countMarkedIn_mono_len (P : ℕ → Prop) [DecidablePred P] (start : ℕ) {len₁ len₂ : ℕ}
    (h : len₁ ≤ len₂) : countMarkedIn P start len₁ ≤ countMarkedIn P start len₂ :=
  Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.range_mono h

/-! ## Parse tree marked count -/

namespace ChomskyNormalFormGrammar

universe uT uN

variable {T : Type uT} {g : ChomskyNormalFormGrammar.{uN, uT} T}

namespace parseTree

/-- The number of marked positions in a parse tree's yield. -/
noncomputable def mc (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} (t : parseTree n) : ℕ :=
  countMarkedIn P offset t.yield.length

lemma mc_node (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n c₁ c₂ : g.NT} (t₁ : parseTree c₁) (t₂ : parseTree c₂)
    (h : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules) :
    (parseTree.node t₁ t₂ h).mc P offset =
      t₁.mc P offset + t₂.mc P (offset + t₁.yield.length) := by
  simp only [mc, yield, List.length_append]
  exact countMarkedIn_add P offset t₁.yield.length t₂.yield.length

/-! ## Marked height -/

/-- The "marked branching depth": maximum number of branching points (where both
    children have marked descendants) on any root-to-leaf path. -/
noncomputable def markedHeight (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} : parseTree n → ℕ
  | leaf _ _ => 0
  | @node _ _ _ c₁ c₂ t₁ t₂ _ =>
    let mc₁ := t₁.mc P offset
    let mc₂ := t₂.mc P (offset + t₁.yield.length)
    if mc₁ > 0 ∧ mc₂ > 0 then
      max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) + 1
    else if mc₁ > 0 then
      t₁.markedHeight P offset
    else
      t₂.markedHeight P (offset + t₁.yield.length)

/-! ## Key bounds -/

/-- mc ≤ 2^markedHeight -/
lemma mc_le_pow_markedHeight (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} (t : parseTree n) :
    t.mc P offset ≤ 2 ^ (t.markedHeight P offset) := by
  induction t generalizing offset with
  | leaf t₁ t₂ =>
    simp [mc, markedHeight]
    exact countMarkedIn_le P offset (leaf t₁ t₂).yield.length
  | node t₁ t₂ hnc ih₁ ih₂ =>
    rw [mc_node]
    show t₁.mc P offset + t₂.mc P (offset + t₁.yield.length) ≤
      2 ^ (markedHeight P offset (t₁.node t₂ hnc))
    rw [show markedHeight P offset (t₁.node t₂ hnc) =
      if t₁.mc P offset > 0 ∧ t₂.mc P (offset + t₁.yield.length) > 0 then
        max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) + 1
      else if t₁.mc P offset > 0 then t₁.markedHeight P offset
      else t₂.markedHeight P (offset + t₁.yield.length) from rfl]
    split_ifs <;> simp_all [pow_succ']
    calc t₁.mc P offset + t₂.mc P (offset + t₁.yield.length)
        ≤ 2 ^ t₁.markedHeight P offset + 2 ^ t₂.markedHeight P (offset + t₁.yield.length) :=
          Nat.add_le_add (ih₁ _) (ih₂ _)
      _ ≤ 2 ^ max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) +
          2 ^ max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) :=
          Nat.add_le_add
            (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
            (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
      _ = _ := by ring

/-- 2^h ≤ mc → h ≤ markedHeight -/
lemma mc_implies_markedHeight (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} (t : parseTree n) (h : ℕ) (hmc : 2 ^ h ≤ t.mc P offset) :
    h ≤ t.markedHeight P offset := by
  have h_mc_le := mc_le_pow_markedHeight P offset t
  exact le_of_not_gt fun hlt => by linarith [pow_lt_pow_right₀ (by decide : 1 < 2) hlt]

/-- markedHeight ≤ height -/
lemma markedHeight_le_height (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} (t : parseTree n) :
    t.markedHeight P offset ≤ t.height := by
  induction t generalizing offset with
  | leaf => exact Nat.zero_le _
  | node t₁ t₂ _ ih₁ ih₂ =>
    unfold markedHeight height
    grind +ring

variable [DecidableEq g.NT] [DecidableEq (Σ _n : g.NT, parseTree _n)]

/-! ## Derivation helper lemmas -/

/-- From a derivation of the left child, build a derivation of the node. -/
lemma node_derives_left {n c₁ c₂ : g.NT} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    {u : List (Symbol T g.NT)}
    (h : g.Derives [Symbol.nonterminal c₁] u) :
    g.Derives [Symbol.nonterminal n] (u ++ t₂.yield.map Symbol.terminal) := by
  have h1 : g.Derives [Symbol.nonterminal n] ([Symbol.nonterminal c₁] ++ [Symbol.nonterminal c₂]) :=
    .single ⟨_, hnc, ChomskyNormalFormRule.Rewrites.input_output⟩
  have h2 : g.Derives ([Symbol.nonterminal c₁] ++ [Symbol.nonterminal c₂])
      (u ++ [Symbol.nonterminal c₂]) :=
    h.append_right _
  have h3 : g.Derives (u ++ [Symbol.nonterminal c₂])
      (u ++ t₂.yield.map Symbol.terminal) :=
    t₂.yield_derives.append_left _
  exact h1.trans (h2.trans h3)

/-- From a derivation of the right child, build a derivation of the node. -/
lemma node_derives_right {n c₁ c₂ : g.NT} {t₁ : parseTree c₁}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    {u : List (Symbol T g.NT)}
    (h : g.Derives [Symbol.nonterminal c₂] u) :
    g.Derives [Symbol.nonterminal n] (t₁.yield.map Symbol.terminal ++ u) := by
  have h1 : g.Derives [Symbol.nonterminal n] ([Symbol.nonterminal c₁] ++ [Symbol.nonterminal c₂]) :=
    .single ⟨_, hnc, ChomskyNormalFormRule.Rewrites.input_output⟩
  have h2 : g.Derives ([Symbol.nonterminal c₁] ++ [Symbol.nonterminal c₂])
      (t₁.yield.map Symbol.terminal ++ [Symbol.nonterminal c₂]) :=
    t₁.yield_derives.append_right _
  have h3 : g.Derives (t₁.yield.map Symbol.terminal ++ [Symbol.nonterminal c₂])
      (t₁.yield.map Symbol.terminal ++ u) :=
    h.append_left _
  exact h1.trans (h2.trans h3)

/-! ## Helper lemmas for extending Ogden results through nodes -/

/-
Extend a Left Ogden result from the left child through a node.
-/
lemma ogden_extend_left_via_left {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {u v x y z : List T}
    (hyield : t₁.yield = u ++ v ++ x ++ y ++ z)
    (hmark : 0 < countMarkedIn P (offset + u.length) v.length +
        countMarkedIn P (offset + u.length + v.length + x.length) y.length)
    (hbound : countMarkedIn P (offset + u.length) (v.length + x.length + y.length) ≤
        2 ^ g.generators.card)
    (hpump : ∀ i : ℕ, g.Derives [Symbol.nonterminal c₁]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal)) :
    ∃ u' v' x' y' z' : List T,
      (parseTree.node t₁ t₂ hnc).yield = u' ++ v' ++ x' ++ y' ++ z' ∧
      0 < countMarkedIn P (offset + u'.length) v'.length +
          countMarkedIn P (offset + u'.length + v'.length + x'.length) y'.length ∧
      countMarkedIn P (offset + u'.length) (v'.length + x'.length + y'.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u' ++ v' ^+^ i ++ x' ++ y' ^+^ i ++ z').map Symbol.terminal) := by
  refine' ⟨ u, v, x, y, z ++ t₂.yield, _, _, _, _ ⟩ <;> simp_all +decide [ List.append_assoc ];
  · unfold parseTree.yield; aesop;
  · intro i
    specialize hpump i
    generalize_proofs at *; (
    convert ChomskyNormalFormGrammar.parseTree.node_derives_left hnc hpump using 1 ; simp +decide [ List.append_assoc ];
    convert rfl using 1)

/-
Extend a Left Ogden result from the right child through a node.
-/
lemma ogden_extend_left_via_right {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {u v x y z : List T}
    (hyield : t₂.yield = u ++ v ++ x ++ y ++ z)
    (hmark : 0 < countMarkedIn P (offset + t₁.yield.length + u.length) v.length +
        countMarkedIn P (offset + t₁.yield.length + u.length + v.length + x.length) y.length)
    (hbound : countMarkedIn P (offset + t₁.yield.length + u.length)
        (v.length + x.length + y.length) ≤ 2 ^ g.generators.card)
    (hpump : ∀ i : ℕ, g.Derives [Symbol.nonterminal c₂]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal)) :
    ∃ u' v' x' y' z' : List T,
      (parseTree.node t₁ t₂ hnc).yield = u' ++ v' ++ x' ++ y' ++ z' ∧
      0 < countMarkedIn P (offset + u'.length) v'.length +
          countMarkedIn P (offset + u'.length + v'.length + x'.length) y'.length ∧
      countMarkedIn P (offset + u'.length) (v'.length + x'.length + y'.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u' ++ v' ^+^ i ++ x' ++ y' ^+^ i ++ z').map Symbol.terminal) := by
  refine' ⟨ t₁.yield ++ u, v, x, y, z, _, _, _, _ ⟩ <;> simp_all +decide [ List.length_append, nTimes ];
  · exact hyield ▸ rfl;
  · simpa only [ add_assoc ] using hmark;
  · simpa only [ add_assoc ] using hbound;
  · intro i;
    convert node_derives_right hnc ( hpump i ) using 1

/-
Extend a Right Ogden result from the left child through a node.
-/
lemma ogden_extend_right_via_left {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (s : Finset g.NT)
    {n' : g.NT} (hn's : n' ∈ s)
    {p' : parseTree n'} {u₁ z₁ : List T}
    (hyield : t₁.yield = u₁ ++ p'.yield ++ z₁)
    (hmc' : 0 < p'.mc P (offset + u₁.length))
    (hderiv : g.Derives [Symbol.nonterminal c₁]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₁.map Symbol.terminal)) :
    ∃ n'' ∈ s, ∃ (p'' : parseTree n'') (u₂ z₂ : List T),
      (parseTree.node t₁ t₂ hnc).yield = u₂ ++ p''.yield ++ z₂ ∧
      0 < p''.mc P (offset + u₂.length) ∧
      g.Derives [Symbol.nonterminal n]
        (u₂.map Symbol.terminal ++ [Symbol.nonterminal n''] ++ z₂.map Symbol.terminal) := by
  use n', hn's, p', u₁, z₁ ++ t₂.yield.map (fun x => x);
  refine' ⟨ _, hmc', _ ⟩;
  · simp +decide [ hyield, parseTree.yield ];
  · convert node_derives_left hnc hderiv using 1 ; simp +decide [ *, List.map_append ];
    congr! 1

/-
Extend a Right Ogden result from the right child through a node.
-/
lemma ogden_extend_right_via_right {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (s : Finset g.NT)
    {n' : g.NT} (hn's : n' ∈ s)
    {p' : parseTree n'} {u₁ z₁ : List T}
    (hyield : t₂.yield = u₁ ++ p'.yield ++ z₁)
    (hmc' : 0 < p'.mc P (offset + t₁.yield.length + u₁.length))
    (hderiv : g.Derives [Symbol.nonterminal c₂]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₁.map Symbol.terminal)) :
    ∃ n'' ∈ s, ∃ (p'' : parseTree n'') (u₂ z₂ : List T),
      (parseTree.node t₁ t₂ hnc).yield = u₂ ++ p''.yield ++ z₂ ∧
      0 < p''.mc P (offset + u₂.length) ∧
      g.Derives [Symbol.nonterminal n]
        (u₂.map Symbol.terminal ++ [Symbol.nonterminal n''] ++ z₂.map Symbol.terminal) := by
  use n';
  refine' ⟨ hn's, p', t₁.yield ++ u₁, z₁, _, _, _ ⟩;
  · simp +decide [ hyield, parseTree.yield ];
  · simpa [ add_assoc, List.length_append ] using hmc';
  · convert node_derives_right hnc hderiv using 1 ; simp +decide [ *, List.map_append ];
    congr! 1

/-
Construct an Ogden Left result from a collision with n in the left child,
    when both children have marked positions (branching node).
-/
lemma ogden_pump_from_left {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (hmc₂ : 0 < t₂.mc P (offset + t₁.yield.length))
    (hmc_bound : (parseTree.node t₁ t₂ hnc).mc P offset ≤ 2 ^ g.generators.card)
    {p' : parseTree n} {u₁ z₁ : List T}
    (hyield₁ : t₁.yield = u₁ ++ p'.yield ++ z₁)
    (hmc' : 0 < p'.mc P (offset + u₁.length))
    (hderiv₁ : g.Derives [Symbol.nonterminal c₁]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n] ++ z₁.map Symbol.terminal)) :
    ∃ u v x y z : List T,
      (parseTree.node t₁ t₂ hnc).yield = u ++ v ++ x ++ y ++ z ∧
      0 < countMarkedIn P (offset + u.length) v.length +
          countMarkedIn P (offset + u.length + v.length + x.length) y.length ∧
      countMarkedIn P (offset + u.length) (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal) := by
  refine' ⟨ [ ], u₁, p'.yield, z₁ ++ t₂.yield, [ ], _, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_range ];
  · simp [parseTree.yield, hyield₁];
  · contrapose! hmc₂; simp_all +decide [ add_assoc, countMarkedIn_add ] ;
    exact hmc₂.2.2;
  · unfold mc at hmc_bound; simp_all +decide [ countMarkedIn ] ;
    convert hmc_bound using 3 ; simp +decide [ *, ChomskyNormalFormGrammar.parseTree.yield ] ; ring!;
  · intro i
    have h_deriv : g.Derives [Symbol.nonterminal n] (map Symbol.terminal (u₁ ^+^ i) ++ [Symbol.nonterminal n] ++ map Symbol.terminal ((z₁ ++ t₂.yield) ^+^ i)) := by
      convert pumping_string _ i using 1;
      rotate_left;
      exact u₁.map Symbol.terminal
      exact ( z₁ ++ t₂.yield ).map Symbol.terminal
      generalize_proofs at *; (
      convert node_derives_left hnc hderiv₁ using 1 ; simp +decide [ hyield₁ ];
      congr! 1);
      exact congr_arg₂ _ ( congr_arg₂ _ ( by exact? ) rfl ) ( by exact? );
    grind +suggestions

/-
Construct an Ogden Left result from a collision with n in the right child,
    when both children have marked positions (branching node).
-/
lemma ogden_pump_from_right {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (hmc₁ : 0 < t₁.mc P offset)
    (hmc_bound : (parseTree.node t₁ t₂ hnc).mc P offset ≤ 2 ^ g.generators.card)
    {p' : parseTree n} {u₁ z₁ : List T}
    (hyield₂ : t₂.yield = u₁ ++ p'.yield ++ z₁)
    (hmc' : 0 < p'.mc P (offset + t₁.yield.length + u₁.length))
    (hderiv₂ : g.Derives [Symbol.nonterminal c₂]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n] ++ z₁.map Symbol.terminal)) :
    ∃ u v x y z : List T,
      (parseTree.node t₁ t₂ hnc).yield = u ++ v ++ x ++ y ++ z ∧
      0 < countMarkedIn P (offset + u.length) v.length +
          countMarkedIn P (offset + u.length + v.length + x.length) y.length ∧
      countMarkedIn P (offset + u.length) (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal) := by
  by_contra h_contra;
  refine' h_contra ⟨ [ ], t₁.yield ++ u₁, p'.yield, z₁, [ ], _, _, _, _ ⟩ <;> simp +decide [ * ];
  · simp +decide [ hyield₂, parseTree.yield ];
  · refine' Or.inl ( lt_of_lt_of_le hmc₁ _ );
    apply_rules [ countMarkedIn_mono_len ] ; simp +decide [ * ] ;
  · convert hmc_bound using 1;
    unfold mc; simp +decide [ *, add_assoc ] ;
    rw [ show ( t₁.node t₂ hnc ).yield = t₁.yield ++ t₂.yield from rfl, hyield₂ ] ; simp +decide [ add_assoc ] ;
  · intro i
    have h_pump : g.Derives [Symbol.nonterminal n] ((t₁.yield ++ u₁).map Symbol.terminal ^+^ i ++ [Symbol.nonterminal n] ++ (z₁.map Symbol.terminal) ^+^ i) := by
      have h_deriv : g.Derives [Symbol.nonterminal n] ((t₁.yield ++ u₁).map Symbol.terminal ++ [Symbol.nonterminal n] ++ (z₁.map Symbol.terminal)) := by
        convert ChomskyNormalFormGrammar.parseTree.node_derives_right hnc _ using 1 ; aesop;
        simpa using hderiv₂;
      have h_pump : ∀ i : ℕ, g.Derives [Symbol.nonterminal n] ((t₁.yield ++ u₁).map Symbol.terminal ^+^ i ++ [Symbol.nonterminal n] ++ (z₁.map Symbol.terminal) ^+^ i) := by
        intro i
        have := h_deriv
        exact?
      generalize_proofs at *;
      exact h_pump i
    generalize_proofs at *;
    grind +suggestions

/-! ## Core Ogden marked-path pigeonhole -/

lemma ogdens_marked_path_decomp {n : g.NT} (p : parseTree n)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (s : Finset g.NT) (hs_sub : s ⊆ g.generators)
    (hp : g.generators.card ≤ p.markedHeight P offset + s.card)
    (hmc : 0 < p.mc P offset)
    (hmc_bound : p.mc P offset ≤ 2 ^ g.generators.card) :
    (∃ u v x y z : List T,
      p.yield = u ++ v ++ x ++ y ++ z ∧
      0 < countMarkedIn P (offset + u.length) v.length +
          countMarkedIn P (offset + u.length + v.length + x.length) y.length ∧
      countMarkedIn P (offset + u.length) (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal)) ∨
    (∃ n' ∈ s, ∃ (p' : parseTree n') (u₁ z₁ : List T),
      p.yield = u₁ ++ p'.yield ++ z₁ ∧
      0 < p'.mc P (offset + u₁.length) ∧
      g.Derives [Symbol.nonterminal n]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₁.map Symbol.terminal)) := by
  induction p generalizing offset s with
  | @leaf n t hnt =>
    simp only [markedHeight] at hp
    have hs_eq : s = g.generators := (Finset.subset_iff_eq_of_card_le (by omega)).mp hs_sub
    have hn_gen : n ∈ g.generators := input_mem_generators hnt
    have hn_s : n ∈ s := hs_eq ▸ hn_gen
    right
    refine ⟨n, hn_s, leaf t hnt, [], [], ?_, ?_, ?_⟩
    · simp [yield]
    · simpa using hmc
    · simp; exact Derives.refl _
  | @node n c₁ c₂ t₁ t₂ hnc ih₁ ih₂ =>
    have hmc_eq := mc_node P offset t₁ t₂ hnc
    by_cases h₁ : (0 : ℕ) < t₁.mc P offset <;> by_cases h₂ : (0 : ℕ) < t₂.mc P (offset + t₁.yield.length)
    · -- Case A: both children have mc > 0
      have hmh : markedHeight P offset (node t₁ t₂ hnc) =
          max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) + 1 := by
        show (let mc₁ := _; let mc₂ := _; if mc₁ > 0 ∧ mc₂ > 0 then _ else _) = _
        simp [h₁, h₂]
      rw [hmh] at hp
      by_cases hns : n ∈ s
      · right
        refine ⟨n, hns, node t₁ t₂ hnc, [], [], ?_, ?_, ?_⟩
        · simp [yield]
        · simpa using hmc
        · simp; exact Derives.refl _
      · have hn_gen : n ∈ g.generators := input_mem_generators hnc
        have hs'_sub : insert n s ⊆ g.generators := Finset.insert_subset hn_gen hs_sub
        have hs'_card : (insert n s).card = s.card + 1 := by
          rw [Finset.card_insert_eq_ite, if_neg hns]
        by_cases hmh_le : t₂.markedHeight P (offset + t₁.yield.length) ≤ t₁.markedHeight P offset
        · -- recurse left
          have hp₁ : g.generators.card ≤ t₁.markedHeight P offset + (insert n s).card := by
            simp only [Nat.max_eq_left hmh_le] at hp; omega
          have hmc₁_bnd : t₁.mc P offset ≤ (2 : ℕ) ^ g.generators.card := by omega
          rcases ih₁ offset (insert n s) hs'_sub hp₁ h₁ hmc₁_bnd with h_l | h_r
          · obtain ⟨u, v, x, y, z, hy, hm, hb, hd⟩ := h_l
            exact Or.inl (ogden_extend_left_via_left hnc P offset hy hm hb hd)
          · obtain ⟨n', hn', p', u₁', z₁', hy, hmc'', hd⟩ := h_r
            have h_or : n' = n ∨ n' ∈ s := Finset.mem_insert.mp hn'
            rcases h_or with h_eq | hn's
            · subst h_eq
              exact Or.inl (ogden_pump_from_left hnc P offset h₂ hmc_bound hy hmc'' hd)
            · exact Or.inr (ogden_extend_right_via_left hnc P offset s hn's hy hmc'' hd)
        · -- recurse right
          push_neg at hmh_le
          have hp₂ : g.generators.card ≤ t₂.markedHeight P (offset + t₁.yield.length) + (insert n s).card := by
            have := Nat.le_max_right (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length))
            omega
          have hmc₂_bnd : t₂.mc P (offset + t₁.yield.length) ≤ (2 : ℕ) ^ g.generators.card := by omega
          rcases ih₂ (offset + t₁.yield.length) (insert n s) hs'_sub hp₂ h₂ hmc₂_bnd with h_l | h_r
          · obtain ⟨u, v, x, y, z, hy, hm, hb, hd⟩ := h_l
            exact Or.inl (ogden_extend_left_via_right hnc P offset hy hm hb hd)
          · obtain ⟨n', hn', p', u₁', z₁', hy, hmc'', hd⟩ := h_r
            have h_or : n' = n ∨ n' ∈ s := Finset.mem_insert.mp hn'
            rcases h_or with h_eq | hn's
            · subst h_eq
              exact Or.inl (ogden_pump_from_right hnc P offset h₁ hmc_bound hy hmc'' hd)
            · exact Or.inr (ogden_extend_right_via_right hnc P offset s hn's hy hmc'' hd)
    · -- Case B: only left child has mc > 0
      simp only [not_lt, Nat.le_zero] at h₂
      have hmh : markedHeight P offset (node t₁ t₂ hnc) = t₁.markedHeight P offset := by
        show (let mc₁ := _; let mc₂ := _; if mc₁ > 0 ∧ mc₂ > 0 then _ else _) = _
        simp [h₁, h₂]
      rw [hmh] at hp
      have hmc₁_bnd : t₁.mc P offset ≤ (2 : ℕ) ^ g.generators.card := by omega
      rcases ih₁ offset s hs_sub hp h₁ hmc₁_bnd with h_l | h_r
      · obtain ⟨u, v, x, y, z, hy, hm, hb, hd⟩ := h_l
        exact Or.inl (ogden_extend_left_via_left hnc P offset hy hm hb hd)
      · obtain ⟨n', hn', p', u₁', z₁', hy, hmc'', hd⟩ := h_r
        exact Or.inr (ogden_extend_right_via_left hnc P offset s hn' hy hmc'' hd)
    · -- Case C: only right child has mc > 0
      simp only [not_lt, Nat.le_zero] at h₁
      have hmh : markedHeight P offset (node t₁ t₂ hnc) =
          t₂.markedHeight P (offset + t₁.yield.length) := by
        show (let mc₁ := _; let mc₂ := _; if mc₁ > 0 ∧ mc₂ > 0 then _ else _) = _
        simp [h₁, h₂]
      rw [hmh] at hp
      have hmc₂_bnd : t₂.mc P (offset + t₁.yield.length) ≤ (2 : ℕ) ^ g.generators.card := by omega
      rcases ih₂ (offset + t₁.yield.length) s hs_sub hp h₂ hmc₂_bnd with h_l | h_r
      · obtain ⟨u, v, x, y, z, hy, hm, hb, hd⟩ := h_l
        exact Or.inl (ogden_extend_left_via_right hnc P offset hy hm hb hd)
      · obtain ⟨n', hn', p', u₁', z₁', hy, hmc'', hd⟩ := h_r
        exact Or.inr (ogden_extend_right_via_right hnc P offset s hn' hy hmc'' hd)
    · -- Case D: neither child has mc > 0, contradiction
      simp only [not_lt, Nat.le_zero] at h₁ h₂
      omega

/-! ## Navigation to bounded-markedHeight subtree -/

/-
Navigate along the marked path to find a subtree with `markedHeight = k`.
-/
lemma ogdens_restrict_mh {n : g.NT} (p : parseTree n)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ) (k : ℕ)
    (hmh : k ≤ p.markedHeight P offset) (hmc : 0 < p.mc P offset) :
    ∃ (n' : g.NT) (q : parseTree n') (u₀ z₀ : List T),
      p.yield = u₀ ++ q.yield ++ z₀ ∧
      q.markedHeight P (offset + u₀.length) = k ∧
      0 < q.mc P (offset + u₀.length) ∧
      g.Derives [Symbol.nonterminal n]
        (u₀.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₀.map Symbol.terminal) := by
  by_contra! h_contra;
  induction' p with _ _ _ _ ih generalizing offset k;
  · unfold markedHeight at *; simp_all +decide [ List.length ] ;
    specialize h_contra _ ( leaf ‹_› ‹_› ) [ ] [ ] ; simp_all +decide [ List.length ];
    exact h_contra ( Relation.ReflTransGen.refl );
  · rename_i t₁ t₂ hnc ih₁ ih₂;
    by_cases h₁ : 0 < mc P offset t₁ <;> by_cases h₂ : 0 < mc P (offset + t₁.yield.length) t₂ <;> simp +decide [ *, markedHeight ] at hmh hmc ⊢;
    · by_cases hk : k ≤ max (markedHeight P offset t₁) (markedHeight P (offset + t₁.yield.length) t₂);
      · by_cases hk₁ : k ≤ markedHeight P offset t₁;
        · specialize ih₁ offset k hk₁ h₁;
          refine' ih₁ fun n' q u₀ z₀ h₁ h₂ h₃ h₄ => h_contra n' q u₀ ( z₀ ++ t₂.yield ) _ _ _ _;
          · simp +decide [ *, parseTree.yield ];
          · exact h₂;
          · exact h₃;
          · convert node_derives_left hnc h₄ using 1;
            any_goals exact t₂;
            simp +decide [ List.map_append ];
        · specialize ih₂ ( offset + t₁.yield.length ) ( k ) ( by
            grind +qlia ) h₂
          generalize_proofs at *; (
          simp +zetaDelta at *;
          obtain ⟨ n', q, u₀, z₀, h₁, h₂, h₃, h₄ ⟩ := ih₂; specialize h_contra n' q ( t₁.yield ++ u₀ ) z₀; simp_all +decide [ parseTree.yield ] ;
          simp_all +decide [ add_assoc ];
          exact h_contra ( by simpa [ ← List.append_assoc ] using node_derives_right hnc h₄ ));
      · specialize h_contra _ ( t₁.node t₂ hnc ) [ ] [ ] ; simp_all +decide [ parseTree.yield ];
        exact h_contra ( by rw [ show markedHeight P offset ( t₁.node t₂ hnc ) = max ( markedHeight P offset t₁ ) ( markedHeight P ( offset + t₁.yield.length ) t₂ ) + 1 from by rw [ markedHeight ] ; aesop ] ; omega ) ( Relation.ReflTransGen.refl );
    · specialize ih₁ offset k hmh h₁;
      refine' ih₁ fun n' q u₀ z₀ h₁ h₂ h₃ h₄ => h_contra n' q u₀ ( z₀ ++ t₂.yield ) _ _ _ _;
      · simp +decide [ h₁, parseTree.yield ];
      · exact h₂;
      · exact h₃;
      · convert ChomskyNormalFormGrammar.parseTree.node_derives_left hnc h₄ using 1 ; simp +decide [ h₁, List.map_append ];
        all_goals tauto;
    · specialize ih₂ ( offset + t₁.yield.length ) k hmh h₂;
      contrapose! ih₂; simp_all +decide [ markedHeight ] ;
      intro n' q u₀ z₀ h₁ h₂ h₃ h₄; specialize h_contra n' q ( t₁.yield ++ u₀ ) z₀; simp_all +decide [ parseTree.yield ] ;
      simp_all +decide [ add_assoc ];
      exact h_contra ( by simpa [ ← List.append_assoc ] using node_derives_right hnc h₄ );
    · simp_all +decide [ mc_node ]

/-! ## Ogden's lemma for CNF grammars -/

/-
Ogden's lemma for CNF grammars. The pumping constant is `2 ^ g.generators.card`.
-/
lemma ogdens_cnf {w : List T} (hwg : w ∈ g.language) (P : ℕ → Prop) [DecidablePred P]
    (hw : countMarkedIn P 0 w.length ≥ 2 ^ g.generators.card) :
    ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      0 < countMarkedIn P u.length v.length +
          countMarkedIn P (u.length + v.length + x.length) y.length ∧
      countMarkedIn P u.length (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, u ++ v ^+^ i ++ x ++ y ^+^ i ++ z ∈ g.language := by
  by_cases h_empty : ∃ p : ChomskyNormalFormGrammar.parseTree g.initial, p.yield = w ∧ p.markedHeight P 0 < g.generators.card;
  · obtain ⟨ p, rfl, hp ⟩ := h_empty;
    exact absurd hw ( not_le_of_gt ( lt_of_le_of_lt ( mc_le_pow_markedHeight P 0 p ) ( pow_lt_pow_right₀ ( by decide ) hp ) ) );
  · -- Apply the Ogden's lemma to the parse tree p.
    obtain ⟨p, hp⟩ : ∃ p : ChomskyNormalFormGrammar.parseTree g.initial, p.yield = w ∧ p.markedHeight P 0 ≥ g.generators.card := by
      obtain ⟨p, hp⟩ : ∃ p : ChomskyNormalFormGrammar.parseTree g.initial, p.yield = w := by
        -- Apply the lemma that states if there's a derivation from the initial nonterminal to the terminal symbols of w, then there exists a parse tree p with yield w.
        apply ChomskyNormalFormGrammar.Derives.yield; assumption;
      exact ⟨ p, hp, le_of_not_gt fun h => h_empty ⟨ p, hp, h ⟩ ⟩;
    -- Apply Ogden's lemma to find a marked path in the parse tree.
    obtain ⟨n', q, u₀, z₀, hq⟩ : ∃ n' : g.NT, ∃ q : parseTree n', ∃ u₀ z₀ : List T,
      p.yield = u₀ ++ q.yield ++ z₀ ∧
      q.markedHeight P (0 + u₀.length) = g.generators.card ∧
      0 < q.mc P (0 + u₀.length) ∧
      g.Derives [Symbol.nonterminal g.initial]
        (u₀.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₀.map Symbol.terminal) := by
          apply ogdens_restrict_mh p P 0 g.generators.card hp.right (by
          have h_mc_pos : p.mc P 0 ≥ 2 ^ g.generators.card := by
            unfold mc; aesop;
          generalize_proofs at *; (
          exact lt_of_lt_of_le ( by positivity ) h_mc_pos));
    -- Apply Ogden's lemma to find a marked path in the parse tree q.
    obtain ⟨u', v, x, y, z', hq'⟩ : ∃ u' v x y z' : List T,
      q.yield = u' ++ v ++ x ++ y ++ z' ∧
      0 < countMarkedIn P (u₀.length + u'.length) v.length +
          countMarkedIn P (u₀.length + u'.length + v.length + x.length) y.length ∧
      countMarkedIn P (u₀.length + u'.length) (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n']
        ((u' ++ v ^+^ i ++ x ++ y ^+^ i ++ z').map Symbol.terminal) := by
          have := ogdens_marked_path_decomp q P (u₀.length) ∅; simp_all +decide ;
          apply this;
          exact le_trans ( mc_le_pow_markedHeight P u₀.length q ) ( by simp +decide [ hq.2.1 ] );
    refine' ⟨ u₀ ++ u', v, x, y, z' ++ z₀, _, _, _, _ ⟩ <;> simp_all +decide [ List.append_assoc ];
    intro i
    have h_deriv : g.Derives [Symbol.nonterminal g.initial] (u₀.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₀.map Symbol.terminal) := by
      convert hq.2.2.2 using 1 ; simp +decide [ List.append_assoc ]
    have h_deriv' : g.Derives [Symbol.nonterminal n'] ((u' ++ v ^+^ i ++ x ++ y ^+^ i ++ z').map Symbol.terminal) := by
      grind
    exact (by
    convert h_deriv.trans _ using 1
    generalize_proofs at *; (
    grind +suggestions))

end parseTree
end ChomskyNormalFormGrammar

/-! ## Ogden's lemma for general context-free languages -/

/-- Ogden's lemma for context-free languages (Mathlib formulation). -/
theorem Language.IsContextFree.ogdens_lemma {L : Language T} (hL : L.IsContextFree) :
    ∃ p : ℕ, ∀ (w : List T), w ∈ L →
      ∀ (P : ℕ → Prop) [DecidablePred P],
        p ≤ countMarkedIn P 0 w.length →
        ∃ u v x y z : List T,
          w = u ++ v ++ x ++ y ++ z ∧
          0 < countMarkedIn P u.length v.length +
              countMarkedIn P (u.length + v.length + x.length) y.length ∧
          countMarkedIn P u.length (v.length + x.length + y.length) ≤ p ∧
          ∀ i : ℕ, u ++ v ^+^ i ++ x ++ y ^+^ i ++ z ∈ L := by
  obtain ⟨g, rfl⟩ := hL
  classical
  use 2 ^ g.toCNF.generators.card
  intro w hwg P _ hw2
  by_cases hw : w = []
  · simp [hw] at hw2
  · obtain ⟨u, v, x, y, z, hw, hvy, hvxy, hL⟩ :=
      ChomskyNormalFormGrammar.parseTree.ogdens_cnf
        (g.toCNF_correct ▸ ⟨hwg, hw⟩) P hw2
    exact ⟨u, v, x, y, z, hw, hvy, hvxy, fun i => Set.diff_subset (g.toCNF_correct ▸ hL i)⟩

/-- Ogden's lemma for context-free languages (project formulation). -/
theorem CF_ogdens_lemma {L : Language T} (cf : is_CF L) :
    ∃ p : ℕ, ∀ (w : List T), w ∈ L →
      ∀ (P : ℕ → Prop) [DecidablePred P],
        p ≤ countMarkedIn P 0 w.length →
        ∃ u v x y z : List T,
          w = u ++ v ++ x ++ y ++ z ∧
          0 < countMarkedIn P u.length v.length +
              countMarkedIn P (u.length + v.length + x.length) y.length ∧
          countMarkedIn P u.length (v.length + x.length + y.length) ≤ p ∧
          ∀ i : ℕ, u ++ v ^+^ i ++ x ++ y ^+^ i ++ z ∈ L := by
  exact Language.IsContextFree.ogdens_lemma (is_CF_iff_isContextFree.mp cf)
