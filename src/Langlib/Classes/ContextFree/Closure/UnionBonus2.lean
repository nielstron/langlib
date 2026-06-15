module

import Langlib.Classes.RecursivelyEnumerable.Closure.Union
import Langlib.Grammars.ContextFree.UnrestrictedCharacterization
import Langlib.Utilities.WrittenByOthers.PrintSorries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
@[expose]
public section




/-! # Auxiliary CFG-to-RE Union Construction

This file records an alternate union proof for context-free languages via unrestricted grammars.

## Main declarations

- `union_CF_grammar_same_language`
- `bonus_CF_of_CF_u_CF`
-/

variable {_T : Type}

private def lift_CF_rule₁ {N₁ : Type} (N₂ : Type) (r : (N₁ × List (symbol T N₁))) :
  (Option (N₁ ⊕ N₂)) × List (symbol T (Option (N₁ ⊕ N₂))) :=
(some (Sum.inl r.fst), lift_string_ (Option.some ∘ Sum.inl) r.snd)

private def lift_CF_rule₂ (N₁ : Type) {N₂ : Type} (r : (N₂ × List (symbol T N₂))) :
  (Option (N₁ ⊕ N₂)) × List (symbol T (Option (N₁ ⊕ N₂))) :=
(some (Sum.inr r.fst), lift_string_ (Option.some ∘ Sum.inr) r.snd)

private def union_CF_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (Option (g₁.nt ⊕ g₂.nt)) none (
  (none, [symbol.nonterminal (some (Sum.inl (g₁.initial)))]) :: (
  (none, [symbol.nonterminal (some (Sum.inr (g₂.initial)))]) :: (
  (List.map (lift_CF_rule₁ g₂.nt) g₁.rules) ++
  (List.map (lift_CF_rule₂ g₁.nt) g₂.rules))))

private lemma union_CF_grammar_same_language (g₁ g₂ : CF_grammar T) :
  CF_language (union_CF_grammar g₁ g₂) = grammar_language (union_grammar (grammar_of_cfg g₁) (grammar_of_cfg g₂)) :=
by
  rw [CF_language_eq_grammar_language]
  congr
  unfold union_CF_grammar grammar_of_cfg union_grammar
  dsimp only [List.map]
  congr
  repeat
    rw [List.map_append]
  congr 1 <;> simp only [List.map_map] <;> (apply List.map_congr_left; intro r _; simp [lift_CF_rule₁, lift_CF_rule₂, lift_rule_, lift_string_])

/-- The class of context-free languages is closed under union.
    This theorem is proved by translation from general grammars.
    Compare to `Classes.ContextFree.Closure.UnionBonus`
    which uses a direct proof for context-free grammars. -/
private theorem bonus_CF_of_CF_u_CF (L₁ : Language T) (L₂ : Language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ + L₂)   :=
by
  rintro ⟨h₁, h₂⟩
  obtain ⟨g₁, eq_L₁⟩ := is_CF_implies_is_CF_via_cfg h₁
  obtain ⟨g₂, eq_L₂⟩ := is_CF_implies_is_CF_via_cfg h₂
  rw [CF_language_eq_grammar_language g₁] at eq_L₁
  rw [CF_language_eq_grammar_language g₂] at eq_L₂
  apply is_CF_via_cfg_implies_is_CF
  refine ⟨union_CF_grammar g₁ g₂, ?_⟩
  rw [union_CF_grammar_same_language]
  apply Set.Subset.antisymm
  ·
    intros w hyp
    rw [←eq_L₁, ←eq_L₂]
    exact in_L₁_or_L₂_of_in_union hyp
  ·
    intros w hyp
    cases hyp with
    | inl case_1 =>
        rw [←eq_L₁] at case_1
        exact in_union_of_in_L₁ case_1
    | inr case_2 =>
        rw [←eq_L₂] at case_2
        exact in_union_of_in_L₂ case_2

#check            bonus_CF_of_CF_u_CF
#print_sorries_in bonus_CF_of_CF_u_CF
