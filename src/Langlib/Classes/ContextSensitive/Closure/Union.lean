module

public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.RecursivelyEnumerable.Closure.Union
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-! # Context-Sensitive Closure Under Union

This file proves that the class of context-sensitive languages is closed under union.

The proof reuses the union grammar construction from the RE closure proof and additionally
shows that the construction preserves the context-sensitive (non-contracting) property.

## Main results

- `union_grammar_context_sensitive` — the union grammar is context-sensitive when both
  inputs are context-sensitive.
- `CS_of_CS_u_CS` — the class of context-sensitive languages is closed under union.
-/

variable {T : Type}

/-
The union grammar preserves the context-sensitive (non-contracting) property.
-/
lemma union_grammar_context_sensitive {g₁ g₂ : grammar T}
    (h₁ : grammar_context_sensitive g₁) (h₂ : grammar_context_sensitive g₂) :
    grammar_context_sensitive (union_grammar g₁ g₂) := by
  intro r hr;
  unfold union_grammar at hr; simp_all +decide [ List.mem_cons ] ;
  rcases hr with ( rfl | rfl | ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ lift_rule_ ];
  · obtain ⟨ γ, hγ₁, hγ₂ ⟩ := h₁ a ha;
    unfold lift_string_ at *; aesop;
  · obtain ⟨ γ, hγ₁, hγ₂ ⟩ := h₂ a ha;
    simp_all +decide [ lift_string_ ]

/-- The class of context-sensitive languages is closed under union. -/
theorem CS_of_CS_u_CS (L₁ : Language T) (L₂ : Language T) :
    is_CS L₁ ∧ is_CS L₂ → is_CS (L₁ + L₂) := by
  rintro ⟨⟨g₁, hcs₁, hL₁⟩, ⟨g₂, hcs₂, hL₂⟩⟩
  refine ⟨union_grammar g₁ g₂, union_grammar_context_sensitive hcs₁ hcs₂, ?_⟩
  ext w
  constructor
  · intro hw
    rw [Language.mem_add, ← hL₁, ← hL₂]
    exact in_L₁_or_L₂_of_in_union hw
  · intro hw
    cases hw with
    | inl h₁ => exact in_union_of_in_L₁ (hL₁ ▸ h₁)
    | inr h₂ => exact in_union_of_in_L₂ (hL₂ ▸ h₂)

/-- The class of context-sensitive languages is closed under union. -/
theorem CS_closedUnderUnion : ClosedUnderUnion (α := T) is_CS :=
  fun L₁ L₂ h₁ h₂ => CS_of_CS_u_CS L₁ L₂ ⟨h₁, h₂⟩
