module

public import Langlib.Classes.RecursivelyEnumerable.Closure.Bijection
public import Langlib.Classes.ContextSensitive.Definition
public import Mathlib.Algebra.Group.End
import Langlib.Grammars.ContextSensitive.UnrestrictedCharacterization
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
@[expose]
public section



/-! # Context-Sensitive Closure Under Bijections

This file proves that context-sensitive languages are preserved under renaming
terminals along an equivalence.

## Strategy

We reuse the unrestricted-level result `bijection_grammar_language` by showing
that the CS bijection construction commutes with the embedding `grammar_of_csg`
into unrestricted grammars.

## Main declarations

- `bijection_csrule`
- `bijection_CS_grammar`
- `bijection_CS_grammar_language`
- `CS_of_bijemap_CS`
- `CS_of_bijemap_CS_rev`
- `CS_bijemap_iff_CS`
-/

variable {T₁ T₂ : Type}

/-- Map a context-sensitive rule along a terminal bijection. -/
def bijection_csrule {N : Type} (π : T₁ ≃ T₂) (r : csrule T₁ N) : csrule T₂ N :=
  csrule.mk (r.context_left.map (map_symbol π)) r.input_nonterminal
    (r.context_right.map (map_symbol π)) (r.output_string.map (map_symbol π))

/-- Map a CS grammar along a terminal bijection. -/
def bijection_CS_grammar (g : CS_grammar T₁) (π : T₁ ≃ T₂) : CS_grammar T₂ :=
  CS_grammar.mk g.nt g.initial (g.rules.map (bijection_csrule π)) (by
    intro r hr
    simp only [List.mem_map] at hr
    rcases hr with ⟨r₀, r₀_in, r_eq⟩
    subst r_eq
    simp only [bijection_csrule, ne_eq, List.map_eq_nil_iff]
    exact g.output_nonempty r₀ r₀_in)

/-- The CS bijection commutes with the embedding into unrestricted grammars. -/
private theorem grammar_of_csg_bijection_comm (g : CS_grammar T₁) (π : T₁ ≃ T₂) :
    grammar_of_csg (bijection_CS_grammar g π) =
    bijection_grammar (grammar_of_csg g) π := by
  unfold grammar_of_csg bijection_grammar bijection_CS_grammar bijection_grule bijection_csrule at * ; aesop ( simp_config := { singlePass := true } ) ;

/-- The bijection CS grammar generates exactly the π-image of the original language. -/
theorem bijection_CS_grammar_language (g : CS_grammar T₁) (π : T₁ ≃ T₂) :
    CS_language (bijection_CS_grammar g π) =
    Language.bijemapLang (CS_language g) π := by
  rw [CS_language_eq_grammar_language, CS_language_eq_grammar_language,
      grammar_of_csg_bijection_comm, bijection_grammar_language]

/-- The class of context-sensitive languages is closed under bijection between terminal alphabets. -/
theorem CS_of_bijemap_CS (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CS L → is_CS (Language.bijemapLang L π) := by
  intro h
  obtain ⟨g, hgL⟩ := is_CS_implies_is_CS_via_csg h
  exact is_CS_via_csg_implies_is_CS ⟨bijection_CS_grammar g π, by rw [bijection_CS_grammar_language, hgL]⟩

/-- The converse direction. -/
theorem CS_of_bijemap_CS_rev (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CS (Language.bijemapLang L π) → is_CS L := by
  intro h
  simpa using CS_of_bijemap_CS π.symm (Language.bijemapLang L π) h

/-- A language is context-sensitive iff its image under a bijection of terminal alphabets is. -/
@[simp] theorem CS_bijemap_iff_CS (π : T₁ ≃ T₂) (L : Language T₁) :
    is_CS (Language.bijemapLang L π) ↔ is_CS L := by
  constructor
  · exact CS_of_bijemap_CS_rev π L
  · exact CS_of_bijemap_CS π L
