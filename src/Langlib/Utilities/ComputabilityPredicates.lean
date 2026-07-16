module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.Language
public import Langlib.Utilities.PromiseComputability
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



/-!
# Abstract Computability Predicates for Encoded Language Classes

This file defines predicates capturing genuine, uniform computability properties of
encoded language presentations.

The important point is that the encoded object representing the language is an
argument of the computed predicate. For example, membership takes both the encoded
language and the candidate word as input; emptiness takes the encoded language as
input; equivalence takes both encoded languages as input.

These predicates are intentionally separate from statements of the form
`ComputablePred (fun w => w ∈ L)` for a fixed language `L`. Such a statement may
only say that one already-chosen language has computable membership. The definitions
below express a uniform algorithm for a whole encoded presentation class.

Each predicate is stated for a *language class* `C : Set (Language α)` together with
raw encoded syntax `Code`, a semantics `languageOf : Code → Language α`, and a
validity promise `valid : Code → Prop`.  It bundles three obligations:

1. `CharacterizesOn C valid languageOf` — the valid codes are **adequate**: their
   range is exactly `C`.
2. `MembershipSemiDecidable languageOf` — the encoding is **effective**: membership is
   uniformly recursively enumerable from the raw code, so `languageOf` cannot hide
   noncomputable semantic information in the decoding map.
3. The relevant predicate is `ComputablePredOnPromise`: one partial-recursive
   evaluator must halt and answer correctly on every valid code.  It may diverge on
   invalid syntax, and `valid` itself need not be decidable.

Adequacy and effectivity make both the positive results (e.g. "regular emptiness is
decidable") and the negative ones (e.g. "r.e. emptiness is not decidable") genuine
statements about the supplied effective presentation.  Without (1)–(2), a result
could instead be vacuous or rely on an arbitrary, non-effective semantic map.

## Main definitions

- `MembershipSemiDecidable`
- `Characterizes`
- `CharacterizesOn`
- `ComputableMembership`
- `ComputableEmptiness`
- `ComputableUniversality`
- `ComputableEquivalence`
-/

variable {α Code : Type}

/-- The encoding has **semi-decidable (r.e.) uniform membership**: the relation
"`w ∈ languageOf c`" is recursively enumerable in the pair `(c, w)`.

This ensures that the language of `c` can actually be recognized from `c`; in
particular, the semantic map cannot smuggle a non-r.e. membership oracle into the
meaning of a raw code.

The counterexample this rules out is an encoding over codes `Bool × Code`, where
`e (false, c)` denotes the empty language and `e (true, c)` denotes the language of
`c` — unless the language of `c` is empty, in which case `e (true, c)` denotes the
full language instead (so that the `true` branch is always nonempty). This family
still covers every language, yet it lets one decide emptiness from the encoding alone
— a language is empty exactly when the first component is `false` — without any
computation on the language itself. But that decoding function branches on the
undecidable test "is the language of `c` empty?", so it has no semi-decidable
membership relation, and is therefore disallowed.

It is the minimal effectivity demanded of a presentation, the common denominator
across all classes (decidable membership implies it). -/
@[expose]
public def MembershipSemiDecidable [Primcodable Code] [Primcodable α]
    (languageOf : Code → Language α) : Prop :=
  REPred (fun p : Code × List α => p.2 ∈ languageOf p.1)

/-- The encoding **characterizes** the class `C`: its range is exactly `C`.

Soundness (`∃` direction, read right-to-left): every code denotes a language in `C`.
Completeness (left-to-right): every language in `C` is denoted by some code. -/
@[expose]
public def Characterizes (C : Set (Language α)) (languageOf : Code → Language α) : Prop :=
  ∀ L, L ∈ C ↔ ∃ c, languageOf c = L

/-- The valid codes characterize `C`: every valid code denotes a language in `C`,
and every language in `C` has at least one valid code.

The promise may be semantic.  For example, raw program syntax is computably
encoded while `valid c` says that program `c` halts on every word. -/
@[expose]
public def CharacterizesOn (C : Set (Language α)) (valid : Code → Prop)
    (languageOf : Code → Language α) : Prop :=
  ∀ L, L ∈ C ↔ ∃ c, valid c ∧ languageOf c = L

/-- With the trivial promise, `CharacterizesOn` is the original range
characterization. -/
public theorem characterizesOn_true_iff
    (C : Set (Language α)) (languageOf : Code → Language α) :
    CharacterizesOn C (fun _ ↦ True) languageOf ↔ Characterizes C languageOf := by
  simp only [CharacterizesOn, Characterizes, true_and]

/-- An ordinary characterization supplies a characterization under the trivial
promise. -/
public theorem Characterizes.onTrue {C : Set (Language α)}
    {languageOf : Code → Language α} (h : Characterizes C languageOf) :
    CharacterizesOn C (fun _ ↦ True) languageOf :=
  (characterizesOn_true_iff C languageOf).2 h

/-- Uniform computability of **membership** for the class `C` under the encoding
`languageOf`: the encoding is an adequate, effective presentation of `C` and
membership is uniformly decidable.

The input to the decision predicate is a pair `(c, w)`, with `c` the encoded
presentation and `w` the candidate word. -/
@[expose]
public def ComputableMembership [Primcodable Code] [Primcodable α]
    (C : Set (Language α)) (languageOf : Code → Language α)
    (valid : Code → Prop := fun _ ↦ True) : Prop :=
  CharacterizesOn C valid languageOf ∧ MembershipSemiDecidable languageOf ∧
    ComputablePredOnPromise (fun p : Code × List α ↦ valid p.1)
      (fun p ↦ p.2 ∈ languageOf p.1)

/-- Uniform computability of **emptiness** for the class `C` under the encoding
`languageOf`: the encoding is an adequate, effective presentation of `C` and
"`languageOf c = ∅`" is uniformly decidable in the code `c`. -/
@[expose]
public def ComputableEmptiness [Primcodable Code] [Primcodable α]
    (C : Set (Language α)) (languageOf : Code → Language α)
    (valid : Code → Prop := fun _ ↦ True) : Prop :=
  CharacterizesOn C valid languageOf ∧ MembershipSemiDecidable languageOf ∧
    ComputablePredOnPromise valid
      (fun c : Code ↦ languageOf c = (∅ : Set (List α)))

/-- Uniform computability of **universality** for the class `C` under the encoding
`languageOf`: the encoding is an adequate, effective presentation of `C` and
"`languageOf c = univ`" is uniformly decidable in the code `c`. -/
@[expose]
public def ComputableUniversality [Primcodable Code] [Primcodable α]
    (C : Set (Language α)) (languageOf : Code → Language α)
    (valid : Code → Prop := fun _ ↦ True) : Prop :=
  CharacterizesOn C valid languageOf ∧ MembershipSemiDecidable languageOf ∧
    ComputablePredOnPromise valid
      (fun c : Code ↦ languageOf c = Set.univ)

/-- Uniform computability of **equivalence** for the class `C` under the encoding
`languageOf`: the encoding is an adequate, effective presentation of `C` and
"`languageOf c₁ = languageOf c₂`" is uniformly decidable in the pair of codes. -/
@[expose]
public def ComputableEquivalence [Primcodable Code] [Primcodable α]
    (C : Set (Language α)) (languageOf : Code → Language α)
    (valid : Code → Prop := fun _ ↦ True) : Prop :=
  CharacterizesOn C valid languageOf ∧ MembershipSemiDecidable languageOf ∧
    ComputablePredOnPromise (fun p : Code × Code ↦ valid p.1 ∧ valid p.2)
      (fun p ↦ languageOf p.1 = languageOf p.2)

/-- A uniform equivalence procedure decides universality by comparison with
any fixed valid code for the universal language. -/
public theorem ComputableEquivalence.computableUniversality
    [Primcodable Code] [Primcodable α]
    {C : Set (Language α)} {languageOf : Code → Language α}
    {valid : Code → Prop}
    (h : ComputableEquivalence C languageOf valid)
    (universalCode : Code) (hvalid : valid universalCode)
    (hlanguage : languageOf universalCode = Set.univ) :
    ComputableUniversality C languageOf valid := by
  refine ⟨h.1, h.2.1, ?_⟩
  obtain ⟨evalEquivalent, hevalPartrec, hevalSpec⟩ := h.2.2
  let evalUniversal : Code →. Bool :=
    fun c => evalEquivalent (c, universalCode)
  refine ⟨evalUniversal, ?_, ?_⟩
  · exact hevalPartrec.comp
      (Computable.pair Computable.id (Computable.const universalCode))
  · intro c hc
    have hrun := hevalSpec (c, universalCode) ⟨hc, hvalid⟩
    refine ⟨hrun.1, ?_⟩
    simpa only [evalUniversal, hlanguage] using hrun.2

/-- If the presented class contains the universal language, equivalence
computability entails universality computability for the same presentation. -/
public theorem ComputableEquivalence.computableUniversality_of_univ_mem
    [Primcodable Code] [Primcodable α]
    {C : Set (Language α)} {languageOf : Code → Language α}
    {valid : Code → Prop}
    (h : ComputableEquivalence C languageOf valid)
    (huniv : (Set.univ : Language α) ∈ C) :
    ComputableUniversality C languageOf valid := by
  obtain ⟨universalCode, hvalid, hlanguage⟩ := (h.1 Set.univ).mp huniv
  exact h.computableUniversality universalCode hvalid hlanguage
