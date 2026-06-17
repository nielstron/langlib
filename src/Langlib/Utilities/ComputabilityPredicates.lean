module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.Language
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
an encoding `languageOf : Code → Language α`, and bundles three obligations:

1. `Characterizes C languageOf` — the encoding is **adequate**: its range is exactly
   `C` (sound: every code denotes a member of `C`; complete: every member of `C` is
   denoted by some code).
2. `MembershipSemiDecidable languageOf` — the encoding is **effective**: membership is
   uniformly recursively enumerable.
3. The relevant decision predicate is `ComputablePred`.

Adequacy and effectivity make both the positive results (e.g. "regular emptiness is
decidable") and the negative ones (e.g. "r.e. emptiness is not decidable") genuine
statements about the *class*: without (1)–(2), `¬ComputableEmptiness` could be made
vacuous or trivially true by an adversarial encoding.

## Main definitions

- `MembershipSemiDecidable`
- `Characterizes`
- `ComputableMembership`
- `ComputableEmptiness`
- `ComputableUniversality`
- `ComputableEquivalence`
-/

variable {α Code : Type}

/-- The encoding has **semi-decidable (r.e.) uniform membership**: the relation
"`w ∈ languageOf c`" is recursively enumerable in the pair `(c, w)`.

This ensures that the language of `c` can actually be computed from `c`, i.e. the
encoding does not "smuggle" information about the language into the code.

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

/-- Uniform computability of **membership** for the class `C` under the encoding
`languageOf`: the encoding is an adequate, effective presentation of `C` and
membership is uniformly decidable.

The input to the decision predicate is a pair `(c, w)`, with `c` the encoded
presentation and `w` the candidate word. -/
@[expose]
public def ComputableMembership [Primcodable Code] [Primcodable α]
    (C : Set (Language α)) (languageOf : Code → Language α) : Prop :=
  Characterizes C languageOf ∧ MembershipSemiDecidable languageOf ∧
    ComputablePred (fun p : Code × List α => p.2 ∈ languageOf p.1)

/-- Uniform computability of **emptiness** for the class `C` under the encoding
`languageOf`: the encoding is an adequate, effective presentation of `C` and
"`languageOf c = ∅`" is uniformly decidable in the code `c`. -/
@[expose]
public def ComputableEmptiness [Primcodable Code] [Primcodable α]
    (C : Set (Language α)) (languageOf : Code → Language α) : Prop :=
  Characterizes C languageOf ∧ MembershipSemiDecidable languageOf ∧
    ComputablePred (fun c : Code => languageOf c = (∅ : Set (List α)))

/-- Uniform computability of **universality** for the class `C` under the encoding
`languageOf`: the encoding is an adequate, effective presentation of `C` and
"`languageOf c = univ`" is uniformly decidable in the code `c`. -/
@[expose]
public def ComputableUniversality [Primcodable Code] [Primcodable α]
    (C : Set (Language α)) (languageOf : Code → Language α) : Prop :=
  Characterizes C languageOf ∧ MembershipSemiDecidable languageOf ∧
    ComputablePred (fun c : Code => languageOf c = Set.univ)

/-- Uniform computability of **equivalence** for the class `C` under the encoding
`languageOf`: the encoding is an adequate, effective presentation of `C` and
"`languageOf c₁ = languageOf c₂`" is uniformly decidable in the pair of codes. -/
@[expose]
public def ComputableEquivalence [Primcodable Code] [Primcodable α]
    (C : Set (Language α)) (languageOf : Code → Language α) : Prop :=
  Characterizes C languageOf ∧ MembershipSemiDecidable languageOf ∧
    ComputablePred (fun p : Code × Code => languageOf p.1 = languageOf p.2)

