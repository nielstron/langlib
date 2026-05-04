import Mathlib
import Langlib.Utilities.LanguageOperations

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

## Main definitions

- `ComputableMembership`
- `ComputableEmptiness`
- `ComputableUniversality`
- `ComputableEquivalence`
-/

variable {α Code : Type}

/-- Uniform computability of membership for an encoded language presentation.

The input is a pair `(c, w)`, where `c` is the encoded presentation and `w` is the
word whose membership in `languageOf c` is being tested. -/
def ComputableMembership [Primcodable Code] [Primcodable α]
    (languageOf : Code → Language α) : Prop :=
  ComputablePred (fun p : Code × List α => p.2 ∈ languageOf p.1)

/-- Uniform computability of emptiness for an encoded language presentation.

The encoded presentation itself is the input to the predicate. -/
def ComputableEmptiness [Primcodable Code] (languageOf : Code → Language α) : Prop :=
  ComputablePred (fun c : Code => languageOf c = (∅ : Set (List α)))

/-- Uniform computability of universality for an encoded language presentation.

The encoded presentation itself is the input to the predicate. -/
def ComputableUniversality [Primcodable Code] (languageOf : Code → Language α) : Prop :=
  ComputablePred (fun c : Code => languageOf c = Set.univ)

/-- Uniform computability of equivalence for an encoded language presentation.

The input is a pair of encoded presentations. -/
def ComputableEquivalence [Primcodable Code] (languageOf : Code → Language α) : Prop :=
  ComputablePred (fun p : Code × Code => languageOf p.1 = languageOf p.2)

