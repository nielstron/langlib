import Mathlib
import Langlib.Utilities.LanguageOperations

/-! # String Homomorphism

A **string homomorphism** `h : α → List β` extends to words by concatenation:
`h(a₁a₂…aₙ) = h(a₁) ++ h(a₂) ++ … ++ h(aₙ)`.
The image of a language `L` under `h` is `{h(w) | w ∈ L}`.

This is a special case of substitution where each symbol `a` is mapped to the
singleton language `{h(a)}`.

-/

variable {α β : Type}

/-- The image of a language `L` under a string homomorphism `h`. -/
def Language.homomorphicImage (L : Language α) (h : α → List β) : Language β :=
  L.subst (fun a => ({h a} : Language β))

/-- A string homomorphism is ε-free if no symbol maps to the empty string. -/
def IsEpsFreeHomomorphism (h : α → List β) : Prop :=
  ∀ a, h a ≠ []
