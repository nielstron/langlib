import Mathlib
import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.ContextFree.Closure.Substitution
import Langlib.Utilities.LanguageOperations

/-! # Context-Free Closure Under String Homomorphism

This file proves that context-free languages are closed under string homomorphism
and epsilon-free string homomorphism.

A **string homomorphism** `h : α → List β` extends to words by concatenation:
`h(a₁a₂…aₙ) = h(a₁) ++ h(a₂) ++ … ++ h(aₙ)`.
The image of a language `L` under `h` is `{h(w) | w ∈ L}`.

This is a special case of substitution where each symbol `a` is mapped to the
singleton language `{h(a)}`.

## Main declarations

- `CF_closed_under_homomorphism` : CFLs are closed under string homomorphism.
- `CF_closed_under_epsfree_homomorphism` : CFLs are closed under ε-free string homomorphism.
-/

variable {α β : Type}

/-- The image of a language `L` under a string homomorphism `h`. -/
def Language.homomorphicImage (L : Language α) (h : α → List β) : Language β :=
  L.subst (fun a => ({h a} : Language β))

/-- A string homomorphism is ε-free if no symbol maps to the empty string. -/
def IsEpsFreeHomomorphism (h : α → List β) : Prop :=
  ∀ a, h a ≠ []

/-- Singleton word languages are context-free. -/
lemma is_CF_singleton (w : List β) : is_CF ({w} : Language β) := by
  rw [is_CF_iff_isContextFree]
  exact isContextFree_singleton w

/-- The class of context-free languages is closed under string homomorphism.

Given a context-free language `L` over alphabet `α` and a string homomorphism `h : α → List β`,
the image `{h(w) | w ∈ L}` is also context-free.

**Proof sketch:** A string homomorphism is a special case of substitution where each symbol `a`
is replaced by the singleton language `{h(a)}`. Since every singleton language is context-free
and CFLs are closed under substitution (`CF_of_subst_CF`), the result follows. -/
theorem CF_closed_under_homomorphism (L : Language α) (h : α → List β)
    (hL : is_CF L) : is_CF (L.homomorphicImage h) := by
  exact CF_of_subst_CF L (fun a => {h a}) hL (fun a => is_CF_singleton (h a))

/-- The class of context-free languages is closed under ε-free string homomorphism.

This is a direct corollary of `CF_closed_under_homomorphism`, since every ε-free
string homomorphism is in particular a string homomorphism. -/
theorem CF_closed_under_epsfree_homomorphism (L : Language α) (h : α → List β)
    (hL : is_CF L) (_heps : IsEpsFreeHomomorphism h) :
    is_CF (L.homomorphicImage h) := by
  exact CF_closed_under_homomorphism L h hL
