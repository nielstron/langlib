import Mathlib.Computability.Language

/-! # Language Operations

This file defines basic operations on languages used throughout the closure-property proofs.

## Main declarations

- `reverseLang_reverseLang`
- `bijemapLang`
- `permuteLang`
-/

open scoped Classical

namespace Grammars

variable {T : Type _}

def reverseLang (L : Language T) : Language T :=
  fun w : List T => w.reverse ∈ L

@[simp] theorem reverseLang_reverseLang (L : Language T) :
  reverseLang (reverseLang L) = L := by
  funext w
  change (w.reverse.reverse ∈ L) = (w ∈ L)
  simp

def bijemapLang {T' : Type _} (L : Language T) (π : T ≃ T') : Language T' :=
  fun w : List T' => List.map π.symm w ∈ L

def permuteLang (L : Language T) (π : Equiv.Perm T) : Language T :=
  bijemapLang L π

end Grammars
