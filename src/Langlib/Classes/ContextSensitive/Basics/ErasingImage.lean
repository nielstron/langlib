module

public import Langlib.Classes.ContextSensitive.Definition
public import Langlib.Classes.RecursivelyEnumerable.Definition
public import Langlib.Grammars.NonContracting.ErasingImage

@[expose]
public section

/-!
# Recursively enumerable languages as erasing images of context-sensitive languages

The padded grammar from `Grammars.NonContracting.ErasingImage` turns an arbitrary
unrestricted grammar into a non-contracting grammar over `Option T`.  Erasing the added
`none` terminal recovers the source language.  Since non-contracting languages are
context-sensitive, every recursively enumerable language is therefore an erasing
homomorphic image of a context-sensitive language.

## Main declarations

* `is_RE_exists_CS_homomorphicImage`
-/

open Grammar.ErasingImage

variable {T : Type}

/-- Every recursively enumerable language over a finite alphabet is the erasing
homomorphic image of a context-sensitive language over the alphabet with one added
padding symbol. -/
public theorem is_RE_exists_CS_homomorphicImage [Fintype T]
    {L : Language T} (hL : is_RE L) :
    ∃ K : Language (Option T),
      is_CS K ∧ K.homomorphicImage erasePadding = L := by
  obtain ⟨g, hg⟩ := hL
  obtain ⟨K, hK, himage⟩ := exists_noncontracting_erasingImage g
  exact ⟨K, is_CS_of_is_noncontracting hK, himage.trans hg⟩
