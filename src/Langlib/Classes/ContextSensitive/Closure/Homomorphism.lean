module

public import Langlib.Classes.ContextSensitive.Basics.ErasingImage
public import Langlib.Utilities.ClosurePredicates
import Langlib.Classes.ContextSensitive.Inclusion.Recursive
import Langlib.Classes.RecursivelyEnumerable.Examples.Halting
import Langlib.Classes.Recursive.Inclusion.StrictRecursivelyEnumerable

@[expose]
public section

/-!
# Context-sensitive languages are not closed under homomorphism

The unary halting language is recursively enumerable, so it is the erasing image of a
context-sensitive padded language.  If context-sensitive languages were closed under
arbitrary string homomorphisms, the unary halting language would therefore be
context-sensitive and hence recursive, a contradiction.

## Main declaration

* `CS_notClosedUnderHomomorphism`
-/

open Grammar.ErasingImage

/-- Context-sensitive languages are not closed under arbitrary string homomorphisms.
The counterexample is a context-sensitive padded cover of the unary halting language;
erasing its padding yields a non-recursive language. -/
public theorem CS_notClosedUnderHomomorphism :
    ¬ ClosedUnderHomomorphism is_CS := by
  intro hclosed
  obtain ⟨K, hK, himage⟩ :=
    is_RE_exists_CS_homomorphicImage (T := Unit) haltingUnaryLanguage_RE
  have hHaltingCS : is_CS haltingUnaryLanguage := by
    have hImageCS : is_CS (K.homomorphicImage erasePadding) :=
      hclosed K erasePadding hK
    rw [himage] at hImageCS
    exact hImageCS
  exact haltingUnaryLanguage_not_Recursive (is_Recursive_of_is_CS hHaltingCS)
