module

public import Langlib.Examples.SingletonWord
public import Langlib.Classes.Regular.Definition
public import Mathlib.Computability.DFA
import Langlib.Classes.Regular.Closure.Homomorphism
import Langlib.Automata.FiniteState.Equivalence.Regular
@[expose]
public section

/-! # The singleton-word language is regular

`{w}` is regular for any word `w`. The Mathlib `IsRegular` form holds over any alphabet;
the Langlib `is_RG` form (a right-regular grammar) needs a finite terminal alphabet.
-/

/-- The singleton-word language `{w}` is regular (Mathlib `IsRegular`). -/
public theorem singletonWordLanguage_isRegular {T : Type} (w : List T) :
    Language.IsRegular (singletonWordLanguage w) :=
  Language.isRegular_singleton_word w

/-- The singleton-word language `{w}` is regular (Langlib `is_RG`). -/
public theorem singletonWordLanguage_is_RG {T : Type} [Fintype T] (w : List T) :
    is_RG (singletonWordLanguage w) :=
  is_RG_of_isRegular (singletonWordLanguage_isRegular w)

end
