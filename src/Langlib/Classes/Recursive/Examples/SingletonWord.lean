module

public import Langlib.Classes.ContextSensitive.Examples.SingletonWord
public import Langlib.Classes.Recursive.Definition
public import Mathlib.Computability.Primrec
import Langlib.Classes.ContextSensitive.Inclusion.Recursive
@[expose]
public section

/-! # The singleton-word language is recursive -/

/-- The singleton-word language `{w}` is recursive (decidable), via `CS ⊆ Recursive`. -/
public theorem singletonWordLanguage_is_Recursive {T : Type} [Fintype T] [DecidableEq T]
    [Primcodable T] (w : List T) :
    is_Recursive (singletonWordLanguage w) :=
  is_Recursive_of_is_CS (singletonWordLanguage_is_CS w)

end
