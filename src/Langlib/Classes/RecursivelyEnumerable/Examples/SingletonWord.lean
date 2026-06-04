module

public import Langlib.Classes.ContextSensitive.Examples.SingletonWord
public import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Classes.ContextSensitive.Inclusion.RecursivelyEnumerable
@[expose]
public section

/-! # The singleton-word language is recursively enumerable -/

/-- The singleton-word language `{w}` is recursively enumerable, via `CS ⊆ RE`. -/
public theorem singletonWordLanguage_is_RE {T : Type} [Fintype T] (w : List T) :
    is_RE (singletonWordLanguage w) :=
  is_RE_of_CS (singletonWordLanguage_is_CS w)

end
