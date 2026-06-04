module

public import Langlib.Classes.ContextFree.Examples.SingletonWord
public import Langlib.Classes.RecursivelyEnumerable.Definition
import Langlib.Classes.ContextFree.Inclusion.RecursivelyEnumerable
@[expose]
public section

/-! # The singleton-word language is recursively enumerable -/

/-- The singleton-word language `{w}` is recursively enumerable, via `CF ⊆ RE`. -/
public theorem singletonWordLanguage_is_RE {T : Type} [Fintype T] (w : List T) :
    is_RE (singletonWordLanguage w) :=
  is_RE_of_is_CF (singletonWordLanguage_is_CF w)

end
