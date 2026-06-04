module

public import Langlib.Classes.ContextFree.Examples.SingletonWord
public import Langlib.Classes.Indexed.Definition
import Langlib.Classes.ContextFree.Inclusion.Indexed
@[expose]
public section

/-! # The singleton-word language is indexed -/

/-- The singleton-word language `{w}` is indexed. -/
public theorem singletonWordLanguage_is_Indexed {T : Type} [Fintype T] (w : List T) :
    is_Indexed (singletonWordLanguage w) :=
  is_Indexed_of_is_CF (singletonWordLanguage_is_CF w)

end
