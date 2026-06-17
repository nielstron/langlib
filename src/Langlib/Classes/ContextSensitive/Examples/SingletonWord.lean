module

public import Langlib.Classes.ContextFree.Examples.SingletonWord
public import Langlib.Classes.ContextSensitive.Definition
import Langlib.Classes.ContextFree.Inclusion.ContextSensitive
@[expose]
public section

/-! # The singleton-word language is context-sensitive -/

/-- The singleton-word language `{w}` is context-sensitive. -/
public theorem singletonWordLanguage_is_CS {T : Type} [Fintype T] (w : List T) :
    is_CS (singletonWordLanguage w) :=
  is_CS_of_is_CF (singletonWordLanguage_is_CF w)

end
