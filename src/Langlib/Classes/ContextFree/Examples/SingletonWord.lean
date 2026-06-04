module

public import Langlib.Classes.Regular.Examples.SingletonWord
public import Langlib.Classes.ContextFree.Definition
import Langlib.Classes.Regular.Inclusion.ContextFree
@[expose]
public section

/-! # The singleton-word language is context-free -/

/-- The singleton-word language `{w}` is context-free. -/
public theorem singletonWordLanguage_is_CF {T : Type} [Fintype T] (w : List T) :
    is_CF (singletonWordLanguage w) :=
  is_CF_of_is_RG (singletonWordLanguage_is_RG w)

end
