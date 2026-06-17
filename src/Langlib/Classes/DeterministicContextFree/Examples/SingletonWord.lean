module

public import Langlib.Classes.Regular.Examples.SingletonWord
public import Langlib.Classes.DeterministicContextFree.Definition
import Langlib.Classes.Regular.Inclusion.DeterministicContextFree
@[expose]
public section

/-! # The singleton-word language is deterministic context-free -/

/-- The singleton-word language `{w}` is deterministic context-free. -/
public theorem singletonWordLanguage_is_DCF {T : Type} [Fintype T] (w : List T) :
    is_DCF (singletonWordLanguage w) :=
  is_DCF_of_is_RG (singletonWordLanguage_is_RG w)

end
