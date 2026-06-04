module

public import Langlib.Classes.Regular.Examples.SingletonWord
public import Langlib.Classes.Linear.Definition
import Langlib.Classes.Regular.Inclusion.Linear
@[expose]
public section

/-! # The singleton-word language is linear -/

/-- The singleton-word language `{w}` is linear. -/
public theorem singletonWordLanguage_is_Linear {T : Type} [Fintype T] (w : List T) :
    is_Linear (singletonWordLanguage w) :=
  is_Linear_of_is_RG (singletonWordLanguage_is_RG w)

end
