module
public import Mathlib.Computability.Language
@[expose]
public section

/-!
# The singleton empty-word language

The language containing exactly the empty word `[]`.
-/

/-- The language containing exactly the empty word. -/
@[expose] public def emptyWordLanguage (T : Type) : Language T := {[]}

end
