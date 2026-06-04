module

public import Mathlib.Computability.Language
@[expose]
public section

/-! # The singleton-word language `{w}`

The language containing exactly one fixed word `w`. This generalizes
`Langlib.Examples.EmptyWord` (`emptyWordLanguage T = singletonWordLanguage ([] : List T)`).

It is regular (`singletonWordLanguage_isRegular`), and hence — being at the bottom of the
Chomsky hierarchy — a member of every language class; those corollaries live in the
`Examples/SingletonWord.lean` file of each class hierarchy.
-/

/-- The language containing exactly the word `w`. -/
@[expose]
public def singletonWordLanguage {T : Type} (w : List T) : Language T := {w}

end
