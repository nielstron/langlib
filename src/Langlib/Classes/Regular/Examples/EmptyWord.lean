module
public import Langlib.Examples.EmptyWord
public import Langlib.Classes.Regular.Closure.Homomorphism
public import Langlib.Classes.Regular.Closure.Complement
@[expose]
public section

/-!
# The singleton empty-word language is regular

`emptyWordLanguage T = {[]}` is regular (it is `Language.isRegular_epsilon`), and so is
its complement.
-/

/-- The singleton empty-word language is regular. -/
public theorem emptyWordLanguage_isRegular {T : Type} : (emptyWordLanguage T).IsRegular :=
  Language.isRegular_epsilon

/-- The complement of the singleton empty-word language is regular. -/
public theorem emptyWordLanguage_compl_isRegular {T : Type} :
    (emptyWordLanguage T)ᶜ.IsRegular :=
  Language.IsRegular.compl emptyWordLanguage_isRegular

end
