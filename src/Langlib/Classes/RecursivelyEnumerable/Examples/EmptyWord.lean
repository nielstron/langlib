module
public import Langlib.Classes.Regular.Examples.EmptyWord
public import Langlib.Classes.Regular.Inclusion.RecursivelyEnumerable
public import Langlib.Classes.RecursivelyEnumerable.Closure.Intersection
@[expose]
public section

/-!
# The singleton empty-word language is recursively enumerable

Since `emptyWordLanguage T` and its complement are regular, they are RE (Regular ⊆ RE).
We also record that the empty language is RE.
-/

/-- The singleton empty-word language is RE. -/
public theorem emptyWordLanguage_isRE {T : Type} [Fintype T] :
    is_RE (emptyWordLanguage T) :=
  is_RE_of_isRegular emptyWordLanguage_isRegular

/-- The complement of the singleton empty-word language is RE. -/
public theorem emptyWordLanguage_compl_isRE {T : Type} [Fintype T] :
    is_RE (emptyWordLanguage T)ᶜ :=
  is_RE_of_isRegular emptyWordLanguage_compl_isRegular

/-- The empty language is RE (here we get it directly as
`emptyWordLanguage T ⊓ (emptyWordLanguage T)ᶜ`). -/
public theorem is_RE_empty {T : Type} [Fintype T] [DecidableEq T] [Primcodable T] :
    is_RE (⊥ : Language T) := by
  have : (⊥ : Language T) = (emptyWordLanguage T) ⊓ (emptyWordLanguage T)ᶜ := by
    simp
  rw [this]
  exact RE_of_RE_i_RE _ _ ⟨emptyWordLanguage_isRE, emptyWordLanguage_compl_isRE⟩

end
