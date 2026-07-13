module

public import Langlib.Classes.ContextFree.Closure.Quotient
public import Langlib.Classes.ContextFree.Inclusion.Indexed
public import Langlib.Classes.Indexed.Closure.IntersectionRegular
public import Langlib.Classes.Indexed.Closure.Substitution

@[expose]
public section

/-!
# Indexed Languages Are Closed Under Regular Right Quotient

The proof uses the standard full-AFL factorization already established in the
context-free quotient development.  First substitute either a left or a right tag
for every input symbol.  Intersect with the regular language consisting of a
left-tagged prefix followed by a right-tagged word in the quotient denominator.
Finally substitute the left tags back to their symbols and erase the right tags.

The set-theoretic identity is independent of the language class.  Indexed closure
under substitution and intersection with a regular language therefore supplies
the result directly.
-/

variable {T : Type} [Fintype T]

/-- Every tagging language used by the quotient factorization is indexed. -/
private theorem is_Indexed_tagSubst (a : T) : is_Indexed (tagSubst a) :=
  is_Indexed_of_is_CF (is_CF_tagSubst a)

/-- Every erasing language used by the quotient factorization is indexed. -/
private theorem is_Indexed_eraseInr (x : T ⊕ T) : is_Indexed (eraseInr x) :=
  is_Indexed_of_is_CF (is_CF_eraseInr x)

/-- The regular block constraint used in the quotient factorization. -/
private theorem blockLang_isRegular_of_isRegular {R : Language T}
    (hR : R.IsRegular) : (blockLang R).IsRegular := by
  obtain ⟨σ, _, D, rfl⟩ := hR
  exact ⟨_, inferInstance, blockLangDFA D, blockLangDFA_accepts D⟩

/-- An indexed language right-quotiented by a regular language is indexed. -/
public theorem is_Indexed_rightQuotient_regular
    {L R : Language T} (hL : is_Indexed L) (hR : R.IsRegular) :
    is_Indexed (L / R) := by
  rw [← subst_inter_block_subst_eq_rightQuotient L R]
  apply Indexed_closedUnderSubstitution
  · exact Indexed_of_Indexed_inter_regular (L.subst tagSubst) (blockLang R)
      (Indexed_closedUnderSubstitution L tagSubst hL is_Indexed_tagSubst)
      (blockLang_isRegular_of_isRegular hR)
  · exact is_Indexed_eraseInr

/-- Indexed languages are closed under right quotient with regular languages,
uniformly over every finite alphabet. -/
public theorem Indexed_closedUnderRightQuotientWithRegular :
    ClosedUnderRightQuotientWithRegular (α := T) is_Indexed := by
  intro L hL R hR
  exact is_Indexed_rightQuotient_regular hL hR

end
