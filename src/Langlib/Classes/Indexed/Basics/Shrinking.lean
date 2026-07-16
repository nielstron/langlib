module

public import Langlib.Classes.Indexed.Definition
public import Langlib.Grammars.Indexed.NormalForm.NormalForm
public import Langlib.Grammars.Indexed.Shrinking.Shrinking

@[expose]
public section

/-!
# The one-factor shrinking theorem for indexed languages

This file lifts the grammar-level critical-scope theorem through the finite-support
normal-form construction.  Consequently the statement applies to an arbitrary
indexed language, independently of the grammar used to present it.

The two outer contexts are fixed by every shrinking.  They can be treated as at
most two additional factors when the usual whole-word formulation is needed.

## Reference

* R. H. Gilman, "A shrinking lemma for indexed languages",
  *Theoretical Computer Science* 163 (1996), 277--281.
-/

variable {T : Type}

/-- The class-level critical-scope form of the one-factor shrinking theorem. -/
public structure IndexedScopedOneFactorShrinking (L : Language T) (w : List T)
    (bound : Nat) where
  leftContext : List T
  factors : List (List T)
  rightContext : List T
  word_eq : w = leftContext ++ factors.flatten ++ rightContext
  two_le : 2 ≤ factors.length
  length_le : factors.length ≤ bound
  factors_nonempty : ∀ factor ∈ factors, factor ≠ []
  shrink : ∀ i : Fin factors.length,
    ∃ kept : List (List T),
      MarkedHigman.RetainsAt kept factors i ∧
      kept.length < factors.length ∧
      leftContext ++ kept.flatten ++ rightContext ∈ L

/-- Every indexed language over a finite alphabet satisfies the critical-scope
one-factor shrinking theorem. -/
public theorem exists_indexedScopedOneFactorShrinking [Fintype T] [Inhabited T]
    {L : Language T} (hL : is_Indexed L) :
    ∃ k > 0, ∀ w : List T, w ∈ L → k ≤ w.length →
      Nonempty (IndexedScopedOneFactorShrinking L w (k - 2)) := by
  obtain ⟨g₀, hg₀⟩ := hL
  obtain ⟨g, hnt, hflag, hdec, hNF, hgen⟩ :=
    g₀.exists_finiteSupport_normalForm_nonempty
  letI := hnt
  letI := hflag
  letI := hdec
  obtain ⟨k, hk, hshrink⟩ :=
    IndexedGrammar.NFParse.exists_scopedOneFactorShrinking g hNF
  refine ⟨k, hk, ?_⟩
  intro w hw hlong
  have hw_ne : w ≠ [] := by
    intro hw_nil
    subst w
    simp at hlong
    omega
  have hwg₀ : g₀.Generates w := by
    change w ∈ g₀.Language
    rw [hg₀]
    exact hw
  have hwg : g.Generates w := (hgen w hw_ne).2 hwg₀
  obtain ⟨result⟩ := hshrink w hwg hlong
  refine ⟨{
    leftContext := result.leftContext
    factors := result.factors
    rightContext := result.rightContext
    word_eq := result.word_eq
    two_le := result.two_le
    length_le := result.length_le
    factors_nonempty := result.factors_nonempty
    shrink := ?_
  }⟩
  intro i
  obtain ⟨kept, hretains, hproper, hkept⟩ := result.shrink i
  let v := result.leftContext ++ kept.flatten ++ result.rightContext
  have hv_ne : v ≠ [] := by
    intro hv
    have hnil : g.Generates [] := by
      simpa [v, hv] using hkept
    exact g.not_generates_nil_of_noEpsilon
      (g.noEpsilon_of_isNormalForm hNF) hnil
  have hvg₀ : g₀.Generates v := (hgen v hv_ne).1 hkept
  have hvL : v ∈ L := by
    change v ∈ g₀.Language at hvg₀
    rwa [hg₀] at hvg₀
  exact ⟨kept, hretains, hproper, by simpa [v] using hvL⟩
