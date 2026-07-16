module

public import Langlib.Grammars.Indexed.Basics.MarkedHigman
public import Langlib.Grammars.Indexed.Shrinking.Critical
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Set.Finite.Basic

@[expose]
public section

/-!
# A finite common basis for indexed-grammar scope frontiers

Gilman's marked Higman argument is applied separately to the finitely many
sources `A` and `Af`.  This file takes their finite union, adds all words of
length at most one, and chooses one common length bound.
-/

variable {T : Type}

namespace IndexedGrammar.NFParse

/-- A source relevant to a beta word: either `A` or `Af`. -/
public abbrev BetaKey (g : IndexedGrammar T) := g.nt × Option g.flag

/-- Sentential form represented by a beta source key. -/
public def betaKeyForm (g : IndexedGrammar T) (key : BetaKey g) : List g.ISym :=
  match key.2 with
  | none => [ISym.indexed key.1 []]
  | some f => [ISym.indexed key.1 [f]]

/-- The source key of a concrete parse node. -/
public def betaKeyOf {g : IndexedGrammar T} (A : g.nt) (sigma : List g.flag) :
    BetaKey g :=
  (A, sigma.head?)

/-- All unstacked frontier words derivable from one source. -/
public def frontierLanguage (g : IndexedGrammar T) (key : BetaKey g) :
    Set (List (g.nt ⊕ T)) :=
  {beta | g.Derives (betaKeyForm g key) (unstackedForm beta)}

@[simp] public theorem betaKeyForm_betaKeyOf {g : IndexedGrammar T}
    (A : g.nt) (sigma : List g.flag) :
    betaKeyForm g (betaKeyOf A sigma) = betaSource A sigma := by
  cases sigma <;> rfl

public theorem beta_mem_frontierLanguage {g : IndexedGrammar T}
    {A : g.nt} {sigma : List g.flag} {w : List T}
    (p : NFParse g A sigma w) :
    p.beta ∈ frontierLanguage g (betaKeyOf A sigma) := by
  simpa [frontierLanguage] using p.derives_beta

/-- A common finite retaining basis for every source `A` and `Af`, together
with a common bound `C ≥ 2`. -/
public theorem exists_globalRetainingBasis (g : IndexedGrammar T)
    [Fintype T] [Fintype g.nt] [Fintype g.flag] :
    ∃ (Z : Finset (List (g.nt ⊕ T))) (C : Nat),
      2 ≤ C ∧
      (∀ z ∈ Z, z.length ≤ C) ∧
      (∀ z : List (g.nt ⊕ T), z.length ≤ 1 → z ∈ Z) ∧
      ∀ (key : BetaKey g) (y : List (g.nt ⊕ T)),
        y ∈ frontierLanguage g key → y ∉ Z → ∀ i : Fin y.length,
          ∃ x ∈ Z, x.length < y.length ∧
            MarkedHigman.RetainsAt x y i ∧
            x ∈ frontierLanguage g key := by
  classical
  choose X hXspec using fun key : BetaKey g =>
    MarkedHigman.exists_finite_retaining_basis (g.nt ⊕ T)
      (frontierLanguage g key)
  have hXfinite : ∀ key, (X key).Finite := fun key => (hXspec key).1
  have hXsub : ∀ key, X key ⊆ frontierLanguage g key :=
    fun key => (hXspec key).2.1
  have hXbasis : ∀ key y, y ∈ frontierLanguage g key → y ∉ X key →
      ∀ i : Fin y.length,
        ∃ x ∈ X key, x.length < y.length ∧ MarkedHigman.RetainsAt x y i :=
    fun key => (hXspec key).2.2
  let basis : Finset (List (g.nt ⊕ T)) :=
    Finset.univ.biUnion fun key => (hXfinite key).toFinset
  let short : Finset (List (g.nt ⊕ T)) :=
    {[]} ∪ Finset.univ.image fun a => [a]
  let Z := basis ∪ short
  let C := max 2 (Z.sup List.length)
  refine ⟨Z, C, le_max_left _ _, ?_, ?_, ?_⟩
  · intro z hz
    exact (Finset.le_sup (f := List.length) hz).trans (le_max_right _ _)
  · intro z hz
    cases z with
    | nil => simp [Z, short]
    | cons a tail =>
        cases tail with
        | nil => simp [Z, short]
        | cons b tail => simp at hz
  · intro key y hy hyZ i
    have hyX : y ∉ X key := by
      intro hyBasis
      apply hyZ
      have hyBasisFin : y ∈ (hXfinite key).toFinset := by simpa using hyBasis
      have hyUnion : y ∈ basis := by
        simp only [basis, Finset.mem_biUnion]
        exact ⟨key, Finset.mem_univ _, hyBasisFin⟩
      exact Finset.mem_union_left short hyUnion
    obtain ⟨x, hxX, hxlt, hxretain⟩ := hXbasis key y hy hyX i
    have hxBasis : x ∈ basis := by
      simp only [basis, Finset.mem_biUnion]
      exact ⟨key, Finset.mem_univ _, by simpa using hxX⟩
    have hxZ : x ∈ Z := Finset.mem_union_left short hxBasis
    exact ⟨x, hxZ, hxlt, hxretain, hXsub key hxX⟩

end IndexedGrammar.NFParse
