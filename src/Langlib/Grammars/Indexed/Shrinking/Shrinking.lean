module

public import Langlib.Grammars.Indexed.Shrinking.Basis

@[expose]
public section

/-!
# A one-factor shrinking theorem for indexed languages

This is the `m = 1` form of Gilman's shrinking theorem.  A long generated
word contains one critical scope.  Its ordered nonempty factors have bounded
length, and after any one factor is distinguished a proper retained
subproduct can replace that scope while remaining generated.
-/

variable {T : Type}

namespace IndexedGrammar.NFParse

/-- The critical-scope form of the one-factor shrinking conclusion.  The two
contexts are kept fixed; adding either nonempty context as an outer factor
recovers the usual proper-subproduct statement for the whole word. -/
public structure ScopedOneFactorShrinking (g : IndexedGrammar T) (w : List T)
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
      g.Generates (leftContext ++ kept.flatten ++ rightContext)

/-- Apply the common marked basis at one critical node and rebuild the whole
parse around the shrunken scope. -/
private noncomputable def scopedShrinking_of_locatedCritical
    {g : IndexedGrammar T} [DecidableEq g.nt] (hNF : g.IsNormalForm)
    {Z : Finset (List (g.nt ⊕ T))} {C : Nat}
    (hbound : ∀ z ∈ Z, z.length ≤ C)
    (hshort : ∀ z : List (g.nt ⊕ T), z.length ≤ 1 → z ∈ Z)
    (hbasis : ∀ (key : BetaKey g) (y : List (g.nt ⊕ T)),
      y ∈ frontierLanguage g key → y ∉ Z → ∀ i : Fin y.length,
        ∃ x ∈ Z, x.length < y.length ∧
          MarkedHigman.RetainsAt x y i ∧
          x ∈ frontierLanguage g key)
    {w : List T}
    (located : LocatedCritical g (Z : Set (List (g.nt ⊕ T)))
      g.initial [] w) (hcriticalBound : located.parse.beta.length ≤ C * C) :
    ScopedOneFactorShrinking g w (C * C) := by
  let pieces := located.parse.betaPieces
  let factors := pieces.map ScopePiece.word
  have htwo : 2 ≤ pieces.length := by
    rw [located.parse.betaPieces_length]
    by_contra hnot
    have hsmall : located.parse.beta.length ≤ 1 := by omega
    exact located.critical.1 (by simpa using hshort located.parse.beta hsmall)
  have hword : w = located.leftContext ++ factors.flatten ++ located.rightContext := by
    have hfactor : located.factor = factors.flatten := by
      have hscope := located.parse.scopeWord_betaPieces
      rw [← hscope]
      simp [factors, pieces, scopeWord, List.flatten_eq_flatMap,
        List.flatMap_map, Function.comp_def]
    exact located.whole_eq.trans
      (congrArg (fun middle =>
        located.leftContext ++ middle ++ located.rightContext) hfactor)
  refine {
    leftContext := located.leftContext
    factors := factors
    rightContext := located.rightContext
    word_eq := hword
    two_le := by simpa [factors] using htwo
    length_le := by simpa [factors, pieces] using hcriticalBound
    factors_nonempty := ?_
    shrink := ?_
  }
  · intro factor hfactor
    obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hfactor
    exact piece.word_ne_nil
  · intro i
    let j : Fin pieces.length := ⟨i, by simpa [factors] using i.isLt⟩
    let betaIndex : Fin located.parse.beta.length :=
      Fin.cast located.parse.betaPieces_length j
    have hy : located.parse.beta ∈
        frontierLanguage g (betaKeyOf located.nt located.stack) :=
      located.parse.beta_mem_frontierLanguage
    obtain ⟨x, _hxZ, hxlt, hxretain, hxfrontier⟩ :=
      hbasis (betaKeyOf located.nt located.stack) located.parse.beta hy
        (by simpa using located.critical.1) betaIndex
    have hxretainMap : MarkedHigman.RetainsAt x
        (pieces.map ScopePiece.symbol)
        (MarkedHigman.mappedIndex ScopePiece.symbol pieces j) := by
      have hsymbols : pieces.map ScopePiece.symbol = located.parse.beta := by
        simpa [pieces, scopeSymbols] using located.parse.scopeSymbols_betaPieces
      have hback := hxretain.cast hsymbols.symm
      simpa [betaIndex, j, pieces, MarkedHigman.mappedIndex] using hback
    obtain ⟨keptPieces, hkeptRetains, hkeptSymbols⟩ :=
      MarkedHigman.RetainsAt.exists_preimage ScopePiece.symbol hxretainMap
    let kept := keptPieces.map ScopePiece.word
    have hkeptLt : kept.length < factors.length := by
      have hlenX : keptPieces.length = x.length := by
        have := congrArg List.length hkeptSymbols
        simpa using this
      simpa [kept, factors, pieces, hlenX] using hxlt
    have hkeptRetainsWords : MarkedHigman.RetainsAt kept factors i := by
      have hmapped := hkeptRetains.map ScopePiece.word
      simpa [kept, factors, pieces, j, MarkedHigman.mappedIndex] using hmapped
    have hxder : g.Derives (betaSource located.nt located.stack)
        (unstackedForm x) := by
      simpa [frontierLanguage] using hxfrontier
    have hsymbols : scopeSymbols keptPieces = x := by
      simpa [scopeSymbols] using hkeptSymbols
    have hlocal := derives_scopeWord_of_derives_unstacked hxder keptPieces hsymbols
    obtain ⟨steps, hcounted⟩ := derives_iff_exists_derivesIn.mp hlocal
    let replacementYield : NFYield g located.nt located.stack
        (scopeWord keptPieces) :=
      NFYield.of_derivesIn_isNormalForm hNF hcounted
    let replacement : NFParse g located.nt located.stack
        (scopeWord keptPieces) := NFParse.ofNFYield replacementYield
    let rebuilt := located.rebuild replacement
    have hgenerated : g.Generates
        (located.leftContext ++ scopeWord keptPieces ++ located.rightContext) :=
      (NFYield.generates_iff_isNormalForm hNF).2 rebuilt.toNFYield
    refine ⟨kept, hkeptRetainsWords, hkeptLt, ?_⟩
    simpa [kept, scopeWord, List.flatten_eq_flatMap, List.flatMap_map,
      Function.comp_def] using hgenerated

/-- Grammar-level one-factor shrinking theorem. -/
public theorem exists_scopedOneFactorShrinking
    (g : IndexedGrammar T) [Fintype T] [Fintype g.nt] [Fintype g.flag]
    [DecidableEq g.nt] (hNF : g.IsNormalForm) :
    ∃ k > 0, ∀ w : List T, g.Generates w → k ≤ w.length →
      Nonempty (ScopedOneFactorShrinking g w (k - 2)) := by
  obtain ⟨Z, C, hC, hbound, hshort, hbasis⟩ := exists_globalRetainingBasis g
  let k := C * C + 2
  refine ⟨k, by omega, ?_⟩
  intro w hw hlong
  have hcert : NFYield g g.initial [] w :=
    (NFYield.generates_iff_isNormalForm hNF).1 hw
  let root : NFParse g g.initial [] w := NFParse.ofNFYield hcert
  have hrootOutside : root.beta ∉ (Z : Set (List (g.nt ⊕ T))) := by
    intro hrootZ
    have hrootBound := hbound root.beta (by simpa using hrootZ)
    have hrootLength : root.beta.length = w.length := root.beta_length_of_empty
    rw [hrootLength] at hrootBound
    dsimp [k] at hlong
    have hCmul : C ≤ C * C := Nat.le_mul_of_pos_right C (by omega)
    omega
  have hnotAll : ¬ root.AllBetaIn (Z : Set (List (g.nt ⊕ T))) := by
    intro hall
    exact hrootOutside (beta_mem_of_allBetaIn hall)
  obtain ⟨located⟩ := root.exists_locatedCritical_of_not_allBetaIn
    (Z : Set (List (g.nt ⊕ T))) hnotAll
  have hcriticalBound : located.parse.beta.length ≤ C * C :=
    beta_length_le_sq_of_critical hC (fun z hz => hbound z (by simpa using hz))
      located.critical
  have hresult := scopedShrinking_of_locatedCritical hNF hbound hshort hbasis
    located hcriticalBound
  have hk : k - 2 = C * C := by simp [k]
  exact ⟨hk ▸ hresult⟩

end IndexedGrammar.NFParse
