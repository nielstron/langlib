module

public import Langlib.Utilities.PromiseComputability

@[expose]
public section

/-!
# Merging complementary semidecision procedures on a promise

The positive equivalence search and the distinguishing-word search are both
partial-recursive.  They are globally disjoint, while completeness of the
positive search is needed only for valid encoded inputs.  The lemma below is
the corresponding promise version of Post's theorem: dovetail the two searches
and return the side which terminates first.
-/

/-- Replace a promise-computable predicate by a propositionally equivalent
predicate on the promised inputs, without changing the evaluator. -/
public theorem ComputablePredOnPromise.congr
    {Code : Type} [Primcodable Code]
    {valid first second : Code → Prop}
    (hfirst : ComputablePredOnPromise valid first)
    (hequivalent : ∀ code, valid code → (first code ↔ second code)) :
    ComputablePredOnPromise valid second := by
  obtain ⟨evaluate, hevaluate, hspec⟩ := hfirst
  refine ⟨evaluate, hevaluate, ?_⟩
  intro code hvalid
  refine ⟨(hspec code hvalid).1, ?_⟩
  exact (hequivalent code hvalid).symm.trans (hspec code hvalid).2

/-- Pull a promise-computable predicate back along a computable compilation
which preserves validity only on the source promise. -/
public theorem ComputablePredOnPromise.pullbackOnPromise
    {Code Input : Type} [Primcodable Code] [Primcodable Input]
    {targetValid targetPredicate : Code → Prop}
    (htarget : ComputablePredOnPromise targetValid targetPredicate)
    {sourceValid : Input → Prop} {compile : Input → Code}
    (hcompile : Computable compile)
    (hvalid : ∀ input, sourceValid input → targetValid (compile input)) :
    ComputablePredOnPromise sourceValid
      (fun input => targetPredicate (compile input)) := by
  obtain ⟨evaluate, hevaluate, hspec⟩ := htarget
  let run : Input →. Bool := fun input => evaluate (compile input)
  refine ⟨run, hevaluate.comp hcompile, ?_⟩
  intro input hsource
  exact hspec (compile input) (hvalid input hsource)

/-- Two disjoint recursively enumerable predicates which cover every promised
input give a single promise-total decision procedure for the first predicate. -/
public theorem computablePredOnPromise_of_disjoint_re
    {Code : Type} [Primcodable Code]
    {valid positive negative : Code → Prop}
    (hpositive : REPred positive)
    (hnegative : REPred negative)
    (hdisjoint : ∀ code, positive code → negative code → False)
    (hcomplete : ∀ code, valid code → positive code ∨ negative code) :
    ComputablePredOnPromise valid positive := by
  let positiveSearch : Code →. Bool := fun code =>
    (Part.assert (positive code) fun _ => Part.some ()).map fun _ => true
  let negativeSearch : Code →. Bool := fun code =>
    (Part.assert (negative code) fun _ => Part.some ()).map fun _ => false
  have hpositiveSearch : Partrec positiveSearch := by
    exact hpositive.map (Computable.const true).to₂
  have hnegativeSearch : Partrec negativeSearch := by
    exact hnegative.map (Computable.const false).to₂
  have hagree : ∀ code, ∀ x ∈ positiveSearch code,
      ∀ y ∈ negativeSearch code, x = y := by
    intro code x hx y hy
    have hxPositive : positive code := by
      exact (by simpa [positiveSearch] using hx : positive code ∧ x = true).1
    have hyNegative : negative code := by
      exact (by simpa [negativeSearch] using hy : negative code ∧ y = false).1
    exact (hdisjoint code hxPositive hyNegative).elim
  obtain ⟨evaluate, hevaluate, hevaluateSpec⟩ :=
    Partrec.merge hpositiveSearch hnegativeSearch hagree
  refine ⟨evaluate, hevaluate, ?_⟩
  intro code hvalid
  have hcoverage := hcomplete code hvalid
  have hdom : (evaluate code).Dom := by
    rcases hcoverage with hpos | hneg
    · apply Part.dom_iff_mem.mpr
      refine ⟨true, (hevaluateSpec code true).2 (Or.inl ?_)⟩
      simp [positiveSearch, hpos]
    · apply Part.dom_iff_mem.mpr
      refine ⟨false, (hevaluateSpec code false).2 (Or.inr ?_)⟩
      simp [negativeSearch, hneg]
  refine ⟨hdom, ?_⟩
  constructor
  · intro hpos
    apply (hevaluateSpec code true).2
    left
    simp [positiveSearch, hpos]
  · intro htrue
    rcases (hevaluateSpec code true).1 htrue with hpos | hneg
    · simpa [positiveSearch] using hpos
    · simp [negativeSearch] at hneg

/-- Promise-local variant of `computablePredOnPromise_of_disjoint_re`.

Away from the promise the two searches may overlap or be semantically
meaningless.  `Partrec.merge'` still dovetails them; disjointness is used only
to prove that its selected answer is correct on promised inputs. -/
public theorem computablePredOnPromise_of_re_cover
    {Code : Type} [Primcodable Code]
    {valid positive negative : Code → Prop}
    (hpositive : REPred positive)
    (hnegative : REPred negative)
    (hdisjoint : ∀ code, valid code → positive code →
      negative code → False)
    (hcomplete : ∀ code, valid code → positive code ∨ negative code) :
    ComputablePredOnPromise valid positive := by
  let positiveSearch : Code →. Bool := fun code =>
    (Part.assert (positive code) fun _ => Part.some ()).map fun _ => true
  let negativeSearch : Code →. Bool := fun code =>
    (Part.assert (negative code) fun _ => Part.some ()).map fun _ => false
  have hpositiveSearch : Partrec positiveSearch := by
    exact hpositive.map (Computable.const true).to₂
  have hnegativeSearch : Partrec negativeSearch := by
    exact hnegative.map (Computable.const false).to₂
  obtain ⟨evaluate, hevaluate, hevaluateSpec⟩ :=
    Partrec.merge' hpositiveSearch hnegativeSearch
  refine ⟨evaluate, hevaluate, ?_⟩
  intro code hvalid
  have hcoverage := hcomplete code hvalid
  have hdom : (evaluate code).Dom := by
    apply (hevaluateSpec code).2.2
    rcases hcoverage with hpos | hneg
    · left
      apply Part.dom_iff_mem.mpr
      refine ⟨true, ?_⟩
      simp [positiveSearch, hpos]
    · right
      apply Part.dom_iff_mem.mpr
      refine ⟨false, ?_⟩
      simp [negativeSearch, hneg]
  refine ⟨hdom, ?_⟩
  constructor
  · intro hpos
    have hselected := (hevaluateSpec code).1
      ((evaluate code).get hdom) (Part.get_mem hdom)
    rcases hselected with hselected | hselected
    · have hvalue : (evaluate code).get hdom = true := by
        exact (by simpa [positiveSearch] using hselected :
          positive code ∧ (evaluate code).get hdom = true).2
      rw [← hvalue]
      exact Part.get_mem hdom
    · have hneg : negative code :=
        (by simpa [negativeSearch] using hselected :
          negative code ∧ (evaluate code).get hdom = false).1
      exact (hdisjoint code hvalid hpos hneg).elim
  · intro htrue
    rcases (hevaluateSpec code).1 true htrue with hpos | hneg
    · exact (by simpa [positiveSearch] using hpos :
        positive code ∧ true = true).1
    · simp [negativeSearch] at hneg
