module

public import Langlib.Classes.Indexed.Closure.Concatenation
public import Langlib.Classes.Indexed.Closure.Injection
public import Langlib.Classes.Indexed.Closure.Reverse
public import Langlib.Classes.Indexed.Examples.CopyQuotientWitness
public import Langlib.Classes.Indexed.Examples.DiagonalNotIndexed
public import Langlib.Classes.Indexed.Examples.SingletonWord
public import Langlib.Utilities.ClosurePredicates

@[expose]
public section

/-!
# Indexed languages are not closed under arbitrary right quotient

For the binary intersection witnesses `A` and `B`, the numerator grammar from
`CopyQuotientWitness` generates

`{ code(w) # reverse(code(w)) | w ∈ A }`.

The denominator is `{ # reverse(code(v)) | v ∈ B }`.  The separator makes
the quotient split unique, so their right quotient is exactly the injective
image of `A ∩ B = {(a b^n)^n | n > 0}`.  The shrinking theorem shows that
this diagonal language is not indexed.
-/

open List

namespace IndexedIntersectionWitness

/-- Denominator of the indexed right-quotient counterexample. -/
public def indexedCopyDenominator : Language CopyLetter :=
  singletonWordLanguage [CopyLetter.separator] *
    (Language.map copyCode indexedIntersectionB).reverse

/-- The quotient denominator is indexed. -/
public theorem indexedCopyDenominator_isIndexed :
    is_Indexed indexedCopyDenominator := by
  apply Indexed_closedUnderConcatenation
  · exact singletonWordLanguage_is_Indexed [CopyLetter.separator]
  · apply Indexed_closedUnderReverse
    exact Indexed_of_map_injective_Indexed copyCode_injective
      indexedIntersectionB indexedIntersectionB_isIndexed

private lemma mem_indexedCopyDenominator_iff {w : List CopyLetter} :
    w ∈ indexedCopyDenominator ↔
      ∃ v ∈ indexedIntersectionB,
        w = [CopyLetter.separator] ++ (v.map copyCode).reverse := by
  constructor
  · intro hw
    rw [indexedCopyDenominator, Language.mul_def] at hw
    obtain ⟨left, hleft, right, hright, rfl⟩ := hw
    have hleft_eq : left = [CopyLetter.separator] := by
      simpa [singletonWordLanguage] using hleft
    subst left
    change right.reverse ∈ Language.map copyCode indexedIntersectionB at hright
    obtain ⟨v, hv, hmap⟩ := hright
    have hright_eq : right = (v.map copyCode).reverse := by
      simpa using (congrArg List.reverse hmap).symm
    exact ⟨v, hv, by rw [hright_eq]⟩
  · rintro ⟨v, hv, rfl⟩
    rw [indexedCopyDenominator, Language.mul_def]
    refine ⟨[CopyLetter.separator], Set.mem_singleton _,
      (v.map copyCode).reverse, ?_, rfl⟩
    change ((v.map copyCode).reverse).reverse ∈
      Language.map copyCode indexedIntersectionB
    simpa using (⟨v, hv, rfl⟩ : v.map copyCode ∈
      Language.map copyCode indexedIntersectionB)

private lemma separator_not_mem_map_copyCode (w : List Bool) :
    CopyLetter.separator ∉ w.map copyCode := by
  intro h
  obtain ⟨b, _hb, heq⟩ := List.mem_map.mp h
  cases b <;> simp [copyCode] at heq

private lemma count_separator_map_copyCode (w : List Bool) :
    (w.map copyCode).count CopyLetter.separator = 0 := by
  exact List.count_eq_zero_of_not_mem (separator_not_mem_map_copyCode w)

/-- Splitting two words immediately before a fresh separator is unique. -/
private lemma append_separator_unique
    {u v r s : List CopyLetter}
    (hu : CopyLetter.separator ∉ u)
    (hv : CopyLetter.separator ∉ v)
    (h : u ++ CopyLetter.separator :: r =
      v ++ CopyLetter.separator :: s) :
    u = v ∧ r = s := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil =>
          simp only [List.nil_append] at h
          exact ⟨rfl, (List.cons.inj h).2⟩
      | cons b bs =>
          simp only [List.nil_append, List.cons_append] at h
          have hsep : CopyLetter.separator = b := (List.cons.inj h).1
          exact False.elim (hv (by simp [← hsep]))
  | cons a us ih =>
      cases v with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h
          have hsep : a = CopyLetter.separator := (List.cons.inj h).1
          exact False.elim (hu (by simp [hsep]))
      | cons b bs =>
          simp only [List.cons_append] at h
          have hab : a = b := (List.cons.inj h).1
          have htail := (List.cons.inj h).2
          subst b
          have hus : CopyLetter.separator ∉ us := by
            intro hm
            exact hu (by simp [hm])
          have hbs : CopyLetter.separator ∉ bs := by
            intro hm
            exact hv (by simp [hm])
          obtain ⟨huv, hrs⟩ := ih hus hbs htail
          exact ⟨by rw [huv], hrs⟩

/-- The explicit quotient is exactly the encoded diagonal intersection. -/
public theorem indexedCopy_quotient_eq_diagonal :
    indexedCopyNumerator / indexedCopyDenominator =
      Language.map copyCode indexedIntersectionH := by
  ext w
  constructor
  · rintro ⟨suffix, hsuffix, hnumerator⟩
    obtain ⟨v, hvB, rfl⟩ := mem_indexedCopyDenominator_iff.mp hsuffix
    rcases hnumerator with ⟨n, m, hn, hm, hword⟩
    have hwcount : w.count CopyLetter.separator = 0 := by
      have hc := congrArg (fun z : List CopyLetter =>
        z.count CopyLetter.separator) hword
      simp [count_separator_map_copyCode] at hc
      omega
    have hwsep : CopyLetter.separator ∉ w := by
      intro hwmem
      have hpos := List.count_pos_iff.mpr hwmem
      omega
    have hsplit := append_separator_unique hwsep
      (separator_not_mem_map_copyCode (blockPower n m)) (by
        simpa [List.append_assoc] using hword)
    have hwmap : w = (blockPower n m).map copyCode := hsplit.1
    have hmaps : v.map copyCode = (blockPower n m).map copyCode := by
      have hrev := congrArg List.reverse hsplit.2
      simpa [List.map_reverse] using hrev
    have hv : v = blockPower n m :=
      List.map_injective_iff.mpr copyCode_injective hmaps
    have huA : blockPower n m ∈ indexedIntersectionA :=
      ⟨n, m, hn, hm, rfl⟩
    have huB : blockPower n m ∈ indexedIntersectionB := by
      simpa [hv] using hvB
    have huH : blockPower n m ∈ indexedIntersectionH := by
      rw [← indexedIntersectionA_inter_indexedIntersectionB]
      exact ⟨huA, huB⟩
    exact ⟨blockPower n m, huH, hwmap.symm⟩
  · rintro ⟨u, huH, rfl⟩
    rcases huH with ⟨n, hn, rfl⟩
    let suffix := [CopyLetter.separator] ++
      ((blockPower n n).map copyCode).reverse
    have huB : blockPower n n ∈ indexedIntersectionB := by
      have huInter : blockPower n n ∈
          indexedIntersectionA ⊓ indexedIntersectionB := by
        rw [indexedIntersectionA_inter_indexedIntersectionB]
        exact ⟨n, hn, rfl⟩
      exact huInter.2
    refine ⟨suffix, mem_indexedCopyDenominator_iff.mpr
      ⟨blockPower n n, huB, rfl⟩, ?_⟩
    refine ⟨n, n, hn, hn, ?_⟩
    simp [suffix, List.map_reverse, List.append_assoc]

/-- The quotient result itself is not indexed. -/
public theorem indexedCopy_quotient_notIndexed :
    ¬ is_Indexed (indexedCopyNumerator / indexedCopyDenominator) := by
  rw [indexedCopy_quotient_eq_diagonal]
  intro hmap
  exact indexedIntersectionH_notIndexed
    (Indexed_of_map_injective_Indexed_rev copyCode_injective
      indexedIntersectionH hmap)

/-- Indexed languages over the three-symbol copy alphabet are not closed under
arbitrary right quotient. -/
public theorem Indexed_notClosedUnderRightQuotient :
    ¬ ClosedUnderRightQuotient (α := CopyLetter) is_Indexed := by
  intro hclosed
  exact indexedCopy_quotient_notIndexed
    (hclosed indexedCopyNumerator indexedCopyDenominator
      indexedCopyNumerator_isIndexed indexedCopyDenominator_isIndexed)

private theorem Language.map_rightQuotient_of_injective
    {alpha beta : Type} {f : alpha → beta} (hf : Function.Injective f)
    (L R : Language alpha) :
    Language.map f (Language.rightQuotient L R) =
      Language.rightQuotient (Language.map f L) (Language.map f R) := by
  ext w
  constructor
  · rintro ⟨u, ⟨v, hvR, huvL⟩, rfl⟩
    exact ⟨v.map f, ⟨v, hvR, rfl⟩, ⟨u ++ v, huvL, by simp⟩⟩
  · rintro ⟨v, ⟨v₀, hv₀R, rfl⟩, ⟨z, hzL, hz⟩⟩
    have hz' : z.map f = w ++ v₀.map f := by simpa using hz
    obtain ⟨w₀, v₁, hz_eq, hw₀, hv₁⟩ := List.map_eq_append_iff.mp hz'
    have hv₁_eq : v₁ = v₀ := List.map_injective_iff.mpr hf hv₁
    subst v₁
    rw [← hw₀]
    exact ⟨w₀, ⟨v₀, hv₀R, by simpa [hz_eq] using hzL⟩, rfl⟩

/-- Nonclosure transports to every alphabet containing the three-symbol
witness alphabet. -/
public theorem Indexed_notClosedUnderRightQuotient_of_embedding
    {alpha : Type} (e : CopyLetter ↪ alpha) :
    ¬ ClosedUnderRightQuotient (α := alpha) is_Indexed := by
  intro hclosed
  apply Indexed_notClosedUnderRightQuotient
  intro L R hL hR
  have hq := hclosed (Language.map e L) (Language.map e R)
    (Indexed_of_map_injective_Indexed e.injective L hL)
    (Indexed_of_map_injective_Indexed e.injective R hR)
  rw [← Language.map_rightQuotient_of_injective e.injective] at hq
  exact Indexed_of_map_injective_Indexed_rev e.injective _ hq

/-- Indexed languages are not closed under arbitrary right quotient over every
finite alphabet with at least three symbols. -/
public theorem Indexed_notClosedUnderRightQuotient_of_card
    {alpha : Type} [Fintype alpha] (halpha : 3 ≤ Fintype.card alpha) :
    ¬ ClosedUnderRightQuotient (α := alpha) is_Indexed := by
  let piC : CopyLetter ≃ Fin (Fintype.card CopyLetter) :=
    Fintype.equivFin CopyLetter
  let piA : alpha ≃ Fin (Fintype.card alpha) := Fintype.equivFin alpha
  have hCA : Fintype.card CopyLetter ≤ Fintype.card alpha := by
    simpa using halpha
  exact Indexed_notClosedUnderRightQuotient_of_embedding
    (piC.toEmbedding.trans ((Fin.castLEEmb hCA).trans piA.symm.toEmbedding))

end IndexedIntersectionWitness
