module

public import Langlib.Examples.AbnPowN
public import Langlib.Examples.SingletonWord
public import Langlib.Utilities.LanguageOperations
import Langlib.Utilities.Tactics

@[expose]
public section

/-!
# The balanced-copy language of `abnPowM`

Let `A = {(a b^n)^m | n,m > 0}` and `B` be the two intersection
witnesses `abnPowM` and `abnAbStarPowPredN`.  Over a fresh three-letter
alphabet, define the numerator

`{ code(w) # reverse(code(w)) | w ∈ A }`

and the denominator `{ # reverse(code(v)) | v ∈ B }`.  The separator
makes the quotient split unique, so their right quotient is exactly the
encoded diagonal intersection.

Indexed-language membership facts live in
`Langlib.Classes.Indexed.Examples.AbnPowMCopy`.
-/

open List

/-- Three-letter alphabet used to separate the copied halves. -/
public inductive CopyLetter where
  | a | b | separator
deriving DecidableEq, Inhabited

public instance : Fintype CopyLetter where
  elems := {.a, .b, .separator}
  complete x := by cases x <;> simp

/-- Embed the binary witness alphabet into the copy alphabet. -/
public def copyCode : Bool → CopyLetter
  | false => .a
  | true => .b

public theorem copyCode_injective : Function.Injective copyCode := by
  intro x y h
  cases x <;> cases y <;> simp [copyCode] at h ⊢

/-- The numerator of the indexed right-quotient witness. -/
public def abnPowMCopy : Language CopyLetter := fun w =>
  ∃ n m : Nat, 0 < n ∧ 0 < m ∧
    w = (blockPower n m).map copyCode ++
      [.separator] ++ (blockPower n m).reverse.map copyCode

/-- Denominator of the indexed right-quotient counterexample. -/
public def abnPowMCopyDenominator : Language CopyLetter :=
  singletonWordLanguage [CopyLetter.separator] *
    (Language.map copyCode abnAbStarPowPredN).reverse

private lemma mem_abnPowMCopyDenominator_iff {w : List CopyLetter} :
    w ∈ abnPowMCopyDenominator ↔
      ∃ v ∈ abnAbStarPowPredN,
        w = [CopyLetter.separator] ++ (v.map copyCode).reverse := by
  constructor
  · intro hw
    rw [abnPowMCopyDenominator, Language.mul_def] at hw
    obtain ⟨left, hleft, right, hright, rfl⟩ := hw
    have hleft_eq : left = [CopyLetter.separator] := by
      change left = [CopyLetter.separator] at hleft
      exact hleft
    subst left
    change right.reverse ∈ Language.map copyCode abnAbStarPowPredN at hright
    obtain ⟨v, hv, hmap⟩ := hright
    have hright_eq : right = (v.map copyCode).reverse := by
      simpa using (congrArg List.reverse hmap).symm
    exact ⟨v, hv, by rw [hright_eq]⟩
  · rintro ⟨v, hv, rfl⟩
    rw [abnPowMCopyDenominator, Language.mul_def]
    refine ⟨[CopyLetter.separator], Set.mem_singleton _,
      (v.map copyCode).reverse, ?_, rfl⟩
    change ((v.map copyCode).reverse).reverse ∈
      Language.map copyCode abnAbStarPowPredN
    simp only [List.reverse_reverse]
    change ∃ u ∈ abnAbStarPowPredN, List.map copyCode u = List.map copyCode v
    exact ⟨v, hv, rfl⟩

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
      | cons x xs =>
          simp only [List.nil_append, List.cons_append] at h
          have hsep : CopyLetter.separator = x := (List.cons.inj h).1
          exact False.elim (hv (by simp [← hsep]))
  | cons x xs ih =>
      cases v with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h
          have hsep : x = CopyLetter.separator := (List.cons.inj h).1
          exact False.elim (hu (by simp [hsep]))
      | cons y ys =>
          simp only [List.cons_append] at h
          have hxy : x = y := (List.cons.inj h).1
          have htail := (List.cons.inj h).2
          subst y
          have hxs : CopyLetter.separator ∉ xs := by
            intro hm
            exact hu (by simp [hm])
          have hys : CopyLetter.separator ∉ ys := by
            intro hm
            exact hv (by simp [hm])
          obtain ⟨huv, hrs⟩ := ih hxs hys htail
          exact ⟨by rw [huv], hrs⟩

/-- The explicit quotient is exactly the encoded diagonal intersection. -/
public theorem abnPowMCopy_quotient_eq_abnPowN :
    abnPowMCopy / abnPowMCopyDenominator =
      Language.map copyCode abnPowN := by
  ext w
  constructor
  · rintro ⟨suffix, hsuffix, hnumerator⟩
    obtain ⟨v, hvB, rfl⟩ := mem_abnPowMCopyDenominator_iff.mp hsuffix
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
    have huA : blockPower n m ∈ abnPowM :=
      ⟨n, m, hn, hm, rfl⟩
    have huB : blockPower n m ∈ abnAbStarPowPredN := by
      simpa [hv] using hvB
    have huH : blockPower n m ∈ abnPowN := by
      rw [← abnPowM_inter_abnAbStarPowPredN]
      exact ⟨huA, huB⟩
    exact ⟨blockPower n m, huH, hwmap.symm⟩
  · rintro ⟨u, huH, rfl⟩
    rcases huH with ⟨n, hn, rfl⟩
    let suffix := [CopyLetter.separator] ++
      ((blockPower n n).map copyCode).reverse
    have huB : blockPower n n ∈ abnAbStarPowPredN := by
      have huInter : blockPower n n ∈
          abnPowM ⊓ abnAbStarPowPredN := by
        rw [abnPowM_inter_abnAbStarPowPredN]
        exact ⟨n, hn, rfl⟩
      exact huInter.2
    refine ⟨suffix, mem_abnPowMCopyDenominator_iff.mpr
      ⟨blockPower n n, huB, rfl⟩, ?_⟩
    refine ⟨n, n, hn, hn, ?_⟩
    simp [suffix, List.map_reverse, List.append_assoc]
