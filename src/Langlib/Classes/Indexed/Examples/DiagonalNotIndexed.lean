module

public import Langlib.Classes.Indexed.Examples.IntersectionWitness
public import Langlib.Classes.Indexed.Basics.Shrinking
import Mathlib.Data.List.SplitOn
import Mathlib.Data.List.Flatten

@[expose]
public section

/-!
# The diagonal intersection witness is not indexed

This file applies the one-factor indexed-language shrinking theorem to the
language `{(a b^n)^n | n > 0}`.  Splitting a word at `a` exposes all complete
`b`-runs.  A bounded factorization of a sufficiently large diagonal word has
one factor (including either fixed outer context) containing two `a`s, hence
an entire run `b^n`.  That run survives shrinking and fixes the parameter of
the resulting diagonal word, contradicting the strict decrease in length.
-/

open List

namespace IndexedIntersectionWitness

private def isA (b : Bool) : Bool := !b

private lemma splitOnA_replicate_true (n : Nat) :
    (replicate n true).splitOnP isA = [replicate n true] := by
  apply List.splitOnP_eq_single
  intro b hb
  have : b = true := by simpa using (List.eq_of_mem_replicate hb)
  subst b
  decide

private lemma splitOnA_blockPower (n m : Nat) :
    (blockPower n m).splitOnP isA =
      [] :: replicate m (replicate n true) := by
  induction m with
  | zero => simp [blockPower]
  | succ m ih =>
      rw [show blockPower n (m + 1) =
        blockPower n m ++ false :: replicate n true by
          simpa [blockPower, abBlock] using blockPower_add n m 1]
      rw [List.splitOnP_append_cons isA _ _ false (by decide), ih,
        splitOnA_replicate_true]
      simp [List.replicate_add]

/-- A complete run between two `a`s contributes one component to splitting
the surrounding word on `a`. -/
private lemma replicate_true_mem_tail_splitOnA_of_gap_infix {n : Nat}
    {w : List Bool}
    (hgap : (false :: replicate n true ++ [false]) <:+: w) :
    replicate n true ∈ (w.splitOnP isA).tail := by
  rcases hgap with ⟨pre, post, rfl⟩
  obtain ⟨head, tail, hpre⟩ :=
    List.exists_cons_of_ne_nil (List.splitOnP_ne_nil isA pre)
  rw [show pre ++ (false :: replicate n true ++ [false]) ++ post =
      pre ++ false :: (replicate n true ++ false :: post) by
        simp [List.append_assoc]]
  rw [List.splitOnP_append_cons isA pre _ false (by decide)]
  rw [List.splitOnP_append_cons isA (replicate n true) post false (by decide)]
  rw [splitOnA_replicate_true]
  simp [hpre]

/-- A complete `b^n` gap occurring inside a positive block power with common
run length `q` forces `n = q`. -/
private lemma gap_rigid_in_blockPower {n q m : Nat}
    (hgap : (false :: replicate n true ++ [false]) <:+: blockPower q m) :
    n = q := by
  have hmem := replicate_true_mem_tail_splitOnA_of_gap_infix hgap
  rw [splitOnA_blockPower] at hmem
  simp only [List.tail_cons, List.mem_replicate] at hmem
  exact (List.replicate_inj.mp hmem.2).1

private lemma exists_first_false_split {w : List Bool} (h : false ∈ w) :
    ∃ pre post : List Bool,
      w = pre ++ false :: post ∧ false ∉ pre := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
      by_cases hb : b = false
      · subst b
        exact ⟨[], w, rfl, by simp⟩
      · have hw : false ∈ w := by simpa [hb] using h
        obtain ⟨pre, post, hsplit, hpre⟩ := ih hw
        refine ⟨b :: pre, post, ?_, ?_⟩
        · simp [hsplit]
        · simp [hb, hpre]

private lemma exists_two_false_split {w : List Bool}
    (hcount : 2 ≤ w.count false) :
    ∃ pre middle post : List Bool,
      w = pre ++ false :: middle ++ false :: post ∧ false ∉ middle := by
  have hfalse : false ∈ w := List.count_pos_iff.mp (by omega)
  obtain ⟨pre, rest, hsplit, hpre⟩ := exists_first_false_split hfalse
  have hpreCount : pre.count false = 0 := List.count_eq_zero.mpr hpre
  have hrestCount : 0 < rest.count false := by
    rw [hsplit, List.count_append] at hcount
    simp only [hpreCount, Nat.zero_add, List.count_cons,
      beq_self_eq_true, if_true] at hcount
    omega
  obtain ⟨middle, post, hrest, hmiddle⟩ :=
    exists_first_false_split (List.count_pos_iff.mp hrestCount)
  refine ⟨pre, middle, post, ?_, hmiddle⟩
  rw [hsplit, hrest]
  simp [List.append_assoc]

/-- A factor of `(a b^n)^m` containing two `a`s contains a whole old
`a b^n a` gap. -/
private lemma gap_infix_of_factor_of_blockPower {n m : Nat} {factor : List Bool}
    (hfactor : factor <:+: blockPower n m)
    (hcount : 2 ≤ factor.count false) :
    (false :: replicate n true ++ [false]) <:+: factor := by
  obtain ⟨pre, middle, post, hsplit, hmiddle⟩ :=
    exists_two_false_split hcount
  have hmiddleTrue : middle = replicate middle.length true := by
    apply List.eq_replicate_of_mem
    intro b hb
    cases b <;> simp_all
  have hgapFactor :
      (false :: replicate middle.length true ++ [false]) <:+: factor := by
    refine ⟨pre, post, ?_⟩
    rw [hsplit, hmiddleTrue]
    simp [List.append_assoc]
  have hlength : middle.length = n :=
    gap_rigid_in_blockPower (hgapFactor.trans hfactor)
  simpa [hlength] using hgapFactor

private def contextFactor (w : List Bool) : List (List Bool) :=
  if w = [] then [] else [w]

@[simp] private lemma contextFactor_flatten (w : List Bool) :
    (contextFactor w).flatten = w := by
  by_cases hw : w = [] <;> simp [contextFactor, hw]

private lemma contextFactor_length_le_one (w : List Bool) :
    (contextFactor w).length ≤ 1 := by
  by_cases hw : w = [] <;> simp [contextFactor, hw]

private lemma eq_context_of_mem_contextFactor {factor w : List Bool}
    (h : factor ∈ contextFactor w) : factor = w := by
  by_cases hw : w = []
  · simp [contextFactor, hw] at h
  · simpa [contextFactor, hw] using h

private lemma count_false_flatten_le_length {parts : List (List Bool)}
    (hparts : ∀ part ∈ parts, part.count false ≤ 1) :
    parts.flatten.count false ≤ parts.length := by
  induction parts with
  | nil => simp
  | cons part parts ih =>
      simp only [List.flatten_cons, List.count_append, List.length_cons]
      have hpart := hparts part (by simp)
      have htail : ∀ piece ∈ parts, piece.count false ≤ 1 := by
        intro piece hpiece
        exact hparts piece (by simp [hpiece])
      have := ih htail
      omega

private lemma exists_factor_with_two_false {parts : List (List Bool)}
    (hcount : parts.length < parts.flatten.count false) :
    ∃ factor ∈ parts, 2 ≤ factor.count false := by
  by_contra hnone
  have hparts : ∀ part ∈ parts, part.count false ≤ 1 := by
    intro part hpart
    by_contra hnot
    have htwo : 2 ≤ part.count false := by omega
    exact hnone ⟨part, hpart, htwo⟩
  have := count_false_flatten_le_length hparts
  omega

private lemma retained_get_mem {α : Type} {kept factors : List α}
    {i : Fin factors.length} (h : MarkedHigman.RetainsAt kept factors i) :
    factors.get i ∈ kept := by
  rcases h with ⟨marked, _hsub, herase, hmarked⟩
  rw [← herase]
  change factors.get i ∈ marked.map Prod.fst
  exact List.mem_map_of_mem hmarked

private lemma factor_infix_flatten_of_mem {α : Type} {factor : List α}
    {parts : List (List α)} (h : factor ∈ parts) :
    factor <:+: parts.flatten := by
  obtain ⟨pre, post, hparts⟩ := List.mem_iff_append.mp h
  refine ⟨pre.flatten, post.flatten, ?_⟩
  rw [hparts]
  simp [List.append_assoc]

private lemma flatten_length_lt_of_proper_nonempty_sublist
    {kept factors : List (List Bool)} (hsub : kept <+ factors)
    (hproper : kept.length < factors.length)
    (hne : ∀ factor ∈ factors, factor ≠ []) :
    kept.flatten.length < factors.flatten.length := by
  induction hsub with
  | slnil => simp at hproper
  | cons head hsub ih =>
      have hfactorPos : 0 < head.length :=
        List.length_pos_iff.mpr (hne head (by simp))
      have hflatLe := hsub.flatten.length_le
      simp only [List.flatten_cons, List.length_append]
      omega
  | cons₂ head hsub ih =>
      have htailProper := hproper
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at htailProper
      have htailLt := ih htailProper (fun piece hpiece =>
        hne piece (List.mem_cons_of_mem head hpiece))
      simp only [List.flatten_cons, List.length_append]
      omega

private lemma length_blockPower (n m : Nat) :
    (blockPower n m).length = m * (n + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp [blockPower, abBlock, ih, Nat.succ_mul]
      omega

/-- The diagonal language `{(a b^n)^n | n > 0}` is not indexed. -/
public theorem indexedIntersectionH_notIndexed :
    ¬ is_Indexed indexedIntersectionH := by
  intro hIndexed
  obtain ⟨k, hk, hshrink⟩ :=
    exists_indexedScopedOneFactorShrinking hIndexed
  let n := k + 1
  have hn : 0 < n := by simp [n]
  have hn_gt_k : k < n := by simp [n]
  have hword : blockPower n n ∈ indexedIntersectionH :=
    ⟨n, hn, rfl⟩
  have hlong : k ≤ (blockPower n n).length := by
    rw [length_blockPower]
    have hnle : n ≤ n * (n + 1) :=
      Nat.le_mul_of_pos_right n (by omega)
    omega
  obtain ⟨shrinking⟩ := hshrink (blockPower n n) hword hlong
  let parts :=
    contextFactor shrinking.leftContext ++
      (shrinking.factors ++ contextFactor shrinking.rightContext)
  have hpartsFlatten : parts.flatten = blockPower n n := by
    dsimp [parts]
    simp only [List.flatten_append, contextFactor_flatten]
    simpa [List.append_assoc] using shrinking.word_eq.symm
  have hpartsLength : parts.length ≤ k := by
    dsimp [parts]
    simp only [List.length_append]
    have hleft := contextFactor_length_le_one shrinking.leftContext
    have hright := contextFactor_length_le_one shrinking.rightContext
    have hmiddle : shrinking.factors.length ≤ k - 2 := shrinking.length_le
    have htwo : 2 ≤ shrinking.factors.length := shrinking.two_le
    calc
      (contextFactor shrinking.leftContext).length +
          (shrinking.factors.length +
            (contextFactor shrinking.rightContext).length) ≤
          1 + ((k - 2) + 1) :=
        Nat.add_le_add hleft (Nat.add_le_add hmiddle hright)
      _ ≤ k := by omega
  have hpartsCount : parts.flatten.count false = n := by
    rw [hpartsFlatten, count_false_blockPower]
  have hpartsShort : parts.length < parts.flatten.count false := by
    rw [hpartsCount]
    omega
  obtain ⟨factor, hfactorParts, hfactorCount⟩ :=
    exists_factor_with_two_false hpartsShort
  have hfactorOld : factor <:+: blockPower n n := by
    have hinfix := factor_infix_flatten_of_mem hfactorParts
    rwa [hpartsFlatten] at hinfix
  have hgapFactor :
      (false :: replicate n true ++ [false]) <:+: factor :=
    gap_infix_of_factor_of_blockPower hfactorOld hfactorCount
  have hfactorCases :
      factor ∈ contextFactor shrinking.leftContext ∨
        factor ∈ shrinking.factors ∨
        factor ∈ contextFactor shrinking.rightContext := by
    simpa only [parts, List.mem_append] using hfactorParts
  obtain ⟨kept, hkeptSublist, hkeptProper, hkeptLanguage,
      hfactorKeptWord⟩ :
      ∃ kept : List (List Bool),
        kept <+ shrinking.factors ∧
        kept.length < shrinking.factors.length ∧
        shrinking.leftContext ++ kept.flatten ++ shrinking.rightContext ∈
          indexedIntersectionH ∧
        factor <:+:
          (shrinking.leftContext ++ kept.flatten ++ shrinking.rightContext) := by
    rcases hfactorCases with hleft | hmiddle | hright
    · have hiLt : 0 < shrinking.factors.length :=
        lt_of_lt_of_le (by decide) shrinking.two_le
      let i : Fin shrinking.factors.length := ⟨0, hiLt⟩
      obtain ⟨kept, hretains, hproper, hlanguage⟩ := shrinking.shrink i
      refine ⟨kept, hretains.sublist, hproper, hlanguage, ?_⟩
      have hfactorEq := eq_context_of_mem_contextFactor hleft
      rw [hfactorEq]
      exact ⟨[], kept.flatten ++ shrinking.rightContext, by
        simp [List.append_assoc]⟩
    · obtain ⟨i, hi⟩ := List.get_of_mem hmiddle
      obtain ⟨kept, hretains, hproper, hlanguage⟩ := shrinking.shrink i
      refine ⟨kept, hretains.sublist, hproper, hlanguage, ?_⟩
      have hfactorMem : factor ∈ kept := by
        have hget := retained_get_mem hretains
        rwa [hi] at hget
      have hfactorMiddle := factor_infix_flatten_of_mem hfactorMem
      exact hfactorMiddle.trans
        ⟨shrinking.leftContext, shrinking.rightContext, rfl⟩
    · have hiLt : 0 < shrinking.factors.length :=
        lt_of_lt_of_le (by decide) shrinking.two_le
      let i : Fin shrinking.factors.length := ⟨0, hiLt⟩
      obtain ⟨kept, hretains, hproper, hlanguage⟩ := shrinking.shrink i
      refine ⟨kept, hretains.sublist, hproper, hlanguage, ?_⟩
      have hfactorEq := eq_context_of_mem_contextFactor hright
      rw [hfactorEq]
      exact ⟨shrinking.leftContext ++ kept.flatten, [], by
        simp [List.append_assoc]⟩
  have hflattenProper :
      kept.flatten.length < shrinking.factors.flatten.length :=
    flatten_length_lt_of_proper_nonempty_sublist hkeptSublist hkeptProper
      shrinking.factors_nonempty
  have hnewLengthLt :
      (shrinking.leftContext ++ kept.flatten ++ shrinking.rightContext).length <
        (blockPower n n).length := by
    have holdLength := congrArg List.length shrinking.word_eq
    simp only [List.length_append] at holdLength ⊢
    omega
  have hgapNew :
      (false :: replicate n true ++ [false]) <:+:
        (shrinking.leftContext ++ kept.flatten ++ shrinking.rightContext) :=
    hgapFactor.trans hfactorKeptWord
  obtain ⟨q, hq, hshape⟩ := hkeptLanguage
  rw [hshape] at hgapNew
  have hnq : n = q := gap_rigid_in_blockPower hgapNew
  subst q
  exact (Nat.ne_of_lt hnewLengthLt) (congrArg List.length hshape)

end IndexedIntersectionWitness
