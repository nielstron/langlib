module

public import Langlib.Examples.AbnAbStarPowPredN
import Mathlib.Tactic

@[expose]
public section

/-!
# The diagonal language `{(a b^n)^n | n >= 1}`

The two shared positive block witnesses `abnPowM` and
`abnAbStarPowPredN` meet in exactly this language.  Language-class membership
facts live in the corresponding files under `Langlib.Classes`.
-/

open List

/-- The language `{(a b^n)^n | n >= 1}`. -/
public def abnPowN : Language Bool := fun w =>
  ∃ n : Nat, 0 < n ∧ w = blockPower n n

/-- Number of initial `b`s after discarding the first letter of a word. -/
private def firstBRun (w : List Bool) : Nat :=
  (w.tail.takeWhile id).length

private lemma takeWhile_id_replicate_true (n : Nat) :
    (replicate n true).takeWhile id = replicate n true := by
  induction n with
  | zero => simp
  | succ n ih => simp [replicate_succ, ih]

private lemma takeWhile_id_replicate_true_false (n : Nat) (w : List Bool) :
    (replicate n true ++ false :: w).takeWhile id = replicate n true := by
  induction n with
  | zero => simp
  | succ n ih => simp [replicate_succ, ih]

private lemma firstBRun_blockPower (n m : Nat) (hm : 0 < m) :
    firstBRun (blockPower n m) = n := by
  cases m with
  | zero => omega
  | succ m =>
      cases m with
      | zero => simp [firstBRun, blockPower, abBlock]
      | succ k =>
          simp [firstBRun, blockPower, abBlock]

private lemma firstBRun_abBlock_varyingBlocks (n : Nat) (ns : List Nat) :
    firstBRun (abBlock n ++ varyingBlocks ns) = n := by
  cases ns with
  | nil => simp [firstBRun, abBlock, varyingBlocks]
  | cons q qs =>
      simp [firstBRun, abBlock, varyingBlocks]

/-- The two positive witness languages meet in exactly `{(a b^n)^n | n >= 1}`. -/
public theorem abnPowM_inter_abnAbStarPowPredN :
    abnPowM ⊓ abnAbStarPowPredN = abnPowN := by
  ext w
  constructor
  · rintro ⟨⟨n, m, hn, hm, hw⟩, q, qs, hq, hlen, hshape⟩
    have hwords : blockPower n m = abBlock q ++ varyingBlocks qs := hw.symm.trans hshape
    have hm_q : m = q := by
      have hc := congrArg (fun x : List Bool => x.count false) hwords
      simp only [count_false_blockPower, List.count_append,
        count_false_abBlock, count_false_varyingBlocks] at hc
      omega
    have hn_q : n = q := by
      have hr := congrArg firstBRun hwords
      simpa [firstBRun_blockPower n m hm,
        firstBRun_abBlock_varyingBlocks q qs] using hr
    refine ⟨n, hn, ?_⟩
    calc
      w = blockPower n m := hw
      _ = blockPower n n := by rw [hm_q, hn_q]
  · rintro ⟨n, hn, rfl⟩
    refine ⟨⟨n, n, hn, hn, rfl⟩, n, replicate (n - 1) n, hn, ?_, ?_⟩
    · simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))]
    · cases n with
      | zero => omega
      | succ k => simp [varyingBlocks_replicate]
