module

public import Langlib.Automata.FiniteState.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Unary regular languages

A language over the one-letter alphabet `Unit` is regular exactly when membership depends
ultimately periodically on the word length.

The forward direction follows the unique run of a finite DFA until two states repeat.  The reverse
direction builds a DFA whose states consist of the finite prefix before the periodic regime and one
cycle of residues after it.
-/

namespace Language

/-- Membership in a unary language is ultimately periodic as a predicate of the word length. -/
public def LengthUltimatelyPeriodic (L : Language Unit) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
    (List.replicate n () ∈ L ↔ List.replicate (n + p) () ∈ L)

private lemma eval_replicate_add {σ : Type*} (M : DFA Unit σ) (m n : ℕ) :
    M.eval (List.replicate (m + n) ()) =
      M.evalFrom (M.eval (List.replicate m ())) (List.replicate n ()) := by
  rw [List.replicate_add]
  exact M.evalFrom_of_append M.start _ _

private def canonicalLength (N p n : ℕ) : ℕ :=
  if n < N then n else N + (n - N) % p

private lemma canonicalLength_eq_of_lt {N p n : ℕ} (hn : n < N) :
    canonicalLength N p n = n := by
  simp [canonicalLength, hn]

private lemma canonicalLength_eq_of_le {N p n : ℕ} (hn : N ≤ n) :
    canonicalLength N p n = N + (n - N) % p := by
  simp [canonicalLength, not_lt.mpr hn]

private lemma canonicalLength_lt_add {N p n : ℕ} (hp : 0 < p) :
    canonicalLength N p n < N + p := by
  by_cases hn : n < N
  · rw [canonicalLength_eq_of_lt hn]
    omega
  · rw [canonicalLength_eq_of_le (not_lt.mp hn)]
    exact Nat.add_lt_add_left (Nat.mod_lt _ hp) N

private lemma canonicalLength_succ {N p n : ℕ} :
    canonicalLength N p (canonicalLength N p n + 1) =
      canonicalLength N p (n + 1) := by
  by_cases hn : n < N
  · rw [canonicalLength_eq_of_lt hn]
  · have hnN : N ≤ n := not_lt.mp hn
    rw [canonicalLength_eq_of_le hnN,
      canonicalLength_eq_of_le (by omega : N ≤ N + (n - N) % p + 1),
      canonicalLength_eq_of_le (by omega : N ≤ n + 1)]
    have hleft : N + (n - N) % p + 1 - N = (n - N) % p + 1 := by
      omega
    have hright : n + 1 - N = (n - N) + 1 := by
      omega
    rw [hleft, hright, Nat.mod_add_mod]

/-- The finite DFA induced by an ultimately periodic unary membership predicate. -/
private def periodicDFA (L : Language Unit) (N p : ℕ) (hp : 0 < p) :
    DFA Unit (Fin (N + p)) where
  step q _ :=
    ⟨canonicalLength N p (q.val + 1), canonicalLength_lt_add hp⟩
  start := ⟨0, by omega⟩
  accept := {q | List.replicate q.val () ∈ L}

private lemma periodicDFA_eval_replicate
    (L : Language Unit) (N p : ℕ) (hp : 0 < p) (n : ℕ) :
    (periodicDFA L N p hp).eval (List.replicate n ()) =
      ⟨canonicalLength N p n, canonicalLength_lt_add hp⟩ := by
  induction n with
  | zero =>
      apply Fin.ext
      simp [DFA.eval, periodicDFA, canonicalLength]
      omega
  | succ n ih =>
      rw [List.replicate_add]
      simp only [List.replicate_one, DFA.eval_append_singleton, ih]
      apply Fin.ext
      exact canonicalLength_succ

private lemma mem_replicate_add_mul_iff
    {L : Language Unit} {N p : ℕ}
    (hperiod : ∀ n, N ≤ n →
      (List.replicate n () ∈ L ↔ List.replicate (n + p) () ∈ L))
    {n : ℕ} (hn : N ≤ n) :
    ∀ k, List.replicate n () ∈ L ↔ List.replicate (n + k * p) () ∈ L
  | 0 => by simp
  | k + 1 => by
      refine (mem_replicate_add_mul_iff hperiod hn k).trans ?_
      simpa [Nat.succ_mul, Nat.add_assoc] using
        hperiod (n + k * p) (by omega)

private lemma mem_canonicalLength_iff
    {L : Language Unit} {N p n : ℕ}
    (hperiod : ∀ n, N ≤ n →
      (List.replicate n () ∈ L ↔ List.replicate (n + p) () ∈ L)) :
    List.replicate (canonicalLength N p n) () ∈ L ↔
      List.replicate n () ∈ L := by
  by_cases hn : n < N
  · rw [canonicalLength_eq_of_lt hn]
  · have hnN : N ≤ n := not_lt.mp hn
    let r := (n - N) % p
    let k := (n - N) / p
    have hdecomp : n = (N + r) + k * p := by
      have hmod : r + k * p = n - N := by
        simpa [r, k, Nat.mul_comm] using Nat.mod_add_div (n - N) p
      omega
    rw [canonicalLength_eq_of_le hnN]
    change List.replicate (N + r) () ∈ L ↔ List.replicate n () ∈ L
    rw [hdecomp]
    exact mem_replicate_add_mul_iff hperiod (by omega) k

private lemma unitList_eq_replicate (w : List Unit) :
    w = List.replicate w.length () := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      cases a
      simpa only [List.length_cons, List.replicate_succ] using
        congrArg (fun x => () :: x) ih

/-- A unary language is regular exactly when its accepted set of lengths is ultimately periodic. -/
public theorem isRegular_iff_lengthUltimatelyPeriodic (L : Language Unit) :
    L.IsRegular ↔ L.LengthUltimatelyPeriodic := by
  constructor
  · intro hregular
    obtain ⟨σ, hσ, M, hM⟩ := hregular
    let stateAt : Fin (Fintype.card σ + 1) → σ :=
      fun n => M.eval (List.replicate n.val ())
    obtain ⟨i, j, hij, hstate⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt stateAt (by simp)
    have hval : i.val ≠ j.val := Fin.val_ne_of_ne hij
    have buildPeriod :
        ∀ {i j : Fin (Fintype.card σ + 1)}, i.val < j.val →
          stateAt i = stateAt j → L.LengthUltimatelyPeriodic := by
      intro i j hlt heq
      refine ⟨i.val, j.val - i.val, Nat.sub_pos_of_lt hlt, ?_⟩
      intro n hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      have hj : j.val = i.val + (j.val - i.val) := by omega
      have hrun :
          M.eval (List.replicate (i.val + k) ()) =
            M.eval (List.replicate ((i.val + k) + (j.val - i.val)) ()) := by
        calc
          M.eval (List.replicate (i.val + k) ()) =
              M.evalFrom (M.eval (List.replicate i.val ()))
                (List.replicate k ()) := eval_replicate_add M i.val k
          _ = M.evalFrom (M.eval (List.replicate j.val ()))
                (List.replicate k ()) := by
                  rw [show M.eval (List.replicate i.val ()) = stateAt i by rfl,
                    show M.eval (List.replicate j.val ()) = stateAt j by rfl, heq]
          _ = M.eval (List.replicate (j.val + k) ()) :=
                (eval_replicate_add M j.val k).symm
          _ = M.eval (List.replicate ((i.val + k) + (j.val - i.val)) ()) := by
                rw [hj]
                congr 2
                omega
      rw [← hM]
      simp only [DFA.mem_accepts]
      rw [hrun]
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · exact buildPeriod hlt hstate
    · exact buildPeriod hgt hstate.symm
  · rintro ⟨N, p, hp, hperiod⟩
    refine ⟨Fin (N + p), inferInstance, periodicDFA L N p hp, ?_⟩
    ext w
    rw [unitList_eq_replicate w]
    rw [DFA.mem_accepts, periodicDFA_eval_replicate]
    change List.replicate (canonicalLength N p _) () ∈ L ↔
      List.replicate _ () ∈ L
    exact mem_canonicalLength_iff hperiod

end Language
